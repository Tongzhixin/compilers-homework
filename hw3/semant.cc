#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"

extern int semant_debug;
extern char *curr_filename;

static ostream& error_stream = cerr;
static int semant_errors = 0;
static Decl curr_decl = 0;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name, type
ObjectEnvironment objectEnv;

typedef std::map<Symbol, bool> InstallFuncMap;
InstallFuncMap installFuncMap;

typedef std::map<Symbol, Symbol> CallMap;
CallMap callMap;

typedef std::map<Symbol, Symbol> GlobalVarMap;
GlobalVarMap globalVarMap;

typedef std::map<Symbol, Symbol> LocalScopeVarMap;
LocalScopeVarMap localVarMap;

typedef std::vector<Symbol> FuncParameter;
typedef std::map<Symbol, FuncParameter> FuncParameterMap;
FuncParameterMap funcParaMap;

///////////////////////////////////////////////
// helper func
///////////////////////////////////////////////


static ostream& semant_error() {
    semant_errors++;
    return error_stream;
}

static ostream& semant_error(tree_node *t) {
    error_stream << t->get_line_number() << ": ";
    return semant_error();
}

static ostream& internal_error(int lineno) {
    error_stream << "FATAL:" << lineno << ": ";
    return error_stream;
}

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////

static Symbol 
    Int,
    Float,
    String,
    Bool,
    Void,
    Main,
    print
    ;

bool isValidCallName(Symbol type) {
    return type != (Symbol)print;
}

bool isValidTypeName(Symbol type) {
    return type != Void;
}

//
// Initializing the predefined symbols.
//

static void initialize_constants(void) {
    // 4 basic types and Void type
    Bool        = idtable.add_string("Bool");
    Int         = idtable.add_string("Int");
    String      = idtable.add_string("String");
    Float       = idtable.add_string("Float");
    Void        = idtable.add_string("Void");  
    // Main function
    Main        = idtable.add_string("main");

    // classical function to print things, so defined here for call.
    print        = idtable.add_string("printf");
}

/*
    TODO :
    you should fill the following function defines, so that semant() can realize a semantic 
    analysis in a recursive way. 
    Of course, you can add any other functions to help.
*/

static bool sameType(Symbol name1, Symbol name2) {
    return strcmp(name1->get_string(), name2->get_string()) == 0;
}

static void install_calls(Decls decls) {
    for (int i=decls->first(); decls->more(i); i=decls->next(i)) {
        Symbol type = decls->nth(i)->getType();
        Symbol name = decls->nth(i)->getName();
        if (decls->nth(i)->isCallDecl()) {
            if (callMap[name] != NULL) {
                semant_error(decls->nth(i)) << "Function " << name << " has been previously defined." << std::endl;
            } 
            if (!isValidCallName(name)) {
                semant_error(decls->nth(i)) << "Function printf cannot have a name as printf" << std::endl;
            }
            if (type != Int && type != String && type != Void && type != Float && type != Bool) {
                semant_error(decls->nth(i)) << "Function returnType error." << std::endl;
            }             
            //installFuncMap[name] = false;
            callMap[name] = type;
            //decls->nth(i)->check();
        }
    }
}

static void install_globalVars(Decls decls) {
    for (int i=decls->first(); decls->more(i); i=decls->next(i)) {
        Symbol type = decls->nth(i)->getType();
        Symbol name = decls->nth(i)->getName();
        if (!decls->nth(i)->isCallDecl()) {
            if (globalVarMap[name] != NULL) {
                semant_error(decls->nth(i)) << "Global variable redefined." << std::endl;
            }
            if (name == print) {
                semant_error(decls->nth(i)) << "Variable cannot have a name as printf" << std::endl;
            }
            if (type == Void) {
                semant_error(decls->nth(i)) << "Var " << name << " cannot be  Void type. Void can just be used as return type." << std::endl;
            } 
            globalVarMap[name] = type;
        }
    }
}

static void check_calls(Decls decls) {
    objectEnv.enterscope();
    for (int i=decls->first(); decls->more(i); i=decls->next(i)) {
        if (decls->nth(i)->isCallDecl()) {
            decls->nth(i)->check();
            localVarMap.clear();
        }
    }
    objectEnv.exitscope();
}

static void check_main() {
    if (callMap[Main] == nullptr) {
        semant_error() << "main is not defined." << std::endl;
    }
}

void VariableDecl_class::check() {
    Symbol type = this->getType();
    Symbol name = this->getName();
    if (type == Void) {
        semant_error() << "Var" <<  name << "can not be Void type." << std::endl;
    } else {
        localVarMap[name] = type;
        objectEnv.addid(name, &type);
    }
}
void StmtBlock_class::checkBreakContinue() {
    Stmts stmts = this->getStmts();
    for (int i=stmts->first(); stmts->more(i); i=stmts->next(i)) {
        if (stmts->nth(i)->isSafe()) {
            continue;
        } else  {
            stmts->nth(i)->checkBreakContinue();
        } 
    }
}
void IfStmt_class::checkBreakContinue() {
    this->thenexpr->checkBreakContinue();
    this->elseexpr->checkBreakContinue();
}
void BreakStmt_class::checkBreakContinue() {
    semant_error(this) << "break must be used in a loop sentence" << std::endl;
}
void ContinueStmt_class::checkBreakContinue() {
    semant_error(this) << "continue must be used in a loop sentence" << std::endl;
}


void CallDecl_class::check() {
    Symbol callName = this->getName();
    Variables paras = this->getVariables();
    Symbol returnType = this->getType();
    StmtBlock body = this->getBody();

    objectEnv.enterscope();

    FuncParameter funcParameter;
    for (int i=paras->first(); paras->more(i); i=paras->next(i)) {
        Symbol paraName = paras->nth(i)->getName();
        Symbol paraType = paras->nth(i)->getType();
            
        /* No need to check paras' type because of syntax rules */

        // check if there are duplicated paras
        if (objectEnv.lookup(name) != NULL) {
            semant_error(this) << "Function " << callName <<  "'s parameter has a duplicate name " << name << std::endl;
        }
        objectEnv.addid(paraName, &paraType);
        localVarMap[paraName] = paraType;
        funcParameter.push_back(paraType);
    }
    funcParaMap[callName] = funcParameter;
        // main function should not have any paras
    if (callName == Main && paras->len() != 0) {
        semant_error(this) << "main function should not have parameter" << std::endl;
    } else if (callMap[Main] != Void) {
        semant_error(this) << "main function should have return Void type." << std::endl;
    }

    // check stmtBlock
    // 1. check variableDecls
    VariableDecls varDecls = body->getVariableDecls();
    for (int i=varDecls->first(); varDecls->more(i); i=varDecls->next(i)) {
        varDecls->nth(i)->check();
    }

    // 2. check stmts
    body->check(returnType);
    if (!body->isReturn()) {
        semant_error(this) << "Function " << name << " must have an overall return statement." << std::endl;
    }
    body->checkBreakContinue();

    objectEnv.exitscope();
}

void StmtBlock_class::check(Symbol type) {
    Stmts stmts = this->getStmts(); 
    for (int j=stmts->first(); stmts->more(j); j=stmts->next(j)) {
        stmts->nth(j)->check(type);
    }
}

void IfStmt_class::check(Symbol type) {
    Expr condition = this->getCondition();
    StmtBlock thenexpr = this->getThen();
    StmtBlock elseexpr = this->getElse();
    
    // If condition should be Bool
    Symbol conditionType = condition->checkType();
    if (conditionType != Bool) {
        semant_error(this) << "condition type should be Bool, but found" << conditionType << std::endl;
    }

    // check thenexpr and elseexpr
    thenexpr->check(type);
    elseexpr->check(type);
}

void WhileStmt_class::check(Symbol type) {
    Expr condition = this->getCondition();
    StmtBlock body = this->getBody();

    // While condition should be Bool
    Symbol conditionType = condition->checkType();
    if (conditionType != Bool) {
        semant_error(this) << "condition type should be Bool, but found" << conditionType << std::endl;
    }

    // check while body
    body->check(type);
}

void ForStmt_class::check(Symbol type) {
    Expr init = this->getInit();
    Expr condition = this->getCondition();
    Expr loop = this->getLoop();
    StmtBlock body = this->getBody();

    init->checkType();
    loop->checkType();
    // For condition should be Bool
    Symbol conditionType = condition->checkType();
    if (conditionType != Bool) {
        semant_error(this) << "condition type should be Bool, but found" << conditionType << std::endl;
    }

    // check For body
    body->check(type);
    
}

void ReturnStmt_class::check(Symbol type) {
    Expr value = this->getValue();

    Symbol valueType = value->checkType();
    if (value->is_empty_Expr()) {
        if (type != Void) {
            semant_error(this) << "need return " << type << " ,not" << "Void" << std::endl;
        }
    } else {
        if (type != valueType) {
            semant_error(this) << "need return " << type << ",not" << valueType << std::endl;
        }
    }
}

void ContinueStmt_class::check(Symbol type) {

}

void BreakStmt_class::check(Symbol type) {

}

Symbol Call_class::checkType(){
    Symbol name = this->getName();
    Actuals actuals = this->getActuals();
    unsigned int j = 0;
    
    if (name == print) {
        if (actuals->len() == 0) {
            semant_error(this) << "printf() must has at last one parameter of type String." << endl;
            this->setType(Void);
            return type;
        }
        Symbol sym = actuals->nth(actuals->first())->checkType();
        if (sym != String) {
            semant_error(this) << "printf()'s first parameter must be of type String." << endl;
            this->setType(Void);
            return type;
        }
        this->setType(Void);
        return type;
    }

    if (actuals->len() > 0){
        if (actuals->len() != int(funcParaMap[name].size())) {
            semant_error(this) << "Wrong number of paras" << endl;
        }
        for (int i=actuals->first(); actuals->more(i) && j<funcParaMap[name].size(); i=actuals->next(i)) {
            Symbol sym = actuals->nth(i)->checkType();
            // check function call's paras fit funcdecl's paras
            if (sym != funcParaMap[name][j]) {
                semant_error(this) << "Function " << name << ", type " << sym << " does not conform to declared type " << funcParaMap[name][j] << endl;
            }
            ++j;      
        }
    }
    
    if (callMap[name] == NULL) {
        semant_error(this) << "Object " << name << " has not been defined" << endl;
        this->setType(Void);
        return type;
    } 
    this->setType(callMap[name]);
    return type;
}

Symbol Actual_class::checkType(){
    Symbol exprType = this->expr->checkType();
    this->setType(exprType);
    return exprType;
}

Symbol Assign_class::checkType(){
    if (objectEnv.lookup(lvalue) == NULL && globalVarMap[lvalue] == NULL) {
        semant_error(this) << "Undefined value" << endl;
    } 
    Symbol lvalueType = localVarMap[lvalue];
    Symbol valueType = this->value->checkType();
    if (lvalueType != valueType) {
        semant_error(this) << "left value type is not match with right type." << std::endl;
    }
    this->setType(valueType);
    return this->type;
}

Symbol Add_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();

    if (e1Type == e2Type) {
        if ( e1Type != Int && e1Type != Float ) {
            semant_error(this) << "value should be int and float type. now the type is" << e1Type << std::endl;
            this->setType(Float);
            return type;
        }
    } else if ((e1Type == Float && e2Type == Int)||(e1Type == Int && e2Type == Float)) {
        this->setType(Float);
        return type;
    } else {
        semant_error(this) << "two value should have same type or a int and another float." << std::endl;
        this->setType(Float);
        return type;
    }

    this->setType(e1Type);
    return this->type;
}

Symbol Minus_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();

    if (e1Type == e2Type) {
        if ( e1Type != Int && e1Type != Float ) {
            semant_error(this) << "value should be int and float type. now the type is" << e1Type << std::endl;
            this->setType(Float);
            return type;
        }
    } else if ((e1Type == Float && e2Type == Int)||(e1Type == Int && e2Type == Float)) {
        this->setType(Float);
        return type;
    } else {
        semant_error(this) << "two value should have same type or a int and another float." << std::endl;
        this->setType(Float);
        return type;
    }

    this->setType(e1Type);
    return this->type;
}

Symbol Multi_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();

    if (e1Type == e2Type) {
        if ( e1Type != Int && e1Type != Float ) {
            semant_error(this) << "value should be int and float type. now the type is" << e1Type << std::endl;
            this->setType(Float);
            return type;
        }
    } else if ((e1Type == Float && e2Type == Int)||(e1Type == Int && e2Type == Float)) {
        this->setType(Float);
        return type;
    } else {
        semant_error(this) << "two value should have same type or a int and another float." << std::endl;
        this->setType(Float);
        return type;
    }

    this->setType(e1Type);
    return this->type;
}

Symbol Divide_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();

    if (e1Type == e2Type) {
        if ( e1Type != Int && e1Type != Float ) {
            semant_error(this) << "value should be int and float type. now the type is" << e1Type << std::endl;
            this->setType(Float);
            return type;
        }
    } else if ((e1Type == Float && e2Type == Int)||(e1Type == Int && e2Type == Float)) {
        this->setType(Float);
        return type;
    } else {
        semant_error(this) << "two value should have same type or a int and another float." << std::endl;
        this->setType(Float);
        return type;
    }

    this->setType(e1Type);
    return this->type;
}

Symbol Mod_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();

    if (e1Type == e2Type) {
        if ( e1Type != Int && e1Type != Float ) {
            semant_error(this) << "value should be int and float type. now the type is" << e1Type << std::endl;
            this->setType(Float);
            return type;
        }
    } else if ((e1Type == Float && e2Type == Int)||(e1Type == Int && e2Type == Float)) {
        this->setType(Float);
        return type;
    } else {
        semant_error(this) << "two value should have same type or a int and another float." << std::endl;
        this->setType(Float);
        return type;
    }

    this->setType(e1Type);
    return this->type;
}

Symbol Neg_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    if (e1Type != Int && e1Type != Float) {
        semant_error(this)<<"neg expr should have a Int or Float value"<<endl;
        this->setType(Int);
        return this->type;
    }
    this->setType(e1Type);
    return this->type;
}

Symbol Lt_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();
    if (e1Type == e2Type) {
        if ( e1Type != Int && e1Type != Float ) {
            semant_error(this) << "Lt expr value should be int and float type. now the type is" << e1Type << std::endl;
        }
    } else if (!(e1Type == Float && e2Type == Int) && !(e1Type == Int && e2Type == Float)) {
        semant_error(this) << "Lt expr two value should have same type or a int and another float." << std::endl;
    }
    this->setType(Bool);
    return this->type;
}

Symbol Le_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();
    if (e1Type == e2Type) {
        if ( e1Type != Int && e1Type != Float ) {
            semant_error(this) << "Lt expr value should be int and float type. now the type is" << e1Type << std::endl;
        }
    } else if (!(e1Type == Float && e2Type == Int) && !(e1Type == Int && e2Type == Float)) {
        semant_error(this) << "Lt expr two value should have same type or a int and another float." << std::endl;
    }
    this->setType(Bool);
    return this->type;
}

Symbol Equ_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();
    if (e1Type == e2Type) {
        if ( e1Type != Int && e1Type != Float && e1Type != Bool) {
            semant_error(this) << "Lt expr value should be int and float and bool type. now the type is" << e1Type << std::endl;
        }
    } else if (!(e1Type == Float && e2Type == Int) && !(e1Type == Int && e2Type == Float)) {
        semant_error(this) << "Lt expr two value should have same type or a int and another float." << std::endl;
    }
    this->setType(Bool);
    return this->type;
}

Symbol Neq_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();
    if (e1Type == e2Type) {
        if ( e1Type != Int && e1Type != Float && e1Type != Bool) {
            semant_error(this) << "Lt expr value should be int and float and bool type. now the type is" << e1Type << std::endl;
        }
    } else if (!(e1Type == Float && e2Type == Int) && !(e1Type == Int && e2Type == Float)) {
        semant_error(this) << "Lt expr two value should have same type or a int and another float." << std::endl;
    }
    this->setType(Bool);
    return this->type;
}

Symbol Ge_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();
    if (e1Type == e2Type) {
        if ( e1Type != Int && e1Type != Float ) {
            semant_error(this) << "Lt expr value should be int and float type. now the type is" << e1Type << std::endl;
        }
    } else if (!(e1Type == Float && e2Type == Int) && !(e1Type == Int && e2Type == Float)) {
        semant_error(this) << "Lt expr two value should have same type or a int and another float." << std::endl;
    }
    this->setType(Bool);
    return this->type;
}

Symbol Gt_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();
    if (e1Type == e2Type) {
        if ( e1Type != Int && e1Type != Float ) {
            semant_error(this) << "Lt expr value should be int and float type. now the type is" << e1Type << std::endl;
        }
    } else if (!(e1Type == Float && e2Type == Int) && !(e1Type == Int && e2Type == Float)) {
        semant_error(this) << "Lt expr two value should have same type or a int and another float." << std::endl;
    }
    this->setType(Bool);
    return this->type;
}

Symbol And_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();
    if (e1Type != Bool || e2Type != Bool) {
        semant_error(this) << "And expr should have both bool type." << std::endl;
    }
    this->setType(Bool);
    return this->type;
}

Symbol Or_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();
    if (e1Type != Bool || e2Type != Bool) {
        semant_error(this) << "Or expr should have both bool type." << std::endl;
    }
    this->setType(Bool);
    return this->type;
}

Symbol Xor_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();
    if (e1Type != Bool || e2Type != Bool) {
        semant_error(this) << "Xor expr should have both bool type." << std::endl;
    }
    this->setType(Bool);
    return this->type;
}

Symbol Not_class::checkType(){
    Symbol e1Type = e1->checkType();
    if (e1Type != Bool) {
        semant_error(this) << "Not class should have Bool type" << endl;
    }

    this->setType(Bool);
    return this->type;
}

Symbol Bitand_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();
    if (e1Type != Int || e2Type != Int) {
        semant_error(this) << "Bitand expr should have both Int type." << std::endl;
    }
    this->setType(Int);
    return this->type;
}

Symbol Bitor_class::checkType(){
    Symbol e1Type = this->e1->checkType();
    Symbol e2Type = this->e2->checkType();
    if (e1Type != Int || e2Type != Int) {
        semant_error(this) << "Bitor expr should have both Int type." << std::endl;
    }
    this->setType(Int);
    return this->type;
}

Symbol Bitnot_class::checkType(){
    Symbol e1Type = e1->checkType();
    if (e1Type != Int) {
        semant_error(this) << "Bitnot expr should have Int type" << endl;
    }

    this->setType(Int);
    return this->type;
}

Symbol Const_int_class::checkType(){
    setType(Int);
    return type;
}

Symbol Const_string_class::checkType(){
    setType(String);
    return type;
}

Symbol Const_float_class::checkType(){
    setType(Float);
    return type;
}

Symbol Const_bool_class::checkType(){
    setType(Bool);
    return type;
}

Symbol Object_class::checkType(){
    if (objectEnv.lookup(this->var) == NULL) {
        semant_error(this) << "object "<< this->var <<" has not been defined." << endl;
        this->setType(Void);
        return this->type;
    }
    Symbol varType = localVarMap[this->var];
    this->setType(varType);
    return this->type;
}

Symbol No_expr_class::checkType(){
    setType(Void);
    return getType();
}

void Program_class::semant() {
    initialize_constants();
    install_calls(decls);
    check_main();
    install_globalVars(decls);
    check_calls(decls);
    
    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}



