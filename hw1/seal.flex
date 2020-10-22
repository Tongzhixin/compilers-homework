 /*
  *  The scanner definition for seal.
  */

 /*
  *  Stuff enclosed in %{ %} in the first section is copied verbatim to the
  *  output, so headers and global definitions are placed here to be visible
  * to the code in the file.  Don't remove anything that was here initially
  */
%{

#include <seal-parse.h>
#include <stringtab.h>
#include <utilities.h>
#include <stdint.h>
#include <stdlib.h>
#include <string>
#include <sstream>
/* The compiler assumes these identifiers. */
#define yylval seal_yylval
#define yylex  seal_yylex

/* Max size of string constants */
#define MAX_STR_CONST 256
#define YY_NO_UNPUT   /* keep g++ happy */

extern FILE *fin; /* we read from this file */

/* define YY_INPUT so we read from the FILE fin:
 * This change makes it possible to use this scanner in
 * the seal compiler.
 */
#undef YY_INPUT
#define YY_INPUT(buf,result,max_size) \
	if ( (result = fread( (char*)buf, sizeof(char), max_size, fin)) < 0) \
		YY_FATAL_ERROR( "read() in flex scanner failed");

char string_buf[MAX_STR_CONST]; /* to assemble string constants */
char *string_buf_ptr;

extern int curr_lineno;
extern int verbose_flag;

extern YYSTYPE seal_yylval;
/*
 *  Add Your own definitions here
 */
char* hex_to_decimal(char* hex_str){
	int x;
	std::string str = hex_str;
	std::stringstream ss;
	ss << std::hex << str;  
	ss >> x;
	std::string str1 = std::to_string(x);
	char* tmp = (char*)str1.data(); 
	return tmp;
}
bool flag = true;

%}
%option noyywrap
 /*
  * Define names for regular expressions here.
  */
IF if
ELSE else 
WHILE while
FOR for
BREAK break
CONTINUE continue 
FUNC func 
RETURN return
VAR var
STRUCT struct

OBJECTID [a-z][a-zA-Z0-9_]*
TYPEID   (Int|Float|String|Bool|Void)
TRUE true
FALSE false
INT (0|[1-9][0-9]*)
INT_HEX  0[Xx][a-fA-F0-9]+
FLOAT (0|[1-9][0-9]*).[0-9]+
AND &&
NE !=
GE >=
LE <=
WHITESPACE [ \f\r\t\v]+
NEWLINE \n
SYMBOLS [+/\-*=<~,;:(){}%>&!\^|]
INVALID		[^a-zA-Z0-9_ \f\r\t\v\n+/\-*=<~,;:(){}%>&!\^|]

%x COMMENT
%x INLINE_COMMENT
%x STRING
%x STRING_SPE

%%

 /*	
 *	Add Rules here. Error function has been given.
 */
  /*
  * Keywords
  */
{IF}			{ return IF; }
{ELSE}			{ return ELSE; }
{WHILE}			{ return WHILE; }
{FOR}           { return FOR; }
{BREAK}         { return BREAK; }
{CONTINUE}      { return CONTINUE; } 
{RETURN}        { return RETURN; }
{FUNC}          { return FUNC; }
{VAR}           { return VAR; }
{STRUCT}        { return STRUCT; }
{AND}           { return AND; }
"||"            { return OR; }
{NE}            { return NE; }
{GE}            { return GE; }
{LE}            { return LE; }
"=="            { return EQUAL; }

{INT} {
	seal_yylval.symbol = inttable.add_string(yytext);
	return CONST_INT;
}
{INT_HEX} {
	char* dec_number = hex_to_decimal(yytext);
	seal_yylval.symbol = inttable.add_string(dec_number);
	return CONST_INT;
}
{FLOAT}  {
	seal_yylval.symbol = floattable.add_string(yytext);
	return CONST_FLOAT;
}
{TRUE} {
	seal_yylval.boolean = true;
	return CONST_BOOL;
}
{FALSE} {
	seal_yylval.boolean = false;
	return CONST_BOOL;
}
{TYPEID} {
	seal_yylval.symbol = idtable.add_string(yytext);
	return TYPEID;
}
{OBJECTID} {
	seal_yylval.symbol = idtable.add_string(yytext);
	return OBJECTID;
}
{WHITESPACE}	{}
{NEWLINE}		{ curr_lineno++; }
{SYMBOLS} 		{ return int(yytext[0]); }

 /*
  *  COMMENT
  */

"/*"	{ BEGIN COMMENT; }
"*/" {
	strcpy(seal_yylval.error_msg, "Unmatched */");
	return ERROR;
}
<COMMENT><<EOF>> {
	BEGIN INITIAL;
	strcpy(seal_yylval.error_msg, "EOF in comment");
	return ERROR;
}
<COMMENT>[^*\n]*				{}
<COMMENT>"*"+[^"*/"\n]*	{}
<COMMENT>\n							{ curr_lineno++; }
<COMMENT>"*"+"/"        { BEGIN INITIAL; }
 /*
  * Inline comments
  */
"//"	{ BEGIN INLINE_COMMENT; }
<INLINE_COMMENT><<EOF>> {
	BEGIN INITIAL;
	strcpy(seal_yylval.error_msg, "EOF in comment");
	return ERROR;
}
<INLINE_COMMENT>[^\n]*	{}
<INLINE_COMMENT>\n {
	curr_lineno++;
	BEGIN INITIAL;
}
 /* 
  *  String constants ,contain string and string `
  *  a series of rules
  */
\" {
	string_buf_ptr = string_buf;
	BEGIN(STRING);
}
<STRING><<EOF>> {
	BEGIN INITIAL;
	strcpy(seal_yylval.error_msg, "EOF in string constant");
	return ERROR;
}
<STRING>\n {
	curr_lineno++;
	BEGIN INITIAL;
	strcpy(seal_yylval.error_msg, "newline in quotation must use a '\\'");
	return ERROR;
}
<STRING>\\0 {
	strcpy(seal_yylval.error_msg, "String contains null character '\\0'");	
	flag = false;	
}
<STRING>\"	{
	if (flag){
		BEGIN INITIAL;
		*string_buf_ptr = '\0';
		seal_yylval.symbol = stringtable.add_string(string_buf);
		return CONST_STRING;
	} else{
		flag = true;
		BEGIN INITIAL;
		return ERROR;
	}
}
<STRING>\\n  {
	if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
		BEGIN INITIAL;
		strcpy(seal_yylval.error_msg, "String constant too long");
		return ERROR;
	}
	*string_buf_ptr++ = '\n';
}
<STRING>\\t  {
	if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
		BEGIN INITIAL;
		strcpy(seal_yylval.error_msg, "String constant too long");
		return ERROR;
	}
	*string_buf_ptr++ = '\t';
}
<STRING>\\b  {
	if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
		BEGIN INITIAL;
		strcpy(seal_yylval.error_msg, "String constant too long");
		return ERROR;
	}
	*string_buf_ptr++ = '\b';
}
<STRING>\\f  {
	if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
		BEGIN INITIAL;
		strcpy(seal_yylval.error_msg, "String constant too long");
		return ERROR;
	}
	*string_buf_ptr++ = '\f';
}
<STRING>\\\n	{
	if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
		BEGIN INITIAL;
		strcpy(seal_yylval.error_msg, "String constant too long");
		return ERROR;
	}
	*string_buf_ptr++ = yytext[1];
	curr_lineno++;
}
<STRING>[^\\\n\"]+ {
	char *yptr = yytext;
	while ( *yptr ) {
		if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
			BEGIN INITIAL;
			strcpy(seal_yylval.error_msg, "String constant too long");
			return ERROR;
		}
		*string_buf_ptr++ = *yptr++;
	}
}
<STRING>\\[^\n] {
	if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
		BEGIN INITIAL;
		strcpy(seal_yylval.error_msg, "String constant too long");
		return ERROR;
	}
	*string_buf_ptr++ = yytext[1];
}
` {
	string_buf_ptr = string_buf;
	BEGIN STRING_SPE;
}
<STRING_SPE><<EOF>> {
	BEGIN INITIAL;
	strcpy(seal_yylval.error_msg, "EOF in string constant");
	return ERROR;
}
<STRING_SPE>\n {
	
	if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
		BEGIN INITIAL;
		strcpy(seal_yylval.error_msg, "String constant too long");
		return ERROR;
	}
	*string_buf_ptr++ = '\n';
	curr_lineno++;
}
<STRING_SPE>`	{
	BEGIN INITIAL;
	*string_buf_ptr = '\0';
	seal_yylval.symbol = stringtable.add_string(string_buf);
	return CONST_STRING;
}
<STRING_SPE>[^\n`]+ {
	char *yptr = yytext;
	while ( *yptr ) {
		if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
			BEGIN INITIAL;
			strcpy(seal_yylval.error_msg, "String constant too long");
			return ERROR;
		}
		*string_buf_ptr++ = *yptr++;
	}
}
{INVALID} {
	strcpy(seal_yylval.error_msg, yytext);
	return ERROR;
}
.	{
	strcpy(seal_yylval.error_msg, yytext); 
	return ERROR; 
}

%%
