 /*
  *  The scanner definition for seal.
  */

 /*
  *  Stuff enclosed in %{ %} in the first section is copied verbatim to the
  *  output, so headers and global definitions are placed here to be visible
  * to the code in the file.  Don't remove anything that was here initially
  */
%{

//#include <seal-parse.h>
#include <stringtab.h>
#include <utilities.h>
#include <stdint.h>
#include <stdlib.h>

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


%}

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

OBJECTID [a-z][a-zA-Z0-9_]*
TYPEID [A-Z][a-zA-Z0-9_]*
TRUE true
FALSE false

VAR var
AND &&
OR ||
EQUAL ==
GE >=
LE <=
WHITESPACE [\f\r\t\v]+
NEWLINE \n
SYMBOLS [+/\-*=<~,;:(){}%>&!\^|]
INVALID					[^a-zA-Z0-9_ \f\r\t\v\n+/\-*=<.~,;:()@{}]
%x COMMENT
%x INLINE_COMMENT
%x STRING

%%

/*	
 *	Add Rules here. Error function has been given.
 */
/*
  *  Nested comments
  */
"(*"										{ BEGIN(COMMENT); }
"*)" {
	cool_yylval.error_msg = "Unmatched *)";
	return ERROR;
}
<COMMENT><<EOF>> {
	BEGIN(INITIAL);
	cool_yylval.error_msg = "EOF in comment";
	return ERROR;
}
<COMMENT>[^*\n]*				{}
<COMMENT>"*"+[^"*)"\n]*	{}
<COMMENT>\n							{ curr_lineno++; }
<COMMENT>"*"+")"        { BEGIN(INITIAL); }

 /*
  * Inline comments
  */
"--"	{ BEGIN(INLINE_COMMENT); }
<INLINE_COMMENT><<EOF>> {
	BEGIN(INITIAL);
	cool_yylval.error_msg = "EOF in comment";
	return ERROR;
}
<INLINE_COMMENT>[^\n]*	{}
<INLINE_COMMENT>\n {
	curr_lineno++;
	BEGIN(INITIAL);
}

 /*
  *  The multiple-character operators.
  */
{INT} {
	cool_yylval.symbol = inttable.add_string(yytext);
	return INT_CONST;
}
{TRUE} {
	cool_yylval.boolean = true;
	return BOOL_CONST;
}
{FALSE} {
	cool_yylval.boolean = false;
	return BOOL_CONST;
}
{DARROW}		{ return (DARROW); }
{LE}				{ return (LE); }
{ASSIGN}		{ return (ASSIGN); }
{WHITESPACE}	{}
{NEWLINE}		{ curr_lineno++; }
{SYMBOLS} 	{ return int(yytext[0]); }


 /*
  * Keywords are -insensitive except for the values true and false,
  * which must begin with a lower- letter.
  */
{CLASS}			{ return (CLASS); }
{ELSE}			{ return (ELSE); }
{FI}				{ return (FI); }
{IF}				{ return (IF); }
{IN}				{ return (IN); }
{INHERITS}	{ return (INHERITS); }
{ISVOID}		{ return (ISVOID); }
{LET}				{ return (LET); }
{LOOP}			{ return (LOOP); }
{POOL}			{ return (POOL); }
{THEN}			{ return (THEN); }
{WHILE}			{ return (WHILE); }
{CASE}			{ return (CASE); }
{ESAC}			{ return (ESAC); }
{NEW}				{ return (NEW); }
{OF}				{ return (OF); }
{NOT}				{ return (NOT); }

{TYPEID} {
	cool_yylval.symbol = idtable.add_string(yytext);
	return (TYPEID);
}
{OBJECTID} {
	cool_yylval.symbol = idtable.add_string(yytext);
	return (OBJECTID);
}
 /*
  *  String constants (C syntax)
  *  Escape sequence \c is accepted for all characters c. Except for
  *  \n \t \b \f, the result is c.
  *
  */
\" {
	string_buf_ptr = string_buf;
	BEGIN(STRING);
}
<STRING><<EOF>> {
	BEGIN(INITIAL);
	cool_yylval.error_msg = "EOF in string constant";
	return ERROR;
}
<STRING>\n {
	curr_lineno++;
	BEGIN(INITIAL);
	cool_yylval.error_msg = "Unterminated string constant";
	return ERROR;
}
<STRING>\0 {
	BEGIN(INITIAL);
	cool_yylval.error_msg = "String contains null character";
	return ERROR;
}
<STRING>\"	{
	BEGIN(INITIAL);
	*string_buf_ptr = '\0';
	cool_yylval.symbol = stringtable.add_string(string_buf);
	return STR_CONST;
}
<STRING>\\n  {
	if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
		BEGIN(INITIAL);
		cool_yylval.error_msg = "String constant too long";
		return ERROR;
	}
	*string_buf_ptr++ = '\n';
}
<STRING>\\t  {
	if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
		BEGIN(INITIAL);
		cool_yylval.error_msg = "String constant too long";
		return ERROR;
	}
	*string_buf_ptr++ = '\t';
}
<STRING>\\b  {
	if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
		BEGIN(INITIAL);
		cool_yylval.error_msg = "String constant too long";
		return ERROR;
	}
	*string_buf_ptr++ = '\b';
}
<STRING>\\f  {
	if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
		BEGIN(INITIAL);
		cool_yylval.error_msg = "String constant too long";
		return ERROR;
	}
	*string_buf_ptr++ = '\f';
}
<STRING>\\(.|\n)	{
	if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
		BEGIN(INITIAL);
		cool_yylval.error_msg = "String constant too long";
		return ERROR;
	}
	*string_buf_ptr++ = yytext[1];
}
<STRING>[^\\\n\"]+ {
	char *yptr = yytext;
	while ( *yptr ) {
		if ((string_buf_ptr - 1) == &string_buf[MAX_STR_CONST-1]) {
			BEGIN(INITIAL);
			cool_yylval.error_msg = "String constant too long";
			return ERROR;
		}
		*string_buf_ptr++ = *yptr++;
	}
}
{INVALID} {
	cool_yylval.error_msg = yytext;
	return ERROR;
}
.	{
	strcpy(seal_yylval.error_msg, yytext); 
	return (ERROR); 
}

%%
