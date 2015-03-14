/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

%{

#include <cstdio>
#include <cstdlib>
/* Keep the following headers in their original order */
#include "Egraph.h"
#include "Transition.h"
#include "mcmt1parser.h"

#define BUFFER1_LENGTH 1024
char   buffer1[ BUFFER1_LENGTH ];
char * pbuffer1;
  
%}

%x start_source
%x start_comment
%option noyywrap
%option yylineno
%option nounput

%%

[ \t\n]                        { }
";".*\n                        { }
":comment".*\n                 { }
":smt"                         { return TK_SMT; }
":initial"                     { return TK_INITIAL; }
":system_axiom"                { return TK_SYST_AXIOM; }
":unsafe"                      { return TK_UNSAFE; }
":suggested_negated_invariant" { return TK_SUGGESTED; }
":var"                         { return TK_VAR; }
":cnj"                         { return TK_CNJ; }
":guard"                       { return TK_GUARD; }
":uguard"                      { return TK_UGUARD; }
":numcases"                    { return TK_NUMCASES; }
":case"                        { return TK_CASE; }
":val"                         { return TK_VAL; }
":abstract"                    { return TK_ABSTRACT; }
":abstract_transition"         { return TK_ABSTRACT_TRANS; }
":transition"                  { return TK_TRANSITION; }
":g_transition"                { return TK_G_TRANSITION; }
":global"                      { return TK_GLOBAL; }
":local"                       { return TK_LOCAL; }
":"                            { return TK_COLON; }
"="                            { return TK_EQ; }
"define-type"                  { return TK_DEFINE_TYPE; }
"subrange"                     { return TK_SUBRANGE; }
"as"                           { return TK_AS; }
"distinct"                     { return TK_DISTINCT; }
"let"                          { return TK_LET; }
"forall"                       { return TK_FORALL; }
"exists"                       { return TK_EXISTS; }
"and"                          { return TK_AND; }
"or"                           { return TK_OR; }
"xor"                          { return TK_XOR; }
"implies"                      { return TK_IMPLIES; }
"=>"                           { return TK_IMPLIES; }
"not"                          { return TK_NOT; }
"!"                            { return TK_ANNOT; }
"+"                            { return TK_PLUS; }
"-"                            { return TK_MINUS; }
"*"                            { return TK_TIMES; }
"/"                            { return TK_DIV; }
"<="                           { return TK_LEQ; }
">="                           { return TK_GEQ; }
"<"                            { return TK_LT; }
">"                            { return TK_GT; }
"Int"                          { return TK_INT; }
"Real"                         { return TK_REAL; }
"Bool"                         { return TK_BOOL; }
"true"                         { return TK_TRUE; }
"["                            { return TK_OSB; }
"]"                            { return TK_CSB; }

0|[1-9][0-9]*                                                                  { mcmt1lval.str = strdup( yytext ); return TK_NUM; }
[0-9]+\.0*[0-9]+                                                               { mcmt1lval.str = strdup( yytext ); return TK_DEC; }
[a-zA-Z~!@\$\%\^&\*_\-\+=\<\>\.\?\/'][a-zA-Z0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\/']* { mcmt1lval.str = strdup( yytext ); return TK_SYM; }

\|		{ pbuffer1 = buffer1; BEGIN(start_source); }
<start_source>{
  [^\|\n]       { *pbuffer1++ = yytext[0]; }
  \n            { *pbuffer1++ = '\n'; }
  \|            { *pbuffer1 = '\0'; mcmt1lval.str = strdup( buffer1 );
                   BEGIN(INITIAL); return TK_SYM; }
}

\".*\"          { mcmt1lval.str = strdup( yytext ); return TK_STR; }    
[()]            { return *yytext; }
.               { printf( "Syntax error at line %d near %s\n", yylineno, yytext ); exit( 1 ); }

%%
