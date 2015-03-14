/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

%{
#include "Global.h"
#include "Egraph.h"
#include "SStore.h"
#include "MCMTContext.h"
#include <cstdio>
#include <cstdlib>
#include <cassert>

extern int mcmt2lineno;
extern int mcmt2lex( );
extern MCMTContext * parser_ctx;

vector< string > * createNumeralList  ( const char * );
vector< string > * pushNumeralList    ( vector< string > *, const char * );
void		   destroyNumeralList ( vector< string > * );

list< Snode * > * createSortList  ( Snode * );
list< Snode * > * pushSortList    ( list< Snode * > *, Snode * );
void		  destroySortList ( list< Snode * > * );

void mcmt2error( const char * s )
{
  printf( "At line %d: %s\n", mcmt2lineno, s );
  exit( 1 );
}

/* Overallocation to prevent stack overflow */
#define YYMAXDEPTH 1024 * 1024
%}

%union
{
  char  *                   str;
  vector< string > *        str_list;
  Enode *                   enode;
  Snode *                   snode;
  list< Snode * > *         snode_list;
  map< Enode *, Enode * > * binding_list;
}

%error-verbose

%token TK_NUM TK_DEC TK_HEX TK_STR TK_SYM TK_KEY TK_BIN
%token TK_BOOL
%token TK_SETLOGIC TK_SETINFO TK_SETOPTION TK_DECLARESORT TK_DEFINESORT TK_DECLAREFUN
%token TK_PUSH TK_POP TK_CHECKSAT TK_CHECKSAFETY TK_GETASSERTIONS TK_GETPROOF TK_GETUNSATCORE TK_GETINTERPOLANTS
%token TK_GETVALUE TK_GETASSIGNMENT TK_GETOPTION TK_GETINFO TK_EXIT
%token TK_AS TK_LET TK_FORALL TK_EXISTS TK_ANNOT TK_DISTINCT TK_DEFINEFUN
%token TK_ASSERT 
%token TK_REAL TK_INT 
%token TK_PLUS TK_MINUS TK_TIMES TK_DIV
%token TK_NE TK_EQ TK_LEQ TK_GEQ TK_LT TK_GT
%token TK_AND TK_OR TK_NOT TK_IFF TK_XOR TK_ITE TK_IFTHENELSE TK_IMPLIES
%token TK_TRUE TK_FALSE TK_INTERPOLATE
%token TK_BVSLT TK_BVSGT TK_BVSLE TK_BVSGE
%token TK_BVULT TK_BVUGT TK_BVULE TK_BVUGE
%token TK_EXTRACT TK_CONCAT TK_BVAND TK_BVOR TK_BVXOR TK_BVNOT TK_BVADD TK_BVNEG TK_BVMUL TK_BVASHR TK_REPEAT
%token TK_SIGN_EXTEND TK_ZERO_EXTEND TK_ROTATE_LEFT TK_ROTATE_RIGHT TK_BVLSHR TK_BVSHL TK_BVSREM TK_BVSDIV TK_BVSUB
%token TK_BVUDIV TK_BVUREM
%token TK_ARRAY_SELECT TK_ARRAY_STORE TK_STATUS
%token TK_PRINT_SUCCESS TK_EXPAND_DEFINITIONS TK_INTERACTIVE_MODE TK_PRODUCE_PROOFS TK_PRODUCE_UNSAT_CORES TK_PRODUCE_INTERPOLANTS
%token TK_PRODUCE_MODELS TK_PRODUCE_ASSIGNMENTS TK_REGULAR_OUTPUT_CHANNEL TK_DIAGNOSTIC_OUTPUT_CHANNEL
%token TK_RANDOM_SEED TK_VERBOSITY

%type <str> TK_NUM TK_DEC TK_HEX TK_STR TK_SYM TK_KEY numeral decimal hexadecimal binary symbol 
%type <str> attribute identifier spec_const b_value
%type <str_list> numeral_list
%type <enode> term_list term
%type <snode> sort
%type <snode_list> sort_list

%start script

%%

script: command_list

command_list: command_list command | command ;

command: '(' TK_SETLOGIC symbol ')'
         { parser_ctx->SetLogic( $3 ); free( $3 ); }
       | '(' TK_SETOPTION option ')'
         { }
       | '(' TK_SETINFO attribute ')'
	 { parser_ctx->SetInfo( $3 ); free( $3 ); }
       | '(' TK_DECLARESORT symbol numeral ')'
	 { parser_ctx->DeclareSort( $3, atoi($4) ); free( $3 ); free( $4 ); }
       /*
       | '(' TK_DEFINESORT symbol '(' symbol_list ')' sort ')'
	 { error( "define-sort is not supported (yet)", "" ); }
       */
       | '(' TK_DECLAREFUN symbol '(' sort_list ')' sort ')'
	 { 
	   Snode * a = parser_ctx->mkCons( *$5 );
	   Snode * s = parser_ctx->mkSort( a );
	   parser_ctx->DeclareFun( $3, s, $7 );
	   destroySortList( $5 ); free( $3 );
	 }
       | '(' TK_DECLAREFUN symbol '(' ')' sort ')'
	 { parser_ctx->DeclareFun( $3, NULL, $6 ); free( $3 ); }
       /*
       | '(' TK_DEFINEFUN symbol '(' sorted_var_list ')' sort term ')'
	 { error( "command not supported (yet)", "" ); }
       | '(' TK_DEFINEFUN symbol '(' ')' sort term ')'
	 { error( "command not supported (yet)", "" ); }
       */
       | '(' TK_PUSH numeral ')'
	 { parser_ctx->addPush( atoi( $3 ) ); free( $3 ); }
       | '(' TK_POP numeral ')'
	 { parser_ctx->addPop( atoi( $3 ) ); free( $3 );}
       | '(' TK_ASSERT term ')'
         { mcmt_error( "command not supported" ); }
       | '(' TK_CHECKSAT ')'
	 { mcmt_error( "command not supported" ); }
       | '(' TK_CHECKSAFETY ')'
	 { parser_ctx->addCheckSafety( ); }
       | '(' TK_GETASSERTIONS ')'
	 { mcmt_error( "command not supported" ); }
       | '(' TK_GETPROOF ')'
	 { mcmt_error( "command not supported" ); }
       | '(' TK_GETUNSATCORE ')'
	 { mcmt_error( "command not supported" ); }
       | '(' TK_GETVALUE '(' term_list ')' ')'
	 { mcmt_error( "command not supported" ); }
       | '(' TK_GETASSIGNMENT ')'
	 { mcmt_error( "command not supported" ); }
       | '(' TK_GETOPTION keyword ')'
	 { mcmt_error( "command not supported" ); }
     /*| '(' TK_GETINFO info_flag ')'*/
       | '(' TK_EXIT ')'
         { parser_ctx->addExit( ); }
       ;

s_expr: spec_const 
	{ free($1); } 
      | TK_SYM 
	{ free($1); } 
      | TK_KEY 
        { free($1); }
      | '(' s_expr ')' 
      ;

spec_const: numeral 
	    { $$ = $1; }
	  | decimal 
	    { $$ = $1; }
	  | hexadecimal 
	    { $$ = $1; }
	  | binary
	    { $$ = $1; }
	  | TK_STR 
	    { $$ = $1; }
          ;

identifier: TK_SYM 
	    { $$ = $1; }
	  | '(' '_' TK_SYM numeral_list ')' 
	  ;

keyword: TK_KEY { free($1); };

symbol: TK_SYM 
        { $$ = $1; }
      ;

symbol_list: symbol_list symbol | symbol ;

attribute_value: spec_const { free($1); } | TK_SYM | '(' s_expr_list ')' | '(' ')' ;

attribute: TK_KEY { free($1); } | TK_KEY s_expr { free($1); } ;

sort: TK_BOOL 
      { $$ = parser_ctx->mkSortBool( ); }
    | TK_INT
      { $$ = parser_ctx->mkSortInt( ); }
    | TK_REAL
      { $$ = parser_ctx->mkSortReal( ); }
    | identifier 
      { $$ = parser_ctx->mkSortVar( $1 ); free( $1 ); }
  /* 
    | '(' identifier sort_list ')' 
      { 
        Snode * s = parser_sstore->cons( parser_sstore->newSymbol( $2 ) ); 
	(*$3).push_front( s );
	$$ = parser_sstore->mkDot( parser_sstore->cons( *$3 ) );
        free( $2 ); 
      }
   */
    ;

sorted_var: '(' TK_SYM sort ')' ;

term: spec_const 
      { $$ = parser_ctx->mkNum( $1 ); free( $1 ); }
  /* 
   * List of predefined identifiers 
   */
    | TK_TRUE
      { $$ = parser_ctx->mkTrue( ); }
    | TK_FALSE
      { $$ = parser_ctx->mkFalse( ); }
    | '(' TK_AND term_list ')'
      { $$ = parser_ctx->mkAnd( $3 ); }
    | '(' TK_OR term_list ')'
      { $$ = parser_ctx->mkOr( $3 ); }
    | '(' TK_XOR term_list ')'
      { $$ = parser_ctx->mkXor( $3 ); }
    | '(' TK_NOT term_list ')'
      { $$ = parser_ctx->mkNot( $3 ); }
    | '(' TK_IMPLIES term_list ')'
      { $$ = parser_ctx->mkImplies( $3 ); }
    | '(' TK_EQ term_list ')'
      { $$ = parser_ctx->mkEq( $3 ); }
    | '(' TK_ITE term_list ')'
      { $$ = parser_ctx->mkIte( $3 ); }
    | '(' TK_PLUS term_list ')'
      { $$ = parser_ctx->mkPlus( $3 ); }
    | '(' TK_MINUS term_list ')'
      { $$ = parser_ctx->mkMinus( $3 ); }
    | '(' TK_TIMES term_list ')'
      { $$ = parser_ctx->mkTimes( $3 ); }
    | '(' TK_DIV term_list ')'
      { $$ = parser_ctx->mkDiv( $3 ); }
    | '(' TK_LEQ term_list ')'
      { $$ = parser_ctx->mkLeq( $3 ); }
    | '(' TK_GEQ term_list ')'
      { $$ = parser_ctx->mkGeq( $3 ); }
    | '(' TK_LT term_list ')'
      { $$ = parser_ctx->mkLt( $3 ); }
    | '(' TK_GT term_list ')'
      { $$ = parser_ctx->mkGt( $3 ); }
    | '(' TK_DISTINCT term_list ')'
      { $$ = parser_ctx->mkDistinct( $3 ); }
    | '(' TK_LET '(' var_binding_list ')' term ')'
      { $$ = $6; }
    | '(' TK_FORALL '(' sorted_var_list ')' term ')'
      { mcmt_error( "case not handled (yet)" ); }
    | '(' TK_EXISTS '(' sorted_var_list ')' term ')'
      { mcmt_error( "case not handled (yet)" ); }
    | '(' TK_ANNOT term attribute_list ')'
      { mcmt_error( "case not handled (yet)" ); }
  /*
   * Variable
   */
    | identifier 
      { $$ = parser_ctx->mkVar( $1 ); free( $1 ); }
  /*
   * Function application
   */
    | '(' identifier term_list ')'
      { $$ = parser_ctx->mkFun( $2, $3 ); free( $2 ); }
    | '(' TK_AS identifier sort ')' 
      { mcmt_error( "case not handled (yet)" ); }
    ;

sort_list: sort_list sort 
	   { $$ = pushSortList( $1, $2 ); }
	 | sort 
	   { $$ = createSortList( $1 ); }
         ;

attribute_list: attribute_list attribute | attribute ;

sorted_var_list: sorted_var_list sorted_var | sorted_var ;

var_binding_list: var_binding_list '(' TK_SYM term ')'
		  { parser_ctx->mkBind( $3, $4 ); free($3); }
                | '(' TK_SYM term ')'
		  { parser_ctx->mkBind( $2, $3 ); free($2); }
		;

term_list: term term_list
	   { $$ = parser_ctx->mkCons( $1, $2 ); }
	 | term 
           { $$ = parser_ctx->mkCons( $1 ); }
         ;

s_expr_list: s_expr_list s_expr | s_expr ;

numeral_list: numeral_list numeral
	      { $$ = pushNumeralList( $1, $2 ); }
	    | numeral
	      { $$ = createNumeralList( $1 ); }
	    ;

numeral: TK_NUM { $$ = $1; } ;

decimal: TK_DEC { $$ = $1; } ;

hexadecimal: TK_HEX { $$ = $1; } ;

binary: TK_BIN ;

option: TK_PRINT_SUCCESS b_value
        { 
	  char buf[256] = ":print-success "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( buf );
	  free( $2 );
        }
      | TK_EXPAND_DEFINITIONS b_value
	{
	  char buf[256] = ":expand-definitions "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( buf );
          free( $2 );
        }
      | TK_INTERACTIVE_MODE b_value
	{
	  char buf[256] = ":interactive-mode "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( buf );
          free( $2 );
        }
      | TK_PRODUCE_PROOFS b_value
	{
	  char buf[256] = ":produce-proofs "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( buf );
          free( $2 );
        }
      | TK_PRODUCE_UNSAT_CORES b_value
	{
	  char buf[256] = ":produce-unsat-cores "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( buf );
          free( $2 );
        }
      | TK_PRODUCE_INTERPOLANTS b_value
	{
	  char buf[256] = ":produce-interpolants "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( buf );
          free( $2 );
        }
      | TK_PRODUCE_MODELS b_value
	{
	  char buf[256] = ":produce-models "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( buf );
          free( $2 );
        }
      | TK_PRODUCE_ASSIGNMENTS b_value
	{
	  char buf[256] = ":produce-assignments "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( buf );
          free( $2 );
        }
      | TK_REGULAR_OUTPUT_CHANNEL TK_STR
	{
	  char buf[256] = ":regular-output-channel "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( buf );
          free( $2 );
        }
      | TK_DIAGNOSTIC_OUTPUT_CHANNEL TK_STR
	{
	  char buf[256] = ":diagnostic-output-channel "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( buf );
          free( $2 );
        }
      | TK_RANDOM_SEED TK_NUM
	{
	  char buf[256] = ":random-seed "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( buf );
          free( $2 );
        }
      | TK_VERBOSITY TK_NUM
	{
	  char buf[256] = ":verbosity "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( buf );
          free( $2 );
	}
      | attribute
	{ parser_ctx->SetOption( $1 ); }
      ;
      
b_value: TK_TRUE
         { 
           char * buf;
           buf = (char *)malloc(sizeof(char) * 10);
	   strcpy( buf, "true" );
	   $$ = buf;
         }
       | TK_FALSE
         {
           char * buf;
           buf = (char *)malloc(sizeof(char) * 10);
	   strcpy( buf, "false" );
	   $$ = buf;
	 }
       ;

%%

//=======================================================================================
// Auxiliary Routines

vector< string > * createNumeralList( const char * s )
{
  vector< string > * l = new vector< string >;
  l->push_back( s );
  return l;
} 

vector< string > * pushNumeralList( vector< string > * l, const char * s )
{
  l->push_back( s );
  return l;
}

void destroyNumeralList( vector< string > * l )
{
  delete l;
}

list< Snode * > * createSortList( Snode * s )
{
  list< Snode * > * l = new list< Snode * >;
  l->push_back( s );
  return l;
} 

list< Snode * > * pushSortList( list< Snode * > * l, Snode * s )
{
  l->push_back( s );
  return l;
}

void destroySortList( list< Snode * > * l )
{
  assert( l );
  delete l;
}
