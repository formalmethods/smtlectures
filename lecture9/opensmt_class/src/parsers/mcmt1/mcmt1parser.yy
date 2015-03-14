/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

%{

#include "Global.h"
#include "Egraph.h"
#include "SStore.h"
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include "Transition.h"
#include "MCMTContext.h"

extern int mcmt1lineno;
extern int mcmt1lex( );
extern MCMTContext * parser_ctx;

vector< Transition::Case * > * createCaseList( Transition::Case * );
vector< Transition::Case * > * pushCase( vector< Transition::Case * > *
                                       , Transition::Case * );
void destroyCaseList( vector< Transition::Case * > * );

vector< Enode * > * createEnodeList( Enode * );
vector< Enode * > * pushEnode( vector< Enode * > *
                             , Enode * );
void destroyEnodeList( vector< Enode * > * );

list< Snode * > * createSortListMCMT  ( Snode * );
list< Snode * > * pushSortListMCMT    ( list< Snode * > *, Snode * );
void		  destroySortListMCMT ( list< Snode * > * );

void mcmt1error( const char * s )
{
  printf( "At line %d: %s\n", mcmt1lineno, s );
  exit( 1 );
}

/* Overallocation to prevent stack overflow */
#define YYMAXDEPTH 1024 * 1024
%}

%union
{
  char  *                        str;
  Enode *                        enode;
  vector< Enode * > *            vlist;
  Transition::Case *             c;
  vector< Transition::Case * > * clist;
  Snode *                        snode;
  list< Snode * > *              snode_list;
  map< Enode *, Enode * > *      binding_list;
}

%error-verbose

%token TK_OSB TK_CSB TK_SMT TK_INITIAL TK_VAR TK_CNJ TK_GUARD TK_UGUARD
%token TK_NUMCASES TK_CASE TK_VAL TK_G_TRANSITION TK_TRANSITION TK_SYST_AXIOM
%token TK_GLOBAL TK_LOCAL TK_DEFINE_TYPE TK_COLON TK_ABSTRACT TK_ABSTRACT_TRANS
%token TK_NUM TK_DEC TK_SUBRANGE TK_UNSAFE TK_STR TK_SUGGESTED
%token TK_AS TK_LET TK_FORALL TK_EXISTS TK_ANNOT TK_DISTINCT TK_DEFINEFUN
%token TK_PLUS TK_MINUS TK_TIMES TK_DIV
%token TK_EQ TK_LEQ TK_GEQ TK_LT TK_GT
%token TK_AND TK_OR TK_NOT TK_IFF TK_XOR TK_ITE TK_IFTHENELSE TK_IMPLIES
%token TK_TRUE TK_FALSE TK_REAL TK_INT TK_BOOL TK_SYM

%type <str> TK_NUM TK_DEC TK_STR TK_SYM
%type <enode> term_list term predicate predicate_list conjunction var_decl
%type <clist> case_list
%type <c> case
%type <vlist> value_list uguard_list
%type <snode> sort
//%type <snode_list> sort_list

%start top

%%

top: smt_decl top
   | array_decl top
   | initial top
   | system_axiom top
   | transition top
   | unsafe top
   | suggested top
   | new_var top
   | abstract top
   | abstract_trans top
   | smt_decl
   | array_decl
   | initial
   | system_axiom
   | transition
   | unsafe
   | suggested
   | new_var
   | abstract
   | abstract_trans
   ;

smt_decl: TK_SMT '(' TK_DEFINE_TYPE TK_SYM '(' TK_SUBRANGE TK_NUM TK_NUM ')' ')'
	  { 
	    parser_ctx->DefineType( $4, atoi( $7 ), atoi( $8 ) ); 
	    free( $4 ); free( $7 ); free( $8 ); 
	  }

array_decl: TK_LOCAL TK_SYM TK_SYM
	    { parser_ctx->DeclareLocal( $2, $3 ); free( $2 ); free( $3 ); }
          | TK_GLOBAL TK_SYM TK_SYM
	    { parser_ctx->DeclareGlobal( $2, $3 ); free( $2 ); free( $3 ); }
          ;

system_axiom: TK_SYST_AXIOM var_decl TK_CNJ term
         { parser_ctx->addSystemAxiom( $2, NULL, NULL, NULL, $4 ); }
        | TK_SYST_AXIOM var_decl var_decl TK_CNJ term
         { parser_ctx->addSystemAxiom( $2, $3, NULL, NULL, $5 ); }
	| TK_SYST_AXIOM var_decl var_decl var_decl TK_CNJ term
         { parser_ctx->addSystemAxiom( $2, $3, $4, NULL, $6 ); }
        | TK_SYST_AXIOM var_decl var_decl var_decl var_decl TK_CNJ term
         { parser_ctx->addSystemAxiom( $2, $3, $4, $5, $7 ); }
        ;

initial: TK_INITIAL var_decl TK_CNJ conjunction
         { parser_ctx->addInitial( $2, NULL, NULL, NULL, $4 ); }
        | TK_INITIAL var_decl var_decl TK_CNJ conjunction
         { parser_ctx->addInitial( $2, $3, NULL, NULL, $5 ); }
	| TK_INITIAL var_decl var_decl var_decl TK_CNJ conjunction
         { parser_ctx->addInitial( $2, $3, $4, NULL, $6 ); }
        | TK_INITIAL var_decl var_decl var_decl var_decl TK_CNJ conjunction
         { parser_ctx->addInitial( $2, $3, $4, $5, $7 ); }
        ;

var_decl: TK_VAR TK_SYM
	 { 
           parser_ctx->DeclareIndexVar( $2 ); 
           $$ = parser_ctx->mkVar( $2 );
           free( $2 ); 
         }
         ;

abstract: TK_ABSTRACT TK_SYM
	 { 
           parser_ctx->setAbstract( $2 ); 
           free( $2 ); 
         }
         ;

abstract_trans: TK_ABSTRACT_TRANS TK_NUM
	 { 
           parser_ctx->setAbstractTransition( atoi( $2 ) ); 
           free( $2 ); 
         }
         ;

new_var: TK_VAR TK_SYM TK_COLON TK_INT
	 { parser_ctx->DeclareIntVar( $2 ); free( $2 ); }
        | TK_VAR TK_SYM TK_COLON TK_REAL
	 { parser_ctx->DeclareRealVar( $2 ); free( $2 ); }
        ;

unsafe: TK_UNSAFE var_decl TK_CNJ conjunction
        { parser_ctx->addUnsafe( $2, NULL, NULL, NULL, $4 ); }
      | TK_UNSAFE var_decl var_decl TK_CNJ conjunction
        { parser_ctx->addUnsafe( $2, $3, NULL, NULL, $5 ); }
      | TK_UNSAFE var_decl var_decl var_decl TK_CNJ conjunction
        { parser_ctx->addUnsafe( $2, $3, $4, NULL, $6 ); }
      | TK_UNSAFE var_decl var_decl var_decl var_decl TK_CNJ conjunction
        { parser_ctx->addUnsafe( $2, $3, $4, $5, $7 ); }
      ;

suggested: TK_SUGGESTED var_decl TK_CNJ conjunction
        { parser_ctx->addSuggested( $2, NULL, NULL, NULL, $4 ); }
      | TK_SUGGESTED var_decl var_decl TK_CNJ conjunction
        { parser_ctx->addSuggested( $2, $3, NULL, NULL, $5 ); }
      | TK_SUGGESTED var_decl var_decl var_decl TK_CNJ conjunction
        { parser_ctx->addSuggested( $2, $3, $4, NULL, $6 ); }
      | TK_SUGGESTED var_decl var_decl var_decl var_decl TK_CNJ conjunction
        { parser_ctx->addSuggested( $2, $3, $4, $5, $7 ); }
      ;

conjunction: predicate_list
	     { $$ = parser_ctx->mkAnd( $1 ); }

predicate: '(' TK_EQ term_list ')'
	   { $$ = parser_ctx->mkEq( $3 ); }
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
         | '(' TK_NOT predicate ')'
           { $$ = parser_ctx->mkNot( parser_ctx->mkCons( $3 ) ); }
         | '(' TK_TRUE ')'
           { $$ = parser_ctx->mkTrue( ); }
         | '(' predicate ')'
           { $$ = $2; }
	 ;
	   
predicate_list: predicate predicate_list
	        { $$ = parser_ctx->mkCons( $1, $2 ); }
	      | predicate
                { $$ = parser_ctx->mkCons( $1 ); }
              ;

term_list: term term_list
	   { $$ = parser_ctx->mkCons( $1, $2 ); }
	 | term 
           { $$ = parser_ctx->mkCons( $1 ); }
         ;

term: TK_NUM
      { $$ = parser_ctx->mkNum( $1 ); free( $1 ); }
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
//    unuseful reduction rule (?)
//    | TK_TRUE
//      { $$ = parser_ctx->mkTrue( ); }
    | '(' TK_EQ term_list ')'
      { $$ = parser_ctx->mkEq( $3 ); }
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
    | '(' TK_ITE term_list ')'
      { $$ = parser_ctx->mkIte( $3 ); }
    | '(' TK_PLUS term_list ')'
      { $$ = parser_ctx->mkPlus( $3 ); }
    | '(' TK_MINUS term_list ')'
      { $$ = parser_ctx->mkMinus( $3 ); }
    | TK_MINUS TK_NUM
      { $$ = parser_ctx->mkMinus( parser_ctx->mkCons( parser_ctx->mkNum( $2 ) ) ); free( $2 ); }
    | '(' TK_TIMES term_list ')'
      { $$ = parser_ctx->mkTimes( $3 ); }
    | '(' TK_DIV term_list ')'
      { $$ = parser_ctx->mkDiv( $3 ); }
    | '(' TK_LET '(' var_binding_list ')' term ')'
      { $$ = $6; }
    | '(' TK_FORALL '(' sorted_var_list ')' term ')'
      { mcmt_error( "case not handled (yet)" ); }
    | '(' TK_EXISTS '(' sorted_var_list ')' term ')'
      { mcmt_error( "case not handled (yet)" ); }
  /*
   * For MCMT language
   */
    | term TK_OSB term TK_CSB
      { $$ = parser_ctx->mkSelect( $1, $3 ); } 
  /*
   * Variable
   */
    | TK_SYM 
      { $$ = parser_ctx->mkVar( $1 ); free( $1 ); }
    | '(' TK_TRUE ')'
      { $$ = parser_ctx->mkTrue( ); }
    | '(' term ')'
      { $$ = $2; }
    ;

sorted_var_list: sorted_var_list sorted_var | sorted_var ;

sorted_var: '(' TK_SYM sort ')' ;
/*
 * UNUSED RULES
sort_list: sort_list sort 
	   { $$ = pushSortList( $1, $2 ); }
	 | sort 
	   { $$ = createSortList( $1 ); }
         ;
*/

sort: TK_BOOL 
      { $$ = parser_ctx->mkSortBool( ); }
    | TK_INT
      { $$ = parser_ctx->mkSortInt( ); }
    | TK_REAL
      { $$ = parser_ctx->mkSortReal( ); }
    | TK_SYM 
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

var_binding_list: var_binding_list '(' TK_SYM term ')'
		  { parser_ctx->mkBind( $3, $4 ); free($3); }
                | '(' TK_SYM term ')'
		  { parser_ctx->mkBind( $2, $3 ); free($2); }
		;

transition: TK_TRANSITION var_decl var_decl TK_GUARD predicate_list uguard_list TK_NUMCASES TK_NUM case_list
	    { 
	      parser_ctx->addTransition( $2, NULL, $3, parser_ctx->mkAnd( $5 ), *($6), *($9) , false );
	      destroyEnodeList( $6 );
	      free( $8 );
              destroyCaseList( $9 );
	    }
          | TK_TRANSITION var_decl var_decl var_decl TK_GUARD predicate_list uguard_list TK_NUMCASES TK_NUM case_list
	    { 
	      parser_ctx->addTransition( $2, $3, $4, parser_ctx->mkAnd( $6 ), *($7), *($10) , false );
	      destroyEnodeList( $7 );
	      free( $9 );
              destroyCaseList( $10 );
	    }
          | TK_TRANSITION var_decl var_decl TK_GUARD predicate_list TK_NUMCASES TK_NUM case_list
	    { 
	      vector< Enode * > tmp;
	      parser_ctx->addTransition( $2, NULL, $3, parser_ctx->mkAnd( $5 ), tmp, *($8) , false );
              free( $7 );
              destroyCaseList( $8 );
	    }
          | TK_TRANSITION var_decl var_decl var_decl TK_GUARD predicate_list TK_NUMCASES TK_NUM case_list
	    { 
              vector< Enode * > tmp;
	      parser_ctx->addTransition( $2, $3, $4, parser_ctx->mkAnd( $6 ), tmp, *($9) , false );
              free( $8 );
              destroyCaseList( $9 );
	    }
          ;

transition: TK_G_TRANSITION var_decl var_decl TK_GUARD predicate_list uguard_list TK_NUMCASES TK_NUM case_list
	    { 
	      parser_ctx->addTransition( $2, NULL, $3, parser_ctx->mkAnd( $5 ), *($6), *($9) , true );
	      destroyEnodeList( $6 );
	      free( $8 );
              destroyCaseList( $9 );
	    }
          | TK_G_TRANSITION var_decl var_decl var_decl TK_GUARD predicate_list uguard_list TK_NUMCASES TK_NUM case_list
	    { 
	      parser_ctx->addTransition( $2, $3, $4, parser_ctx->mkAnd( $6 ), *($7), *($10) , true );
	      destroyEnodeList( $7 );
	      free( $9 );
              destroyCaseList( $10 );
	    }
          | TK_G_TRANSITION var_decl var_decl TK_GUARD predicate_list TK_NUMCASES TK_NUM case_list
	    { 
	      vector< Enode * > tmp;
	      parser_ctx->addTransition( $2, NULL, $3, parser_ctx->mkAnd( $5 ), tmp, *($8) , true );
              free( $7 );
              destroyCaseList( $8 );
	    }
          | TK_G_TRANSITION var_decl var_decl var_decl TK_GUARD predicate_list TK_NUMCASES TK_NUM case_list
	    { 
              vector< Enode * > tmp;
	      parser_ctx->addTransition( $2, $3, $4, parser_ctx->mkAnd( $6 ), tmp, *($9) , true );
              free( $8 );
              destroyCaseList( $9 );
	    }
          ;


uguard_list: uguard_list TK_UGUARD conjunction
	     {	
	       pushEnode( $1, $3 ); 
               $$ = $1;
             }
           | TK_UGUARD conjunction
	     { $$ = createEnodeList( $2 ); }
           ;

case_list: case_list case 
	   {
	     pushCase( $1, $2 );
	   }
	 | case
           {
	     $$ = createCaseList( $1 );
	   }
         ;

case: TK_CASE predicate_list value_list
      {
        Transition::Case * c = new Transition::Case( parser_ctx->mkAnd( $2 ), *($3) );
	$$ = c;
	destroyEnodeList( $3 );
      }
/*    BETTER SPECIFYING ALWAYS ALL THE CONDITIONS
      | TK_CASE value_list
      {
	Transition::Case * c = new Transition::Case( NULL, *($2) );
	$$ = c;
	destroyEnodeList( $2 );
      }*/
    ;

value_list: value_list TK_VAL term
	   { 
	     pushEnode( $1, $3 ); 
             $$ = $1;
	   }
	 | TK_VAL term
           { $$ = createEnodeList( $2 ); }
         ;

%%

//=======================================================================================
// Auxiliary Routines

vector< Transition::Case * > * createCaseList( Transition::Case * c )
{
  vector< Transition::Case * > * l = new vector< Transition::Case * >;
  l->push_back( c );
  return l;
} 

vector< Transition::Case * > * pushCase( vector< Transition::Case * > * l
                                       , Transition::Case * c )
{
  l->push_back( c );
  return l;
}

void destroyCaseList( vector< Transition::Case * > * l )
{
  delete l;
}

vector< Enode * > * createEnodeList( Enode * c )
{
  vector< Enode * > * l = new vector< Enode * >;
  l->push_back( c );
  return l;
} 

vector< Enode * > * pushEnode( vector< Enode * > * l, Enode * c )
{
  l->push_back( c );
  return l;
}

void destroyEnodeList( vector< Enode * > * l )
{
  delete l;
}

list< Snode * > * createSortListMCMT( Snode * s )
{
  list< Snode * > * l = new list< Snode * >;
  l->push_back( s );
  return l;
} 

list< Snode * > * pushSortListMCMT( list< Snode * > * l, Snode * s )
{
  l->push_back( s );
  return l;
}

void destroySortListMCMT( list< Snode * > * l )
{
  assert( l );
  delete l;
}
