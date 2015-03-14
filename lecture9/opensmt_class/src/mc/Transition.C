/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#include "Transition.h"

Enode *
Transition::getVar( int n_var )
{
  assert ( n_var == 1 || n_var == 2 );
  return ( n_var == 1 ) ? v1 : v2 ; 
}

void Transition::print( ostream & os )
{
  os << "Transition n."<< id <<": " << endl;
  os << " Var1: " << v1 << endl;
  if ( v2 )
    os << " Var2: " << v2 << endl;
  os << " Varj: " << vj << endl;
  os << " Guard: ";
  guard->yicesPrint( os );
  os << endl;
  for ( size_t i = 0 ; i < uguards.size( ) ; ++ i )
  {
    os << " uGuard: ";
    uguards[ i ]->yicesPrint( os );
    os << endl;
  }
  for ( size_t i = 0 ; i < cases.size( ) ; ++ i )
  {
    os << "  case ";
    cases[ i ]->condition->yicesPrint( os );
    os << endl; 
    for ( size_t j = 0 ; j < cases[ i ]->values.size( ) ; ++ j )
    {
      os << "   val ";
      cases[ i ]->values[ j ]->yicesPrint( os );
      os << endl;
    }
  }
}

bool
Transition::avoidNewVariable ( int i )
{
  assert( i == FIRST || i == SECOND || i == BOTH );

  if ( i == FIRST )
    return !new_var_x;
  if ( i == SECOND )
    return !new_var_y;

  assert( i == BOTH );
  return !new_var_xy;
}

void
Transition::setNewVar ( int i , bool new_var )
{
  assert( i == FIRST || i == SECOND || i == BOTH );
  if ( i == FIRST )
    new_var_x = new_var;
  if ( i == SECOND )
    new_var_y = new_var;
  if ( i == BOTH )
    new_var_xy = new_var;
}

vector < Enode * > &
Transition::getUpdates ( size_t z , size_t c )
{
  if ( !ready )
  {
    setUpCube( );
  }
  assert( ready );
  assert( z < updates.size( ) );
  assert( c < updates[ z ].size( ) );
  return updates[ z ][ c ];
}

Enode *
Transition::getUpdate ( size_t z , size_t c , size_t a )
{
  if ( !ready )
  {
    setUpCube( );
  }
  assert( ready );
  assert( z < updates.size( ) );
  assert( c < updates[ z ].size( ) );
  assert( a < updates[ z ][ c ].size( ) );
  return updates[ z ][ c ][ a ];
}

void
Transition::setUpCube( )
{
  if ( ready )
    return;
 
  updates.clear( );

  updates.resize( MAX_INDEX_VARS );

  assert( vj );
  vector < Enode * > origs;
  origs.push_back( vj );

  Snode * nat = sstore.mkVar( "Nat" );
  for (unsigned id = 0 ; id < MAX_INDEX_VARS ; id++ )
  {
    updates[ id ].resize( cases.size( ) );
    // declare zid
    char buf[ 64 ] = { "\0" };
    sprintf( buf, "z%u", id );
    // Declare symbol if not there
    if ( !egraph.hasSymbol( buf, NULL, nat ) )
    {
      egraph.newSymbolLog( buf, NULL, nat );
    }
    // Create a variable
    Enode * new_var = egraph.mkVar( buf );
    vector < Enode * > dests;
    dests.push_back( new_var );

    for ( size_t c = 0 ; c < cases.size( ) ; c++ )
    {
      for ( size_t v = 0 ; v < cases[ c ]->values.size( ) ; v++ )
      {
        updates[ id ][ c ].push_back( egraph.substitute( cases[ c ]->values[ v ] , origs , dests ) );
      }
    }
  }
  ready = true;
}

Transition::Case *
Transition::getCase ( size_t c )
{
  assert( c < cases.size( ) );
  return cases[ c ];
}

void
Transition::preprocess( )
{
  assert( identical_preprocessing_done );
  this->uselessVariablePreprocess( );
  this->uguardPreprocess( );
}

void
Transition::uselessVariablePreprocess( )
{ 
  
  assert( identical_preprocessing_done );
  if ( ! preprocessed )
  {
    uguardPreprocess( );
  }
  assert( preprocessed );


  // July 1st, 2011
  // check if in the guard contains only global variables
  // if it is so, do no add new variables!
  vector < Enode * > lits;

  // retrieve literals
  assert( guard->isAnd( ) || guard->isLit( ) );
  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( guard );
  egraph.initDup1( );
  
  while ( !unprocessed_enodes.empty( ) )
  {
    Enode * e = unprocessed_enodes.back( );
    unprocessed_enodes.pop_back( );
    if ( egraph.isDup1( e ) )
      continue;

    Enode * arg_list;
    if ( e->isAnd( ) )
    {
      for ( arg_list = e->getCdr( )
	  ; !arg_list->isEnil( )
	  ; arg_list = arg_list->getCdr( ) )
      {
	Enode * arg = arg_list->getCar( );
	assert( arg->isTerm( ) );
	if ( !egraph.isDup1( arg ) )
	  unprocessed_enodes.push_back( arg );
      }
    }
    else
    {
      assert( e->isLit( ) || e->isEq( ) );
      lits.push_back( e );
    }
    egraph.storeDup1( e );
  }
  egraph.doneDup1( );

/*
  // search in all literals if there are only global variables
  for ( size_t i = 0 ; i < lits.size( ) ; i++ )
  {
    Enode * l = lits[ i ];
    if ( l->isNot( ) )
    {
      l = l->get1st( );
    }
    if ( l->get1st( )->isSelect( ) && !( l->get1st( )->get1st( )->getGlobal( ) ) )
    {
      goto SKIP;
    }
    if ( l->get2nd( )->isSelect( ) && !( l->get2nd( )->get1st( )->getGlobal( ) ) )
    {
      goto SKIP;
    }
  }
  
  // if we arrive here there are no local variable in the guard, so
  // we can avoid to introduce a new variable when we apply the transition
  new_var_x = false;
  new_var_y = false;
  new_var_xy = false;
  
  return;

SKIP:

*/
  // partial implementation: only two cases, and we check only for the fist variable!
  if ( cases.size( ) != 2 )
  {
    return;
  }
  
  for ( size_t c = 0 ; c < cases.size( ) ; c++ )
  {
    // must be identical!
    if ( cases[ c ]->identical
      && cases[ c ]->condition->isNot( )
      && cases[ c ]->condition->get1st( )->isEq( )
      && ( ( cases[ c ]->condition->get1st( )->get1st( ) == v1 && cases[ c ]->condition->get1st( )->get2nd( ) == vj )
        || ( cases[ c ]->condition->get1st( )->get1st( ) == vj && cases[ c ]->condition->get1st( )->get2nd( ) == v1 )
         )
       )
    {
      new_var_x = false;
    }
  }

}

void
Transition::uguardPreprocess( )
{
  if ( preprocessed )
    return;

  if ( uguards.empty( ) )
  {
    preprocessed = true;
    return;
  }

  vector < Case * > new_cases;
  for ( size_t u = 0 ; u < uguards.size( ) ; u++ )
  {
    for ( size_t c = 0 ; c < cases.size( ) ; c++ )
    {
      // skip when (= x j) or (= y j)
      if ( cases[ c ]->condition->isEq( )
        && ( cases[ c ]->condition->get1st( ) == v1 || cases[ c ]->condition->get1st( ) == v2 )
        && cases[ c ]->condition->get2nd( ) == vj )
      {
        vector < Enode * > duplicate_values = cases[ c ]->values;
        Case * new_case = new Case ( cases[ c ]->condition , duplicate_values );
        new_cases.push_back( new_case );
        continue;
      }
      // skip when (= j x) or (= j y)
      if ( cases[ c ]->condition->isEq( )
        && cases[ c ]->condition->get1st( ) == vj
        && ( cases[ c ]->condition->get2nd( ) == v1 || cases[ c ]->condition->get2nd( ) == v2 ) )
      {
        vector < Enode * > duplicate_values = cases[ c ]->values;
        Case * new_case = new Case ( cases[ c ]->condition , duplicate_values );
        new_cases.push_back( new_case );
        continue;
      }
      
      vector < Enode * > duplicate_values = cases[ c ]->values;
      Case * new_case = new Case ( egraph.mkAnd( egraph.cons( cases[ c ]->condition , egraph.cons( uguards[ u ] ) ) ) , duplicate_values );
      new_case->identical = cases[ c ]->identical;
      new_cases.push_back( new_case );
    }
  }

  // Eliminate old cases
  while( !cases.empty( ) )
  {
    delete cases.back( );
    cases.pop_back( );
  }
  
  // store new cases
  cases = new_cases;
 
  preprocessed = true;
  ready = false;
}

void
Transition::identicalPreprocessing ( vector < ArrayVar * > & array_vars )
{
  for ( size_t c = 0 ; c < cases.size( ) ; c++ )
  {
    cases[ c ]->identical = true;
    assert( cases[ c ]->values.size( ) == array_vars.size( ) );
    for ( size_t v = 0 ; v < cases[ c ]->values.size( ) && cases[ c ]->identical ; v++ )
    {
      assert( cases[ c ]->values[ v ] );
      if ( ! ( cases[ c ]->values[ v ]->isSelect( )
        && cases[ c ]->values[ v ]->get1st( ) == array_vars[ v ]->enode
        && cases[ c ]->values[ v ]->get2nd( ) == vj
      ) )
      {
        cases[ c ]->identical = false;
      }
    }
  }
  identical_preprocessing_done = true;
}

#else

// Stubs to fool linker

#endif
