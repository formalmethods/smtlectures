/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#include "Formula.h"

vector < Enode * > &
Formula::getLiterals( )
{
  if ( !literals_ready )
  {
    retrieveLits( );
  }

  return literals;
}

vector < Enode * > &
Formula::getVariables( )
{
  if ( !variables_ready )
  {
    retrieveVars( );
  }

  return variables;
}

vector < Enode * > &
Formula::getArrays( )
{
  if ( !variables_ready )
  {
    retrieveVars( );
  }

  return arrays;
}

unsigned
Formula::getVarMaxId( )
{
  if ( !variables_ready )
  {
    retrieveVars( );
  }

  return variables_max_id;
}


Enode *
Formula::getValue( Enode * var , Enode * array , bool global_array )
{
  if ( !matrix_ready )
  {
    buildMatrix( );
  }

  // if there is no a column for this variable, return NULL
  // (means that this formula do not contains any value for this array, so
  // it can't be equal to any other value...
  if ( !global_array )
  {
    if ( matrix.size( ) <= var->getMcmtId( ) )
    {
      return NULL;
    }
    if( matrix[ var->getMcmtId( ) ].size( ) <= array->getMcmtId( ) )
    {
      return NULL;
    }

    return matrix[ var->getMcmtId( ) ][ array->getMcmtId( ) ];
  }
  else
  {
    assert( !matrix.empty() );
    
    if( matrix[ 0 ].size( ) <= array->getMcmtId() )
    {
      // in this formula there is not this variable!
      return NULL;
    }
    
    if ( matrix[ var->getMcmtId( ) ][ array->getMcmtId( ) ] && !matrix[ var->getMcmtId( ) ][ array->getMcmtId( ) ]->isEnil() )
    {
      return matrix[ var->getMcmtId( ) ][ array->getMcmtId( ) ];
    }
    else
    {
      // if the variable is global, return the first non-NULL position
      for ( size_t k = 0 ; k <= variables_max_id ; k++ )
      {
        if ( matrix[ k ][ array->getMcmtId( ) ] && !matrix[ k ][ array->getMcmtId( ) ]->isEnil() )
        {
          return matrix[ k ][ array->getMcmtId( ) ];
        }
      }
      return NULL;
    }
  }
}

void
Formula::retrieveVars( )
{
  if ( variables_ready )
    return;

  assert( formula );
  assert( formula->isAnd( ) || formula->isLit( ) );

  set< Enode * > cache;
  vector< Enode * > unprocessed_enodes;

  unprocessed_enodes.push_back( formula );

  while( !unprocessed_enodes.empty( ) )
  {
    Enode * e = unprocessed_enodes.back( );

    if ( cache.find( e ) != cache.end( ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = e->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( cache.find( arg ) == cache.end( ) )
      {
	unprocessed_enodes.push_back( arg );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );

    if ( e->isVar( ) 
      && egraph.hasSortIndex( e ) )
    {
      variables.push_back( e );
      if ( variables_max_id < e->getMcmtId( ) )
      {
        variables_max_id = e->getMcmtId( ) ;
      }
    }
    else if ( e->isVar( )
	   && e->hasSortArray( ) )
    {
      arrays.push_back( e );
      if ( arrays_max_id < e->getMcmtId( ) )
      {
        arrays_max_id = e->getMcmtId( ) ;
      }
    }

    assert( cache.find( e ) == cache.end( ) );
    cache.insert( e );
  }

  //cerr << "Variables max id = " << variables_max_id << endl;
  //cerr << "Arrays max id = " << arrays_max_id << endl;

  variables_ready = true;
  
  // sort variables
  sort( variables.begin( ) , variables.end( ) , Enode::mcmt_compare_enodes ); 
}

void
Formula::retrieveLits( )
{
  
  if ( literals_ready )
    return;
  
  assert( formula );
  assert( formula->isAnd( ) || formula->isLit( ) );
  
  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( formula );
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
      if ( !e->isLit( ) )
      {
        has_disjunctions = true;
        literals_ready = true;
        literals.clear( );
        egraph.doneDup1( );
        return;
      }
      literals.push_back( e );
    }

    egraph.storeDup1( e );
  }
  egraph.doneDup1( );
  
  literals_ready = true;
}


void
Formula::buildMatrix( )
{
  if ( matrix_ready )
    return;
  
  assert( formula );
  assert( formula->isAnd() || formula->isLit() );
 
  if ( !variables_ready )
  {
    retrieveVars( );
  }
  
  assert( variables.size() > 0 );
  
  // create the matrix
  matrix.resize( variables_max_id+1 );
  for ( size_t r = 0 ; r < matrix.size() ; r++ )
  {
    matrix[ r ].resize( arrays_max_id+1 );
    for ( size_t c = 0 ; c < matrix[ r ].size() ; c++ )
    {
      matrix[ r ][ c ] = NULL;
    }
  }
  
  // retrieve the list of literals
  if ( !literals_ready )
  {
    retrieveLits( ); 
  }

  if ( has_disjunctions )
  {
    // the formula has disjunctions, return now and leave the matrix empty
    // (i.e. is compatible with every formula!)
    matrix_ready = true;
    return;
  }

  // now create the matrix for this formula
  for ( size_t l = 0 ; l < literals.size() ; l++ )
  {
    if ( (  literals[ l ]->isNot() && !literals[ l ]->get1st( )->isEq( ) ) 
      || ( !literals[ l ]->isNot() && !literals[ l ]->isEq( ) )
       )
    {
      continue;
    }
    if ( literals[ l ]->isNot() 
      && literals[ l ]->get1st()->isEq() 
      && egraph.hasSortIndex( literals[ l ]->get1st( )->get1st( ) ) 
      && egraph.hasSortIndex( literals[ l ]->get1st( )->get2nd( ) ) )
    {
      continue;
    }

    if ( !literals[ l ]->isNot( ) )
    {
      if ( literals[ l ]->get1st( )->isSelect( ) && literals[ l ]->get2nd( )->isConstant( ) )
      {
        assert( literals[ l ]->get1st( )->get2nd( )->getMcmtId( ) <= variables_max_id );
        assert( literals[ l ]->get1st( )->get1st( )->getMcmtId( ) <= arrays_max_id );
        assert( egraph.hasSortIndex( literals[ l ]->get1st( )->get2nd( ) ) );
        assert( literals[ l ]->get1st( )->get1st( )->hasSortArray( ) );
        assert( literals[ l ]->get2nd( )->isConstant( ) );
        matrix[ literals[ l ]->get1st( )->get2nd( )->getMcmtId( ) ][ literals[ l ]->get1st( )->get1st( )->getMcmtId( ) ] = literals[ l ]->get2nd( );
      }
      if ( literals[ l ]->get2nd( )->isSelect( ) && literals[ l ]->get1st( )->isConstant( ) )
      {
        assert( literals[ l ]->get2nd( )->get2nd( )->getMcmtId( ) <= variables_max_id );
        assert( literals[ l ]->get2nd( )->get1st( )->getMcmtId( ) <= arrays_max_id );
        assert( egraph.hasSortIndex( literals[ l ]->get2nd( )->get2nd( ) ) );
        assert( literals[ l ]->get2nd( )->get1st( )->hasSortArray( ) );
        assert( literals[ l ]->get1st( )->isConstant( ) );
        matrix[ literals[ l ]->get2nd( )->get2nd( )->getMcmtId( ) ][ literals[ l ]->get2nd( )->get1st( )->getMcmtId( ) ] = literals[ l ]->get1st( );
      }
    }
  }
  
  matrix_ready = true;
  
}

void
Formula::printMatrix ( ostream & os )
{
  // print the matrix!
  os << "Label was " << formula << endl;
  os << "Matrix is:" << endl;
  for ( vector< vector< Enode * > >::iterator r = matrix.begin( ) ; r != matrix.end( ) ; r++ )
  {
    os << "\t";
    for ( vector< Enode * >::iterator c = (*r).begin( ) ; c != (*r).end( ) ; c++)
    {
      if ( !(*c) )
        os << "X\t";
      else
        os << (*c) << "\t";
    }
    os << endl;
  }
}

void
Formula::print( ostream & os )
{
  // os << formula ;
  formula->yicesPrint( os );
}

void
Formula::checkDisjunctions( )
{
  assert( formula );
  
  if ( formula->isOr( ) )
  {
    has_disjunctions = true;
    literals_ready = true;
    return;
  }

  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( formula );
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
      if ( !e->isLit( ) )
      {
        has_disjunctions = true;
        literals_ready = true;
        egraph.doneDup1( );
        return;
      }
    }

    egraph.storeDup1( e );
  }
  egraph.doneDup1( );
  
  literals_ready = true;
}

#endif
