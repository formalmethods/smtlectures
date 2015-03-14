/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2011, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include "Egraph.h"

//
// Convert input formula into DNF. Yes it is a bit crazy,
// but MCMT formulae are pretty small and so the task
// can be carried out quite effortlessly
//
Enode * Egraph::convertIntoDNF( Enode * formula )
{
  if ( isDNF( formula ) )
    return formula;

  assert( formula );

  // First step, push nots to the leaves
  formula = pushNot( formula, false );

  list< Enode * > new_clauses;
  vector< Enode * > unprocessed_enodes;
  initDupMap1( );

  unprocessed_enodes.push_back( formula );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( ) ;
	  arg_list != enil ;
	  arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );

      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed and not in DNF already
      //
      if ( valDupMap1( arg ) == NULL 
	&& arg->hasSortBool( ) )
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
    Enode * result = NULL;
    //
    // At this point, every child is in DNF
    //
    if ( enode->isOr( ) )
    {
      list< Enode * > new_args;
      // Just merge childs into a single big OR
      for ( Enode * arg_list = enode->getCdr( )
	  ; !arg_list->isEnil( ) 
	  ; arg_list = arg_list->getCdr( ) )
      {
	Enode * arg = valDupMap1( arg_list->getCar( ) );
	// If argument is OR, merge
	if ( arg->isOr( ) )
	{
	  assert( isDNF( arg ) );
	  for ( Enode * arg_arg_list = arg->getCdr( ) 
	      ; !arg_arg_list->isEnil( )
	      ; arg_arg_list = arg_arg_list->getCdr( ) )
	    new_args.push_back( arg_arg_list->getCar( ) );
	}
	// Otherwise just push
	else
	{
	  new_args.push_back( arg );
	}
      }

      result = mkOr( cons( new_args ) );
    }
    else if ( enode->isAnd( ) )
    {
      // Retrieve conjuncts
      vector< Enode * > conj;
      for ( Enode * arg_list = enode->getCdr( )
	  ; !arg_list->isEnil( ) 
	  ; arg_list = arg_list->getCdr( ) )
      {
	Enode * arg = valDupMap1( arg_list->getCar( ) );
	// If argument is OR, merge
	if ( arg->isAnd( ) )
	{
	  assert( isDNF( arg ) );
	  for ( Enode * arg_arg_list = arg->getCdr( ) 
	      ; !arg_arg_list->isEnil( )
	      ; arg_arg_list = arg_arg_list->getCdr( ) )
	    conj.push_back( arg_arg_list->getCar( ) );
	}
	// Otherwise just push
	else
	{
	  conj.push_back( arg );
	}
      }

      result = distribute( conj );
    }
    else if ( enode->isLit( ) )
    {
      result = enode;
    }
    else
    {
      opensmt_error( "Case not handled" );
    }

    assert( result );
    assert( isDNF( result ) );
    assert( valDupMap1( enode ) == NULL );
    storeDupMap1( enode, result );
  }

  Enode * new_formula = valDupMap1( formula );
  assert( new_formula );
  doneDupMap1( );

  return new_formula;
}

// Check if this formula is in DNF
bool Egraph::isDNF( Enode * formula )
{
  if ( formula->isTrue( )
    || formula->isFalse( ) )
    return true;

  if ( isCube( formula ) )
    return true;

  if ( formula->isOr( ) )
  {
    for ( Enode * arg_list = formula->getCdr( )
	; !arg_list->isEnil( ) 
	; arg_list = arg_list->getCdr( ) )
    {
      if ( !isCube( arg_list->getCar( ) ) )
	return false;
    }

    return true;
  }

  return false;
}

bool Egraph::isCube( Enode * formula )
{
  if ( formula->isLit( ) )
    return true;

  if ( formula->isAnd( ) )
  {
    for ( Enode * arg_list = formula->getCdr( )
	; !arg_list->isEnil( ) 
	; arg_list = arg_list->getCdr( ) )
    {
      if ( !arg_list->getCar( )->isLit( ) )
	return false;
    }

    return true;
  }

  return false;
}

// Distribute (C1 \/ C2) /\ (D1 \/ D2) --> (C1 /\ D1) \/ (C1 /\ D2) \/ (C2 /\ D1) \/ (C2 \/ D2)
// conjunction in input is implicit, disjunction on output is explicit
Enode * Egraph::distribute( vector< Enode * > & conj )
{
  vector< vector< Enode * > > cubes;

  // Collect cubes for simplicity
  for ( size_t i = 0 ; i < conj.size( ) ; i ++ )
  {
    vector< Enode * > cube;
    if ( conj[ i ]->isOr( ) )
    {
      for ( Enode * arg_list = conj[ i ]->getCdr( )
	  ; !arg_list->isEnil( ) 
	  ; arg_list = arg_list->getCdr( ) )
      {
	cube.push_back( arg_list->getCar( ) );
      }
    }
    else
    {
      assert( conj[ i ]->isLit( ) );
      cube.push_back( conj[ i ] );
    }
    cubes.push_back( cube );
  }

  // Distribution happens here
  vector< Enode * > partial_cube;
  vector< Enode * > partial_dnf;
  distributeRec( cubes, 0, partial_cube, partial_dnf );
  Enode * res = mkOr( cons( partial_dnf ) );
  assert( isDNF( res ) );
  return res;
}

// Try changing to iterative if becomes slow
void Egraph::distributeRec( vector< vector< Enode * > > & cubes
                          , const size_t depth
			  , vector< Enode * > & partial_cube
                          , vector< Enode * > & partial_dnf )
{
  if ( depth == cubes.size( ) )
  {
    partial_dnf.push_back( mkAnd( cons( partial_cube ) ) );
    assert( isCube( partial_dnf.back( ) ) );
  }
  else
  {
    for ( size_t i = 0 ; i < cubes[ depth ].size( ) ; i ++ )
    {
      partial_cube.push_back( cubes[ depth ][ i ] );
      distributeRec( cubes
	  , depth + 1
	  , partial_cube
	  , partial_dnf );
      partial_cube.pop_back( );
    }
  }
}

// Try changing to iterative if becomes slow
Enode * Egraph::pushNot( Enode * formula, bool negate )
{
  assert( formula );
  if ( formula->isAnd( ) || formula->isOr( ) )
  {
    vector< Enode * > new_args;
    for ( Enode * arg_list = formula->getCdr( )
	; !arg_list->isEnil( ) 
	; arg_list = arg_list->getCdr( ) )
    {
      new_args.push_back( pushNot( arg_list->getCar( ), negate ) );
    }

    if ( negate )
      return formula->isAnd( ) 
	   ? mkOr ( cons( new_args ) ) 
	   : mkAnd( cons( new_args ) ) ;
    else
      return formula->isAnd( ) 
	   ? mkAnd( cons( new_args ) ) 
	   : mkOr ( cons( new_args ) ) ;
  }
 
  if ( formula->isLit( ) )
  {
    if ( negate )
      return mkNot( formula );
    else
      return formula;
  }

  // If here, it is a not with some formula inside
  assert( formula->isNot( ) );

  Enode * arg = formula->get1st( );

  // Two negations cancel out
  return pushNot( arg, !negate );
}
