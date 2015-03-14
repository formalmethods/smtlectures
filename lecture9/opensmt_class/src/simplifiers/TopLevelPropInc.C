/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

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

#include "TopLevelPropInc.h"
#include "LA.h"

void TopLevelPropInc::pushBacktrackPoint( )
{
  assert( undo_stack_oper.size( ) == undo_stack_lhs.size( ) );
  assert( undo_stack_oper.size( ) == undo_stack_rhs.size( ) );
  backtrack_points.push_back( undo_stack_oper.size( ) );
}

void TopLevelPropInc::popBacktrackPoint( )
{
  assert( !backtrack_points.empty( ) );
  assert( undo_stack_oper.size( ) == undo_stack_lhs.size( ) );
  assert( undo_stack_oper.size( ) == undo_stack_rhs.size( ) );
  const size_t new_stack_size = backtrack_points.back( );
  backtrack_points.pop_back( );
  while ( undo_stack_oper.size( ) > new_stack_size )
  {
    oper_t oper = undo_stack_oper.back( );
    undo_stack_oper.pop_back( );

    if ( oper == SUBSTITUTION )
    {
      // Retrieve lhs to modify
      Enode * lhs = undo_stack_lhs.back( );
      undo_stack_lhs.pop_back( );
      // Retrieve old rhs to restore
      Enode * rhs = undo_stack_rhs.back( );
      undo_stack_rhs.pop_back( );
      // Make sure it exists
      assert( all_substitutions.find( lhs ) != all_substitutions.end( ) );
      all_substitutions[ lhs ] = rhs;
    }
    else if ( oper == ADD_SUBST )
    {
      // Retrieve lhs to erase
      Enode * lhs = undo_stack_lhs.back( );
      undo_stack_lhs.pop_back( );
      // Retrieve rhs stored
      Enode * rhs = undo_stack_rhs.back( );
      (void)rhs;
      undo_stack_rhs.pop_back( );
      // Make sure it exists
      assert( all_substitutions.find( lhs ) != all_substitutions.end( ) );
      assert( all_substitutions[ lhs ] == rhs );
      all_substitutions.erase( lhs );
    }
    else if ( oper == ADD_FORMULA )
    {
      undo_stack_lhs.pop_back( );
      undo_stack_rhs.pop_back( );
      all_formulae.pop_back( );
    }
    else if ( oper == STATUS_FALSE )
    {
      undo_stack_lhs.pop_back( );
      undo_stack_rhs.pop_back( );
      status = true;
    }
    else
    {
      opensmt_error( "Case not handled" );
    }
  }
}

Enode *
TopLevelPropInc::doit( Enode * formula )
{
  if ( !status )
    return egraph.mkFalse( );

#ifndef PRODUCE_PROOF
  //
  // First step, apply all_substitutions collected
  // so far to formula. Now formula does not contain
  // lhs substitution variables 
  //
  formula = substitute( formula );
#endif

  assert( formula );
  //
  // Canonize Arithmetic, but don't split equalities
  //
  if ( config.logic == QF_IDL
    || config.logic == QF_RDL
    || config.logic == QF_LRA
    || config.logic == QF_LIA
    || config.logic == QF_UFIDL
    || config.logic == QF_UFLRA )
  {
    if ( ( config.logic == QF_UFIDL 
	|| config.logic == QF_UFLRA )
	&& config.sat_lazy_dtc != 0 )
      formula = egraph.canonizeDTC( formula );
    else
      formula = egraph.canonize( formula );
  }
#ifndef PRODUCE_PROOF
  list< Enode * > to_reinsert;
  //
  // Repeat until fix point
  //
  bool stop = false;
  while ( !stop )
  {
    if ( formula->isTrue( ) 
      || formula->isFalse( ) )
    {
      stop = true;
      continue;
    }
    //
    // Retrieve new top level eqs
    //
    vector< Enode * > top_level_eqs;
    vector< Enode * > top_level_iffs;
    retrieveTopLevelEqs( formula, top_level_eqs, top_level_iffs, to_reinsert );
    //
    // Produce new substitutions, and
    // simplify existing ones 
    //
    if ( !produceSubstitutions( top_level_eqs, top_level_iffs ) )
    {
      stop = true;
      status = false;
      undo_stack_oper.push_back( STATUS_FALSE );
      undo_stack_lhs.push_back( NULL );
      undo_stack_rhs.push_back( NULL );
      continue;
    }

    Enode * pre_formula = formula;
    //
    // Apply new substitution, and simplify.
    // May result into a new formula, may
    // expose new substitutions, or may
    // leave formula unchanged
    //
    if ( !all_substitutions.empty( ) )
      formula = egraph.canonize( substitute( pre_formula ) );

    // Fix point reached, exit
    stop = pre_formula == formula;
  }
  // Reinsert predicates like
  // P( a )
  // f( x ) = 1
  // which might have been used to produce substitutions
  // P( a ) --> true
  // f( x ) --> 1
  // and have to be kept, otherwise unsound
  to_reinsert.push_back( formula );
  formula = egraph.mkAnd( egraph.cons( to_reinsert ) );
#endif

  //
  // Substitutions are false already
  //
  if ( !status )
    return egraph.mkFalse( );

  // 
  // Now we have to split equalities on the resulting formula
  //
  if ( config.split_equalities )
  {
    if ( config.logic == QF_IDL
      || config.logic == QF_RDL
      || config.logic == QF_LRA
      || config.logic == QF_LIA
      || config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
      formula = splitEqs( formula );
  }

  list< Enode * > simp_formulae;
  all_formulae.push_back( formula );
  // Save backtrack info
  undo_stack_oper.push_back( ADD_FORMULA );
  undo_stack_lhs.push_back( NULL );
  undo_stack_rhs.push_back( NULL );
  // Accumulate in list of formule to return
  simp_formulae.push_back( formula );

  // Now use new substitutions to simplify
  // previous formulae (i.e., not the last one
  for ( size_t i = 0 ; i + 1 < all_formulae.size( ) ; i ++ )
    simp_formulae.push_back( substitute( all_formulae[ i ] ) );

  // printSubstitutions( );

  return egraph.mkAnd( egraph.cons( simp_formulae ) );
}

void
TopLevelPropInc::retrieveTopLevelEqs( Enode * formula
                                    , vector< Enode * > & top_level_eqs 
				    , vector< Enode * > & top_level_iffs
				    , list< Enode * > & to_reinsert
				    )
{
  assert( formula );
  vector< Enode * > unprocessed_enodes;
  vector< bool >    unprocessed_polarity;

  egraph.initDup1( );

  unprocessed_enodes  .push_back( formula );
  unprocessed_polarity.push_back( true );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    assert( unprocessed_enodes.size( ) == unprocessed_polarity.size( ) );
    Enode * enode = unprocessed_enodes.back( );
    const bool polarity = unprocessed_polarity.back( );
    unprocessed_enodes  .pop_back( );
    unprocessed_polarity.pop_back( );
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup1( enode ) )
      continue;

    egraph.storeDup1( enode );
    //
    // Process children
    //
    if ( enode->isBooleanOperator( ) )
    {
      bool recurse = true;
      bool new_polarity;

      if ( enode->isAnd( ) && polarity )
	new_polarity = true;
      else if ( enode->isNot( ) )
	new_polarity = !polarity;
      else if ( enode->isOr( ) && !polarity )
	new_polarity = false;
      else
	recurse = false;

      if ( recurse )
      {
	Enode * arg_list;
	for ( arg_list = enode->getCdr( )
	    ; arg_list != egraph.enil
	    ; arg_list = arg_list->getCdr( ) )
	{
	  Enode * arg = arg_list->getCar( );
	  assert( arg->isTerm( ) );
	  unprocessed_enodes  .push_back( arg );
	  unprocessed_polarity.push_back( new_polarity );
	}
	continue;
      }
    }
    //
    // Add a new substitution for iff if possible
    //
    if ( enode->isIff( ) )
    {
      Enode * x = enode->get1st( );
      Enode * y = enode->get2nd( );

      // Make sure that if there is a variable is in x
      assert( x->isVar( ) || !y->isVar( ) );

      if ( polarity )
	top_level_iffs.push_back( enode );
      else
	top_level_iffs.push_back( egraph.mkIff( egraph.cons( x
		                              , egraph.cons( egraph.mkNot( y ) ) ) ) 
	                        );
    }
    //
    // Add a new substitution for some boolean or theory atom if possible
    //
    else if ( enode->isAtom( ) )
    {
      // Substitute boolean variable with true/false
      if ( enode->isVar( ) )
      {
	top_level_iffs.push_back( polarity ? enode : egraph.mkNot( enode ) );
      }
      else if ( !enode->isEq( ) )
      {
	/*
	 * This form of constant propagation 
	 * is not sound at the moment (see smtcomp11/test4.smt2)
	 * Maybe soundness can be easily achieved by keeping
	 * a set of substitutions with constants that are re-added
	 * to the formula everytime
	 *
	assert( enode->isTAtom( ) );
	top_level_iffs.push_back( polarity ? enode : egraph.mkNot( enode ) );
	to_reinsert.push_back( polarity ? enode : egraph.mkNot( enode ) );
	 */
      }
      else if ( polarity )
      {
	assert( enode->isEq( ) );
	top_level_eqs.push_back( enode );
      }
    }
  }

  // Done with cache
  egraph.doneDup1( );
}

bool
TopLevelPropInc::contains( Enode * term, Enode * var )
{
  assert( term );
  assert( var );
  vector< Enode * > unprocessed_enodes;
  egraph.initDup2( );

  unprocessed_enodes.push_back( term );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    if ( enode == var )
    {
      egraph.doneDup2( );
      return true;
    }
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup2( enode ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( ) ;
	arg_list != egraph.enil ;
	arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( !egraph.isDup2( arg ) )
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
    egraph.storeDup2( enode );
  }

  egraph.doneDup2( );

  return false;
}

//
// Substitute term with all the substitutions 
// so far accumulated
//
Enode *
TopLevelPropInc::substitute( Enode * formula )
{
  assert( formula );

  vector< Enode * > unprocessed_enodes;
  egraph.initDupMap1( );

  for ( map< Enode *, Enode * >::iterator it = all_substitutions.begin( )
      ; it != all_substitutions.end( )
      ; it ++ )
  {
    egraph.storeDupMap1( it->first, it->second );
  }

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
    if ( egraph.valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; arg_list != egraph.enil
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );

      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( egraph.valDupMap1( arg ) == NULL )
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

    Enode * result = egraph.copyEnodeEtypeTermWithCache( enode );

    //
    // Canonize again arithmetic atoms
    //
    if ( result->isTAtom( ) 
      && !result->isUp( ) 
      && !result->isDistinct( ) )
    {
      if ( config.logic == QF_IDL
	|| config.logic == QF_RDL
	|| config.logic == QF_LRA
	|| config.logic == QF_LIA
	|| config.logic == QF_UFIDL
	|| config.logic == QF_UFLRA )
      {
	LAExpression a( result );
	result = a.toEnode( egraph );
      }
    }

    assert( result );
    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );

  egraph.doneDupMap1( );
  assert( new_formula );
  return new_formula;
}

Enode *
TopLevelPropInc::splitEqs( Enode * formula )
{
  assert( formula );
  assert( config.logic == QF_IDL
       || config.logic == QF_RDL
       || config.logic == QF_LRA
       || config.logic == QF_LIA
       || config.logic == QF_UFIDL
       || config.logic == QF_UFLRA );

  vector< Enode * > unprocessed_enodes;
  egraph.initDupMap1( );

  list< Enode * > dtc_axioms;

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
    if ( egraph.valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; arg_list != egraph.enil
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( egraph.valDupMap1( arg ) == NULL )
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
    // Replace arithmetic atoms with canonized version
    //
    if ( enode->isTAtom( ) 
      && enode->isEq( ) )
    {
      // 
      // If DTC is active
      //
      if ( ( config.logic == QF_UFIDL
	  || config.logic == QF_UFLRA )
	  && config.sat_lazy_dtc != 0 )
      {
	//
	// These equalities will be given to the arithmetic 
	// solvers, and hence split, only if they are not 
	// "purely" uf (at the root level -- we assume we 
	// did purification before).
	//
	if ( !egraph.isRootUF( enode ) )
	{
	  LAExpression a( enode );
	  Enode * e = a.toEnode( egraph );
	  Enode * lhs = e->get1st( );
	  Enode * rhs = e->get2nd( );
	  Enode * leq = egraph.mkLeq( egraph.cons( lhs
		                    , egraph.cons( rhs ) ) );
	  LAExpression b( leq );
	  leq = b.toEnode( egraph );
	  Enode * geq = egraph.mkGeq( egraph.cons( lhs
		                    , egraph.cons( rhs ) ) );
	  LAExpression c( geq );
	  geq = c.toEnode( egraph );
	  Enode * not_e = egraph.mkNot( egraph.cons( enode ) );
	  Enode * not_l = egraph.mkNot( egraph.cons( leq ) );
	  Enode * not_g = egraph.mkNot( egraph.cons( geq ) );
	  // Add clause ( !x=y v x<=y )
	  Enode * c1 = egraph.mkOr( egraph.cons( not_e
		                  , egraph.cons( leq ) ) );
	  // Add clause ( !x=y v x>=y )
	  Enode * c2 = egraph.mkOr( egraph.cons( not_e
		                  , egraph.cons( geq ) ) );
	  // Add clause ( x=y v !x>=y v !x<=y )
	  Enode * c3 = egraph.mkOr( egraph.cons( enode
		                  , egraph.cons( not_l
		                  , egraph.cons( not_g ) ) ) );
	  // Add conjunction of clauses
	  Enode * ax = egraph.mkAnd( egraph.cons( c1
	 	                   , egraph.cons( c2
		                   , egraph.cons( c3 ) ) ) );

	  dtc_axioms.push_back( ax );
	}
	result = enode;
      }
      else
      {
	LAExpression a( enode );
	Enode * e = a.toEnode( egraph );
	Enode * lhs = e->get1st( );
	Enode * rhs = e->get2nd( );
	Enode * leq = egraph.mkLeq( egraph.cons( lhs, egraph.cons( rhs ) ) );
	LAExpression b( leq );
	leq = b.toEnode( egraph );
	Enode * geq = egraph.mkGeq( egraph.cons( lhs, egraph.cons( rhs ) ) );
	LAExpression c( geq );
	geq = c.toEnode( egraph );
	result = egraph.mkAnd( egraph.cons( leq, egraph.cons( geq ) ) );
      }
    }
    //
    // If nothing have been done copy and simplify
    //
    if ( result == NULL )
      result = egraph.copyEnodeEtypeTermWithCache( enode );

    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );
  assert( new_formula );
  egraph.doneDupMap1( );

  if ( ( config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
      && config.sat_lazy_dtc != 0 )
  {
    dtc_axioms.push_back( new_formula );
    new_formula = egraph.mkAnd( egraph.cons( dtc_axioms ) );
  }

  return new_formula;
}

bool TopLevelPropInc::produceSubstitutions( vector< Enode * > & top_level_eqs
                                          , vector< Enode * > & top_level_iffs )
{
  //
  // Process top_level_iffs first
  //
  for ( size_t i = 0 ; i < top_level_iffs.size( ) ; i ++ )
  {
    Enode * iff = top_level_iffs[ i ];

    if( iff->isIff( ) )
    {
      // Apply all substitutions
      iff = substitute( iff );
      Enode * x = iff->get1st( );
      Enode * y = iff->get2nd( );
      // Make sure that if there is a variable, it is in x
      if ( !x->isVar( ) )
      {
	Enode * tmp = x;
	x = y;
	y = tmp;
      }
      // Useless substitution, skip
      if ( !x->isVar( ) )
	continue;
      // Useless substitution, skip
      if ( contains( y, x ) )
	continue;
      // Adds substitution
      assert( all_substitutions.find( x ) == all_substitutions.end( ) );
      all_substitutions[ x ] = y;
      // Save backtrack info
      undo_stack_lhs.push_back( x );
      undo_stack_rhs.push_back( y );
      undo_stack_oper.push_back( ADD_SUBST );
      // Substitute backward x with y
      backwardSubstitute( x );
    }
    else
    {
      // If not of the form
      // (not (= x y))
      assert( !iff->isNot( ) 
	   || !iff->get1st( )->isEq( ) ); 
      // Or of the form
      // (= x y)
      assert( !iff->isEq( ) );

      Enode * lhs = iff;
      Enode * rhs = egraph.mkTrue( );
      if ( iff->isNot( ) )
      {
	lhs = iff->get1st( );
	rhs = egraph.mkFalse( );
      }

      // Adds substitution
      assert( all_substitutions.find( lhs ) == all_substitutions.end( ) );
      all_substitutions[ lhs ] = rhs;
      // Save backtrack info
      undo_stack_lhs.push_back( lhs );
      undo_stack_rhs.push_back( rhs );
      undo_stack_oper.push_back( ADD_SUBST );
    }
  }
  // 
  // Process top_level_eqs
  //
  for ( size_t i = 0 ; i < top_level_eqs.size( ) ; i ++ )
  {
    Enode * eq = top_level_eqs[ i ];
    // Apply all substitutions
    eq = substitute( eq );

    if ( eq->isFalse( ) )
      return false;

    if ( eq->isTrue( ) )
      continue;

    // Canonize (arithmetic formulae might get uncanonized)
    eq = egraph.canonize( eq );
    Enode * lhs = eq->get1st( );
    Enode * rhs = eq->get2nd( );
    //
    // Determine what kind of equality it is
    //
    // If arithmetic equality, solve w.r.t. a variable
    if ( lhs->isArithmeticOp( )
      || rhs->isArithmeticOp( ) )
    {
      assert( !lhs->isArithmeticOp( ) || rhs->isConstant( ) );
      assert( !rhs->isArithmeticOp( ) || lhs->isConstant( ) );
      LAExpression lae( eq );
      pair< Enode *, Enode * > sub = lae.getSubst( egraph ); 
      lhs = sub.first;
      rhs = sub.second;
    }
    else
    {
      // Make sure that if there is a variable, it is in x
      if ( !lhs->isVar( ) )
      {
	Enode * tmp = lhs;
	lhs = rhs;
	rhs = tmp;
      }
      // Useless substitution, skip
      if ( !lhs->isVar( ) )
	continue;
      // Useless substitution, skip
      if ( contains( rhs, lhs ) )
	continue;
    }
    // Make sure substitution does not exists
    assert( all_substitutions.find( lhs ) == all_substitutions.end( ) );
    // Adds substitution
    all_substitutions[ lhs ] = egraph.canonize( rhs );
    // Save backtrack info
    undo_stack_lhs.push_back( lhs );
    undo_stack_rhs.push_back( rhs );
    undo_stack_oper.push_back( ADD_SUBST );
    // Substitute backward lhs with rhs
    backwardSubstitute( lhs );
  }

  return true;
}

void TopLevelPropInc::backwardSubstitute( Enode * lhs )
{
  assert( lhs );
  for ( map< Enode *, Enode * >::iterator it = all_substitutions.begin( )
      ; it != all_substitutions.end( )
      ; it ++ )
  {
    // Skip new substitution
    if ( it->first == lhs )
      continue;
    Enode * new_it_second = egraph.canonize( substitute( it->second ) );
    // Skip, nothing has changed
    if ( new_it_second == it->second )
      continue;
    // Save substitution for backtracking
    undo_stack_oper.push_back( SUBSTITUTION );
    // Store mod lhs
    undo_stack_lhs.push_back( it->first );
    // Store old rhs
    undo_stack_rhs.push_back( it->second );
    // Replace
    it->second = new_it_second;
  }
}

void TopLevelPropInc::printSubstitutions( )
{
  cerr << "Substitutions: " << endl;
  for ( map< Enode *, Enode * >::iterator it = all_substitutions.begin( )
      ; it != all_substitutions.end( ) 
      ; it ++ )
  {
    cerr << it->first << " --> " << it->second << endl;
  }
}
