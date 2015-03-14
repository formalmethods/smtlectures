/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#include "MCMTContext.h"
#include "MC.h"

void
MC::updateCoveringRelation ( Node * n , vector< Node * > & parents )
{
  // parents contains all the nodes that has been asserted 
  // to make the fixpoint-check valid.
  // So n is covered by "parents"
  n->addCoveringParents( parents );

  // for each coverinf parent, add n as a covered child
  for ( size_t i = 0 ; i < parents.size( ) ; i++ )
  {
    parents[ i ]->addCoveredChild( n );
  }
  
  if ( config.verbosity > 2 )
  {
    n->printCoveringRelation( );
  }
  
  cout << "node " << n->getId() << " is covered";
#ifdef PEDANTIC_DEBUG
  cout << "(4)";
#endif
  cout << endl;

  n->setCovered( true );
  container.setCoveredNodes( container.getCoveredNodes( ) + 1 );
  
  // lock children of this node n that has been covered
  n->lockChildren( );

  if ( config.verbosity > 1 )
  {
    n->printCoveringRelation( );
  }
}


Enode *
MC::cleanFormulaFromConcreteArrays( Enode * f )
{
  
  assert( false );
  assert( f );
 
  vector < Enode * > origs, dests;

  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( f );
  egraph.initDup1( );
  while ( !unprocessed_enodes.empty( ) )
  {
    Enode * e = unprocessed_enodes.back( );
    unprocessed_enodes.pop_back( );
    if ( egraph.isDup1( e ) )
      continue;

    Enode * arg_list;
    if ( !e->isLit( ) )
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
      assert( e->isLit( ) );
      
      Enode * lit = e;
      if ( lit->isNot( ) )
      {
        lit = lit->get1st( );
      }

      // check if the first variable is an abstracted array
      if ( lit->get1st( )->isSelect( ) )
      {
        if ( !lit->get1st( )->get1st( )->getAbstr( ) )
        {
          origs.push_back( e );
          dests.push_back( egraph.mkTrue( ) );
        }
      }
      // the first variable is not an array, check if the second variable is an abstracted array
      else
      {
        if ( lit->get2nd( )->isSelect( ) )
        {
          if ( !lit->get2nd( )->get1st( )->getAbstr( ) )
          {
            origs.push_back( e );
            dests.push_back( egraph.mkTrue( ) );
          }
        }
      }
    }

    egraph.storeDup1( e );
  }
  egraph.doneDup1( );

  return egraph.substitute( f , origs , dests );
}


// check if a formula has mixed literals
bool
MC::isTermAbstracted( Enode * t )
{
  assert( t );
  assert( t->isTerm( ) );
  
  unsigned abstracted = 0 , concrete = 0; 


  set< Enode * > cache;
  vector< Enode * > unprocessed_enodes;

  unprocessed_enodes.push_back( t );

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

    if ( e->isVar( ) && index_vars.find( e ) == index_vars.end( ) )
    {
      if ( e->getAbstr( ) )
      {
        abstracted++;
      }
      else
      {
        concrete++;
      }
    }

    assert( cache.find( e ) == cache.end( ) );
    cache.insert( e );
  }
  
  if ( abstracted > 0 && concrete > 0 )
  {
    cerr << "MIXED TERM: " << t << endl;
    exit( );
  }
  
  if ( abstracted > 0 )
  {
    return true;
  }
  if ( concrete > 0 )
  {
    return false;
  }

    
  cerr << "NO TERM: " << t << endl;
  exit( );
  
  return false;
}


// check if a formula has mixed literals
bool
MC::existMixedLiteralsInFormula( Enode * f )
{
  assert( f->isLit( ) || f->isAnd( ) );

  vector < Enode * > lits;
  retrieveLits( f , lits );

  for ( size_t i = 0 ; i < lits.size( ) ; i++ )
  {
    Enode * lit = lits[ i ];
    if ( lit->isNot( ) )
    {
      lit = lits[ i ]->get1st( );
    }
    
    if ( lit->isTrue( ) || lit->isFalse( ) )
    {
      continue;
    }

    assert( lit->isLit( ) );
    assert( lit->get1st( )->isTerm( ) && lit->get2nd( )->isTerm( ) );
    
    // constants
    if ( lit->get1st( )->isConstant( ) || lit->get2nd( )->isConstant( ) )
    {
      continue;
    }
    
    // index vars
    if ( index_vars.find( lit->get1st( ) ) != index_vars.end( ) || index_vars.find( lit->get2nd( ) ) != index_vars.end( ) )
    {
      continue;
    }

    if ( isTermAbstracted( lit->get1st( ) ) != isTermAbstracted( lit->get2nd( ) ) )
    {
      return true;
    }
  }

  return false;
}


// check the existence of mixed literals or the possibility to build them
bool
MC::existMixedLiterals(  )
{  
  
  // check the initial formula
  if ( existMixedLiteralsInFormula( initial ) )
  {
    cerr << "Error: Initial formula ";
    initial->yicesPrint( cerr );
    cerr << " has mixed (abstract and non abstract) literals!" << endl;
    return true;
  }
 
  // check the unsafe formulas
  list< Node * > tbv = container.getTbvList( );
  for ( list< Node * >::iterator it = tbv.begin( )
      ; it != tbv.end( )
      ; it++ )
  {
    if ( (*it)->isUnsafe( ) && existMixedLiteralsInFormula( (*it)->getLabel( ) ) )
    {
      cerr << "Error: Unsafe formula ";
      (*it)->getLabel( )->yicesPrint( cerr );
      cerr << " has mixed (abstract and non abstract) literals!" << endl;
      return true;
    }
  }

  // check transitions
  for ( size_t t = 0 ; t < transitions.size( ) ; t++ )
  {
    // check transition guard
    if ( existMixedLiteralsInFormula( transitions[ t ]->getGuard( ) ) )
    {
      cerr << "Error: Transition " << transitions[ t ]->getId( );
      cerr << " has mixed (abstract and non abstract) literals in the guard!" << endl;
      return true;
    }
    vector < Enode * > uguards = transitions[ t ]->getUGuards( );
    
    // check transition uguards
    for ( size_t u = 0 ; u < uguards.size( ) ; u++ )
    {
      if ( existMixedLiteralsInFormula( uguards[ u ] ) )
      {
        cerr << "Error: Transition " << transitions[ t ]->getId( );
        cerr << " has mixed (abstract and non abstract) literals in the universal guard ";
        uguards[ u ]->yicesPrint( cerr );
        cerr << endl;
        return true;
      }
    }
    
    // check cases: condition and updates
    vector < Transition::Case* > cases = transitions[ t ]->getCases( );
    for ( size_t c = 0 ; c < cases.size( ) ; c++ )
    {
      // case condition
      if ( existMixedLiteralsInFormula( cases[ c ]->condition ) )
      {
        cerr << "Error: Transition " << transitions[ t ]->getId( );
        cerr << " has mixed (abstract and non abstract) literals in the case ";
        cases[ c ]->condition->yicesPrint( cerr );
        cerr << endl;
        return true;
      }

      for ( size_t a = 0 ; a < array_vars.size( ) ; a++ )
      {
        if ( index_vars.find( cases[ c ]->values[ a ] ) != index_vars.end( ) )
        {
          continue;
        }
        if ( cases[ c ]->values[ a ]->isConstant( ) )
        {
          continue;
        }
        if ( isTermAbstracted( cases[ c ]->values[ a ] ) != array_vars[ a ]->enode->getAbstr( ) )
        {
          cerr << "Error: Transition " << transitions[ t ]->getId( );
          cerr << " will generate formule with mixed (abstract and non abstract) literals because of the update '";
          cerr << array_vars[ a ]->enode << " --> ";
          cases[ c ]->values[ a ]->yicesPrint( cerr );
          cerr << "'" << endl;
          return true;
        }
      }
    }
  }
  
  return false;
}



Enode *
MC::cleanAbstractLabel( Enode * f , bool /* force */ )
{
  
  if ( config.abstraction_arithmetic )
  {
    f = abstractArithmeticLiterals( f );
  }
  
  if ( config.abstraction_limit == 0 )
    return f;
  if ( config.abstraction_limit > 0 )
    config.abstraction_limit--;

  // convert the formula in DNF
  Enode * DNF_label = egraph.convertIntoDNF( f );
 
  if ( DNF_label->isOr( ) )
  {

    if ( config.verbosity > 1 )
    {
      cerr << "original formula " << f << endl;
      cerr << "converted formula " << DNF_label << endl;
    } 
  
    vector < Enode * > disjuncts;
    
    vector< Enode * > unprocessed_enodes;
    unprocessed_enodes.push_back( DNF_label );
    while ( !unprocessed_enodes.empty( ) )
    {
      Enode * e = unprocessed_enodes.back( );
      unprocessed_enodes.pop_back( );
 
      Enode * arg_list;
      if ( e->isOr( ) )
      {
        for ( arg_list = e->getCdr( )
            ; !arg_list->isEnil( )
            ; arg_list = arg_list->getCdr( ) )
        {
          Enode * arg = arg_list->getCar( );
          unprocessed_enodes.push_back( arg );
        }
      }
      else
      {
        assert( e->isAnd( ) );
        disjuncts.push_back( cleanAbstractLabel( e ) );
      }
    }

    return egraph.mkOr( egraph.cons( disjuncts ) );
  }
  else
  {
    assert( f->isAnd( ) || f->isLit( ) );
    vector < Enode * > lits;
    retrieveLits ( f , lits );
  
    list < Enode * > new_label;
    for ( size_t i = 0 ; i < lits.size( ) ; i++ )
    {
      Enode * lit = lits[ i ];
      if ( lit->isNot( ) )
      {
        lit = lit->get1st( );
      }
 
      bool del = true;
      // check if the first variable is an abstracted array
      if ( lit->get1st( )->isSelect( ) )
      {
        if ( !lit->get1st( )->get1st( )->getAbstr( ) )
        {
          del = false;
        }
      }
      // the first variable is not an array, check if the second variable is an abstracted array
      else
      {
        if ( lit->get2nd( )->isSelect( ) )
        {
          if ( !lit->get2nd( )->get1st( )->getAbstr( ) )
          {
            del = false;
          }
        }
      }
      if ( !del )
      {
        new_label.push_back( lits[ i ] );
      }
    }
    
    
    // assert( !new_label.empty( ) );
    
    // keeps the literals over index variables, otherwise we can reduce the number of index
    // variables in the formulas, and this will produce a wrong counterexample!
    vector < Enode * > label_vars;
    retrieveVars( f , label_vars );
    for ( size_t v1 = 0 ; v1 != label_vars.size( ) ; v1 ++ )
    {
      for ( size_t v2 = 0 ; v2 != label_vars.size( ) ; v2 ++ )
      {
        if ( v1 == v2 ) continue;
        new_label.push_back( egraph.mkNot( egraph.cons( egraph.mkEq ( egraph.cons( label_vars[ v1 ] , egraph.cons( label_vars[ v2 ] ) ) ) ) ) );
      }
    }
 
    return egraph.mkAnd( egraph.cons( new_label ) ) ;              
  }
}




void
MC::cleanAbstractLabel( Node * n , bool force )
{
  
  if ( !force && config.abstract_transitions && !n->getParentTransition( )->getAbstracted( ) ) 
  {
    return;
  }
  
  Enode * new_label = cleanAbstractLabel( n->getLabel( ) , force );
  
  if ( config.verbosity > 1 ) {
    cerr << "Label cleaning:" << endl;
    cerr << " From: ";
    n->getLabel( )->yicesPrint( cerr );
    cerr << endl;
    cerr << " To: ";
    new_label->yicesPrint( cerr );
    cerr << endl << endl;
  }
  
  n->setLabel( new_label );
  if ( n->getAbstracted( ) ) cerr << "WARNING: node " << n->getId( ) << " has already been abstracted!" << endl;
  n->setAbstracted( true );
}


void
MC::getCE( Node * n 
         , vector < Enode * > & counterexample
         , vector < Enode * > & origs_interp
         , vector < Enode * > & dests_interp )
{
  assert( n );
  
  if ( config.verbosity > 1 )
  {
    cerr << "\n\n\n";
    cerr << "This node intersect with the initial set of states:";
    n->getLabel( )->yicesPrint( cerr );
    cerr << endl;
    n->printHistory( );
    cerr << endl;
  }

  // clear the tmp vector for counterexamples
  counterexample.clear( );

  // retrieve transitions in this path
  // in the meanwhile collect the number of index variables
  vector < Transition * > historyTransitions;
  vector < Node * > historyNodes;
  set < Enode * > ce_index_vars;
  Node * unsafe = n;
  while ( !unsafe->isUnsafe( ) )
  {
    historyTransitions.push_back( unsafe->getParentTransition( ) );
    vector < Enode * > vars = unsafe->getLabelVars( );
    ce_index_vars.insert( vars.begin( ) , vars.end( ) );
    historyNodes.push_back( unsafe );
    unsafe = unsafe->getParent( );
  }
  
  vector < Enode * > vars = unsafe->getLabelVars( );
  ce_index_vars.insert( vars.begin( ) , vars.end( ) );

  assert( unsafe->isUnsafe( ) );
  assert( historyTransitions.size( ) == historyNodes.size( ) );

  vector < Enode * > index_vars;
  for ( set< Enode * >::iterator it = ce_index_vars.begin( )
      ; it != ce_index_vars.end( )
      ; it++ )
  {
    index_vars.push_back( (*it) );
  }
  cerr << endl;

  // subscript index for each variable
  int sub_index = 0;

  assert( !historyTransitions.empty( ) );
  
  // tmp vectors for saving substitutions
  vector < Enode * > origs, dests;
  
  // starting from the initial, we instantiate the array variables
  Enode * inst_initial = getIndexedFormula( instantiateInitial( index_vars ) , sub_index , origs_interp , dests_interp );
  // initial node pushed in the counterexample
  counterexample.push_back( inst_initial );
  
  // every time we retrieve a new formula in the counterexample, we need to check how many variables had the corresponding
  // node, since 

  // retrieve the formula representing the transition
  size_t t;
  for ( t = 0 ; t < historyTransitions.size( )-1 ; t++ )
  {
    origs.clear( );
    dests.clear( );
    // save the formula of the counterexample
    Enode * tr_formula = getTransitionFormula( historyTransitions[ t ] , historyNodes[ t ] , historyNodes[ t+1 ]->getLabelVars( ) , historyNodes[ t ]->getCases( ) , sub_index , origs , dests );
    counterexample.push_back( tr_formula );
    // save origs and dests in origs_interp and dests_interp
    origs_interp.insert( origs_interp.end( ) , origs.begin( ) , origs.end( ) );
    dests_interp.insert( dests_interp.end( ) , dests.begin( ) , dests.end( ) );

    sub_index++;
  }
  
  origs.clear( );
  dests.clear( );
  // save the formula of the counterexample
  Enode * tr_formula = getTransitionFormula( historyTransitions[ historyTransitions.size( )-1 ] , historyNodes[ historyTransitions.size( )-1 ] , unsafe->getLabelVars( ) , historyNodes[ historyTransitions.size( )-1 ]->getCases( ) , sub_index , origs , dests );
  counterexample.push_back( tr_formula );
  // save origs and dests in origs_interp and dests_interp
  origs_interp.insert( origs_interp.end( ) , origs.begin( ) , origs.end( ) );
  dests_interp.insert( dests_interp.end( ) , dests.begin( ) , dests.end( ) );
  sub_index++;


  counterexample.push_back( getIndexedFormula( unsafe->getLabel( ) , sub_index , origs , dests ) );
  // save origs and dests in origs_interp and dests_interp
  origs_interp.insert( origs_interp.end( ) , origs.begin( ) , origs.end( ) );
  dests_interp.insert( dests_interp.end( ) , dests.begin( ) , dests.end( ) );
}





// instantiate the initial formula
Enode *
MC::instantiateInitial( vector < Enode * > & index_vars )
{
  // works only if the initial formula has only one variable!
  assert( initial_vars.size( ) == 1 );

  // in subformulae we put each instance of the initial formula, then we will make the AND
  list < Enode * > subformulae;
  vector < Enode * > dests;
  for ( size_t v = 0 ; v < index_vars.size( ) ; v++ )
  {
    dests.clear( );
    dests.push_back( index_vars[ v ] );
    subformulae.push_back( egraph.substitute( initial, initial_vars , dests ) );
  }

  return egraph.mkAnd ( egraph.cons( subformulae ) );
}



void
MC::refineNodes( vector < Enode * > & interpolants 
               , Node * last 
               , vector < Enode * > & origs_interp
               , vector < Enode * > & dests_interp )
{
  // iterate over all the interpolants starting from the back, and skipping
  // the last (because it is false and tells that the initial is unreachable!)

  Node * n = last , * prev = last->getParent( );
 
  // a False interpolants means that the node we are refining would not have been computed!
  int refinements = 0;
  for ( vector< Enode * >::reverse_iterator it = interpolants.rbegin( )+1
      ; it != interpolants.rend( ) && !(*it)->isTrue( ) && !(*it)->isTrue( )
      ; it++ , refinements++ )
  {

    if ( config.abstraction_refinement_depth > 0 && refinements > config.abstraction_refinement_depth )
    {
      // do not refine nodes under the 'abstraction_refinement_depth' threshold
      return;
    }
    
    assert( n );

    if ( (*it)->isFalse( ) )
    {
      
      // false labels are not considered refinements
      refinements--;

      // delete this node!
      if ( !( n->isDeleted( ) ) )
      {
        cout << "node " << n->getId( ) << " is deleted (empty label) ";
#ifdef PEDANTIC_DEBUG
        cout << "(1)";
#endif
        cout << endl;
        deleteNode ( n );
      }
    }
    else
    {
      Enode * interp = egraph.substitute( (*it) , origs_interp , dests_interp );
      if ( !interp->isTrue( ) )
      {

#ifdef PEDANTIC_DEBUG
        checkInterpolant( interp );
#endif


        // refine the label
        Enode * old_label = n->getLabel( );

        // conjoint the interpolant with the label
        n->setLabel( egraph.mkAnd( egraph.cons( n->getLabel( ) , egraph.cons( interp ) ) ) );
        
        Enode * new_label = n->getLabel( );
        
        // check if the node has really been refined!
        // the new label implies the old one by definition
        // if the old one implies the new one, they are equivalent
        if ( config.verbosity > 1 )
        {
          cerr << "node " << n->getId( ) << ":";
          old_label->yicesPrint( cerr );
          cerr << endl;
        }
        if ( !checkValidImplication( old_label , new_label ) )
        {
          
#ifdef PEDANTIC_DEBUG
          // check that the new preimage implies the old one!
          if ( !checkValidImplication( new_label , old_label ) )
          {
            cerr << "\n\nERROR!!! ---------------------------------" << endl;
            cerr << " After refinement, the new label do not implies the old one!" << endl;
            cerr << " Old label: ";
            old_label->yicesPrint( cerr );
            cerr << endl;
            cerr << " New label: ";
            new_label->yicesPrint( cerr );
            cerr << endl;
            
            cerr << "\n\nERROR!!! ---------------------------------" << endl;
            
          }

          
          // check that the number of variables is still the same!
          vector < Enode * > old_vars, new_vars;
          retrieveVars( old_label , old_vars );
          retrieveVars( new_label , new_vars );
          if ( old_vars.size( ) != new_vars.size( ) )
          {
            cerr << "NEW_VARIABLES DIFFERENT FROM OLD VARIABLES!" << endl;
            
            cerr << "Old label: " << old_label << endl;
            cerr << "New label: " << new_label << endl;
            
            cerr << "Old vars:" << endl;
            for ( size_t i = 0 ; i < old_vars.size( ) ; i++ )
            {
              cerr << "\t" << old_vars[ i ] << endl;
            }
            cerr << "New vars:" << endl;
            for ( size_t i = 0 ; i < new_vars.size( ) ; i++ )
            {
              cerr << "\t" << new_vars[ i ] << endl;
            }
            assert( false );
          }
#endif
          
          if ( isSat( n ) )
          {
            cout << "node " << n->getId( ) << " is refined" << endl;
            if ( config.verbosity > 2 )
            {
              cerr << "new label: ";
              new_label->yicesPrint( cout );
              cerr << endl;
            }
          }
          else
          {
            cout << "node " << n->getId( ) << " is deleted (empty label) ";
#ifdef PEDANTIC_DEBUG
            cout << "(2)";
#endif
            cout << endl;
            deleteNode( n );
          }
        
          n->setRedefinition( n->getRedefinition( ) + 1 );
          // re-define the node with the new label!
          solver.Define( n , array_vars );
          
          fixCoveredChildren( n );
          checkChildren( n );
        }
        else
        {
          if ( config.verbosity > 1 )
          {
            cerr << "node " << n->getId( ) << " has not been refined because the old label implies the new one!" << endl;
          }
        }
      }
    }
    n = prev;
    if ( !n->isUnsafe( ) )
    {
      prev = n->getParent( );
    }
  }
}





Enode *
MC::getArrayVar( ArrayVar * var , int id )
{
  assert( var );
  
  char buf[ 64 ] = { "\0" };
  sprintf( buf, "%s_%u", var->getName( ), id );
  Snode * type = var->getType( );
  // Declare symbol if not there
  bool declared = false;
  if ( !egraph.hasSymbol( buf, NULL, type ) )
  {
    declared = true;
    egraph.newSymbolLog( buf, NULL, type );
  }


  // Create a variable
  Enode * new_var = egraph.mkVar( buf );
  new_var->setMcmtId( var->enode->getMcmtId( ) );
  new_var->setAbstr( var->enode->getAbstr( ) );
 
  /*
  if ( declared )
  {
    // Assert that it is a global array (if it is so)
    if ( var->global )
    {
      assert( !z_variables.empty( ) );
      for ( size_t i = 1 ; i < z_variables.size( ) ; i++ )
      {
        i_solver.Assert( egraph.mkEq( egraph.cons( egraph.mkSelect( new_var , z_variables[ i ] ) , egraph.cons( egraph.mkSelect( new_var , z_variables[ i-1 ] ) ) ) ) );
      }
    }
  }
  */

  return new_var;
}





Enode *
MC::getIndexedFormula( Enode * formula 
                       , int vars_id
                       , vector < Enode * > & origs_interp
                       , vector < Enode * > & dests_interp )
{
  // create all the variables with the right index
  vector < Enode * > origs , dests;
  for ( size_t v = 0 ; v < array_vars.size( ) ; v++ )
  {
    origs.push_back( array_vars[ v ]->enode );
    dests.push_back( getArrayVar( array_vars[ v ] , vars_id ) );

    // save the association to remove subscript indexes and retrieve labels
    dests_interp.push_back( array_vars[ v ]->enode );
    origs_interp.push_back( getArrayVar( array_vars[ v ] , vars_id ) );
  }
  return egraph.substitute( formula , origs , dests );
}




Enode *
MC::getTransitionUpdate ( Transition * t 
                        , Node * n 
                        , vector < Enode * > & vars
                        , vector < unsigned > & vars_cases
                        , int vars_id
                        , vector < Enode * > & origs_interp
                        , vector < Enode * > & dests_interp
                        )
{
  if ( n->isUnsafe( ) )
  {
    cerr << "UNSAFE!" << endl;
  }
  
  vector< Transition::Case * >cases = t->getCases( );
 
  vector < bool > used_var( array_vars.size( ) , false );
  
  list < Enode * > update_formulae;


  // for every index var used in the counterexample instantiate the j in the cases
  for ( size_t j = 0 ; j < vars.size( ) ; j++ )
  {    
    // partial updates (cases + assignments)
    list< Enode * >cases_formulae;

    vector< Enode * >origs, dests;
    assert( t->getVar( FIRST ) );
    origs.push_back( t->getVar( FIRST ) );
    assert( n->getVar( FIRST ) );
    dests.push_back( n->getVar( FIRST ) );
    if ( t->getVar( SECOND ) )
    {
      assert( t->getVar( SECOND ) );
      origs.push_back( t->getVar( SECOND ) );
      assert( n->getVar( SECOND ) );
      dests.push_back( n->getVar( SECOND ) );
    }
    origs.push_back( t->getVj( ) );
    dests.push_back( vars[ j ] );
    
    
    // for each case we instantiate the case and create the update for each variable
    list< Enode * >update_list;
   
    // in this case, create the formula that represents it
    assert( vars_cases.size( ) > vars[ j ]->getMcmtId( )  );
    size_t c = vars_cases[ vars[ j ]->getMcmtId( ) ];
    assert( c < cases.size( ) );
    for ( size_t v = 0 ; v < cases[ c ]->values.size( ) ; v++ )
    {
      // add the case correctly instantiated ( pushing back the case "(= x j)" )
      update_list.push_back( getIndexedFormula( cases[ c ]->condition , vars_id , origs_interp , dests_interp ) );
//      cerr << "(1) ";
//      getIndexedFormula( cases[ c ]->condition , vars_id , origs_interp , dests_interp )->yicesPrint( cerr );
//      cerr << endl;

      if ( array_vars[ v ]->global )
      {
        assert( v < array_vars.size( ) );
        // second part of the equality: create the new var with the right id ( array_new_var is the array_var[ v ] with the "_vars_id" added at the end of the name )
        Enode * array_new_var = getArrayVar( array_vars[ v ] , vars_id+1 );
//        cerr << "(2) ";
//        getArrayVar( array_vars[ v ] , vars_id+1 )->yicesPrint( cerr );
//        cerr << endl;
       
        used_var[ v ] = true;
        // add indexes to the update ( this is the first part of the equality, i.e. the update -- remember that the trace is built from the unsafe! )
        vector < Enode * > origs;
        vector < Enode * > dests;
        origs.push_back( t->getVj( ) );
        dests.push_back( z_variables[ 0 ] );
        Enode * update = egraph.substitute( getIndexedFormula( cases[ c ]->values[ v ] , vars_id , origs_interp , dests_interp ) , origs , dests );
//        cerr << "(3) ";
//        getIndexedFormula( cases[ c ]->values[ v ] , vars_id , origs_interp , dests_interp )->yicesPrint( cerr );
//        cerr << endl;

        // creates the equality we need to track the update
        update_list.push_back( egraph.mkEq( egraph.cons( egraph.mkSelect( array_new_var , z_variables[ 0 ] ) , egraph.cons( update ) ) ) );
//        cerr << "(4) ";
//        egraph.mkEq( egraph.cons( egraph.mkSelect( array_new_var , z_variables[ 0 ] ) , egraph.cons( update ) ) )->yicesPrint( cerr );
//        cerr << endl << endl << endl;

      }
      else
      {
        assert( v < array_vars.size( ) );
        // create the new var with the right id ( array_new_var is the array_var[ v ] with the "_vars_id" added at the end of the name )
        Enode * array_new_var = getArrayVar( array_vars[ v ] , vars_id+1 );
//        cerr << "(2) ";
//        getArrayVar( array_vars[ v ] , vars_id+1 )->yicesPrint( cerr );
//        cerr << endl;
       
        used_var[ v ] = true;
        // add indexes to the update ( this is the first part of the equaliti, i.e. the name of the 
        Enode * update = getIndexedFormula( cases[ c ]->values[ v ] , vars_id , origs_interp , dests_interp );
//        cerr << "(3) ";
//        getIndexedFormula( cases[ c ]->values[ v ] , vars_id , origs_interp , dests_interp )->yicesPrint( cerr );
//        cerr << endl;

        // creates the equality we need to track the update
        update_list.push_back( egraph.mkEq( egraph.cons( egraph.mkSelect( array_new_var , t->getVj( ) ) , egraph.cons( update ) ) ) );
//        cerr << "(4) ";
//        egraph.mkEq( egraph.cons( egraph.mkSelect( array_new_var , t->getVj( ) ) , egraph.cons( update ) ) )->yicesPrint( cerr );
//        cerr << endl << endl << endl;
      }
    }
    // creates the formula that represents the update of this case!
    cases_formulae.push_back( egraph.mkAnd ( egraph.cons( update_list ) ) );
    
    update_list.clear( );

    Enode * update_formula = egraph.mkAnd( egraph.cons( cases_formulae ) );
    
    // instantiate the variables
    assert( origs.size( ) == dests.size( ) );
    assert( !origs.empty( ) );
    update_formulae.push_back( egraph.substitute( update_formula , origs , dests ) );
  }
  
//  cerr << endl << endl << endl << endl << endl;
  // return the AND of all the cases
  return egraph.mkAnd ( egraph.cons( update_formulae ) );
}

Enode *
MC::getTransitionFormula ( Transition * t 
                         , Node * n 
                         , vector < Enode * > & vars
                         , vector < unsigned > & vars_cases
                         , int vars_id
                         , vector < Enode * > & origs_interp 
                         , vector < Enode * > & dests_interp )
{
  Enode * guard = getIndexedFormula( t->getGuard( ), vars_id , origs_interp , dests_interp );
  vector< Enode * >origs, dests;
  assert( t->getVar( FIRST ) );
  origs.push_back( t->getVar( FIRST ) );
  assert( n->getVar( FIRST ) );
  dests.push_back( n->getVar( FIRST ) );
  if ( t->getVar( SECOND ) )
  {
    assert( t->getVar( SECOND ) );
    origs.push_back( t->getVar( SECOND ) );
    assert( n->getVar( SECOND ) );
    dests.push_back( n->getVar( SECOND ) );
  }
   
  Enode * updates = getTransitionUpdate( t , n , vars , vars_cases , vars_id , origs_interp , dests_interp );
  return egraph.mkAnd( egraph.cons( egraph.substitute( guard, origs, dests ) , egraph.cons( updates ) ) );
}

void
MC::printCE ( vector < Enode * > & counterexample , ostream & os )
{
  assert( !counterexample.empty( ) );
  os << "\n\n +++++++++++++++++++++++++++  COUNTEREXAMPLE FOUND  +++++++++++++++++++++++++++" << endl;
  for ( size_t i = 0 ; i < counterexample.size( ) ; i++ )
  {
    os << "\t";
    counterexample[ i ]->yicesPrint( os );
    os << endl;
  }
  os << " +++++++++++++++++++++++++++  COUNTEREXAMPLE - END  +++++++++++++++++++++++++++" << endl;
}

bool
MC::CounterexampleIsFeasible( vector < Enode * > & counterexample 
                            , vector < Enode * > & interpolants
                            , vector < Enode * > & origs_interp 
                            , vector < Enode * > & dests_interp ) 
{
  
  if( config.verbosity > 1 )
  {
    cerr << "\n\n\n\n\n\n\n\n\n\n";
    cerr << "COUNTEREXAMPLE IS:" << endl;
  }


  // in order to avoid interpolants with more zN variables than the one shared
  // between the two formulas, assert the "globality" of arrays (e.g. "pc[zN] = pc[zM]")
  // and instantiated system axioms only in the partitions.

  // cache for the already asserted var zN
  set < Enode * > asserted_vars;
  vector < Enode * > introduced_vars;
  vector < Enode * > to_be_asserted;
  
  // befor starting to assert the counterexample
  // check if all the needed variables have been declared
  for ( size_t k = 0 ; k < counterexample.size( ) ; k++ )
  {
    for ( size_t a = 0 ; a < array_vars.size( ) ; a++ )
    {
      getArrayVar( array_vars[ a ] , k ); 
    }
  }

  i_solver.Push( );

#ifdef BACKWARD_INTERPOLANTION
  unsigned i = 1;
  for ( vector< Enode * >::reverse_iterator it = counterexample.rbegin( )
      ; it != counterexample.rend( ) 
      ; it++ , i++ )
  {
#else  // FORWARD INTERPOLATION
  unsigned i = 0;
  for ( vector< Enode * >::iterator it = counterexample.begin( )
      ; it != counterexample.end( ) 
      ; it++ , i++ )
  {
#endif

    // clear the "to be asserted" vector with all the system axioms etc...
    to_be_asserted.clear( );
    to_be_asserted.push_back( (*it) );

    // now find the arrays with the correct index
    // for the array_variables
#ifdef BACKWARD_INTERPOLANTION
    int index = (counterexample.size( ) -1) - i;
#else  // FORWARD INTERPOLATION
    int index = i;
#endif
    assert( index >= -1 );
    
    
    vector < Enode * > vars;
    retrieveVars( (*it) , vars );
    assert( !vars.empty( ) );
    for ( size_t v = 0 ; v < vars.size( ) ; v++)
    {
      // vars are >= 0
      to_be_asserted.push_back( egraph.mkGeq( egraph.cons( vars[ v ] , egraph.cons( egraph.mkNum( "0" ) ) ) ) );

      if ( asserted_vars.find( vars[ v ] ) == asserted_vars.end( ) )
      {
        // assert that this variable is different from all the others
        // already asserted
        for ( size_t v1 = 0 ; v1 < introduced_vars.size( ) ; v1++ )
        {
          to_be_asserted.push_back( egraph.mkNot( egraph.mkEq( egraph.cons( vars[ v ] , egraph.cons( introduced_vars[ v1 ] ) ) ) ) );
        }
        
        // introduce the new var to instantiate correctly the system axiom!
        asserted_vars.insert( vars[ v ] );
        introduced_vars.push_back( vars[ v ] );
      }
      
      // now introduced_vars is a vector with all the variables introduced in the CE up to now!
    }
      
    vector < Enode * > sys_ax_vars;
    retrieveVars( (*it) , sys_ax_vars );
      
    vector < Enode * > origs;
    vector < Enode * > dests;
    // set up the list of arrays to instantiate system axioms
    // and "globality" of arrays
    for ( size_t a = 0 ; a < array_vars.size( ) ; a++ )
    {
      origs.push_back( array_vars[ a ]->enode );
      
      // when we instantiate the initial formula index can be -1.
      // So we force it to be 0
      Enode *indexed_array = getArrayVar( array_vars[ a ] , index ); 
      if ( index >= 0 )
        indexed_array = getArrayVar( array_vars[ a ] , index ); 
      else
        indexed_array = getArrayVar( array_vars[ a ] , 0 ); 

      dests.push_back( indexed_array );
      
      for ( size_t j = 1 ; j < sys_ax_vars.size( ) ; j++ )
      {
        if ( array_vars[ a ]->global && introduced_vars.size( ) > 1 )
        {
          to_be_asserted.push_back( egraph.mkEq( egraph.cons( egraph.mkSelect( indexed_array , sys_ax_vars[ j-1 ] ), egraph.cons( egraph.mkSelect ( indexed_array , sys_ax_vars[ j ] ) ) ) ) );
        }
      }
      
    
      assert( origs.size( ) == dests.size( ) );
      // instantiate all the system axioms
      for ( size_t s = 0 ; s < system_axioms.size( ) ; s++ )
      {
        Enode * inst_syst_ax = egraph.substitute( system_axioms[ s ]->s_ax , origs, dests );
        // find all the combinations of the variables
        assertAllCombinationsWithRepetitions( inst_syst_ax , system_axioms[ s ]->s_ax_vars, sys_ax_vars, to_be_asserted );
      }
    }
    

    if ( config.verbosity > 1 )
    {
      cerr << "Asserting " << endl;
      for ( size_t j = 0 ; j < to_be_asserted.size( ) ; j++ )
      {
        to_be_asserted[ j ]->yicesPrint( cerr );
        cerr << endl;
      }
    }

#ifdef BACKWARD_INTERPOLANTION
    i_solver.AssertInt( egraph.mkAnd( egraph.cons( to_be_asserted ) ) , i );
#else  // FORWARD INTERPOLATION
    i_solver.AssertInt( egraph.mkAnd( egraph.cons( to_be_asserted ) ) , i+1 );
#endif
    
    if ( config.verbosity > 1 )
    {
      cerr << "\t";
      (*it)->yicesPrint( cerr );
      cerr << endl;
    }
  }

  if ( config.starting_interp_algo == 0 )  i_solver.SetOption( ":proof-set-inter-algo" , "0" ); 
  if ( config.starting_interp_algo == 1 )  i_solver.SetOption( ":proof-set-inter-algo" , "1" );
  if ( config.starting_interp_algo == 2 )  i_solver.SetOption( ":proof-set-inter-algo" , "2" );
//  config.starting_interp_algo ++;
//  config.starting_interp_algo = config.starting_interp_algo % 3;


  if ( i_solver.Check( ) == l_True )
  {
    i_solver.Pop( );
    return true;
  }
  else
  {
    
    cegar_loops++;


    // retrieve interpolants!
#ifdef BACKWARD_INTERPOLANTION
    for ( size_t i = 0 ; i <= counterexample.size( ) ; i++ )
    {
      interpolants.push_back( i_solver.GetInt( i ) );
    }
#else  // FORWARD INTERPOLATION
    for ( int i = counterexample.size( ) ; i >= 0 ; i-- )
    {
      interpolants.push_back( egraph.mkNot( i_solver.GetInt( i ) ) );
    }
#endif


    if( config.verbosity > 1 )
    {
      cerr << "INTERPOLANTS ARE:" << endl;
      for ( size_t i = 0 ; i < interpolants.size( ) ; i++ )
      {
        cerr << "\t";
        interpolants[ i ]->yicesPrint( cerr );
        cerr << endl;
      }
    }
  
    i_solver.Pop( );

/*
    // exploit "useful predicates" to retrieve smarter predicates
    // check interpolants
    solver.Push( );
    solver.Comment( "" );
    solver.Comment( "" );
    solver.Comment( "" );
    solver.Comment( "" );
    solver.Comment( "Checking interpolants" );
    for ( size_t i = 0 ; i < to_be_asserted.size( ) ; i++ )
    {
      solver.Push( );
      if ( interpolants.size( ) < interpolants.size( )-i )
      {
        cerr << "inteprolants.size() = " << interpolants.size( ) << endl;
        cerr << "i = " << i << endl;
        assert( false );
      }
      solver.Assert( egraph.substitute( interpolants[ interpolants.size( )-i ] , origs_interp , dests_interp ) );
      solver.Assert( egraph.substitute( to_be_asserted[ i ] , origs_interp , dests_interp ) );
      if( interpolants.size( ) < (interpolants.size( )-1)-i )
      {
        cerr << "inteprolants.size() = " << interpolants.size( ) << endl;
        cerr << "i = " << i << endl;
        assert( false );
      }
      solver.Assert( egraph.mkNot( egraph.substitute( interpolants[ (interpolants.size( )-2)-i ] , origs_interp , dests_interp ) ) );
      if ( solver.Check( ) != l_False )
      {
        cerr << "Error for interpolant #" << i << ":" << endl;
        cerr << "int" << i << ": ";
        egraph.substitute( interpolants[ (interpolants.size( )-1)-i ] , origs_interp , dests_interp)->yicesPrint( cerr );
        cerr << endl;
        cerr << "transition formula: ";
        egraph.substitute( to_be_asserted[ i ] , origs_interp , dests_interp)->yicesPrint( cerr );
        cerr << endl;
        cerr << "int" << i+1 << ": ";
        egraph.substitute( interpolants[ (interpolants.size( )-2)-i ] , origs_interp , dests_interp)->yicesPrint( cerr );
        cerr << endl;
      }
      solver.Pop( );
    }
    solver.Comment( "" );
    solver.Comment( "" );
    solver.Comment( "" );
    solver.Comment( "" );
    solver.Pop( );
*/
    
    return false;
  }

}

void
MC::cleanUnsafe ( )
{

  list < Node * > tbv = container.getTbvList( );
  for ( list< Node *>::iterator it = tbv.begin( )
      ; it != tbv.end( )
      ; it++ )
  {
    assert( (*it)->isUnsafe( ) );
    cleanAbstractLabel( (*it) );
  }
}

void
MC::fixCoveredChildren( Node * n )
{
  
  assert( n );

  // check if nodes covered by this one are still covered after deleting it
  set < Node * > covered_children = n->getCoveredChildren( );
  for ( set< Node * >::iterator it = covered_children.begin( )
      ; it != covered_children.end( )
      ; it++ )
  {
    
    // (*it) is the child we want to check!

    // skip if it is deleted
    if ( (*it)->isDeleted( ) ) continue;
    
    assert( (*it) );
    set < Node * > parents_covering_this_child = (*it)->getCoveringParents( );
    set < Node * > new_set_of_covering_parents;
    for ( set< Node * >::iterator p_it = parents_covering_this_child.begin( )
        ; p_it != parents_covering_this_child.end( )
        ; p_it++ )
    {
      if ( (*p_it)->isDeleted( ) ) continue;
      
      new_set_of_covering_parents.insert( (*p_it) );
    }

    // clear the set of covering nodes (if the node is still covered will build again anyway)
    (*it)->informCoveringParentsImFree( );
    (*it)->clearCoveringParents( );
    // check if the node is still covered
    if ( checkFixpoint( (*it) , new_set_of_covering_parents ) )
    {
      // yep, it is still covered!
      if ( ! (*it)->isCovered( ) )
      {
        n->printCoveringRelation( );
        cerr << "NODE " << (*it)->getId( ) << " is in the list of covered children of node " << n->getId( ) << " but it is not covered!" << endl;
      }
      assert( (*it)->isCovered( ) );
      
      // reinsert covering parents
      (*it)->addCoveringParents( new_set_of_covering_parents );
      // for each parent, inform them that they still covers this node
      for ( set< Node * >::iterator p_it = new_set_of_covering_parents.begin( )
          ; p_it != new_set_of_covering_parents.end( )
          ; p_it++ )
      {
        (*p_it)->addCoveredChild( (*it) );
      }
      if ( config.verbosity > 1 )
      {
        cerr << "Node " << (*it)->getId( ) << "\n\t";
        (*it)->getLabel( )->yicesPrint( cerr );
        cerr << endl;
        cerr << "is still covered!" << endl;
        (*it)->printCoveringRelation( );
      }
      
    }
    else
    {
      if ( n->isCovered( ) )
        container.setCoveredNodes( container.getCoveredNodes( ) - 1 );
      (*it)->setCovered( false );
      cout << "node " << (*it)->getId( ) << " is uncovered" << endl;
      // free all the nodes locked by this node
      set< Node * > locked_children = (*it)->getLockedChildren( );
      for ( set< Node * >::iterator l_it = locked_children.begin( )
          ; l_it != locked_children.end( )
          ; l_it++ )
      {
        assert( (*l_it)->isLocked( ) );
        (*l_it)->unlock( );
        cout << "node " << (*l_it)->getId( ) << " is unlocked" << endl;
      }
      (*it)->informCoveringParentsImFree( );
      (*it)->clearCoveringParents( );
      (*it)->setCovered( false );
    }
  }
}

void
MC::checkCovering ( Node * n ) {
  // check if n is covered by its covering parents or not
  if ( !checkFixpoint( n , n->getCoveringParents( ) ) )
  {
    cout << "node " << n->getId( ) << " is uncovered" << endl;
    // free all the nodes locked by this node
    set< Node * > locked_children = n->getLockedChildren( );
    for ( set< Node * >::iterator l_it = locked_children.begin( )
        ; l_it != locked_children.end( )
        ; l_it++ )
    {
      assert( (*l_it)->isLocked( ) );
      (*l_it)->unlock( );
      cout << "node " << (*l_it)->getId( ) << " is unlocked" << endl;
    }

    n->informCoveringParentsImFree( );
    n->clearCoveringParents( );
    n->setCovered( false );
  }
}


// FIXME! This function checks covering with all past nodes...
void
MC::checkCoveredParentForLock ( Node * n )
{
  // check covering, allowing only past nodes to cover new ones.
  if ( checkAbstractFixpoint( n , NULL , true ) )
  {
    // this node is covered by its ancestors
    cout << "node " << n->getId( ) << " is covered";
#ifdef PEDANTIC_DEBUG
    cout << "(2)";
#endif
    if ( config.verbosity > 1 )
    {
      cout << "(fixpoint checked for lock)";
    }
    cout << endl;

    // covering relation is updated by function "updateCoveringRelation"

    // lock every descendent of this node!
    set < Node * > descendants = n->getDescendants( );
    for ( set < Node * >::iterator it = descendants.begin( )
        ; it != descendants.end( )
        ; it++ )
    {
      if ( !(*it)->isDeleted( ) )
      {
        (*it)->lock( );
        // release covering of this node!
        // take all the covered children
        set < Node * > covered_children = (*it)->getCoveredChildren( );
        for ( set< Node * >::iterator c_it = covered_children.begin( )
            ; c_it != covered_children.end( )
            ; c_it++ )
        {
          (*c_it)->removeCoveringParent( (*it) );
          checkCovering( (*c_it) );
        }
        (*it)->clearCoveredChildren( );
        n->addLockedChild( (*it) );
        cout << "node " << (*it)->getId( ) << " is locked" << endl;
      }
    }
  }
  else
  {
    if ( !n->isUnsafe( ) )
    {
      checkCoveredParentForLock( n->getParent( ) );
    }
  }
}


void
MC::checkCoveredAncestorsForLock ( Node * n )
{
  
  // check covering, allowing only past nodes to cover new ones.
  if ( checkAbstractFixpoint( n , NULL , true ) )
  {
    // this node is covered by its ancestors
    cout << "node " << n->getId( ) << " is covered";
#ifdef PEDANTIC_DEBUG
    cout << "(3)";
#endif
    if ( config.verbosity > 1 )
    {
      cout << "(fixpoint checked for lock)";
    }
    cout << endl;

    // covering relation is updated by function "updateCoveringRelation"

    // lock every descendent of this node!
    set < Node * > descendants = n->getDescendants( );
    for ( set < Node * >::iterator it = descendants.begin( )
        ; it != descendants.end( )
        ; it++ )
    {
      if ( !(*it)->isDeleted( ) )
      {
        (*it)->lock( );
        // release covering of this node!
        // take all the covered children
        set < Node * > covered_children = (*it)->getCoveredChildren( );
        for ( set< Node * >::iterator c_it = covered_children.begin( )
            ; c_it != covered_children.end( )
            ; c_it++ )
        {
          (*c_it)->removeCoveringParent( (*it) );
          checkCovering( (*c_it) );
        }
        (*it)->clearCoveredChildren( );
        n->addLockedChild( (*it) );
        cout << "node " << (*it)->getId( ) << " is locked" << endl;
      }
    }
  }
  else
  {
    if ( !n->isUnsafe( ) )
    {
      checkCoveredParentForLock( n->getParent( ) );
    }
  }
}

void
MC::fixCoveredParentForLock ( Node * n )
{
  // if node n locked some other nodes, check if we should release the lock

  // collect n's parents
  vector < Node * > parents;
  Node * tmp = n;
  while ( !tmp->isUnsafe( ) )
  {
    parents.push_back( tmp->getParent( ) );
    tmp = tmp->getParent( );
  }
  if ( !checkFixpoint( n , parents ) )
  {
    // release the lock
    set < Node * > locked = n->getLockedChildren( );
    for ( set < Node * >::iterator it = locked.begin( )
        ; it != locked.end( )
        ; it++ )
    {
      (*it)->unlock( );
      cout << "node " << (*it)->getId( ) << " has been unlocked" << endl;
    }
  }
}

void
MC::checkChildren( Node * n )
{
  // this function is no more enabled since the abstraction function
  // has not yet been extended to formulas with disjunctions
  //return;
  
  set < Node * > children = n->getChildren( );
  for ( set< Node * >::iterator it = children.begin( )
      ; it != children.end( )
      ; it++ )
  {
    if ( (*it)->isDeleted( ) ) continue;
    vector < Node * > preimages;
    buildFormula ( preimages , (*it)->getVar( FIRST ) , (*it)->getVar( SECOND ) , n , (*it)->getParentTransition( ) );

    if ( preimages.empty( ) || preimages[ 0 ]->getLabel( )->isFalse( ) )
    {
      cout << "node " << (*it)->getId( ) << " is deleted (ancestor refined, path infeasible)" << endl;
      deleteNode( (*it) );
    }
  }
}


Enode *
MC::abstractArithmeticLiterals ( Enode * f )
{
  // when there is a literal like "a[zN] + 1" define a new variable 'n' and
  // abstract it as "a[zN] + n"
  vector < Enode * > origs;
  vector < Enode * > dests;

  char buf[ 32 ];
  sprintf( buf, "abs_var%u", var_id++ );
  
  origs.push_back( egraph.mkNum( "1" ) );
  declareIntVar( buf );
  dests.push_back( egraph.mkVar( buf ) ); 

  cerr << "old formula: " << f << endl;
  cerr << "new formula: " << egraph.substitute( f , origs , dests ) << endl;
  return egraph.substitute( f , origs , dests );

}
#endif
