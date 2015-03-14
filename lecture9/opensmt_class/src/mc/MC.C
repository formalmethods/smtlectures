/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#include "MC.h"

status_t MC::checkSafety(  )
{
  // easy to reset...
  solver.Push( );
  
  initializeSolver( );
  initializeDataStructures( );


  // intialize simplify_origs and simplify_dests
  assert( !z_variables.empty( ) );
  for ( size_t a = 0 ; a < array_vars.size( ) ; a++ )
  {
    if ( array_vars[ a ]->global )
    {
      for ( size_t v = 0 ; v < z_variables.size( ) ; v++ )
      {
        simplify_origs.push_back( egraph.mkSelect( array_vars[ a ]->enode , z_variables[ v ] ) );
        simplify_dests.push_back( egraph.mkSelect( array_vars[ a ]->enode , z_variables[ 0 ] ) );
//        cerr << "adding " << egraph.mkSelect( array_vars[ a ]->enode , z_variables[ v ] ) << "  -->  " << egraph.mkSelect( array_vars[ a ]->enode , z_variables[ 0 ] ) << endl;
      }
    }
  }


  // define in the smt ctx unsafe configurations
  defineUnsafeConfigs(  );

  // set up predicates that will be used in the search
  if ( config.abstraction )
    setUpPredicates(  );

  // check safety of all the unsafe nodes
  if ( checkSafetyUnsafe( ) )
  {
    status = UNSAFE;
    return status;
  }

  // abstract unsafe nodes
  if ( config.abstraction && config.abstract_unsafe )
  {
    cleanUnsafe( );
  }
  
  
  if ( config.depth_search )
  {
    container.setStrategy( DEPTH_FIRST_STRATEGY );
  }
  
  if ( config.verbosity > 1 )
  {
    cerr << "MC::Safety Check BEGINS" << endl;
  }

  if ( !invariants )
  {
    cout << "\nDoing state space exploration..." << endl;
  }

  if ( stoppingFailure && !invariants )
  {
    cout << "Stopping Failures (i.e. approximated) Model Adopted." << endl;
  }
  if ( !invariants )
  {
    cout << endl;
  }

  // Take the first state to be expanded from the TBV list
  while ( container.hasMoreTbvNodes( ) )
  {
    // get a new node and remove it from the TBV list
    Node *tbv = container.getNextTbvNode( );
    container.removeFromTbv( tbv );

    if( tbv->isDeleted( ) )
    {
      
      // TODO: free memory!!!
      if ( !config.abstraction )
      {
        delete tbv;
        continue;
      }
      else
      {
        // FIXME: memory won't be deallocated!!
        tbv->informCoveringParentsImFree( );
        container.addDeletedNode( tbv );
        continue;
      }
    }

#ifdef PEDANTIC_DEBUG
    container.checkNodes( );
    
    if ( tbv->explored ) {
      cerr << "ERROR: node " << tbv->getId( ) << " has already been explored!" << endl;
      assert( false );
    }
    if ( tbv->isCovered( ) ) {
      cerr << "ERROR: node " << tbv->getId( ) << " is covered and cannot be explored!" << endl;
      assert( false );
    }
    tbv->explored = true;
#endif


    if ( config.abstraction && config.abstraction_locking > 0 )
    {
      if ( !tbv->isDeleted( ) )
      {
        if ( config.abstraction_locking == 1 ) // soft locking
          checkCoveredParentForLock( tbv );
        if ( config.abstraction_locking == 2 ) // eager locking
          checkCoveredAncestorsForLock( tbv ); 
      }
      if ( tbv->isLocked( ) )
        continue;
    }
   
   

    // INVARIANT SEARCH -- check maximum number of index variable for invariant check
    if ( invariants && ( variables.size() >= 4 || container.getNodes( ) > config.invariant_nodes  ) )
    {
      status = UNKNOWN;
      return status;
    }
    
    assert( tbv != NULL );
    


    // check local fixpoint before computing preimages
    bool fixpoint = ( config.s_lfp ) ? false : checkFixpoint(tbv);
    if ( fixpoint )
    {
      if ( !config.abstraction ) 
      {
        if ( !invariants )
        {
          cout << "node " << tbv->getId() << " is deleted" << endl;
        }
        container.setDeletedNodes( container.getDeletedNodes() + 1);
        tbv->Delete( );
      }
      else
      {
        cout << "node " << tbv->getId() << " is covered";
#ifdef PEDANTIC_DEBUG
        cout << "(1)";
#endif
        cout << endl;
        tbv->setCovered( true ); 
        container.setCoveredNodes( container.getCoveredNodes( ) + 1 );
        if ( config.verbosity > 1 )
        {
          tbv->printCoveringRelation( );
        }
        container.addTbvNode( tbv , candidate_invariants , false , config.global_invariant , true );
#ifdef PEDANTIC_DEBUG
        tbv->explored = false;
#endif
      }

      continue;
    }
    
    
    // vector where preimages will be saved
    vector < Node * > preimages;
    
    // Get preimages using all transitions 
    for (size_t i = 0; i < transitions.size(); i++)
    {
      Transition * t = transitions[ i ];
      // Get preimage from the state
       
      if ( config.iterative && config.verbosity < 2 )
      {
        // cerr << "Press [Enter] to go ahead...\n\n\n";
        cerr << "\n\n\n\nComputing preimages" << endl;
        cerr << "Starting from " << tbv->getLabel()<< endl;
        cerr << "With " << t << endl;
      }
      
      computePreimages( preimages , tbv , t );
    }


    // add tbv in the set of Already Visited nodes
    container.addAvNode(tbv);
   

    // if there are no preimages, skip!
    if ( config.iterative && preimages.empty( ) )
    {
      cerr << "\n\n\n\nNO NEW PREIMAGES!" << endl;
      continue;
    }
    

    for (size_t n_pre = 0; n_pre < preimages.size( ); n_pre++)
    {
      
      /* check if a preimage can be deleted by using a concrete fixpoint test  */
      if ( checkFixpoint( preimages[ n_pre ] , tbv ) )
      {
        if ( config.verbosity > 1 )
        {
          cout << "node " << preimages[ n_pre ]->getId() << " has been deleted by concrete fixpoint-test" << endl;
        }
        preimages[ n_pre ]->Delete( );
        continue;
      }

      // check if the preimage has been deleted
      if ( preimages[ n_pre ]->isDeleted( ) )
      {
        continue;
      }
      
      // check max depth
      if ( config.depth_limit != 0 && preimages[ n_pre ]->getDepth() > config.depth_limit )
      {
        continue;
      }
 
            
      // Insert new node in the tbv list (abstraction)
      if ( config.abstraction )
      {
        
        // for every new preimage check if the parent is still alive!
        // (can be the case that a previous node hit the initial set of states
        // and interpolats were false up to this tbv node!)
        if ( tbv->isDeleted( ) ) continue;
        
        container.addTbvNode( preimages[ n_pre ] , candidate_invariants , !invariants , config.global_invariant );
        tbv->addChild( preimages[ n_pre ] );
        
        // comment to the yices file
        stringstream ss;
        ss << "Defining new node derived from node " << tbv->getId()
           << " applying transition " << preimages[ n_pre ]->getParentTransition( )->getId();
       
        solver.Comment("");solver.Comment("");solver.Comment("");solver.Comment("");solver.Comment("");
        solver.Comment( const_cast<char*>( ss.str().c_str() ) );
        createDefinition( preimages[ n_pre ] );
      
        // inserting the node in the tbv list 
        if ( config.verbosity > 1 ) {
          cerr << "\n\n\n NEW PREIMAGE ADDED TO THE TBV LIST:\n\t";
          preimages[ n_pre ]->getLabel()->yicesPrint( cerr );
          cerr << "\n\n\n\n";
        }
        if ( config.iterative )
        {
          cerr << "\t" << preimages[ n_pre ]->getLabel() << endl;
        }
      }


      if ( config.abstraction && config.abstraction_power == 1 )
      {
        cleanAbstractLabel( preimages[ n_pre ] );
      }


      // check if the node is subsumed
      if ( !config.s_efp )
      {
        // eager fixpoint test
        bool eager_fixpoint = checkFixpoint( preimages[ n_pre ] , tbv );
        if ( eager_fixpoint )
        {
          if ( config.iterative )
          {
            cerr << "\tThis preimage has been deleted by eager fixpoint test!" << endl;
          }
          
          // if we are abstracting this node is covered and should not be deleted!
          if ( !config.abstraction )
          {
            delete preimages[ n_pre ];
          }
          /*  THIS COVERING IS HANDLED BY THE FUNCTION updateCoveringRelation
          else
          {
            preimages[ n_pre ]->setCovered( true ); cerr << "(c4)" << endl;
            container.setCoveredNodes( container.getCoveredNodes( ) + 1 );
            cout << "node " << preimages[ n_pre ]->getId() << " is covered" << endl;
            if ( config.verbosity > 1 )
            {
              preimages[ n_pre ]->printCoveringRelation( );
            }
          }
          */
          continue;
        }
      }
      

      // a node is abstracted only if it is not covered!
      // weakest abstraction
      if ( config.abstraction && config.abstraction_power == 0 )
      {
        cleanAbstractLabel( preimages[ n_pre ] );
      }


              
      // Insert new node in the tbv list
      if ( !config.abstraction )
      {
        container.addTbvNode( preimages[ n_pre ] , candidate_invariants , !invariants , config.global_invariant );
        tbv->addChild( preimages[ n_pre ] );
        
        // comment to the yices file
        stringstream ss;
        ss << "Defining new node derived from node " << tbv->getId()
           << " applying transition " << preimages[ n_pre ]->getParentTransition( )->getId();
       
        solver.Comment("");solver.Comment("");solver.Comment("");solver.Comment("");solver.Comment("");
        solver.Comment( const_cast<char*>( ss.str().c_str() ) );
        createDefinition( preimages[ n_pre ] );
      
        // inserting the node in the tbv list 
        if ( config.verbosity > 1 ) {
          cerr << "\n\n\n NEW PREIMAGE ADDED TO THE TBV LIST:\n\t";
          preimages[ n_pre ]->getLabel()->yicesPrint( cerr );
          cerr << "\n\n\n\n";
        }
        if ( config.iterative )
        {
          cerr << "\t" << preimages[ n_pre ]->getLabel() << endl;
        }
      }


    
      if ( config.report_tex ) {
        latexNode( preimages[ n_pre ] );
      }
      if ( config.report )
      {
        preimages[ n_pre ]->getLabel( )->yicesPrint( log_file );
        log_file << endl;
        graphviz << "\tN_" << preimages[ n_pre ]->getId( ) << " -> N_" << tbv->getId( ) << " [ label = \"t" << preimages[ n_pre ]->getParentTransition( )->getId( ) << "\" ];\n";
      }

      // assert the initial formula instantiated with all the possible
      // combination af the variables in the formula
      if ( config.verbosity > 1 )
      {
        cerr << "\n\nCheck if there's non-empty intersection with the initial state" << endl;
      }
      if (checkInitialIntersection( preimages[ n_pre ] ) )
      {
        if ( !config.abstraction )
        {
          status = UNSAFE;
          if ( config.counterexample )
          {
            vector < Enode * > counterexample, interpolants;
            // unuseful...
            vector < Enode * > origs_interp , dests_interp;
            getCE ( preimages[ n_pre ] , counterexample , origs_interp , dests_interp );
            assert( CounterexampleIsFeasible( counterexample , interpolants , origs_interp , dests_interp ) );
            printCE( counterexample , cout );
          }
          last_node = preimages[ n_pre ];
          return status;
        }
        else
        {
          
          // ABSTRACTION!!

          vector < Enode * > counterexample , interpolants;
          vector < Enode * > origs_interp , dests_interp;
          getCE( preimages[ n_pre ] , counterexample , origs_interp , dests_interp );

          cout << "Checking counterexample... ";
          

          if ( config.abstraction_report )
          {
            // dotty
            char buffer [ 256 ];
            sprintf( buffer , "abstract_log_%d.gv" , cegar_loops );
            abs_graphviz.open ( const_cast<char*>( buffer ) );
            container.outputDotty( abs_graphviz , preimages[ n_pre ]->identifier );
            abs_graphviz.close( );
            
            // log formulas
            sprintf( buffer , "abstract_log_%d.log" , cegar_loops );
            abs_log_file.open ( const_cast<char*>( buffer ) );
            container.outputLog( abs_log_file );
            abs_log_file.close( );
          }
          

          bool ce_is_feasible = CounterexampleIsFeasible( counterexample , interpolants , origs_interp , dests_interp );
          
          assert( origs_interp.size( ) == dests_interp.size( ) );
          
          if ( ce_is_feasible )
          {
            cout << "COUNTEREXAMPLE IS FEASIBLE!" << endl;
            status = UNSAFE;
            if ( config.counterexample )
            {
              printCE( counterexample , cout );
            }
            last_node = preimages[ n_pre ];

            // TODO we should free all the nodes retrieved after preimages[ n_pre ]
            
            return status;
          }
          else
          {
            cout << "counterexample is unfeasible." << endl;
            cout << "Refining abstraction...\n" << endl ;
            
            assert( interpolants.size( ) == counterexample.size( ) + 1 );
            
            refineNodes( interpolants , preimages[ n_pre ] , origs_interp , dests_interp );
            
          }
        }
      }
      assert ( status != UNSAFE );
      if ( config.verbosity > 1 )
      {
        cerr << "The intersection is empty, go ahead!\n" << endl;
      }
    }
    
    
    // Insert this state in the AV list
    if ( config.verbosity > 1 )
    {
      cerr << "\n\n\n Node added to the av list" << endl;
    }
    
    
    if ( !invariants )
    {
      //size_t c_size = candidate_invariants.size();
      // check the new candidate invariants
      checkInvariant( );
      // assert( candidate_invariants.size() >= c_size );
    }

    // check if we can go ahead
    if ( container.getNodeNum( ) >= config.node_limit )
    {
      return status;
    }

    
    
    if ( config.verbosity > 1 )
    {
      tbv->printChildren( );
    }
  }
  
  if ( config.abstraction_report )
  {
    // dotty
    char buffer [ 256 ];
    sprintf( buffer , "abstract_log_%d.gv" , cegar_loops );
    abs_graphviz.open ( const_cast<char*>( buffer ) );
    container.outputDotty( abs_graphviz );
    abs_graphviz.close( );
    
    // log formulas
    sprintf( buffer , "abstract_log_%d.log" , cegar_loops );
    abs_log_file.open ( const_cast<char*>( buffer ) );
    container.outputLog( abs_log_file );
    abs_log_file.close( );
    

    // log only alive nodes
    abs_log_file.open ( const_cast<char*>( "abstract_log_final.log" ) );
    container.outputLog( abs_log_file , true );
    abs_log_file.close( );
  
  }
  
  
  status = SAFE;
  

  if ( !invariants && config.auto_test ) {
    autoTest( ) ;
  }

  solver.Pop( );

  if ( config.verbosity > 1 )
    cerr << "MC::Safety Check ENDS" << endl;


  return status;
}


bool
MC::checkSafetyUnsafe( )
{
  list < Node * > tbv = container.getTbvList( );
  for ( list< Node * >::iterator it = tbv.begin( )
      ; it != tbv.end( )
      ; it++ )
  {
    if ( checkInitialIntersection( (*it) ) ) {
      cout << "Node " << (*it)->getId( ) << " intersect set of initial states" << endl;
      return true;
    }
  }

  return false;
}



// return true if it's valid that (f1 -> f2)
bool
MC::checkValidImplication ( Enode * f1 , Enode * f2 )
{
  
  solver.Comment( "" );
  solver.Comment( "" );
  solver.Comment( "Checking valid implication" );
  assert( f1 );
  assert( f2 );
  bool res = false;
  solver.Push();
  solver.Assert( f1 );
  
  vector < Enode * > f1_vars, f2_vars;
  retrieveVars( f1 , f1_vars );
  retrieveVars( f2 , f2_vars );

  int assertions = assertAllCombinations( f2 , f2_vars, f1_vars, true );
  
  if ( assertions > 0 && solver.Check() == l_False )
    res = true;
  solver.Pop();
  solver.Comment( "" );
  solver.Comment( "" );
  return res;
}


// return true if it's valid that (f1 -> f2)
bool
MC::checkValidImplication ( Node * n1 , Node * n2 )
{
  assert( n1 );
  assert( n2 );
  Enode * f1 = n1->getLabel();
  bool res = false;
  solver.Push();
  solver.Assert( f1 );
  
  int assertions = assertSuitableCombinations( n1 , n2 , true );
  
  if ( assertions > 0 && solver.Check() == l_False )
    res = true;
  solver.Pop();
  return res;
}

bool
MC::checkValidImplication ( Node *n , vector< Node *> & l )
{
  if ( config.verbosity > 1 )
  {
    cerr << "CHECK SUBSUMPTION" << endl;
    cerr << "\tStarting from the node" << n->getLabel() << endl;
  }
  solver.Comment("Check subsumption");
  solver.Push();

  solver.Assert(n->getLabel());

  bool subsumed = false;
  for ( vector<Node*>::reverse_iterator it = l.rbegin()
        ; !subsumed && it != l.rend()
        ; ++it )
  {
    
    Node * av_node = *it;
    if ( av_node == n || av_node->isDeleted() )
      continue;
      
    solver.Push();

    int assertions = assertAllCombinations( (*it)->getLabel( ) , (*it)->getLabelVars( ) , n->getLabelVars( ) , true );

    if (assertions > 0 && solver.Check( ) == l_False )
      subsumed = true;

    solver.Pop();
  }
  
  solver.Pop();

  return subsumed;
}


bool
MC::checkSubsumption ( Node *n , vector< Node *> & l )
{
  if ( config.verbosity > 1 )
  {
    cerr << "CHECK SUBSUMPTION" << endl;
    cerr << "\tStarting from the node" << n->getLabel() << endl;
  }
  solver.Comment("Check subsumption");
  solver.Push();

  solver.Assert(n->getLabel());

  bool subsumed = false;
  for ( vector<Node*>::reverse_iterator it = l.rbegin()
        ; !subsumed && it != l.rend()
        ; ++it )
  {
    
    Node * av_node = *it;
    if ( av_node == n || av_node->isDeleted() )
      continue;
      
    solver.Push();

    int assertions = assertSuitableCombinations( n , av_node , true );

    if (assertions > 0 && solver.Check( ) == l_False )
      subsumed = true;

    solver.Pop();
  }
  
  solver.Pop();

  return subsumed;
}


bool
MC::checkSubsumption ( Node *n , list< Node *> & l )
{
  solver.Comment("Check subsumption");
  solver.Push();
  
  solver.Assert(n->getLabel());

  bool subsumed = false;
  for ( list<Node*>::reverse_iterator it = l.rbegin()
        ; !subsumed && it != l.rend()
        ; ++it )
  {
    Node * av_node = *it;
    if ( av_node == n )
      continue;
    
    solver.Push();
    
    int assertions = assertSuitableCombinations( n , av_node , true );

    if (assertions > 0 && solver.Check( ) == l_False )
      subsumed = true;

    solver.Pop();
  }
  
  solver.Pop();

  return subsumed;
}


void MC::pushBacktrackPoint( )
{
  // TODO: for later use
}

void MC::popBacktrackPoint( )
{
  // TODO: for later use
}

void MC::exit( )
{
}

Enode * MC::checkCondition( Enode * label, Enode * cond
                          , Enode * x, Enode * px
                          , Enode * y, Enode * py
		          , Enode * j, Enode * pj )
{
  assert( label );
  assert( cond );
  assert( x );
  assert( px );
  assert( j );
  assert( pj );
 
  
  egraph.initDupMap1( );
  vector< Enode * > unprocessed_enodes;

  egraph.storeDupMap1( x, px );
  if ( y ) {
    assert( py );
    egraph.storeDupMap1( y, py );
  }
  egraph.storeDupMap1( j, pj );

  unprocessed_enodes.push_back( cond );

  while( !unprocessed_enodes.empty( ) )
  {
    Enode * e = unprocessed_enodes.back( );

    if ( egraph.valDupMap1( e ) != NULL )
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

    Enode * result = egraph.copyEnodeEtypeTermWithCache( e );

    egraph.storeDupMap1( e, result );
  }

  assert( egraph.valDupMap1( cond ) != NULL );
  Enode * res = egraph.valDupMap1( cond );

  egraph.doneDupMap1( );

  if ( !res->isTrue( ) 
    && !res->isFalse( ) )
  {
    if ( res->isEq( ) )
    {
      Enode * lhs = res->get1st( );
      Enode * rhs = res->get2nd( );
      if ( lhs->isVar( ) 
        && rhs->isVar( )
	&& lhs != rhs )
	res = egraph.mkFalse( );
    }
    else if ( res->isNot( ) && res->get1st( )->isEq( ) )
    {
      Enode * lhs = res->get1st( )->get1st( );
      Enode * rhs = res->get1st( )->get2nd( );
      if ( lhs->isVar( ) 
        && rhs->isVar( )
	&& lhs != rhs )
	res = egraph.mkTrue( );
    }
  }

  if ( config.verbosity > 1 )
  {
    cerr << "CheckCondition!" << endl
         << "label: " << label << endl
         << "condition: " << cond << endl
         << "\t" << x << " --> " << px << endl;
    if ( y )
      cerr << "\t" << y << " --> " << py << endl;
    cerr << "\t" << j << " --> " << pj << endl
         << "res: " << res << endl << endl;
  }
  return res;
}

//
// Check if the label and value are compatible w.r.t.
//
bool MC::checkCompatible( Node * n                 // Node where I'm starting
			, Enode * i                // Index to consider
			, vector<Enode *> & values // Value for a in case
			)
{
  bool res = true;
  if ( n->getFormula( )->hasDisjunctions( ) )
  {
    // this formula has disjunctions in the label, returns that it is compatible!
    return res;
  }
  
  Enode * label = n->getLabel( );

  // TODO: make it a configure parameter
  // It tells the egraph not to go deep
  // into tsolvers to check satisfiability
  // At the moment true would not work as
  // canonization for atoms is not done
  // properly apparently
  const bool use_tsolvers = false;

  for ( size_t array = 0 ; array < array_vars.size() && res ; array++ )
  {
    Enode * a = array_vars[ array ]->enode;
    Enode * value = values[ array ];

    Enode * sel = egraph.mkSelect( a, i );
  
    assert( label );
    assert( a );
    assert( value );
    assert( label->isAnd( ) || label->isLit( ) );
  
    vector< Enode * > & lits = n->getFormula( )->getLiterals( );
    vector< Enode * > undo_stack;

    Enode * eq = egraph.mkEq( egraph.cons( sel
                            , egraph.cons( value ) ) );
  
    // When there is an array of booleans,
    // eq is not an equality, and has to be
    // dealt with as an uninterpreted predicate
    if ( eq->isEq( ) )
    {
      egraph.inform( eq, use_tsolvers );
      assert( eq->isTerm( ) );
      eq->setPolarity( l_True );
    }
    else
    {
      assert( value->isTrue( ) || value->isFalse( ) );
      if ( value->isTrue( ) )
      {
	assert( sel == eq );
	eq->setPolarity( l_True );
      }
      else
      {
	assert( egraph.mkNot( egraph.cons( sel ) ) == eq );
	// Override (not sel) and set sel to false
	eq = sel;
	eq->setPolarity( l_False );
      }
    }
  
    for ( size_t j = 0 ; j < lits.size( ) && res ; j ++ )
    {
      Enode * lit = lits[ j ];
      Enode * atom = NULL;
      if ( lit->isNot( ) )
      {
        atom = lit->get1st( );
        egraph.inform( atom, use_tsolvers );
        // Already asserted
        // Stop if polarity is opposite
        if ( atom->hasPolarity( ) )
        {
          res = atom->getPolarity( ) == l_False;
          if ( !res )
            break;
        }
        else
        {
          atom->setPolarity( l_False );
          undo_stack.push_back( atom );
        }
      }
      else
      {
        atom = lit;
        egraph.inform( atom, use_tsolvers );
        // Already asserted atom
        // Stop if polarity is opposite
        if ( atom->hasPolarity( ) )
        {
          res = atom->getPolarity( ) == l_True;
          if ( !res )
            break;
        }
        else
        {
          atom->setPolarity( l_True );
          undo_stack.push_back( atom );
        }
      }
    }
  
    egraph.pushBacktrackPoint( );
    res = res && egraph.assertLit( eq, use_tsolvers, false );
    
    for ( size_t j = 0 ; j < lits.size( ) && res ; j ++ )
    {
      Enode * atom = lits[ j ]->isNot( ) ? lits[ j ]->get1st( ) : lits[ j ];
      res = egraph.assertLit( atom, use_tsolvers, false );
    }
  
    egraph.popBacktrackPoint( );
    eq->resetPolarity( );
    // Clear explanation as not used
    egraph.resetExplanation( );
  
    for ( size_t j = 0 ; j < undo_stack.size( ) ; j ++ )
      undo_stack[ j ]->resetPolarity( );
  
    if ( config.verbosity > 2 )
      cerr << "CheckCompatible: " << endl
           << "  " << label << endl
           << "  and " << endl
           << "  " << eq << endl
           << "  are " << (res? "" : "NOT") << " compatible "
           << endl;
  }
 
  return res;
}

//
// Retrieve literals from a conjunction
//
void MC::retrieveLits( Enode * f, vector< Enode * > & lits )
{
  assert( f );
  assert( f->isAnd( ) || f->isLit( ) );
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
      assert( e->isLit( ) );
      lits.push_back( e );
    }

    egraph.storeDup1( e );
  }
  egraph.doneDup1( );
}


Enode *
MC::simplify( Enode * f )
{
  assert ( f );
 
  //cerr << "\tSIMPLIFY FROM:" << f << endl;
  
  vector <Enode *> origs, dests;
  
  egraph.initDupMap1( );
  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( f );
  
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * e = unprocessed_enodes.back( );
   
    if ( egraph.valDupMap1( e ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    if ( e->isEq( ) 
      && egraph.valDupMap1( e ) == NULL )
    {
      //cerr << "Equality: " << e << endl;
      
      // save the two terms to be substituted
      Enode * lhs = e->get1st( );
      Enode * rhs = e->get2nd( );
      //cerr << "\tLHS " << lhs << endl;
      //cerr << "\tRHS " << rhs << endl;
      
      if ( !egraph.hasSortIndex( lhs ) 
	&& !egraph.hasSortIndex( rhs ) )
      {
        if ( lhs->isConstant() )
        {
          //cerr << "\t" << rhs << "-->" << lhs << endl;
          egraph.storeDupMap1( e, e );
          origs.push_back( rhs );
          dests.push_back( lhs );
        }
        else if ( rhs->isConstant( ) )
        {
          //cerr << "\t" << lhs << "-->" << rhs << endl;
          egraph.storeDupMap1( e, e );
          origs.push_back( lhs );
          dests.push_back( rhs );
        }
      }
    }
    
    if ( e->isNot( ) ) 
    {
      unprocessed_enodes.pop_back();
      egraph.storeDupMap1( e, e );
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
      if ( egraph.valDupMap1( arg ) == NULL )
      {
        unprocessed_enodes.push_back( arg );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children ) {
      continue;
    }

    unprocessed_enodes.pop_back( );

    egraph.storeDupMap1( e , e );

  }
  
  /*
  cerr << "\tSUBSTITUTION TO BE DONE:" << endl;
  for (size_t i = 0; i < origs.size() ; i++)
  {
    cerr << origs[ i ] << " --> " << dests[ i ] << endl;
  }
  */

  egraph.doneDupMap1( );

  f = egraph.substitute ( f, origs, dests );
  
  if ( !f->isFalse( ) )
  {
    // insert again the equality literals
    for ( size_t i = 0 ; i < origs.size() ; i ++ )
    {
      f = egraph.mkAnd( egraph.cons( f
	              , egraph.cons( egraph.mkEq( egraph.cons( origs[ i ] 
			                        , egraph.cons( dests[ i ] ) ) ) ) ) );
    }
  }

  //cerr << "\tSIMPLIFY TO:" << f << endl;
  
  return f;
}



void
MC::simplifyPreimages ( vector < Node * > & preimages )
{
  // we start from the last node becasue usually the last
  // is the one with the new variable (so we would like
  // to get rid of it asap if it's possible)
  for ( vector<Node*>::reverse_iterator it = preimages.rbegin()
        ; it != preimages.rend()
        ; ++it )
  {
    Node * n = *it;
    if ( !n->isDeleted( ) )
    {
      solver.Comment(""); 
      solver.Comment(""); 
      solver.Comment("SimplifyPreimages"); 
      if ( checkSubsumption( n , preimages ) )
      {
        simplified++;
        n->Delete();
      }
      solver.Comment(""); 
      solver.Comment(""); 
    }
  }
}

void
MC::retrieveVars ( Enode * l , vector <Enode*> & vars )
{
  vars.clear();

  set< Enode * > cache;
  vector< Enode * > unprocessed_enodes;

  unprocessed_enodes.push_back( l );

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
      vars.push_back( e );

    assert( cache.find( e ) == cache.end( ) );
    cache.insert( e );
  }
}


/* TODO: rewrite these two functions as only one that works with
   iterators! */
bool
MC::checkFixpoint ( Node * n , set < Node * > & nodes )
{
  
  assert( n );

#ifdef PEDANTIC_DEBUG
  n->checkLabel( );
  for ( set< Node * >::iterator it = nodes.begin( )
      ; it != nodes.end( )
      ; it++ )
  {
    (*it)->checkLabel( );
  }
#endif

  solver.Comment("");
  solver.Comment("");
  solver.Comment("Fixpoint test starts (1)");
  solver.Push();

  // assert the node
  solver.Comment("Asserting the label of the node");
  solver.Assert( n->getLabel() );
  
  
  // assert all the previews nodes in all possible
  // configuration

  int total_assertions = 0;
  bool done_at_least_one_check = false;
  for ( set<Node*>::iterator it = nodes.begin()
        ; it != nodes.end( )
        ; it++ )
  {
    if ( (*it)->isDeleted( ) || (*it)->getId( ) == n->getId( ) || (*it)->isCovered( ) || (*it)->isLocked( ) ) continue;

    int assertions = assertSuitableCombinations( n , (*it) , true );

    // check fixpoint
    if ( (config.abstraction ||
           (assertions > 0 &&
            total_assertions >= config.fix_point_period
           )
         ) && solver.Check( ) == l_False
       )
    {
      done_at_least_one_check = true;
      total_assertions = 0;
      solver.Pop();
      solver.Comment("End fixpoint check");
      
      if ( config.verbosity > 1)
      {
        cerr << "\n\t(1) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
      }
      
      return true;
    }
  }
  
  if ( !done_at_least_one_check && solver.Check( ) == l_False)
  {
    solver.Pop();
    solver.Comment("End fixpoint check");
    
    if ( config.verbosity > 1)
    {
      cerr << "\n\t(7) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
    }
        
    return true;
  }

  solver.Pop( );
  solver.Comment("End fixpoint check");
  solver.Comment("");
  solver.Comment("");
  if ( config.verbosity > 1)
  {
    cerr << "\n\tFixpoint check ends with true." << endl;
  }
  
  return false;
}


bool
MC::checkFixpoint ( Node * n , vector < Node * > & nodes )
{

  assert( n );

#ifdef PEDANTIC_DEBUG
  n->checkLabel( );
  for ( vector< Node * >::iterator it = nodes.begin( )
      ; it != nodes.end( )
      ; it++ )
  {
    (*it)->checkLabel( );
  }
#endif

  solver.Comment("");
  solver.Comment("");
  solver.Comment("Fixpoint test starts (2)");
  solver.Push();

  // assert the node
  solver.Comment("Asserting the label of the node");
  solver.Assert( n->getLabel() );
  
  // assert all the previews nodes in all possible configuration

  int total_assertions = 0;
  bool done_at_least_one_check = false;
  for ( vector<Node*>::iterator it = nodes.begin()
        ; it != nodes.end( )
        ; it++ )
  {
    if ( (*it)->isDeleted( ) || (*it)->getId( ) == n->getId( ) || (*it)->isCovered( ) || (*it)->isLocked( )) continue;
    
    int assertions = assertSuitableCombinations( n , (*it) , true );

    // check fixpoint
    if ( (config.abstraction ||
           (assertions > 0 &&
            total_assertions >= config.fix_point_period
           )
         ) && solver.Check( ) == l_False
       )
    {
      done_at_least_one_check = true;
      total_assertions = 0;
      solver.Pop();
      solver.Comment("End fixpoint check");
      
      if ( config.verbosity > 1)
      {
        cerr << "\n\t(1) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
      }
      
      return true;
    }
  }
  
  if ( !done_at_least_one_check && solver.Check( ) == l_False)
  {
    solver.Pop();
    solver.Comment("End fixpoint check");
    
    if ( config.verbosity > 1)
    {
      cerr << "\n\t(7) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
    }
        
    return true;
  }

  solver.Pop( );
  solver.Comment("End fixpoint check");
  solver.Comment("");
  solver.Comment("");
  if ( config.verbosity > 1)
  {
    cerr << "\n\tFixpoint check ends with true." << endl;
  }
  
  return false;
}



bool
MC::checkAbstractFixpoint ( Node * n , Node * tbv , bool skip_younger_nodes )
{

  assert( n );

#ifdef PEDANTIC_DEBUG
  n->checkLabel( );
  if ( tbv ) tbv->checkLabel( );
  container.checkNodes( );
#endif

 
  if ( config.verbosity > 1 )
  {
    cerr << "\n\n\tSTART FIXPOINT CHECK" << endl;
  }
  
  solver.Comment("");
  solver.Comment("");
  solver.Comment("Fixpoint test starts (c3)");
  solver.Push();

  // ABSTRACTION
  // clear the tmp parent cover vector
  if ( config.abstraction ) parent_cover.clear( );

  // assert the node
  solver.Comment("Asserting the label of the node");
  solver.Assert( n->getLabel() );
  
  
  // assert all the previews nodes in all possible
  // configuration

  list < Node * > & avNodes  = container.getAvList( );
  list < Node * > & tbvNodes = container.getTbvList( );

  int total_assertions = 0;
  bool done_at_least_one_check = false;
  if ( config.fix_point_strategy == FORWARD )
  {
    for ( list<Node*>::iterator it = avNodes.begin()
          ; it != avNodes.end( )
          ; it++ )
    { 
      
      if ( (*it)->isDeleted( ) || (*it)->isCovered( ) || (*it)->getId( ) == n->getId( ) || (*it)->isLocked( )) continue;
      // avoid to check fixpoint with younger nodes
      if ( skip_younger_nodes && (*it)->getId( ) > n->getId( ) ) continue;

      Node *tmp_node = *it;
      
      int assertions = assertSuitableCombinations( n , tmp_node , true );
      if ( config.abstraction && assertions > 0 ) parent_cover.push_back( tmp_node );

      // check fixpoint
      if (assertions > 0 &&
          total_assertions >= config.fix_point_period &&
          solver.Check( ) == l_False)
      {
        done_at_least_one_check = true;
        total_assertions = 0;
        solver.Pop();
        solver.Comment("End fixpoint check");
        
        if ( config.verbosity > 1)
        {
          cerr << "\n\t(1) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
        }
       
        if ( config.abstraction )
        {
          updateCoveringRelation( n , parent_cover );
        }
        return true;
      }
    }

    // If it's not NULL it means that n is a new
    // candidate node originated from tbv, and so
    // also tbv goes inside the check
    if (
          tbv != NULL
       && ! tbv->isDeleted( )
       && ! tbv->isCovered( )
       && tbv->getId( ) != n->getId( )
       && ! tbv->isLocked( )
       && ! ( skip_younger_nodes && tbv->getId( ) > n->getId( ) )
       )
    {
      
      int assertions = assertSuitableCombinations( n , tbv , true );
      if ( config.abstraction && assertions > 0 ) parent_cover.push_back( tbv );
      
      // check fixpoint
      total_assertions += assertions;
      if (assertions > 0 &&
          total_assertions >= config.fix_point_period &&
          solver.Check( ) == l_False)
      {
        done_at_least_one_check = true;
        total_assertions = 0;
        solver.Pop();
        solver.Comment("End fixpoint check");
        
        if ( config.verbosity > 1)
        {
          cerr << "\n\t(2) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
        }
        
        if ( config.abstraction )
        {
          updateCoveringRelation( n , parent_cover );
        }
        return true;
      }
    }

    for ( list<Node*>::iterator it = tbvNodes.begin()
        ; it != tbvNodes.end( )
        ; it++ )
    { 
      
      if ( (*it)->isDeleted( ) || (*it)->isCovered( ) || (*it)->getId( ) == n->getId( ) || (*it)->isLocked( )) continue;
      // avoid to check fixpoint with younger nodes
      if ( skip_younger_nodes && (*it)->getId( ) > n->getId( ) ) continue;
      
      Node *tmp_node = *it;
      
      int assertions = assertSuitableCombinations( n , tmp_node , true );
      if ( config.abstraction && assertions > 0 ) parent_cover.push_back( tmp_node );
      
      // check fixpoint
      total_assertions += assertions;
      if (assertions > 0 &&
          total_assertions >= config.fix_point_period &&
          solver.Check( ) == l_False)
      {
        done_at_least_one_check = true;
        total_assertions = 0;
        solver.Pop();
        solver.Comment("End fixpoint check");
        
        if ( config.verbosity > 1)
        {
          cerr << "\n\t(3) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
        }
        
        if ( config.abstraction )
        {
          updateCoveringRelation( n , parent_cover );
        }
        return true;
      }
    }

  }
  else if ( config.fix_point_strategy == BACKWARD )
  {
    
    // If it's not NULL it means that n is a new
    // candidate node originated from tbv, and so
    // also tbv goes inside the check
    if (
          tbv != NULL
      && ! tbv->isDeleted( )
      && ! tbv->isCovered( )
      && tbv->getId( ) != n->getId( )
      && ! tbv->isLocked( )
      && ! ( skip_younger_nodes && tbv->getId( ) > n->getId( ) )
      )
    {

      int assertions = assertSuitableCombinations( n , tbv , true );
      if ( config.abstraction && assertions > 0 ) parent_cover.push_back( tbv );
      
      // check fixpoint
      total_assertions += assertions;
      if (assertions > 0 &&
          total_assertions >= config.fix_point_period &&
          solver.Check( ) == l_False)
      {
        done_at_least_one_check = true;
        total_assertions = 0;
        solver.Pop();
        solver.Comment("End fixpoint check");
        
        if ( config.verbosity > 1)
        {
          cerr << "\n\t(4) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
        }
        
        if ( config.abstraction )
        {
          updateCoveringRelation( n , parent_cover );
        }
        return true;
      }
    }

    for ( list<Node*>::reverse_iterator it = tbvNodes.rbegin()
        ; it != tbvNodes.rend()
        ; ++it )
    { 
      
      if ( (*it)->isDeleted( ) || (*it)->isCovered( ) || (*it)->getId( ) == n->getId( ) || (*it)->isLocked( ) ) continue;
      // avoid to check fixpoint with younger nodes
      if ( skip_younger_nodes && (*it)->getId( ) > n->getId( ) ) continue;
      
      Node *tmp_node = *it;
    
      int assertions = assertSuitableCombinations( n , tmp_node , true );
      if ( config.abstraction && assertions > 0) parent_cover.push_back( tmp_node );
      
      // check fixpoint
      total_assertions += assertions;
      if (assertions > 0 &&
          total_assertions >= config.fix_point_period &&
          solver.Check( ) == l_False)
      {
        done_at_least_one_check = true;
        total_assertions = 0;
        solver.Pop();
        solver.Comment("End fixpoint check");
        
        if ( config.verbosity > 1)
        {
          cerr << "\n\t(5) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
        }
        
        if ( config.abstraction )
        {
          updateCoveringRelation( n , parent_cover );
        }
        return true;
      }
    }
    
    
    for ( list<Node*>::reverse_iterator it = avNodes.rbegin()
        ; it != avNodes.rend()
        ; ++it )
    { 
      
      if ( (*it)->isDeleted( ) || (*it)->isCovered( ) || (*it)->getId( ) == n->getId( ) || (*it)->isLocked( )) continue;
      // avoid to check fixpoint with younger nodes
      if ( skip_younger_nodes && (*it)->getId( ) > n->getId( ) ) continue;
      
      Node *tmp_node = *it;
    
      int assertions = assertSuitableCombinations( n , tmp_node , true );
      if ( config.abstraction && assertions > 0 ) parent_cover.push_back( tmp_node );
      
      // check fixpoint
      total_assertions += assertions;
      if (assertions > 0 &&
          total_assertions >= config.fix_point_period &&
          solver.Check( ) == l_False)
      {
        done_at_least_one_check = true;
        total_assertions = 0;
        solver.Pop();
        solver.Comment("End fixpoint check");
        
        if ( config.verbosity > 1)
        {
          cerr << "\n\t(6) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
        }
        
        if ( config.abstraction )
        {
          updateCoveringRelation( n , parent_cover );
        }
        return true;
      }
    }
  }

  if ( !done_at_least_one_check && solver.Check( ) == l_False)
  {
    solver.Pop();
    solver.Comment("End fixpoint check");
    
    if ( config.verbosity > 1)
    {
      cerr << "\n\t(7) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
    }
        
    if ( config.abstraction )
    {
      updateCoveringRelation( n , parent_cover );
    }
    return true;
  }

  solver.Pop( );
  solver.Comment("End fixpoint check");
  solver.Comment("");
  solver.Comment("");
  if ( config.verbosity > 1)
  {
    cerr << "\n\tFixpoint check ends with true." << endl;
  }
  
  return false;
}


bool
MC::checkFixpoint ( Node * n , Node * tbv )
{
  assert( n );

#ifdef PEDANTIC_DEBUG
  n->checkLabel( );
  if ( tbv ) tbv->checkLabel( );
  container.checkNodes( );
#endif

 
  if ( config.verbosity > 1 )
  {
    cerr << "\n\n\tSTART FIXPOINT CHECK" << endl;
  }
  
  solver.Comment("");
  solver.Comment("");
  solver.Comment("Fixpoint test starts (c3)");
  solver.Push();

  // assert the node
  solver.Comment("Asserting the label of the node");
  solver.Assert( n->getLabel() );
  
  
  // assert all the previews nodes in all possible
  // configuration

  list < Node * > & avNodes  = container.getAvList( );
  list < Node * > & tbvNodes = container.getTbvList( );

  int total_assertions = 0;
  bool done_at_least_one_check = false;
  if ( config.fix_point_strategy == FORWARD )
  {
    for ( list<Node*>::iterator it = avNodes.begin()
          ; it != avNodes.end( )
          ; it++ )
    { 
      
      if ( (*it)->isDeleted( ) ) continue;

      Node *tmp_node = *it;
      
      int assertions = assertSuitableCombinations( n , tmp_node , true );

      // check fixpoint
      if (assertions > 0 &&
          total_assertions >= config.fix_point_period &&
          solver.Check( ) == l_False)
      {
        done_at_least_one_check = true;
        total_assertions = 0;
        solver.Pop();
        solver.Comment("End fixpoint check");
        
        if ( config.verbosity > 1)
        {
          cerr << "\n\t(1) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
        }
       
        return true;
      }
    }

    // If it's not NULL it means that n is a new
    // candidate node originated from tbv, and so
    // also tbv goes inside the check
    if ( tbv != NULL && ! tbv->isDeleted( ) )
    {
      int assertions = assertSuitableCombinations( n , tbv , true );
      
      // check fixpoint
      total_assertions += assertions;
      if (assertions > 0 &&
          total_assertions >= config.fix_point_period &&
          solver.Check( ) == l_False)
      {
        done_at_least_one_check = true;
        total_assertions = 0;
        solver.Pop();
        solver.Comment("End fixpoint check");
        
        if ( config.verbosity > 1)
        {
          cerr << "\n\t(2) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
        }
        return true;
      }
    }

    for ( list<Node*>::iterator it = tbvNodes.begin()
        ; it != tbvNodes.end( )
        ; it++ )
    { 
      
      if ( (*it)->isDeleted( ) ) continue;
      
      Node *tmp_node = *it;
      
      int assertions = assertSuitableCombinations( n , tmp_node , true );
      
      // check fixpoint
      total_assertions += assertions;
      if (assertions > 0 &&
          total_assertions >= config.fix_point_period &&
          solver.Check( ) == l_False)
      {
        done_at_least_one_check = true;
        total_assertions = 0;
        solver.Pop();
        solver.Comment("End fixpoint check");
        
        if ( config.verbosity > 1)
        {
          cerr << "\n\t(3) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
        }
        
        return true;
      }
    }

  }
  else if ( config.fix_point_strategy == BACKWARD )
  {
    
    // If it's not NULL it means that n is a new
    // candidate node originated from tbv, and so
    // also tbv goes inside the check
    if ( tbv != NULL && ! tbv->isDeleted( ) )
    {
      int assertions = assertSuitableCombinations( n , tbv , true );
      
      // check fixpoint
      total_assertions += assertions;
      if (assertions > 0 &&
          total_assertions >= config.fix_point_period &&
          solver.Check( ) == l_False)
      {
        done_at_least_one_check = true;
        total_assertions = 0;
        solver.Pop();
        solver.Comment("End fixpoint check");
        
        if ( config.verbosity > 1)
        {
          cerr << "\n\t(4) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
        }
        return true;
      }
    }

    for ( list<Node*>::reverse_iterator it = tbvNodes.rbegin()
        ; it != tbvNodes.rend()
        ; ++it )
    { 
      
      if ( (*it)->isDeleted( ) ) continue;
      
      Node *tmp_node = *it;
    
      int assertions = assertSuitableCombinations( n , tmp_node , true );
      
      // check fixpoint
      total_assertions += assertions;
      if (assertions > 0 &&
          total_assertions >= config.fix_point_period &&
          solver.Check( ) == l_False)
      {
        done_at_least_one_check = true;
        total_assertions = 0;
        solver.Pop();
        solver.Comment("End fixpoint check");
        
        if ( config.verbosity > 1)
        {
          cerr << "\n\t(5) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
        }
        
        return true;
      }
    }
    
    
    for ( list<Node*>::reverse_iterator it = avNodes.rbegin()
        ; it != avNodes.rend()
        ; ++it )
    { 
      
      if ( (*it)->isDeleted( ) ) continue;
      
      Node *tmp_node = *it;
    
      int assertions = assertSuitableCombinations( n , tmp_node , true );
      
      // check fixpoint
      total_assertions += assertions;
      if (assertions > 0 &&
          total_assertions >= config.fix_point_period &&
          solver.Check( ) == l_False)
      {
        done_at_least_one_check = true;
        total_assertions = 0;
        solver.Pop();
        solver.Comment("End fixpoint check");
        
        if ( config.verbosity > 1)
        {
          cerr << "\n\t(6) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
        }
        
        return true;
      }
    }
  }

  if ( !done_at_least_one_check && solver.Check( ) == l_False)
  {
    solver.Pop();
    solver.Comment("End fixpoint check");
    
    if ( config.verbosity > 1)
    {
      cerr << "\n\t(7) FIXPOINT CHECK ENDS WITH FALSE!" << endl;
    }
        
    return true;
  }

  solver.Pop( );
  solver.Comment("End fixpoint check");
  solver.Comment("");
  solver.Comment("");
  if ( config.verbosity > 1)
  {
    cerr << "\n\tFixpoint check ends with true." << endl;
  }
  
  return false;
}

Enode * MC::newExtVar( Node * n , int increment )
{
  // this counter keeps the number of new variables
  // created to develop the new node
  char buf[ 32 ];
  sprintf( buf, "z%lu", n->getLabelVars( ).size( ) + increment );
  
  declareIndexVar( buf );

  return egraph.mkVar( buf );  
}


Enode * MC::addLiteral( Enode * label
                      , Enode * z 
		      , Enode * array 
		      , Enode * new_term )
{
  assert( label );
  assert( z );
  assert( array );
  assert( new_term );

  vector< Enode * > unprocessed_enodes;
  list< Enode * > conjuncts;

  Enode * to_find = egraph.mkSelect( array, z );
  unprocessed_enodes.push_back( label );

  while( !unprocessed_enodes.empty( ) )
  {
    Enode * e = unprocessed_enodes.back( );
    
    unprocessed_enodes.pop_back( );
    
    Enode * arg_list;
    // Push children if not a literal
    if ( !e->isLit( ) )
    {
      for ( arg_list = e->getCdr( )
	  ; !arg_list->isEnil( )
	  ; arg_list = arg_list->getCdr( ) )
      {
	Enode * arg = arg_list->getCar( );
	assert( arg->isTerm( ) );
	unprocessed_enodes.push_back( arg );
      }
    }
    // Try to substitute if a literal
    else
    {
      bool found = false;

      Enode * atom = e;
      if ( e->isNot( ) )
	atom = e->get1st( );

      assert( atom->isEq( ) || atom->isLeq( ) );
      Enode * l = atom->get1st( );
      Enode * r = atom->get2nd( );

      if ( l == to_find )
      {
	found = true;
	l = new_term;
      }
      else if ( r == to_find )
      {
	found = true;
	r = new_term;
      }

      Enode * res = egraph.cons( atom->getCar( ), egraph.cons( l, egraph.cons( r ) ) );

      if ( e->isNot( ) )
	res = egraph.mkNot( egraph.cons( res ) );

      if ( found )
	conjuncts.push_back( res );
    }
  }

  Enode * ret = NULL;
  if ( conjuncts.empty( ) )
    ret = egraph.mkTrue( );
  else
    ret = egraph.mkAnd( egraph.cons( conjuncts ) );

  return ret;
}

Enode * MC::updateLabel ( Enode * formula 
                        , vector< Enode * > & old_vars 
                        , vector< Enode * > & new_vars )
{
  assert( formula );

  list< Enode * > new_label_list;
  set< Enode * > is_top_level;
  set< Enode * > touched;

  egraph.initDupMap1( );
  vector< Enode * > unprocessed_enodes;

  if ( formula->isLit( ) )
    is_top_level.insert( formula );

  assert( old_vars.size( ) == new_vars.size( ) );

  unprocessed_enodes.push_back( formula );

  while( !unprocessed_enodes.empty( ) )
  {
    Enode * e = unprocessed_enodes.back( );

    if ( egraph.valDupMap1( e ) != NULL )
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
      if ( egraph.valDupMap1( arg ) == NULL )
      {
	if ( e->isAnd( ) && arg->isLit( ) )
	  is_top_level.insert( arg );

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

    // cout << "CONSIDERING: " << e << endl;

    Enode * result = NULL;
    bool touch = false;
    if ( !e->isAnd( ) )
    {
      for ( size_t i = 0 ; i < old_vars.size( ) && result == NULL ; i ++ )
      {
	if ( old_vars[ i ] == e )
	{
	  // This is a substitution. This enode is relevant
	  result = new_vars[ i ];
	  touched.insert( e );
	  // cerr << "Subst done: " << e << " --> " << result << endl;
	  // cerr << e << " is relevant" << endl;
	}
      }
      // If no substitution was done, check
      // if arguments are relevant, so that this
      // node is relevant as well
      if ( result == NULL )
      {
	// cerr << "No subst done for: " << e << endl;
	for ( Enode * l = e->getCdr( ) 
	    ; !l->isEnil( ) && !touch
	    ; l = l->getCdr( ) )
	{
	  Enode * arg = l->getCar( );
	  if ( touched.find( arg ) != touched.end( ) )
	  {
	    touched.insert( e );
	    touch = true;
	    // cerr << "Arg " << arg << " of " << e << " is relevant" << endl;
	  }
	}
      }
    }

    if ( result == NULL )
      result = egraph.copyEnodeEtypeTermWithCache( e );

    if ( touch 
      && is_top_level.find( e ) != is_top_level.end( ) )
    {
      new_label_list.push_back( result );
    }

    /*
    cout << "To  : " << result << endl;
    cout << "List is: " << endl;
    for ( list< Enode * >::iterator it = new_label_list.begin( ) ; it != new_label_list.end( ) ; ++ it )
    {
      cout << "  " << *it << endl;
    }
    */
    
    egraph.storeDupMap1( e, result );
  }

  assert( egraph.valDupMap1( formula ) != NULL );

  egraph.doneDupMap1( );
  
  // cerr << "RES: " << res << endl;
  return egraph.mkAnd( egraph.cons( new_label_list ) );
}

bool
MC::isSat( Enode * n )
{
  solver.Push();
  solver.Assert( n );
  if (solver.Check( ) == l_False)
  {
    solver.Pop();
    return false;
  }
  else
  {
    solver.Pop();
    return true;
  }
}

bool
MC::isSat( Node * n )
{
  solver.Comment("");
  solver.Comment("");
  solver.Comment("");
  solver.Comment("Check if the preimage is sat");
  solver.Push();
  solver.Assert( n->getLabel( ) );
  if (solver.Check( ) == l_False)
  {
    solver.Pop();
    return false;
  }
  else
  {
    solver.Pop();
    return true;
  }
}

bool
MC::checkInitialIntersection( Node * n )
{
  solver.Comment("");
  solver.Comment("");
  solver.Comment("");
  solver.Comment("Check initial intersection");
  solver.Push();
  solver.Assert( n->getLabel() );
  vector < Enode * > & vars = n->getLabelVars( );
  size_t vars_size = vars.size();

  // number of "positions"
  size_t av_positions = initial_vars.size( );
    
  assert( av_positions <= vars.size( ) ); // otherwise it won't work...


  // assert the new node (all the combinations) and check.
  bool used_vars [vars_size];
  for (size_t i = 0; i < vars_size; i++) {
    used_vars[i] = false;
  }

  unsigned inst_vars [av_positions];
  // initialize vector
  for (size_t i = 0; i < av_positions; i++) {
    inst_vars[i] = i;
    used_vars[i] = true;
  }
    
  // substitute
  // position[i] indicates the variable of the formula
  // to be substituted in the avNode.
  // E.g.
  // inst_vars[2] = 4
  // means that the second variable of the label of the avnode
  // will be instantiated with the 4th variable of the actual
  // label
  // the vector "used_vars" will be used to avoid to instantiate
  // two different position with the same variable!
  bool done = false;

  // TODO: rewrite this quick hack
  vector< Enode * > origs, dests;

  while ( !done ) 
  {  
      
    // new formula to be asserted
      
    // check if the configuration is well formed (no overflow)    
    bool used_vars [vars_size];
    bool instantiate = true;
    for ( size_t i = 0; i < vars_size; i++ ) { 
      used_vars[i] = false;
    }   
    for ( size_t i = 0; i < av_positions && instantiate; i++ ) { 
      if ( used_vars[ inst_vars[ i ] ] == false)
        used_vars[ inst_vars[ i ] ] = true;
      else
        instantiate = false;
    }   
        
    
    if ( config.verbosity > 2 ) {
      cerr << "Considering this schema:";
      for (size_t j = 0; j < av_positions; j++) {
        cerr << " " << inst_vars[j];
      }   
      cerr << "\n";
    }

    if ( instantiate )
    {
      // asserting all combinations
      assert( av_positions <= vars.size() );

      solver.InstantiateInitial( av_positions
	                       , array_vars
			       , vars
			       , inst_vars );
    }
    
    // increase the last item
    inst_vars[ av_positions-1 ]++;
    for ( size_t p = av_positions-1
        ; p > 0 && inst_vars[ p-1 ] < vars_size
        ; p-- )
      {   
      if ( inst_vars[ p ] >= vars_size )
      {   
         inst_vars[ p ] = 0;
         inst_vars[ p-1 ]++;
      }   
    }   

    if ( inst_vars[ 0 ] >= vars_size )
      done = true;
  }

  if (solver.Check() == l_False)
  {
    solver.Pop();
    return false;
  }
  else
  {
    solver.Pop();
    return true;
  }
}

unsigned MC::getNodes ( )
{
 return container.getNodes(); 
}

unsigned MC::getDeletedNodes ( )
{
 return container.getDeletedNodes(); 
}

unsigned MC::getCoveredNodes ( )
{
 return container.getCoveredNodes(); 
}

unsigned MC::getDepth ( )
{
 return container.getDepth(); 
}

unsigned MC::getExCounter ( )
{
  return variables.size();
}

void
MC::reset ( )
{
  // this function should be used only with the invariant validator  
  assert( invariants || config.generate_invariants );
  status = UNKNOWN;
  
  // we need to reset the yices stack, and start again from the beginning.
  // reset all the relevat yices stack
  solver.Pop();
  
  // reset the number of unsafe formulae
  unsafe = 0;

  // crear the old container
  container.clear();
}

void
MC::newUnsafe ( Enode * new_unsafe )
{
  // this function should be used only with the invariant validator  
  assert( invariants );
  
  if ( unsafe_node )
  {
    unsafe_node->setLabel( new_unsafe );
    if ( config.abstraction ) {
      unsafe_node->setAbstractLabel( new_unsafe );
    }
    unsafe_node->setRedefinition( unsafe_node->getRedefinition() + 1 );
  }
  else
  {
    // Create new Node
    unsafe_node = new Node( egraph , nodes_univ_identifier ); 
    
    // Initialize Node
    unsafe_node->setLabel( new_unsafe );
    if ( config.abstraction ) {
      unsafe_node->setAbstractLabel( new_unsafe );
    }
    unsafe_node->setUnsafe( 0 );
  }
  container.addTbvNode( unsafe_node , candidate_invariants , false , config.global_invariant );
  createDefinition( unsafe_node );
}

void
MC::addAvNode ( Node * n )
{
  container.addAvNode( n );
}

void
MC::checkInvariant ( )
{
  assert ( !invariants );
/*

  while ( next_candidate < candidate_invariants.size( ) )
  {
    mc_i->reset( );

    // take the next candidate invariant
    Enode * candidate = candidate_invariants[ next_candidate ];
    next_candidate++;
    
    mc_i->newUnsafe( candidate );
    
    // check the safety of the candidate
    status_t result = mc_i->checkSafety( );
    if ( result == SAFE )
    {
      list < Node * > & av_list = mc_i->getAvList();
      if ( !av_list.empty() )
      {
        cerr << "=================================================================================================================" << endl;
        cerr << " Invariant(s) found:" << endl;
        // if it is safe, include the list of the av_nodes to the "main" list of the av_nodes
        for ( list< Node * >::iterator it = av_list.begin()
            ; it != av_list.end()
            ; it++ )
        {
          Node * n = new Node ( egraph );
          n->setLabel( (*it)->getLabel() );
          n->setId( discovered_invariants );
          n->setInvariant( true );
          createDefinition( n );
          container.addAvNode( n );
          discovered_invariants++;
          // print the invariant
          vector < Enode * > & vars = n->getFormula()->getVariables();
          cerr << " (forall " << vars[ 0 ];
          for ( size_t i = 1 ; i < vars.size() ; i++)
          {
            cerr << ", " << vars[ i ];
          }
          cerr << ". (not " << n->getLabel(); 
          cerr << "))" << endl; 
        }
        cerr << "=================================================================================================================" << endl;
      }
    }
  } 
*/
}

list < Node * > &
MC::getAvList( )
{
  return container.getAvList();
}
















void
MC::computePreimages ( vector < Node * > & preimages
                     , Node * n 
                     , Transition * t
                     , bool abstract_preimage )
{
  assert( n );
  assert( t );
  assert( n->getLabel( ) );


  if ( config.abstraction )
  {
    // ensure that everything is fine...
    assert( !n->getLabel( )->isFalse( ) );
    assert( isSat( n->getLabel( ) ) );
  }

  // retrieve label vars
  vector < Enode * > vars = n->getLabelVars( );  
  
  // check if we have enough variables
  if ( vars.size( ) == MAX_INDEX_VARS )
  {
    cerr << "Please increase the number of INDEX variables!" << endl;
    assert( false );
  }



  if ( t->getGlobal( ) )
  {
    if ( config.verbosity > 1 )
    {
      cerr << "WARNING! transition " << t->getId( ) << " is global!" << endl;
    }
    // global transition: compute preimages only mapping x --> z0
    assert( t->getVar( SECOND ) == NULL );

    buildFormula( preimages , z_variables[ 0 ] , NULL , n , t );  
    return;
  }



  vector < Transition::Case* > cases = t->getCases( );

  // find the limit
  int x_extra_var = 0, y_extra_var = 0;
  Enode * new_x_var = NULL, * new_y_var = NULL;
  if ( !t->avoidNewVariable( FIRST ) )
  {
    x_extra_var = 1;
    new_x_var = getNewIndexVariable( vars ); 
  }
  if ( t->getVar( SECOND ) && !t->avoidNewVariable( SECOND ) )
  {
    y_extra_var = 1;
    if ( new_x_var )
    {
      new_y_var = getNewIndexVariable( vars , new_x_var ); 
    }
    else
    {
      new_y_var = getNewIndexVariable( vars ); 
    }
  }

  if ( config.verbosity > 2 )
  {  
    cerr << "x will iterate over ";
    for ( size_t x = 0 ; x < vars.size( ) ; x++ )
    {
      cerr << vars[ x ] << ", ";
    }
    if ( new_x_var )
    {
      cerr << new_x_var;
    }
    cerr << endl;
    if ( t->getVar( SECOND ) )
    {
      cerr << "y will iterate over ";
      for ( size_t y = 0 ; y < vars.size( ) ; y++ )
      {
        cerr << vars[ y ] << ", ";
      }
      if ( new_x_var )
      {
        cerr << new_x_var << ", ";
      }
      if ( new_y_var )
      {
        cerr << new_y_var;
      }
      cerr << endl;
    }
  }

  // x will iterate over 'vars'
  for ( size_t x = 0 ; x < vars.size( )+x_extra_var ; x++ )
  {
    // y will iterate over 'vars'
    for ( size_t y = 0 ; y < vars.size( )+y_extra_var ; y++ )
    {
      // if x and y point to the same OLD variable (that's why we check
      // that x < vars.size( ) && y < vars.size( )
      // we continue.
      // the new variables are different even if x == y!
      if ( t->getVar( SECOND ) && x == y && x < vars.size( ) && y < vars.size( ) ) continue;
      
      Enode * x_var , * y_var;
      // choose x and y (add new variable if it's allowed!) 
      if ( x == vars.size( ) )
      {
        assert( new_x_var );
        x_var = new_x_var;
      }
      else
      {
        assert( x < vars.size( ) );
        x_var = vars[ x ];
      }

      if ( !t->getVar( SECOND ) )
      {
        y_var = NULL;
        // erase the y loop
        y = vars.size( )+y_extra_var;
      }
      else
      {
        if ( y == vars.size( ) )
        {
          if ( x < vars.size( ) )
          {
            if ( new_x_var )
            {
              y_var = new_x_var;
            }
            else
            {
              assert( new_y_var );
              y_var = new_y_var;
            }
          }
          else
          {
            assert( new_y_var );
            y_var = new_y_var;
          }
        }
        else
        {
          assert( y < vars.size( ) );
          y_var = vars[ y ];
        }
      }

      if ( config.verbosity > 2 )
      {
        cerr << "T (" << t->getId( ) << "), Calling 'BuildFormula' with this mapping" << endl;
        cerr << "x --> " << x_var << endl;
        if ( y_var )  cerr << "y --> " << y_var << endl;
      }
      
      buildFormula( preimages , x_var , y_var , n , t , abstract_preimage );    
    }
  }  
}



void
MC::buildFormula ( vector < Node * > & preimages
                    , Enode * var_x 
                    , Enode * var_y 
                    , Node * n
                    , Transition * t
                    , bool abstract_preimage )
{
  
  // data structures to build the formula
  vector < unsigned > j_cases;
  list < Enode * > inst_cases;
   
  buildFormulaBody( preimages 
                  , var_x 
		  , var_y 
		  , n->getLabelVars( ) 
		  , j_cases 
		  , inst_cases 
		  , 0 
		  , n 
		  , t 
		  , abstract_preimage 
		  );
}





/* due to the complexity of this function, all the tests
   that are done inside must be very very very cheap!!! */
/* Parameters:
   preimages is a vector of nodes used to collect all the preimages computed by the function
   var_x is the Enode (so it represent an INDEX variable zN) on which we are mapping the variable 'x' of the transition
   var_y is the Enode ( " ) on which we are mapping the variable 'y' of the transition
   vars are all the variables of the label of node 'n'. 'j' has to iterate over all the variables in 'vars'
   j_cases will hold, at the end, the case of each variable, i.e., j_cases[ vars[ i ] ] is the case where the ith variable has been mapped
   inst_cases  
*/
void
MC::buildFormulaBody ( vector < Node * > & preimages
                        , Enode * var_x 
                        , Enode * var_y 
                        , vector < Enode * > & vars
                        , vector < unsigned > & j_cases
                        , list < Enode * > & inst_cases
                        , size_t j
                        , Node * n
                        , Transition * t
                        , bool abstract_preimage )
{
  
  vector < Transition::Case* > cases = t->getCases( );
  
  if ( config.verbosity > 2 )
  {
    cerr << "\tj --> " << vars[ j ] << endl;
  }

  vector < Enode * > origs, dests;
  origs.push_back( t->getVar( FIRST ) );
  dests.push_back( var_x );
  if ( t->getVar( SECOND ) )
  {
    origs.push_back( t->getVar( SECOND ) );
    dests.push_back( var_y );
  }
  // vectors for substitution
  origs.push_back( t->getVj( ) );
  assert( !vars.empty( ) );
  assert( j < vars.size( ) );
  dests.push_back( vars[ j ] );
  
  // Every j variable must find it's own case,
  // otherwise the preimage will be empty
  bool found_right_case = false;
  for ( size_t c = 0 ; c < cases.size( ) ; c++ )
  {
    
    // origs and dests contains only x, y and j.
    assert( origs.size( ) == dests.size( ) );
    assert( origs.size( ) <= 3 );
    
    if ( config.verbosity > 2 )
    {
      cerr << "\tCase " << c << endl;
    }

    // check compatible
    // too slow!!
    //if ( ! checkCompatible ( n , vars[ j ] , cases[ c ]->values ) ) continue;

    // check the updates
    if ( !checkUpdates( vars[ j ] , n , cases[ c ]->values ) )
    {
      if ( config.verbosity > 2 )
      {
        cerr << "\tUpdates are not compatible!" << endl;
      }
      continue;
    }

    assert( inst_cases.size( ) == j );
    // check the case
    if ( !checkCase( cases[ c ]->condition , origs , dests , inst_cases ) )
    {
      if ( config.verbosity > 2 )
      {
        cerr << "\tCase is not sat!" << endl;
      }
      continue;
    }

    // found right case!
    // save this association
    assert( j_cases.size( ) == j );
    j_cases.push_back( c );
    found_right_case = true;
    
    // if this is the last variable, build the formula!
    if ( j == vars.size( )-1 )
    {
      if ( config.verbosity > 1 )
      {
        cerr << "\n\n\n\n\n\n\n\n\n";
        cerr << "\n\nBuilding new formula!" << endl;
        cerr << "From node ";
        n->getLabel( )->yicesPrint( cerr );
        cerr << endl;
        cerr << "With transition " << t << endl;
        cerr << "Using this assignments" << endl; 
        cerr << "\tx --> " << var_x << endl;
        if ( var_y )
        {
          cerr << "\ty --> " << var_y << endl;
        }
        cerr << "And these cases: " ;
        for ( size_t i = 0 ; i < j_cases.size( ) ; i++ ) {
          cerr << j_cases[ i ] << ", ";
        }
        cerr << endl;
      }

      //retrieve the label updated 
      Enode * updated_label;
      if ( abstract_preimage )
        updated_label = getUpdatedLabel( vars , j_cases , n->getAbstractLabel( ) , t );
      else
        updated_label = getUpdatedLabel( vars , j_cases , n->getLabel( ) , t );

      // the preimage is the conjunction of the guard with the updates
      Enode * new_preimage = egraph.mkAnd( egraph.cons( t->getGuard( ) , egraph.cons( updated_label , egraph.cons( inst_cases ) ) ) );
      
      if ( config.simplify_preimages )
      {
        new_preimage = simplify( new_preimage );
      }

      if ( !new_preimage->isFalse( ) )
      {

        // instantiate x and y in this preimage
        // remove the last element ( j )
        assert( origs.size( ) == dests.size( ) );
        assert( origs.size( ) > 0 );
        assert( origs.size( ) <= 3 );
        
        if ( checkIdenticalUpdates( j_cases , t ) )
        {
          if ( config.verbosity > 2 )
          {
            cerr << "All the old variables goes in an identical update, skip!" << endl;
       
          }
        }
      
        new_preimage = egraph.substitute( new_preimage , origs , dests );
      }

      if ( !new_preimage->isFalse( ) && isSat( new_preimage ) )
      {
        Node * new_node = new Node( egraph, nodes_univ_identifier );
        
        if ( config.verbosity > 1 )
        {
          cerr << "\n\nNEW PREIMAGE: ";
          new_preimage->yicesPrint( cerr );
          cerr << "\n\n\n\n";
        } 

        new_preimage = egraph.substitute( new_preimage , simplify_origs , simplify_dests );
        // build a new node with the new_preimage
        new_node->setLabel( new_preimage );
        new_node->setVar( FIRST, var_x );
        if ( t->getVar( SECOND ) )
          new_node->setVar( SECOND, var_y );
        else
          new_node->setVar( SECOND, NULL );
        new_node->setParent( n );
        new_node->setParentTransition( t );
        new_node->setCases( vars , j_cases );
        preimages.push_back( new_node );
      
        // if abstraction, build also the abstract formula computing the
        // preimage from the abstract label on 'n'
        if ( config.abstraction && !abstract_preimage ) {
          vector < Node * > abs_preimages;
          vector < unsigned > tmp_v;
          list < Enode * > tmp_l;
          buildFormulaBody ( abs_preimages , var_x , var_y , vars , tmp_v , tmp_l , 0 , n , t , true );
          assert ( abs_preimages.size( ) == 1 );
          cerr << "\n\nCOMPUTED NEW PREIMAGE:";
          cerr << " From node " << n->getId( );
          cerr << "\n Concrete label: ";
          n->getLabel( )->yicesPrint( cerr );
          cerr << "\n To concrete label: ";
          new_node->getLabel( )->yicesPrint( cerr );
          cerr << "\n Abstract label: ";
          n->getAbstractLabel( )->yicesPrint( cerr );
          cerr << "\n To abstract label: ";
          egraph.substitute( abs_preimages[ 0 ]->getLabel( ) , simplify_origs , simplify_dests )->yicesPrint( cerr );
          new_node->setAbstractLabel( abs_preimages[ 0 ]->getLabel( ) );
          cerr << endl << endl;
          getchar( );
        } 

      }
      else
      {
        if ( config.verbosity > 1 )
        {
          cerr << "\n\nNew preimage is empty!";
        } 
       }  

    }
    else
    {
      buildFormulaBody( preimages , var_x , var_y , vars , j_cases , inst_cases , j+1 , n , t );
    }

    // search for a new case (but at least one has been discovered!)
    j_cases.pop_back( );
    inst_cases.pop_back( );

  }
  if ( !found_right_case )
  {
    // this variable j cannot fit in any case, so the transition cannot be applied!
    return;
  }
}

bool
MC::checkCase ( Enode * formula 
              , vector< Enode * > & origs
              , vector< Enode * > & dests 
              , list < Enode * > & inst_cases )
{
  // INSTANTIATE THE FORMULA AND CHECK IF IT IS SAT

  assert( origs.size( ) == dests.size( ) );
  // instantiate the case (instantiate x , y and j)
  Enode * inst_case = egraph.substitute( formula , origs , dests );
  // TODO : CONTROLLARE QUESTO CHECK!!
  // potrebbe fallire se le formule non sono "semplificate"
  // if the case is false do not continue
  if ( inst_case->isFalse( ) 
    || ( inst_case->isEq( )
      && inst_case->get1st( ) != inst_case->get2nd( )
       )
  )
  {
    return false;
  }
  
  inst_cases.push_back( inst_case );
  return true;
}


bool
MC::checkUpdates( Enode * var_j 
                , Node * n 
                , vector < Enode * > & values )
{
  assert( array_vars.size( ) == values.size( ) );
  for ( size_t a = 0 ; a < array_vars.size( ) ; a++ )
  {
    // if the update is a constant should match!
    if ( values[ a ]->isConstant( ) )
    {
      Enode * value_in_the_label = n->getValue( var_j , array_vars[ a ]->enode , array_vars[ a ]->global );
      if ( value_in_the_label && values[ a ] && value_in_the_label != values[ a ] )
      {
        return false;
      }
    }
  }
  return true;
}

      
Enode *
MC::getUpdatedLabel( vector < Enode * > & vars
                   , vector < unsigned > & j_cases
                   , Enode * label
                   , Transition * t )
{
  
  assert( vars.size( ) == j_cases.size( ) );
  assert( !vars.empty( ) );
  assert( label );
  assert( t );

  if ( config.verbosity > 2 )
  {
    cerr << "And this cases assignment" << endl; 
    for ( size_t j = 0 ; j < vars.size( ) ; j++ )
    {
      cerr << "\t" << vars[ j ] << " --> case " << j_cases[ j ] << endl;
    }
    cerr << "\n\n\n\n\n";
  }

  vector < Enode * > origs, dests;
  // FIXME
  // these two loops are too expensive: would be great to avoid the second loop
  for ( size_t j = 0 ; j < vars.size( ) ; j++ )
  {
    for ( size_t a = 0 ; a < array_vars.size( ) ; a++ )
    {
      // add only the variables that changes!
      // check if the update is from  a[z0] --> a[z0]
      assert( array_index_matrix.size( ) > vars[ j ]->getMcmtId( ) );
      assert( array_index_matrix[ vars[ j ]->getMcmtId( ) ].size( ) > a );
      assert( array_index_matrix[ vars[ j ]->getMcmtId( ) ][ a ] );
      if ( array_index_matrix[ vars[ j ]->getMcmtId( ) ][ a ] != t->getUpdate( vars[ j ]->getMcmtId( ) , j_cases[ j ] , a ) )
      {
        origs.push_back( array_index_matrix[ vars[ j ]->getMcmtId( ) ][ a ] );
        dests.push_back( t->getUpdate( vars[ j ]->getMcmtId( ) , j_cases[ j ] , a ) );
      }
    }
  }

  if ( config.verbosity > 2 )
  {
    cerr << "\n\n\n\n\n";
    cerr << "Collected updates:" << endl;
    for ( size_t i = 0 ; i < origs.size( ) ; i++ )
    {
      cerr << "\t";
      origs[ i ]->yicesPrint( cerr );
      cerr << " --> "; 
      dests[ i ]->yicesPrint( cerr );
      cerr << endl;
    }
    cerr << "\n\n\n\n\n";
  }

  Enode * updated_label = egraph.substitute( label , origs , dests ); 

  return updated_label;
}

bool
MC::checkIdenticalUpdates( vector< unsigned > & j_vars , Transition * t )
{
  for ( size_t j = 0 ; j < j_vars.size( ) ; j++ )
  {
    if ( !t->isIdenticalUpdate( j_vars[ j ] ) )
    {
      return false;
    }
  }
  return true;
}

void
MC::deleteNode( Node * n )
{

  if ( n->isDeleted( ) ) return;
  n->Delete( );
  
  if ( config.verbosity > 1 )
  {
    n->printChildren( ); 
  }

  if ( n->isCovered( ) )
  {
    n->informCoveringParentsImFree( );
    n->clearCoveringParents( );
    n->setCovered( false );
    container.setCoveredNodes( container.getCoveredNodes( ) - 1 );
  }
  fixCoveredChildren( n );

  // take all the descendants (a superset of the children nodes) of this node and delete them!
  set < Node * > descendants = n->getDescendants( );
  for ( set < Node * >::iterator it = descendants.begin( )
      ; it != descendants.end( ) 
      ; it++ )
  {
    if ( (*it)->isDeleted( ) ) continue;
    cout << "node " << (*it)->getId( ) << " is deleted (ancestor deleted)" << endl;
    container.setCoveredNodes( container.getCoveredNodes( ) - 1 );
    deleteNode ( (*it) );
  }

}



































































































































































































































/* ******************************************************************************************************
 *    INVARIANT GENERATION
 * ******************************************************************************************************/
 
void
MC::generateInvariants ( )
{
/*  
  // get all the unsafe formulas
  list < Node * > & unsafe = container.getTbvList( );
  // empty the container
  solver.Push(); // this because when we start the backtrack we Push...
  reset();
  vector < Node * > invariants_found;

  // build the Invariant Container
  InvariantContainer * invariants_container = new InvariantContainer( egraph , config );
  // populate the invariant container with all the unsafe formulas
  for ( list< Node * >::iterator it = unsafe.begin() ; it != unsafe.end() ; it++ )
  {
    invariants_container->addTbvNode( (*it) );
  }

  
  


  // while I have invariants to be refined I continue to iterate
  while ( invariants_container->hasMoreTbvNodes( ) )
  {
    
    // take the next node to be refined
    Node * nextCandidate = invariants_container->getNextTbvNode( );
    
    newUnsafe ( nextCandidate->getLabel() );
    status_t s = checkSafety ();
    
    assert ( s == SAFE || s == UNSAFE );

    if ( s == SAFE )
    {
      list < Node * > & av_list = mc_i->getAvList();
      if ( !av_list.empty() )
      {
        cerr << "=================================================================================================================" << endl;
        cerr << " Invariant(s) found:" << endl;
        // if it is safe, include the list of the av_nodes to the "main" list of the av_nodes
        for ( list< Node * >::iterator it = av_list.begin()
            ; it != av_list.end()
            ; it++ )
        {
          Node * n = new Node ( egraph );
          n->setLabel( (*it)->getLabel() );
          n->setId( discovered_invariants );
          n->setInvariant( true );
          createDefinition( n );
          invariants_found.push_back( n );
          discovered_invariants++;
          // print the invariant
          vector < Enode * > & vars = n->getFormula()->getVariables();
          cerr << " (forall " << vars[ 0 ];
          for ( size_t i = 1 ; i < vars.size() ; i++)
          {
            cerr << ", " << vars[ i ];
          }
          cerr << ". (not " << n->getLabel(); 
          cerr << "))" << endl; 
        }
        cerr << "=================================================================================================================" << endl;
      }
    }
    else //( s == UNSAFE )
    {
      cerr << "Unsafety detected... refining!" << endl;

      Node * tmp = last_node;
      // go back to the beginning to find the first transition applied
      while ( !tmp->getParent()->isUnsafe( ) )
      {
        tmp = tmp->getParent( );
      }

      cerr << "Last node was " << tmp->getLabel() << endl;

      Enode * guard = tmp->getParentTransition( )->getGuard( );
      cerr << "First applied guard was " << guard << endl;

      // add the negation of the guard
      vector < Enode * > lits;
      retrieveLits( guard, lits );

      for ( size_t l = 0 ; l < lits.size() ; l++ )
      {
        // save the new candidate invariants!
        Node *n = new Node ( egraph );
        n->setLabel( egraph.mkAnd( egraph.cons( last_node->getLabel( ) , egraph.cons( egraph.mkNot( lits[ l ] ) ) ) ) );
        invariants_container->addTbvNode( n );
        cerr << "New candidate: " << n->getLabel() << endl;
      }
      delete last_node;
    }
  
    reset();
    
    for ( size_t i = 0 ; i < invariants_found.size( ) ; i++ )
    {
      container.addAvNode( invariants_found[ i ] );
    }
  }
*/
}





/* Function that set up useful predicates that will be tried during
   the search. */
void
MC::setUpPredicates(  )
{
  
  // create the variable z0
  Enode * z0 = egraph.mkVar( "z0" );
  z0->setIndex( true );
  
  Snode * i = sstore.mkVar( "Nat" );
  // Add variable only if not there before
  assert( egraph.hasSymbol( "z0", NULL, i ) );

  // generate predicates of the kind "a[z0] > b[z0]" where both 'a' and 'b' are global variables
  for ( size_t i = 0 ; i < array_vars.size( ) ; i++ )
  {
    for ( size_t j = 0 ; j < array_vars.size( ) ; j++ )
    {
      if ( j == i ) continue;
      if ( !array_vars[ i ]->global || !array_vars[ j ]->global ) continue;
      useful_predicates.push_back( egraph.mkLt( egraph.cons( egraph.mkSelect( array_vars[ i ]->enode , z0 ) , egraph.cons( egraph.mkSelect( array_vars[ j ]->enode , z0 ) ) ) ) );
    }
  }

/*
  cerr << "Useful predicates:" << endl;
  for ( size_t i = 0 ; i < useful_predicates.size( ) ; i++ )
  {
    cerr << "\t";
    useful_predicates[ i ]->yicesPrint( cerr );
    cerr << endl;
  }
  cerr << endl;
*/

}




/* Function that auto-certificate if the search space produced an invariant.
   We remove all covered/deleted nodes and re-start the search.
   If a node is generated, then there is an error!! */
void
MC::autoTest( ) {
  // avoid infinite loop!
  config.auto_test = false;
  
  cout << endl;
  cout << "=================================================================================================================" << endl;
  cout << "           SETTING UP AUTO-TEST" << endl;
  cout << "=================================================================================================================" << endl;
  cout << endl;

  // delete all the covered/deleted/locked nodes in the container
  container.autoTestPrepare( );
  
  // the tool should not generate new nodes!
  unsigned max_nodes = container.getTbvList( ).size( );

  cout << endl;
  cout << "=================================================================================================================" << endl;
  cout << "           STARTING AUTO-TEST (" << max_nodes << ")" << endl;
  cout << "=================================================================================================================" << endl;
  cout << endl;
  
  // no abstraction now!
  config.abstraction = false;
  for ( size_t a = 0 ; a < array_vars.size( ) ; a++ )
  {
    array_vars[ a ]->enode->setAbstr( false );
  }
  
  // check again the safety
  checkSafety( );

  unsigned new_av = container.getAvList( ).size( );
  if ( new_av <= max_nodes )
  {
    cout << endl;
    cout << "=================================================================================================================" << endl;
    cout << "           AUTO-TEST ENDED: no errors found. :-)" << endl;
    cout << "=================================================================================================================" << endl;
    cout << endl;
  }
  else
  {
    cout << endl;
    cout << "=================================================================================================================" << endl;
    cout << "           AUTO-TEST ENDED: ERRORS FOUND:" << endl;
    if ( new_av > max_nodes ) {
      cout << "             - fake global fixpoint: " << new_av << " more nodes have been generated" << endl;
    }
    cout << "=================================================================================================================" << endl;
    cout << endl;
    assert( false );
  }
}


















#ifdef PEDANTIC_DEBUG
void
MC::checkInterpolant ( Enode * formula )
{
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
        cerr << "\n\nWARNING!!! ---------------------------------" << endl;
        cerr << "Retrieved interpolant " << formula << "";
        cerr << endl << endl;
        //assert( false );
      }
      //literals.push_back( e );
    }

    egraph.storeDup1( e );
  }
  egraph.doneDup1( );
}
#endif

#endif
