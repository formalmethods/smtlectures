#ifndef SMTCOMP

#include "MC.h"

void MC::latexNode( Node * n )
{
  assert( n );

  // tex report
  assert( n->getId( ) );
  latex_file << "\n\\subsection{Node " << n->getId( ) << "}\n";
  latexFormula( n->getLabel( ) , true );
  
  // some statistics about this node
  latex_file << "\nNode obtained from the node " 
             << n->getParent( )->getId( );
  latex_file << " applying backward the transition number " 
             << n->getParentTransition( )->getId( );
  
  stringstream ss;
  n->getVar( FIRST )->latexPrint( ss );
  latex_file << " mapping $x \\mapsto " << ss.str( ) << "$";
  if ( n->getVar( SECOND ) )
  {
    n->getVar( SECOND )->latexPrint( ss );
    latex_file << ", $y \\mapsto " << ss.str( ) << "$";
  }
  latex_file << ".";
}


void MC::latexFormula( Enode * formula , bool existential )
{
  // latex formula for this node
  if ( existential )
    latex_file << "$$\n\\exists ";
  else 
    latex_file << "$$\n\\forall ";
  
  // used to print correctly the set of variables
  bool first = true;
  
  // search the variables and print them
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

    if ( e->isVar( ) && !e->hasSortArray( ) ) {
      if ( !first )
        latex_file << ",";
      latex_file << e;
      first = false;
    }

    assert( cache.find( e ) == cache.end( ) );
    cache.insert( e );
  }
  
  // print the formula
  stringstream ss;
  formula->latexPrint(ss);
  latex_file << ".\\left(" << ss.str() << "\\right)";
  latex_file << "\n$$\n";
}


// used to assert all combinations of a formula (without repetitions of variables)
void
MC::assertAllCombinationsWithRepetitions( Enode * av_formula, vector< Enode * > & av_vars, vector < Enode * > & vars, vector < Enode * > & toBeAsserted)
{
  // number of "positions"
  size_t av_positions = av_vars.size( );
  // number of variables
  size_t vars_size = vars.size();
  
  unsigned inst_vars [av_positions];
  // initialize vector
  for (size_t i = 0; i < av_positions; i++) {
    inst_vars[i] = 0;
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
    Enode * inst_formula;

    if ( config.verbosity > 2 )
    {
      cerr << "Considering this schema:" << endl;
      for (size_t j = 0; j < av_positions; j++) {
        cerr << "\t" << av_vars[ j ] << " -> " << vars[ inst_vars[ j ] ] << endl;
      }   
      cerr << "\nfor this label:\n" << av_formula << endl;
    }
    
    origs.clear();
    dests.clear();
    for (size_t i = 0; i < av_positions; i++) 
    {
      origs.push_back( av_vars[ i ] );
      dests.push_back( vars[ inst_vars[ i ] ] );
    } 
    inst_formula = egraph.substitute( av_formula, origs, dests );
    if ( config.verbosity > 2 ) 
    {
      cerr << "av_formula instantiated: " << inst_formula << endl;
    }
    toBeAsserted.push_back( inst_formula );
              
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
}




// used to assert all combinations of a formula (without repetitions of variables)
int
MC::assertAllCombinationsWithRepetitions( Enode * av_formula, vector< Enode * > & av_vars, vector < Enode * > & vars, bool negated)
{
  // number of "positions"
  size_t av_positions = av_vars.size( );
  // number of variables
  size_t vars_size = vars.size();
  
  int assertions = 0;
  
  solver.Comment( "Asserting with repetitions" );
  // if the formula to be instantiated
  // has more "position" than the number of variables
  // that I have, it reduces to false, and so I can
  // skip this formula.
  if( av_positions > vars.size( ) ) {
    solver.Comment("Number of variables less than number of positions");
    return assertions; 
  }

  unsigned inst_vars [av_positions];
  // initialize vector
  for (size_t i = 0; i < av_positions; i++) {
    inst_vars[i] = 0;
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
    Enode * inst_formula;

    if ( config.verbosity > 2 )
    {
      cerr << "Considering this schema:" << endl;
      for (size_t j = 0; j < av_positions; j++) {
        cerr << "\t" << av_vars[ j ] << " -> " << vars[ inst_vars[ j ] ] << endl;
      }   
      cerr << "\nfor this label:\n" << av_formula << endl;
    }
    
    origs.clear();
    dests.clear();
    for (size_t i = 0; i < av_positions; i++) 
    {
      origs.push_back( av_vars[ i ] );
      dests.push_back( vars[ inst_vars[ i ] ] );
    } 
    inst_formula = egraph.substitute( av_formula, origs, dests );
    if ( config.verbosity > 2 ) 
    {
      cerr << "av_formula instantiated: " << inst_formula << endl;
    }
    solver.Assert( inst_formula , negated );
    assertions++; 
              
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

  return assertions;
}

// used to assert all combinations of a formula (without repetitions of variables)
int
MC::assertAllCombinationsWithRepetitions( Enode * av_formula, vector< Enode * > & av_vars, vector < Enode * > & vars, bool negated , AbstractSolver & mySolver )
{
  // number of "positions"
  size_t av_positions = av_vars.size( );
  // number of variables
  size_t vars_size = vars.size();
  
  int assertions = 0;
  
  mySolver.Comment( "Asserting with repetitions" );
  // if the formula to be instantiated
  // has more "position" than the number of variables
  // that I have, it reduces to false, and so I can
  // skip this formula.
  if( av_positions > vars.size( ) ) {
    mySolver.Comment("Number of variables less than number of positions");
    return assertions; 
  }

  unsigned inst_vars [av_positions];
  // initialize vector
  for (size_t i = 0; i < av_positions; i++) {
    inst_vars[i] = 0;
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
    Enode * inst_formula;

    if ( config.verbosity > 2 )
    {
      cerr << "Considering this schema:" << endl;
      for (size_t j = 0; j < av_positions; j++) {
        cerr << "\t" << av_vars[ j ] << " -> " << vars[ inst_vars[ j ] ] << endl;
      }   
      cerr << "\nfor this label:\n" << av_formula << endl;
    }
    
    origs.clear();
    dests.clear();
    for (size_t i = 0; i < av_positions; i++) 
    {
      origs.push_back( av_vars[ i ] );
      dests.push_back( vars[ inst_vars[ i ] ] );
    } 
    inst_formula = egraph.substitute( av_formula, origs, dests );
    if ( config.verbosity > 2 ) 
    {
      cerr << "av_formula instantiated: " << inst_formula << endl;
    }
    mySolver.Assert( inst_formula , negated );
    assertions++; 
              
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

  return assertions;
}




// used to assert all combinations of a formula (without repetitions of variables)
int
MC::assertAllCombinations( Enode * av_formula, vector < Enode * > & av_vars, vector < Enode * > & vars, bool negated)
{
  // number of "positions"
  size_t av_positions = av_vars.size( );
  // number of variables
  size_t vars_size = vars.size();
  
  int assertions = 0;

  // if the formula to be instantiated
  // has more "position" than the number of variables
  // that I have, it reduces to false, and so I can
  // skip this formula.
  if( av_positions > vars.size( ) ) {
    solver.Comment("Number of variables less than number of positions");
    return assertions; 
  }

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
    Enode * inst_formula;

    // check if the configuration is well formed (no overflow)    
    for ( size_t i = 0; i < vars_size; i++ ) { 
      used_vars[i] = false;
    }   
    for ( size_t i = 0; i < av_positions; i++ ) { 
      if ( used_vars[ inst_vars[ i ] ] == false)
        used_vars[ inst_vars[ i ] ] = true;
      else
        goto RESTART;
    }   
        
  
    if ( config.verbosity > 2 ) {
      cerr << "Considering this schema:" << endl;
      for (size_t j = 0; j < av_positions; j++) {
        cerr << "\t" << av_vars[ j ] << " -> " << vars[ inst_vars[ j ] ] << endl;
      }   
      cerr << "\nfor this label:\n" << av_formula << endl;
    }
    
    origs.clear();
    dests.clear();
    for (size_t i = 0; i < av_positions; i++) 
    {
      origs.push_back( av_vars[ i ] );
      dests.push_back( vars[ inst_vars[ i ] ] );
    } 
    inst_formula = egraph.substitute( av_formula, origs, dests );
    if ( config.verbosity > 2 ) 
    {
      cerr << "av_formula instantiated: " << inst_formula << endl;
    }
    solver.Assert( inst_formula , negated );
    assertions++; 
              
RESTART: 

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

  return assertions;
}

int
MC::assertSuitableCombinations ( Node * n1 , Node * n2 , bool negated )
{
 
  Enode * f1 = n1->getLabel();
  Enode * f2 = n2->getLabel();
 
  assert( f1 );
  assert( f1->isAnd( ) || f1->isLit( ) );
  assert( f2 );
  assert( f2->isAnd( ) || f2->isLit( ) );

  if ( config.verbosity > 2 )
  {
    cerr << "\n\n\n\n\n\n\n\n";
    cerr << "ASSERT SUITABLE START!" << endl;
    cerr << "  f1 = " << f1 << endl;
    cerr << "  f2 = " << f2 << endl;
  }

  // first of all, if f2 is bigger than f1 it is not possible
  // that  (f1 -> f2)  is valid
  // check the number of variables
  const vector < Enode * > & f1_vars = n1->getLabelVars();
  const vector < Enode * > & f2_vars = n2->getLabelVars();

  if ( f1_vars.size() < f2_vars.size() )
  {
    if ( config.verbosity > 2 )
    {
      cerr << "OPTIMIZATION: f2 has less VARIABLES than f1, 0 assertions done!" << endl;
    }
    return 0;
  }

  int assertions = 0;

  // select next instantiation schema
  // number of "positions"
  size_t av_positions = f2_vars.size( );
  // number of variables
  size_t vars_size = f1_vars.size();
  
  // assert the new node (all the combinations) and check.
  bool used_vars[ vars_size ];
  vector < unsigned > inst_vars;
  inst_vars.resize(av_positions);
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

  vector< Enode * > origs, dests, heuristic1;
  while ( !done ) 
  {  
    // check if the configuration is well formed (no overflow)    
    for ( size_t i = 0; i < vars_size; i++ ) { 
      used_vars[i] = false;
    }   
    for ( size_t i = 0; i < av_positions; i++ ) { 
      if ( used_vars[ inst_vars[ i ] ] == false)
        used_vars[ inst_vars[ i ] ] = true;
      else
        goto RESTART;
    }   
        
  
    if ( config.verbosity > 2 )
    {
      cerr << "Considering this schema:" << endl;
      for (size_t j = 0; j < av_positions; j++) {
        cerr << "\t" << f2_vars[ j ] << " -> " << f1_vars[ inst_vars[ j ] ] << endl;
      }   
      cerr << "\nfor this label:\n" << f2 << endl;
      cerr << "\nto fixpoint:\n" << f1 << endl;
    }
    
    
    // check if this schema is correct
    for (size_t j = 0; j < av_positions; j++)
    {
      for (size_t a = 0 ; a < array_vars.size() ; a++ )
      {
        Enode * v1 = n1->getValue( f1_vars[ inst_vars[ j ] ] , array_vars[ a ]->enode , array_vars[ a ]->global );
        Enode * v2 = n2->getValue( f2_vars[ j ] , array_vars[ a ]->enode , array_vars[ a ]->global );
      
        if (v1 && v2 && v1 != v2 )
        {
          if ( config.verbosity > 2 )
          {
            cerr << "This instance is trivially sat" << endl;
          }
          goto RESTART;
        }
      }
    }
    
    
    instantiate( n2 , f1_vars , inst_vars , negated );
    assertions++; 
    
RESTART: 

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

  //getchar();
  return assertions;
}


int
MC::assertSuitableAbstractCombinations ( Node * n1 , Node * n2 , bool negated )
{
 
  Enode * f1 = n1->getAbstractLabel();
  Enode * f2 = n2->getAbstractLabel();
 
  assert( f1 );
  assert( f1->isAnd( ) || f1->isLit( ) );
  assert( f2 );
  assert( f2->isAnd( ) || f2->isLit( ) );

  if ( config.verbosity > 2 )
  {
    cerr << "\n\n\n\n\n\n\n\n";
    cerr << "ASSERT SUITABLE START!" << endl;
    cerr << "  f1 = " << f1 << endl;
    cerr << "  f2 = " << f2 << endl;
  }

  // first of all, if f2 is bigger than f1 it is not possible
  // that  (f1 -> f2)  is valid
  // check the number of variables
  const vector < Enode * > & f1_vars = n1->getLabelVars();
  const vector < Enode * > & f2_vars = n2->getLabelVars();

  if ( f1_vars.size() < f2_vars.size() )
  {
    if ( config.verbosity > 2 )
    {
      cerr << "OPTIMIZATION: f2 has less VARIABLES than f1, 0 assertions done!" << endl;
    }
    return 0;
  }

  int assertions = 0;

  // select next instantiation schema
  // number of "positions"
  size_t av_positions = f2_vars.size( );
  // number of variables
  size_t vars_size = f1_vars.size();
  
  // assert the new node (all the combinations) and check.
  bool used_vars[ vars_size ];
  vector < unsigned > inst_vars;
  inst_vars.resize(av_positions);
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

  vector< Enode * > origs, dests, heuristic1;
  while ( !done ) 
  {  
    // check if the configuration is well formed (no overflow)    
    for ( size_t i = 0; i < vars_size; i++ ) { 
      used_vars[i] = false;
    }   
    for ( size_t i = 0; i < av_positions; i++ ) { 
      if ( used_vars[ inst_vars[ i ] ] == false)
        used_vars[ inst_vars[ i ] ] = true;
      else
        goto RESTART;
    }   
        
  
    if ( config.verbosity > 2 )
    {
      cerr << "Considering this schema:" << endl;
      for (size_t j = 0; j < av_positions; j++) {
        cerr << "\t" << f2_vars[ j ] << " -> " << f1_vars[ inst_vars[ j ] ] << endl;
      }   
      cerr << "\nfor this label:\n" << f2 << endl;
      cerr << "\nto fixpoint:\n" << f1 << endl;
    }
    
    
    // check if this schema is correct
    for (size_t j = 0; j < av_positions; j++)
    {
      for (size_t a = 0 ; a < array_vars.size() ; a++ )
      {
        Enode * v1 = n1->getAbstractValue( f1_vars[ inst_vars[ j ] ] , array_vars[ a ]->enode , array_vars[ a ]->global );
        Enode * v2 = n2->getAbstractValue( f2_vars[ j ] , array_vars[ a ]->enode , array_vars[ a ]->global );
      
        if (v1 && v2 && v1 != v2 )
        {
          if ( config.verbosity > 2 )
          {
            cerr << "This instance is trivially sat" << endl;
          }
          goto RESTART;
        }
      }
    }
    
    
    instantiate( n2 , f1_vars , inst_vars , negated );
    assertions++; 
    
RESTART: 

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

  //getchar();
  return assertions;
}





void
MC::instantiate( Node * n 
               , const vector < Enode * > & variables 
	       , vector < unsigned > & order 
	       , bool negated )
{
  solver.Instantiate( n, array_vars, variables, order, negated );
  /*
  assert( order.size( ) <= variables.size( ) );

  // now create the string to instantiate
  stringstream ss;
  if ( !n->isInvariant( ) )
  {
    ss << "(node[" << n->getId( ) << "_" << n->getRedefinition( ) << "] ";
  }
  if ( n->isInvariant( ) )
  {
    ss << "(inv[" << n->getId( ) << "_" << n->getRedefinition( ) << "] ";
  }
  for ( size_t  i = 0 ; i < order.size( ) ; i ++ )
  {
    assert( order[i] < variables.size( ) );
    ss << variables[ order [ i ] ] << " ";
    for (size_t  a = 0 ; a < array_vars.size() ; a++ )
    {
      ss << array_vars[ a ]->enode << "[" << variables[ order [ i ] ] << "] ";
    }
  }
  ss << ")";

  //cerr << "Instantiating " << ss.str() << endl;
  solver.Assert( const_cast<char*>( ss.str().c_str() ) , negated );
  */

}

#endif
