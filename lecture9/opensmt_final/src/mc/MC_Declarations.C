#ifndef SMTCOMP

#include "MC.h"

void MC::defineType( char * n, int l, int u )
{
  if ( config.verbosity > 1 )
    cerr << "MC::Defining new type " << n << " [" << l << ":" << u << "]" << endl;

   solver.DefineType( n, l, u );
}

void MC::declareLocal( char * name, Snode * type )
{
  Enode * new_var = egraph.mkVar( name );
  new_var->setMcmtId( array_vars.size( ) );
  array_vars.push_back( new ArrayVar( name
	                            , type
				    , new_var 
				    , false 
				    , false ) 
                      );
}

void MC::declareGlobal( char * name, Snode * type )
{
  Enode * new_var = egraph.mkVar( name );
  new_var->setMcmtId( array_vars.size( ) );
  new_var->setGlobal( true );
  array_vars.push_back( new ArrayVar ( name 
	                             , type 
				     , new_var 
				     , true 
				     , false ) 
                      );
}

void MC::setAbstract( char * name )
{
  assert( name );
  bool found = false;
  for ( size_t i = 0 ; i < array_vars.size( ) ; i++ )
  {
    if ( strcmp( array_vars[ i ]->getName( ), name ) == 0 )
    {
      array_vars[ i ]->enode->setAbstr( true );
      found = true;
    }
  }
  if ( !found )
  {
    cerr << "Error: variable to abstract has not been defined!" << endl;
  }
  else
  {
    config.abstraction = true;
    // Activate interpolation reasoning
    // FIXME: do a proper initialization
    // somewhere else, of better via config
    config.produce_inter = 1;
  }
}

void MC::setAbstractTransition( unsigned n )
{
  assert( n < transitions.size( ) );
  transitions[ n ]->setAbstracted( true );
  config.abstract_transitions = true;
}

void MC::declareIntVar( char * var )
{
  assert( var );
  Snode * i = sstore.mkVar( "Int" );

  // Add variable only if not there before
  if ( !egraph.hasSymbol( var, NULL, i ) )
  {
    egraph.newSymbolLog( var, NULL, i );
  }

  solver.Declare( var, NULL, i );
}

void MC::declareRealVar( char * var )
{
  assert( var );
  Snode * i = sstore.mkVar( "Real" );

  // Add variable only if not there before
  if ( !egraph.hasSymbol( var, NULL, i ) )
  {
    egraph.newSymbolLog( var, NULL, i );
  }

  solver.Declare( var, NULL, i );
}

void MC::declareIndexVar( char * ind_var )
{
  assert( ind_var );
  Snode * i = sstore.mkVar( "Nat" );

  // Add variable only if not there before
  if ( !egraph.hasSymbol( ind_var, NULL, i ) )
  {
    egraph.newSymbolLog( ind_var, NULL, i );

    // it's little dirty, but let's do it this way!
    if ( ind_var[0] == 'z' )
    {
      if ( config.verbosity > 2 )
      {
        cerr << "Introducing a new variable: " << ind_var << endl;
      }
    }
    
    // this variable could have been initialized by another instance of MC.
      
    // create the variable
    Enode * new_var = egraph.mkVar( ind_var );
    new_var->setMcmtId( variables.size() );
    new_var->setIndex( true );
    
    if ( index_vars.find( new_var ) == index_vars.end() )
    {
      index_vars.insert( new_var );
      // insert the new variable in the vector of all variables
      variables.push_back( new_var );
    }
  }
}

void MC::declareInitial( Enode * v1, Enode * v2, Enode *v3, Enode *v4, Enode * pred )
{
  assert(v1);
  assert(pred);
  
  initial = pred;
  
  if ( v1 )
    initial_vars.push_back( v1 );
  if ( v2 )
    initial_vars.push_back( v2 );
  if ( v3 )
    initial_vars.push_back( v3 );
  if ( v4 )
    initial_vars.push_back( v4 );


  if ( config.verbosity > 1 )
  {
    cerr << "MC::Adding initial state: Forall " << v1;
    if ( v2 )
      cerr << "," << v2;
    if ( v3 )
      cerr << "," << v3;
    if ( v4 )
      cerr << "," << v4;
    cerr << ". " << initial << endl;
  }

  assert( !initial_vars.empty() );
}


void MC::declareSystemAxiom( Enode * v1, Enode * v2, Enode *v3, Enode *v4, Enode * pred )
{
  assert(v1);
  assert(pred);

  MC::SystemAxiom * i = new MC::SystemAxiom ();
  
  i->s_ax = pred;
  
  if ( v1 )
    i->s_ax_vars.push_back( v1 );
  if ( v2 )
    i->s_ax_vars.push_back( v2 );
  if ( v3 )
    i->s_ax_vars.push_back( v3 );
  if ( v4 )
    i->s_ax_vars.push_back( v4 );


  if ( config.verbosity > 1 )
  {
    cerr << "MC::Adding system axiom: Forall " << v1;
    if ( v2 )
      cerr << "," << v2;
    if ( v3 )
      cerr << "," << v3;
    if ( v4 )
      cerr << "," << v4;
    cerr << ". " << pred << endl;
  }

  system_axioms.push_back(i);
}


void MC::declareTransition( Enode * v1
                          , Enode * v2
			  , Enode * vj
                          , Enode * guard
                          , vector< Enode * > & uguards
		          , vector< Transition::Case * > & cases
                          , bool global )
{
  
  // If last case is empty, fill with
  // conjunction of negation of previous
  if ( cases.back( )->condition == NULL )
  {
    list< Enode * > conj;
    for ( size_t i = 0 ; i + 1 < cases.size( ) ; ++ i )
    {
      assert( cases[ i ]->condition );
      conj.push_back( egraph.mkNot( egraph.cons( cases[ i ]->condition ) ) );
    }
    cases.back( )->condition = egraph.mkAnd( egraph.cons( conj ) );
  }

  if ( config.verbosity > 1 )
  {
    cerr << "MC::Adding transition n."<< transitions.size( ) <<": " << endl;
    cerr << " Var1: " << v1 << endl;
    if ( v2 )
      cerr << " Var2: " << v2 << endl;
    cerr << " Varj: " << vj << endl;
    cerr << " Guard: " << guard << endl;
    for ( size_t i = 0 ; i < uguards.size( ) ; ++ i )
      cerr << " uGuard: " << uguards[ i ] << endl;
    for ( size_t i = 0 ; i < cases.size( ) ; ++ i )
    {
      cerr << "  case " << cases[ i ]->condition << endl; 
      for ( size_t j = 0 ; j < cases[ i ]->values.size( ) ; ++ j )
	cerr << "   val " << cases[ i ]->values[ j ] << endl;
    }
  }
  // Creates and initializes transitions
  Transition * tr = new Transition( egraph
                       , sstore
                       , transitions.size( )+1
	               , v1
		       , v2
		       , vj
		       , guard
		       , uguards
		       , cases
                       , global );
  
  transitions.push_back( tr );
  tr->identicalPreprocessing( array_vars );
  tr->preprocess( );
}

void MC::declareUnsafe( Enode * v1
                      , Enode * v2
		      , Enode * v3
		      , Enode * v4
		      , Enode * pred )
{
  if ( config.verbosity > 1 )
  {
    cerr << "MC::Adding unsafe state: Exist " << v1;
    if ( v2 ) cerr << ", " << v2;
    cerr << ". " << pred << endl;
  }
  
  // vectors to egraph.substitute the variables different from z0, z1, etc...

  vector < Enode * > origs, dests;
  // new variable z0
  declareIndexVar( const_cast<char*>("z0") );
  Enode * z0, * z1, * z2, * z3;
  z0 = egraph.mkVar( "z0" ); 
  origs.push_back( v1 );
  dests.push_back( z0 );
  
  // add inequality (not (= v1 v2))
  if ( v2 )
  {
    pred = egraph.mkAnd( egraph.cons( pred , egraph.cons ( egraph.mkNot ( egraph.cons( egraph.mkEq( egraph.cons ( v1 , egraph.cons ( v2 ) ) ) ) ) ) ) );
    // new variable z1
    declareIndexVar( const_cast<char*>("z1") );
    z1 = egraph.mkVar( "z1" ); 
    origs.push_back( v2 );
    dests.push_back( z1 );

    if ( v3 )
    {
      pred = egraph.mkAnd( egraph.cons( pred , egraph.cons ( egraph.mkNot ( egraph.cons( egraph.mkEq( egraph.cons ( v1 , egraph.cons ( v3 ) ) ) ) ) ) ) );
      pred = egraph.mkAnd( egraph.cons( pred , egraph.cons ( egraph.mkNot ( egraph.cons( egraph.mkEq( egraph.cons ( v2 , egraph.cons ( v3 ) ) ) ) ) ) ) );
      // new variable z2
      declareIndexVar( const_cast<char*>("z2") );
      z2 = egraph.mkVar( "z2" ); 
      origs.push_back( v3 );
      dests.push_back( z2 );
    
      if ( v4 )
      {
        pred = egraph.mkAnd( egraph.cons( pred , egraph.cons ( egraph.mkNot ( egraph.cons( egraph.mkEq( egraph.cons ( v1 , egraph.cons ( v4 ) ) ) ) ) ) ) );
        pred = egraph.mkAnd( egraph.cons( pred , egraph.cons ( egraph.mkNot ( egraph.cons( egraph.mkEq( egraph.cons ( v2 , egraph.cons ( v4 ) ) ) ) ) ) ) );
        pred = egraph.mkAnd( egraph.cons( pred , egraph.cons ( egraph.mkNot ( egraph.cons( egraph.mkEq( egraph.cons ( v3 , egraph.cons ( v4 ) ) ) ) ) ) ) );
        // new variable z3
        declareIndexVar( const_cast<char*>("z3") );
        z3 = egraph.mkVar( "z3" ); 
        origs.push_back( v4 );
        dests.push_back( z3 );
      }
    }
  }

  pred = egraph.substitute( pred , origs , dests );

  if ( config.verbosity > 1 )
  {
    cerr << "MC::Adding unsafe state: Exist " << z0;
    if ( v2 ) cerr << ", " << z1;
    if ( v3 ) cerr << ", " << z2;
    if ( v4 ) cerr << ", " << z3;
    cerr << ". " << pred << endl;
  }
  

  // Create new Node
  Node * n = new Node( egraph , nodes_univ_identifier ); 
  // Initialize Node
  n->setLabel( pred );
  n->setUnsafe( unsafe );
  if ( config.abstraction )
  {
    n->setAbstractLabel( pred );
  }
  unsafe += 1;
  // Add to the container
  container.addTbvNode( n , candidate_invariants , false , config.global_invariant );
}

void
MC::defineUnsafeConfigs(  )
{
  list< Node * > unsafes = container.getTbvList( );
  for (list< Node * >::iterator it = unsafes.begin( )
      ; it != unsafes.end( )
      ; it++ )
  {
    if ( (*it)->isUnsafe( ) )
    {
      createDefinition( (*it) );
    }
  }
}

void MC::declareSuggested( Enode * v1, Enode * v2, Enode * v3, Enode * v4, Enode * pred )
{
  if ( config.verbosity > 1 )
  {
    cerr << "MC::Adding unsafe state: Exist " << v1;
    if ( v2 ) cerr << ", " << v2;
    cerr << ". " << pred << endl;
  }
  
  // vectors to egraph.substitute the variables different from z0, z1, etc...

  vector < Enode * > origs, dests;
  // new variable z0
  declareIndexVar( const_cast<char*>("z0") );
  Enode * z0, * z1, * z2, * z3;
  z0 = egraph.mkVar( "z0" ); 
  origs.push_back( v1 );
  dests.push_back( z0 );
  
  // add inequality (not (= v1 v2))
  if ( v2 )
  {
    pred = egraph.mkAnd( egraph.cons( pred , egraph.cons ( egraph.mkNot ( egraph.cons( egraph.mkEq( egraph.cons ( v1 , egraph.cons ( v2 ) ) ) ) ) ) ) );
    // new variable z1
    declareIndexVar( const_cast<char*>("z1") );
    z1 = egraph.mkVar( "z1" ); 
    origs.push_back( v2 );
    dests.push_back( z1 );

    if ( v3 )
    {
      pred = egraph.mkAnd( egraph.cons( pred , egraph.cons ( egraph.mkNot ( egraph.cons( egraph.mkEq( egraph.cons ( v1 , egraph.cons ( v3 ) ) ) ) ) ) ) );
      pred = egraph.mkAnd( egraph.cons( pred , egraph.cons ( egraph.mkNot ( egraph.cons( egraph.mkEq( egraph.cons ( v2 , egraph.cons ( v3 ) ) ) ) ) ) ) );
      // new variable z2
      declareIndexVar( const_cast<char*>("z2") );
      z2 = egraph.mkVar( "z2" ); 
      origs.push_back( v3 );
      dests.push_back( z2 );
    
      if ( v4 )
      {
        pred = egraph.mkAnd( egraph.cons( pred , egraph.cons ( egraph.mkNot ( egraph.cons( egraph.mkEq( egraph.cons ( v1 , egraph.cons ( v4 ) ) ) ) ) ) ) );
        pred = egraph.mkAnd( egraph.cons( pred , egraph.cons ( egraph.mkNot ( egraph.cons( egraph.mkEq( egraph.cons ( v2 , egraph.cons ( v4 ) ) ) ) ) ) ) );
        pred = egraph.mkAnd( egraph.cons( pred , egraph.cons ( egraph.mkNot ( egraph.cons( egraph.mkEq( egraph.cons ( v3 , egraph.cons ( v4 ) ) ) ) ) ) ) );
        // new variable z3
        declareIndexVar( const_cast<char*>("z3") );
        z3 = egraph.mkVar( "z3" ); 
        origs.push_back( v4 );
        dests.push_back( z3 );
      }
    }
  }

  pred = egraph.substitute ( pred , origs , dests );

  if ( config.verbosity > 1 )
  {
    cerr << "MC::Adding suggested negated invariant: Exist " << z0;
    if ( v2 ) cerr << ", " << z1;
    if ( v3 ) cerr << ", " << z2;
    if ( v4 ) cerr << ", " << z3;
    cerr << ". " << pred << endl;
  }
  
  candidate_invariants.push_back( pred );
  suggested_invariants.push_back( pred );
}


void
MC::initializeSolver( )
{
  if ( initialized )
  {
    return;
  }

  // Add variable only if not there before
  for ( int idx = 0 ; idx <= MAX_INDEX_VARS ; idx ++ )
  {
    char buf[ 32 ];
    sprintf( buf, "z%d", idx );
    declareIndexVar( buf );
    declareIndexVarInSolver( buf );
    if ( index_vars.find ( egraph.mkVar( buf ) ) == index_vars.end( ) )
    {
      index_vars.insert( egraph.mkVar( buf ) );
      z_variables.push_back( egraph.mkVar( buf ) );
    }
  }

  const int spaces = 6;
  for ( int i = 0 ; i < spaces ; i ++ )
  {
    solver.Comment("");
  }

  // asserting system axioms
  solver.Comment("ASSERTING SYSTEM AXIOMS");
  assertSystemAxioms();

  // assert in the i_solver (OpenSMT) that all the z variables are different
  //i_solver.Assert( egraph.mkDistinct( egraph.cons( z_variables ) ) );

  for ( int i = 0 ; i < spaces ; i ++ )
  {
    solver.Comment("");
  }

  // asserting index formula
  solver.Comment("DECLARING THE INITIAL FORMULA");
  solver.DeclareInitial( initial, initial_vars, array_vars );

  initialized = true;
}

//
// We assume that index variables are always
// integers >= 0
//
void MC::declareIndexVarInSolver ( char * ind_var )
{
  assert( ind_var );
  solver.DeclareIndexVar( ind_var, z_variables, array_vars );

#if USE_YICES
  // we are using Yices, so we have to initialize also OpenSMT
  //i_solver.DeclareIndexVar( ind_var, z_variables, array_vars );
#endif
}

Enode *
MC::getNewIndexVariable( vector < Enode * > & vars )
{
  // try to create a new variable with id = 0
  bool done = false;
  unsigned id = 0;
  while ( !done )
  {
    done = true;
    for ( size_t x = 0 ; x < vars.size( ) ; x++ )
    {
      if ( vars[ x ]->getMcmtId( ) == id )
      {
        done = false;
        id++;
      }
    }
  }
  
  Snode * nat = sstore.mkVar( "Nat" );
  char buf[ 64 ] = { "\0" };
  sprintf( buf, "z%u", id );
  // Declare symbol if not there
  if ( !egraph.hasSymbol( buf, NULL, nat ) )
  {
    egraph.newSymbolLog( buf, NULL, nat );
  }
  // Create a variable
  Enode * new_var = egraph.mkVar( buf );
  if ( new_var->getMcmtId( ) != id )
  {
    new_var->setMcmtId( id );
  }
  return new_var;
}

Enode *
MC::getNewIndexVariable( vector < Enode * > & vars , Enode * var2)
{
  // try to create a new variable with id = 0
  bool done = false;
  unsigned id = 0;
  while ( !done )
  {
    done = true;
    for ( size_t x = 0 ; x < vars.size( ) ; x++ )
    {
      if ( vars[ x ]->getMcmtId( ) == id )
      {
        done = false;
        id++;
      }
    }
    if ( var2->getMcmtId( ) == id )
    {
      done = false;
      id++;
    }
  }
  
  Snode * nat = sstore.mkVar( "Nat" );
  char buf[ 64 ] = { "\0" };
  sprintf( buf, "z%u", id );
  // Declare symbol if not there
  if ( !egraph.hasSymbol( buf, NULL, nat ) )
  {
    egraph.newSymbolLog( buf, NULL, nat );
  }
  // Create a variable
  Enode * new_var = egraph.mkVar( buf );
  if ( new_var->getMcmtId( ) != id )
  {
    new_var->setMcmtId( id );
  }
  return new_var;
}

void
MC::initializeDataStructures( )
{
  array_index_matrix.resize( MAX_INDEX_VARS );
  Snode * nat = sstore.mkVar( "Nat" );
  for (unsigned id = 0 ; id < MAX_INDEX_VARS ; id++ )
  {
    // declare zid
    char buf[ 64 ] = { "\0" };
    sprintf( buf, "z%u", id );
    // Declare symbol if not there
    assert( egraph.hasSymbol( buf , NULL , nat ) );
    // Create a variable
    Enode * new_var = egraph.mkVar( buf );
    
    for ( size_t a = 0 ; a < array_vars.size( ) ; a++ )
    {
      array_index_matrix[ id ].push_back( egraph.mkSelect( array_vars[ a ]->enode , new_var ) );
    }
  }
}

void
MC::initializeIndexVariables( )
{
  vector < Enode * > tmp;
  for ( int i = 0 ; i < MAX_INDEX_VARS ; i++ )
  {
    tmp.push_back( getNewIndexVariable( tmp ) );
  }
}

void MC::assertSystemAxioms ( )
{
  for (size_t sa = 0 ; sa < system_axioms.size() ; sa++)
  {
    if ( config.verbosity > 1 )
    {
      cerr << "Asserting the invariant " << system_axioms[ sa ]->s_ax << endl;
    }
    solver.Comment("Asserting system axiom");
    assertAllCombinationsWithRepetitions ( system_axioms[ sa ]->s_ax , system_axioms[ sa ]->s_ax_vars , z_variables , false ); 
#if USE_YICES
    // we are using Yices, so we have to initialize also OpenSMT
    // assertAllCombinationsWithRepetitions ( system_axioms[ sa ]->s_ax , system_axioms[ sa ]->s_ax_vars , z_variables , false , i_solver ); 
#endif

  }
} 

#endif
