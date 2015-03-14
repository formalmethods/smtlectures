/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#include "MCMTContext.h"

#include <csignal>

namespace mcmt {

bool stop;

} // namespace mcmt

//
// Execute a MCMT script
//
int
MCMTContext::execute( )
{
  status_t status = UNKNOWN;

  for ( size_t i = 0 ; i < command_list.size( ) ;  ++ i )
  {
    Command & c = command_list[ i ];

    switch( c.command )
    {
      case DECLARE_SORT:
	DeclareSort( c.str, c.num );
	break;
      case DEFINE_SORT:
	mcmt_error( "construct define-sort not yet supported" );
	break;
      case DECLARE_FUN:
	DeclareFun( c.str, c.sort_arg, c.sort_ret );
	break;
      case DEFINE_FUN:
	mcmt_error( "construct define-fun not yet supported" );
	break;
      case PUSH:
	Push( );
	break;
      case POP:
	Pop( );
	break;
      case CHECK_SAFETY:
	status = CheckSafety( );
	break;
      case GENERATE_INVARIANTS:
	GenerateInvariants( );
	break;
      case EXIT:
	Exit( );
	break;
      default:
	mcmt_error( "case not handled" );
    }
  }

  return 0;
}

void MCMTContext::DeclareFun( const char * name
                            , Snode * args
			    , Snode * rets )
{
  egraph.newSymbolLog( name, args, rets );
}

void MCMTContext::DeclareSort( const char * name, int )
{
  sstore.newSymbol( name );
}

void MCMTContext::Assert( Enode * )
{ 
  mcmt_error( "not implemented yet" );
}

void MCMTContext::GetProof( )
{
  mcmt_error( "not implemented yet" );
}

void MCMTContext::GetInterpolants( )
{
  mcmt_error( "not implemented yet" );
}

lbool MCMTContext::CheckSAT( )
{
  mcmt_error( "not implemented yet" );
  return l_Undef;
}

void MCMTContext::PrintResult( )
{

  if ( !config.generate_invariants)
  {
    
    const status_t s = mc.getStatus( );
    fflush( stderr );
    fflush( stdout );
 
    //
    // Statistics
    if ( config.verbosity > 0 )
    {
      cout << "\n=================================================================================================================" << "\nSystem is "; 
    }
 
    if ( s == SAFE )
    {
      cout << "SAFE!\n" << endl;
    }
    else if ( s == UNSAFE )
    {
      cout << "UNSAFE!\n" << endl;
    }
    else if ( s == UNKNOWN )
    {
      cout << "UNKNOWN!!\n" << endl;
    }
    else
    {
      mcmt_error( "UNEXPECTED RESULT!!\n" );
    }
    
    if ( config.verbosity > 0 )
    {
      cout << "Max depth:"<< mc.getDepth( );
      cout << "   #nodes:" << mc.getNodes( );
      if ( config.abstraction )
        cout << "   #covered nodes:"<< mc.getCoveredNodes( );
      else
        cout << "   #deleted nodes:"<< mc.getDeletedNodes( );
      cout << "   #SMT-solver calls:"<< solver.getCalls( );
      cout << "   #index_vars:" << mc.getExCounter( );
      cout << "   #invariants found: " << mc.getInvariants( ) - mc.getSuggestedInvariants().size();
      if ( mc.getInvariants( ) > 0 && mc.getSuggestedInvariants( ).size() > 0 )
      {
        cout << " (+" << mc.getSuggestedInvariants().size() << ")";
      }
      /* Lazy abstraction */
      cout << "   #CEGAR iterations: " << mc.getCegarLoops( );
      
      if ( config.verbosity > 0 && s == UNSAFE && mc.stoppingFailureAdopted() )
      {
        cout << "\nWarning: unsafety has been detected for the stopping failures model." << endl;
      }
 
      cout << endl;
 
      double   cpu_time = cpuTime();
      fprintf( stdout, "CPU Time used: %g s                                                           ", cpu_time == 0 ? 0 : cpu_time );
      uint64_t mem_used = memUsed();
      fprintf( stdout, "Memory used: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
      cout << "=================================================================================================================" << endl; 
    }
  }
  else
  {
  
    fflush( stderr );
    fflush( stdout );
 
    //
    // Statistics
    if ( config.verbosity > 0 )
    {
      cout << "\n=================================================================================================================" << "\nInvariant generation is DONE! "; 
    }
    
    if ( config.verbosity > 0 )
    {
      cout << "Max depth:"<< mc.getDepth( );
      cout << "   #nodes:" << mc.getNodes( );
      cout << "   #deleted nodes:"<< mc.getDeletedNodes( );
      cout << "   #SMT-solver calls:"<< solver.getCalls( );
      cout << "   #index_vars:" << mc.getExCounter( );
      cout << "   #invariants found: " << mc.getInvariants( );
      
      cout << endl;
 
      double   cpu_time = cpuTime();
      fprintf( stdout, "CPU Time used: %g s                     MCMT-executions: %d                    ", cpu_time == 0 ? 0 : cpu_time , mc.getNumberOfExecutions());
      uint64_t mem_used = memUsed();
      fprintf( stdout, "Memory used: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
      cout << "=================================================================================================================" << endl; 
    }
  }
}

//
// Functions for adding information
//
void MCMTContext::addCheckSafety( )
{
  Command c;
  c.command = CHECK_SAFETY;
  command_list.push_back( c );
}

void MCMTContext::addGenerateInvariants( )
{
  Command c;
  c.command = GENERATE_INVARIANTS;
  command_list.push_back( c );
}

void MCMTContext::DefineType( char * n, int l, int u )
{
  assert( n );
  // Allocate new sort symbol
  sstore.newSymbol( n );

  if ( config.verbosity > 1 )
    cerr << "MCMTContext::Added new type " << n << endl;
  
  mc.defineType( n, l, u );
//  mc_i.defineType( n, l, u );
}

void MCMTContext::DeclareIndexVar( char * ind_var )
{
  mc.declareIndexVar( ind_var );
//  mc_i.declareIndexVar( ind_var );
}

void MCMTContext::DeclareIntVar( char * var )
{
  assert( var );
  // Sort Int
  Snode * a = sstore.mkVar( "Int" );
  // Now creating the new variable (must not be there)
  egraph.newSymbolLog( var, NULL, a );
  // Adding array variable to the model checker
  mc.declareIntVar( var );
//  mc_i.declareIntVar( var );
}

void MCMTContext::DeclareNatVar( char * var )
{
  assert( var );
  // Sort Int
  Snode * a = sstore.mkVar( "Nat" );
  // Now creating the new variable (must not be there)
  egraph.newSymbolLog( var, NULL, a );
  // Adding array variable to the model checker
  mc.declareIntVar( var );
//  mc_i.declareIntVar( var );
}

void MCMTContext::DeclareRealVar( char * var )
{
  assert( var );
  // Sort Int
  Snode * a = sstore.mkVar( "Real" );
  // Now creating the new variable (must not be there)
  egraph.newSymbolLog( var, NULL, a );
  // Adding array variable to the model checker
  mc.declareRealVar( var );
//  mc_i.declareRealVar( var );
}

void MCMTContext::DeclareLocal( char * arr_var, char * type )
{
  assert( arr_var );
  assert( type );

  char buf[ 32 ];

  if ( strcmp( type, "nat" ) == 0 )
    sprintf( buf, "Nat" );
  else if ( strcmp( type, "int" ) == 0 )
    sprintf( buf, "Int" );
  else if ( strcmp( type, "bool" ) == 0 )
    sprintf( buf, "Bool" );
  else
  {
    mcmt_warning2( "Adding custom type: ", type );
    strcpy( buf, type );
  }

  // Sort Array
  Snode * a = sstore.mkVar( "Array" );
  Snode * i = sstore.mkVar( "Nat" );
  Snode * e = sstore.mkVar( buf );
  Snode * arr_sort = sstore.mkDot( sstore.cons( a
                                 , sstore.cons( i
	                         , sstore.cons( e ) ) ) ); 

  // Now creating array variable (must not be there)
  egraph.newSymbolLog( arr_var, NULL, arr_sort );
  // Adding array variable to the model checker
  // mc.declareLocal( arr_var, buf );
  // mc_i.declareLocal( arr_var, buf );
  mc.declareLocal( arr_var, arr_sort );
//  mc_i.declareLocal( arr_var, arr_sort );
}

void MCMTContext::DeclareGlobal( char * arr_var, char * type )
{
  assert( arr_var );
  assert( type );

  char buf[ 32 ];

  if ( strcmp( type, "nat" ) == 0 )
    sprintf( buf, "Nat" );
  else if ( strcmp( type, "int" ) == 0 )
    sprintf( buf, "Int" );
  else if ( strcmp( type, "bool" ) == 0 )
    sprintf( buf, "Bool" );
  else
  {
    mcmt_warning2( "Adding custom type: ", type );
    strcpy( buf, type );
  }

  // Sort Array
  Snode * a = sstore.mkVar( "Array" );
  Snode * i = sstore.mkVar( "Nat" );
  Snode * e = sstore.mkVar( buf );
  Snode * arr_sort = sstore.mkDot( sstore.cons( a
                                 , sstore.cons( i
	                         , sstore.cons( e ) ) ) ); 

  // Now creating array variable (must not be there)
  egraph.newSymbolLog( arr_var, NULL, arr_sort );
  // Declare a global array variable in the model checker
  // mc.declareGlobal( arr_var, type );
  // mc_i.declareGlobal( arr_var, type );
  mc.declareGlobal( arr_var, arr_sort );
//  mc_i.declareGlobal( arr_var, arr_sort );
}

void MCMTContext::setAbstract ( char * name )
{
  mc.setAbstract( name );
//  mc_i.setAbstract( name );
}

void MCMTContext::setAbstractTransition ( unsigned n )
{
  mc.setAbstractTransition( n );
//  mc_i.setAbstract( n );
}


void MCMTContext::addInitial( Enode * v1
			    , Enode * v2
			    , Enode * v3
			    , Enode * v4
                            , Enode * p )
{
  assert( v1 );
  assert( p );
  mc.declareInitial( v1, v2, v3, v4, p );
//  mc_i.declareInitial( v1, v2, v3, v4, p );
}

void MCMTContext::addSystemAxiom( Enode * v1
			        , Enode * v2
			        , Enode * v3
			        , Enode * v4
                                , Enode * p )
{
  assert( v1 );
  assert( p );
  mc.declareSystemAxiom( v1, v2, v3, v4, p );
//  mc_i.declareSystemAxiom( v1, v2, v3, v4, p );
}

void MCMTContext::addUnsafe( Enode * v1
                           , Enode * v2
                           , Enode * v3
                           , Enode * v4
                           , Enode * p )
{
  assert( v1 );
  assert( p );
  mc.declareUnsafe( v1, v2, v3, v4, p );
}

void MCMTContext::addSuggested( Enode * v1
                              , Enode * v2
                              , Enode * v3
                              , Enode * v4
                              , Enode * p )
{
  assert( v1 );
  assert( p );
  mc.declareSuggested( v1, v2, v3, v4, p );
}

void MCMTContext::addTransition( Enode * v1
                               , Enode * v2
			       , Enode * vj
                               , Enode * guard
			       , vector< Enode * > & uguards
			       , vector< Transition::Case * > & cases
                               , bool global )
{
  assert( v1 );
  assert( guard );
  assert( !cases.empty( ) );
  mc.declareTransition( v1, v2, vj, guard, uguards, cases, global );
//  mc_i.declareTransition( v1, v2, vj, guard, uguards, cases, global );
} 

void MCMTContext::addAssert( Enode * )
{
  mcmt_error( "can't process assert" );
}

void MCMTContext::addCheckSAT( )
{
  mcmt_error( "can't process check-sat" );
}

void MCMTContext::addPush( int )
{
  mcmt_error( "can't process push" );
}

void MCMTContext::addPop( int )
{
  mcmt_error( "can't process pop" );
}

void MCMTContext::addExit( )
{
  Command c;
  command_list.push_back( c );
  command_list.back( ).command = EXIT;
}

void MCMTContext::addGetProof( )
{
  mcmt_error( "can't process get-proof" );
}

#else

// Stubs to fool linker

#endif
