/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso

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

#include "OpenSMTContext.h"
#include "ExpandITEs.h"
#include "AXDiffPreproc.h"
#include "BVBooleanize.h"
#include "TopLevelProp.h"
#include "DLRescale.h"
#include "Ackermanize.h"

#include <csignal>
#include <cstdio>

namespace opensmt {

bool stop;

} // namespace opensmt

extern int  smt2set_in  ( FILE * );
extern int  smt2parse   ( );
extern OpenSMTContext * parser_ctx;

void 
OpenSMTContext::SetLogic( const logic_t l ) 
{ 
  if ( config.dump_log )
    config.getLogOut( ) << "(set-logic " << logicStr( l ) << ")" << endl;

  config.logic = l; 

#ifdef SMTCOMP
  loadCustomSettings( );
#endif

  egraph.initializeStore( ); 
  solver.initialize( );

  // If not incremental delay initialization after preprocessing
  if ( config.incremental )
    egraph.initializeTheorySolvers( &solver );

  init = true;

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

void
OpenSMTContext::SetLogic( const char * str )
{
  logic_t l = UNDEF;

       if ( strcmp( str, "EMPTY" )     == 0 ) l = EMPTY;
  else if ( strcmp( str, "QF_UF" )     == 0 ) l = QF_UF;
  else if ( strcmp( str, "QF_BV" )     == 0 ) l = QF_BV;
  else if ( strcmp( str, "QF_RDL" )    == 0 ) l = QF_RDL;
  else if ( strcmp( str, "QF_IDL" )    == 0 ) l = QF_IDL;
  else if ( strcmp( str, "QF_LRA" )    == 0 ) l = QF_LRA;
  else if ( strcmp( str, "QF_LIA" )    == 0 ) l = QF_LIA;
  else if ( strcmp( str, "QF_UFRDL" )  == 0 ) l = QF_UFRDL;
  else if ( strcmp( str, "QF_UFIDL" )  == 0 ) l = QF_UFIDL;
  else if ( strcmp( str, "QF_UFLRA" )  == 0 ) l = QF_UFLRA; 
  else if ( strcmp( str, "QF_UFLIA" )  == 0 ) l = QF_UFLIA;
  else if ( strcmp( str, "QF_UFBV" )   == 0 ) l = QF_UFBV;
  else if ( strcmp( str, "QF_AX" )     == 0 ) l = QF_AX;
  else if ( strcmp( str, "QF_AXDIFF" ) == 0 ) l = QF_AXDIFF;
  else if ( strcmp( str, "QF_AUFBV" )  == 0 ) l = QF_AUFBV;
  else if ( strcmp( str, "QF_AXLIA" )  == 0 ) l = QF_AXLIA;
  else if ( strcmp( str, "QF_RD" )     == 0 ) l = QF_RD;
  // DO NOT REMOVE THIS COMMENT !!
  // IT IS USED BY CREATE_THEORY.SH SCRIPT !!
  // NEW_THEORY_INIT

   SetLogic( l );

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

void
OpenSMTContext::SetInfo( const char * key )
{
  opensmt_error2( "command not supported (yet)", key );
}

void
OpenSMTContext::SetInfo( const char * key, const char * attr )
{
  assert( key );
  assert( attr );

  if ( config.dump_log )
    config.getLogOut( ) << "(set-info " << key << " " << attr << ")" << endl;

  if ( strcmp( key, ":status" ) == 0 )
  {
    if ( strcmp( attr, "sat" ) == 0 )
      config.status = l_True;
    else if ( strcmp( attr, "unsat" ) == 0 )
      config.status = l_False;
    else if ( strcmp( attr, "unknown" ) == 0 )
      config.status = l_Undef;
    else
      opensmt_error2( "unrecognized attribute", attr );
  }
  else if ( strcmp( key, ":smt-lib-version" ) == 0 )
    ; // Do nothing
  else if ( strcmp( key, ":category" ) == 0 )
    ; // Do nothing
  else if ( strcmp( key, ":source" ) == 0 )
    ; // Do nothing
  else if ( strcmp( key, ":notes" ) == 0 )
    ; // Do nothing 
  else
    opensmt_error2( "unrecognized key", key );
}

void
OpenSMTContext::SetOption( const char * key )
{
  opensmt_error2( "command not supported (yet)", key );
}

void
OpenSMTContext::SetOption( const char * key, const char * attr )
{
  assert( key );
  assert( attr );

  if ( config.dump_log )
    config.getLogOut( ) << "(set-option " << key << " " << attr << ")" << endl;

  if ( strcmp( key, ":print-success" ) == 0 )
  {
    if ( strcmp( attr, "true" ) == 0 )
      config.print_success = true;
    else if ( strcmp( attr, "false" ) == 0 )
      config.print_success = false;
  }
  else if ( strcmp( key, ":expand-definitions" ) == 0 )
    opensmt_warning2( key, " not yet supported, skipping.")
  else if ( strcmp( key, ":interactive-mode" ) == 0 )
    opensmt_warning2( key, " not yet supported, skipping.")
  else if ( strcmp( key, ":produce-proofs" ) == 0 )
  {
    if ( strcmp( attr, "true" ) == 0 )
    {
#ifndef PRODUCE_PROOF
      opensmt_error( "You must configure code with --enable-proof to produce proofs" );
#endif
      config.setProduceProofs( );
    }
  }
  else if ( strcmp( key, ":produce-interpolants" ) == 0 )
  {
    if ( strcmp( attr, "true" ) == 0 )
    {
#ifndef PRODUCE_PROOF
      opensmt_warning( "You must configure code with --enable-proof to produce interpolants" );
#endif
      config.setProduceInter( );
    }
  }
  else if ( strcmp( key, ":produce-unsat-cores" ) == 0 )
    opensmt_warning2( key, " not yet supported, skipping.")
  else if ( strcmp( key, ":produce-models" ) == 0 )
  {
    if ( strcmp( attr, "true" ) == 0 )
      config.setProduceModels( );
  }
  else if ( strcmp( key, ":produce-assignments" ) == 0 )
    opensmt_warning2( key, " not yet supported, skipping.")
  else if ( strcmp( key, ":produce-interpolants" ) == 0 )
    config.setProduceInter( );
  else if ( strcmp( key, ":regular-output-channel" ) == 0 )
    config.setRegularOutputChannel( attr );
  else if ( strcmp( key, ":diagnostic-output-channel" ) == 0 )
    config.setDiagnosticOutputChannel( attr );
  else if ( strcmp( key, ":random-seed" ) == 0 )
    opensmt_warning2( key, " not yet supported, skipping.")
  else if ( strcmp( key, ":verbosity" ) == 0 )
    config.verbosity = atoi( attr );
  else if ( strcmp( key, ":split-equalities" ) == 0 )
  {
    if ( strcmp( attr, "false" ) == 0 )
      config.setSplitEqualities( false );
  }
  else if ( strcmp( key, ":lra-gaussian-elim" ) == 0 )
  {
    if ( strcmp( attr, "0" ) == 0 )
      config.setLraGaussianElim( 0 );
    else if ( strcmp( attr, "1" ) == 0 )
      config.setLraGaussianElim( 1 );
  }
  else if ( strcmp( key, ":proof-set-inter-algo" ) == 0 )
  {
    if ( strcmp( attr, "0" ) == 0 )
      config.setInterAlgo( 0 );
    else if ( strcmp( attr, "1" ) == 0 )
      config.setInterAlgo( 1 );
    else if ( strcmp( attr, "2" ) == 0 )
      config.setInterAlgo( 2 );
    else
      opensmt_warning2( "skipping :proof-set-inter-algo ", key );
  }
  else
    opensmt_warning2( "skipping option ", key );

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

//
// Here set the right parameter values for SMTCOMP
//
void OpenSMTContext::loadCustomSettings( )
{
  // Comment to produce binary for application track
  config.incremental = 0;

  if ( config.logic == QF_IDL )
  {
    config.sat_polarity_mode = 5;
    config.sat_learn_up_to_size = 5;
    config.sat_minimize_conflicts = 1;
    config.sat_restart_first = 70;
    config.dl_theory_propagation = 1;
    config.sat_preprocess_booleans = 1;
  }
  else if ( config.logic == QF_UFIDL )
  {
    config.sat_polarity_mode = 1;
    config.sat_learn_up_to_size = 5;
    config.sat_minimize_conflicts = 1;
    config.sat_restart_first = 100;
    config.dl_theory_propagation = 1;
    config.sat_preprocess_booleans = 0;
  }
  else if ( config.logic == QF_RDL )
  {
    config.sat_polarity_mode = 0;
    config.sat_learn_up_to_size = 5;
    config.sat_minimize_conflicts = 1;
    config.sat_preprocess_booleans = 1;
    config.sat_restart_first = 70;
    config.dl_theory_propagation = 1;
    config.sat_restart_inc = 1.2;
  }
  else if ( config.logic == QF_UF )
  {
    config.sat_polarity_mode = 0;
    config.sat_learn_up_to_size = 8;
    config.sat_minimize_conflicts = 1;
    config.sat_preprocess_booleans = 1;
    config.sat_restart_first = 50;
    config.uf_theory_propagation = 1;
  }
  else if ( config.logic == QF_LRA )
  {
    config.sat_polarity_mode = 0;
    config.sat_learn_up_to_size = 12;
    config.sat_minimize_conflicts = 0;
    config.sat_restart_first = 70;
    config.lra_theory_propagation = 1;
    config.sat_preprocess_booleans = 0;
  }
}

// =======================================================================
// Functions that actually execute actions

void OpenSMTContext::DeclareSort( const char * name, const int arity )
{
  if ( config.dump_log )
    config.getLogOut( ) << "(declare-sort " << name << " " << arity << ")" << endl;

  if ( config.tool == OPENSMT  
    && config.verbosity > 1 )
    cerr << "# OpenSMTContext::Declaring sort " 
         << name 
	 << " of arity "
	 << arity
	 << endl;

  sstore.newSymbol( name );

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

void OpenSMTContext::DeclareSubrange( Snode *   s
                                    , const int l
				    , const int u )
{
  if ( config.dump_log )
    config.getLogOut( ) << "(declare-sort " << s << " 0)" << endl;

  map< Snode *, Pair( int ) >::iterator it = sort_to_range.find( s );
  if ( it != sort_to_range.end( ) )
    mcmt_error2( "subrange already declared: ", s );
  
  sort_to_range[ s ] = make_pair( l, u );

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

void OpenSMTContext::DeclareFun( const char * name
                               , Snode * args
                               , Snode * rets )
{
  /*
  if ( config.dump_log )
  {
    config.getLogOut( ) << "(declare-fun " 
                        << name;
    if ( args )
      config.getLogOut( ) << " (" << args << ")";
    else
      config.getLogOut( ) << " ()";

    config.getLogOut( ) << " " 
			<< rets 
			<< ")" 
			<< endl;
  }
  */

  if ( config.tool == OPENSMT
    && config.verbosity > 1 )
  {
    cerr << "# OpenSMTContext::Declaring function " 
	 << name 
	 << " of sort ";
    if ( args ) cerr << args;
    else cerr << "()";
    cerr << " " << rets << endl;
  }

  if ( config.tool == MCMT )
  {
    if ( args != NULL )
      mcmt_error2( "Received arg sort, but assumed none ", args );

    // Add variable only if not there before
    if ( !egraph.hasSymbol( name, args, rets ) )
    {
      egraph.newSymbolLog( name, args, rets );
    }
    assert( egraph.hasSymbol( name, args, rets ) );

    // Find if this sort is bounded and add range if necessary
    map< Snode *, Pair( int ) >::iterator it = sort_to_range.find( rets );
    if ( it != sort_to_range.end( ) )
    {
      Enode * l = egraph.mkNum( it->second.first );
      Enode * u = egraph.mkNum( it->second.second );
      Enode * var = egraph.mkVar( name );
      Enode * lb = egraph.mkLeq( l, var );
      Enode * ub = egraph.mkLeq( var, u );
      Assert( lb );
      Assert( ub );

      if ( config.verbosity > 2 )
      {
	cerr << "OPENSMT INPUT: " << lb << endl;
	cerr << "OPENSMT INPUT: " << ub << endl;
      }
    }
  }
  else
  {
    egraph.newSymbol( name, args, rets );
  }

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

void OpenSMTContext::DefineFun( const char * name
                              , Enode * var_list
			      , Enode * fun )
{
  /*
  if ( config.dump_log )
  {
    config.getLogOut( ) << "(define-fun " << name << " ("; 
    for ( Enode * v_list = var_list 
	; !v_list->isEnil( ) 
	; v_list = v_list->getCdr( ) )
    {
      Enode * v = v_list->getCar( );
      config.getLogOut( ) << " (" << v << " " << v->getRetSort( ) << ")";
    }
    config.getLogOut( ) << " )" << " " << fun->getRetSort( ) << " " << fun << ")" << endl;
  }
  */

  if ( config.tool == OPENSMT 
    && config.verbosity > 1 )
    cerr << "# OpenSMTContext::Defining " << name << " " << var_list << " " << fun << endl;

  egraph.newDefine( name, var_list, fun );

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

void OpenSMTContext::Push( unsigned n )
{
  assert( n >= 1 );
  while ( n -- >= 1 ) Push( );
}

void OpenSMTContext::Pop( unsigned n )
{
  assert( n >= 1 );
  while ( n -- >= 1 ) Pop( );
}

void OpenSMTContext::Push( )
{ 
  if ( config.dump_log )
    config.getLogOut( ) << "(push 1)" << endl;

  if ( config.tool == OPENSMT
    && config.verbosity > 1 )
    cerr << "# OpenSMTContext::Pushing backtrack point" << endl;

  // Save assertion size
  undo_stack_assertions.push_back( active_assertions.size( ) );
  // Save processed assertions
  undo_proc_assertions.push_back( processed_assertions );
  // Save toplevelprop state
  ipropagator.pushBacktrackPoint( );
  // Save solver state
  solver.pushBacktrackPoint( ); 
#ifdef PRODUCE_PROOF
  // Save coloring
  if ( config.produce_inter != 0 )
    egraph.saveColors( );
#endif

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

void OpenSMTContext::Pop( )
{
  if ( config.dump_log )
    config.getLogOut( ) << "(pop 1)" << endl;

  if ( config.tool == OPENSMT
    && config.verbosity > 1 )
    cerr << "# OpenSMTContext::Popping backtrack point" << endl;
  
  if ( undo_stack_assertions.empty( ) )
    opensmt_error( "A pop without a push ?" );

  // Retrieve size at last push time
  const size_t new_size = undo_stack_assertions.back( );

  // Dispose backtrack point
  undo_stack_assertions.pop_back( );
  // Backtracks assertions
  active_assertions.resize( new_size );
  // Set processed_assertions
  processed_assertions = undo_proc_assertions.back( );
  // Dispose backtrack point
  undo_proc_assertions.pop_back( );
  // Restore ipropagator state
  ipropagator.popBacktrackPoint( );
  // Restore solver state
  solver.popBacktrackPoint( );
#ifdef PRODUCE_PROOF
  if ( config.produce_inter != 0 )
  {
    // Clear partitions
    active_partitions.clear( );
    // Clear interpolant sequence
    interpolants.clear( );
    // Reinitialize partitions
    egraph.setNofPartitions( 0 );
    nof_partitions = 0;
    // Undo coloring
    egraph.restoreColors( );
  }
#endif

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

void OpenSMTContext::Reset( )
{
  if ( config.tool == OPENSMT
    && config.verbosity > 1 )
    cerr << "# OpenSMTContext::Resetting" << endl;

  solver.reset( );

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

void OpenSMTContext::Assert( Enode * e, const bool neg )
{
  assert( e );

  if ( config.dump_log )
  {
    config.getLogOut( ) << "(assert " 
                        << ( neg ? "(not " : "" )
			<< e
                        << ( neg ? ") )" : " )" )
			<< endl;
  }

  if ( config.tool == OPENSMT
    && config.verbosity > 1 )
  {
    if ( e->isBooleanOperator( ) )
      cerr << "# OpenSMTContext::Asserting formula with id " << e->getId( ) << endl;
    else
      cerr << "# OpenSMTContext::Asserting formula " << e << endl;
  }

#if 1
  active_assertions.push_back( neg ? egraph.mkNot( e ) : e );
  //
  // BELOW OLD CODE TO BE REMOVED
  //
#else
  // Move an assertion into the Egraph
  // They are stored and might be preprocessed 
  // before entering the actual solver
  // For static
  if ( config.incremental == 0 )
    active_assertions.push_back( neg ? egraph.mkNot( e ) : e );
  // Ideally here replace with a class Preprocessor 
  // which is incremental and backtrackable ... Then
  // the next and previous instruction disappear and
  // a Preprocessor.doIt( ) will be called from CheckSAT
  // when requested
  else
    active_assertions.push_back( egraph.prepareAssertion( e, neg ) );
#endif

#ifdef PRODUCE_PROOF
  if ( config.produce_inter != 0 )
    egraph.colorAsShared( active_assertions.back( ) );
#endif

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

void OpenSMTContext::AssertPartition( Enode * e )
{
#ifdef PRODUCE_PROOF
  if ( config.produce_inter == 0 )
  {
    Assert( e );
  }
  else
  {
    nof_partitions ++;
    AssertPartition( e, nof_partitions );
  }
#else
  Assert( e );
#endif

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

void OpenSMTContext::AssertPartition( Enode * e, const unsigned 
#ifdef PRODUCE_PROOF
    p 
#endif
    )
{
#ifdef PRODUCE_PROOF
  assert( e );
  if ( config.produce_inter == 0 )
  {
    opensmt_warning( "You need to enable produde_inter to compute interpolants. Asserting as normal assertion." );
    Assert( e );
  }
  else
  {
    if ( config.dump_log )
    {
      config.getLogOut( ) << "; Partition " << p << endl;
      config.getLogOut( ) << "(assert-partition " 
	<< e
	<< " )"
	<< endl;
    }

    ipartitions_t partitions;
    setbit( partitions, p );

    // Otherwise colors are initialized later
    if ( config.term_abstraction )
      active_partitions.push_back( e );
    // If term abstraction is enabled, don't preprocess partitions
    else
    {
      active_partitions.push_back( egraph.preparePartition( e, partitions ) );
      egraph.setNofPartitions( p );
    }

    if ( config.print_success )
      config.getRegularOut( ) << "success" << endl;
  }
#else
  opensmt_warning( "You need a version of opensmt compiled with --enable-proof" );
  opensmt_warning( "You need to enable produde_inter to compute interpolants" );
  Assert( e );
#endif
}

void OpenSMTContext::GetModel( )
{
#ifndef SMTCOMP
  if ( config.produce_models == 0 )
  {
    opensmt_warning( "Skipping command (get-model) as produce-models is not set" );
    return;
  }

  if ( state == l_True )
    solver.printModel( );
#endif
}

void OpenSMTContext::GetProof( )
{
#ifdef PRODUCE_PROOF
  if ( state == l_False )
    solver.printProof( config.getRegularOut( ) );
  else
    opensmt_warning( "Skipping command (get-proof) as formula is not unsat" );
#else
  opensmt_warning( "Skipping command (get-proof): you need a version of opensmt compiled with --enable-proof" );
#endif

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

void OpenSMTContext::GetInterpolants( )
{
  if ( config.dump_log )
    config.getLogOut( ) << "(get-interpolants)" << endl;

#ifdef PRODUCE_PROOF
  if ( config.produce_inter == 0 )
  {
    opensmt_warning( "Skipping command (get-interpolants) as (produce-interpolants) is not set" );
  }
  else if ( state == l_False )
  {
    for ( size_t i = 0 ; i < interpolants.size( ) ; i ++ )
      GetInterpolant( i, true );
  }
  else
  {
    opensmt_warning( "Skipping command (get-interpolants) as formula is not unsat" );
  }
#else
  opensmt_warning( "Skipping command (get-interpolants): you need a version of opensmt compiled with --enable-proof" );
#endif

  if ( config.print_success )
    config.getRegularOut( ) << "success" << endl;
}

Enode * OpenSMTContext::GetInterpolant( const unsigned n, const bool print_out )
{
  if ( config.dump_log )
    config.getLogOut( ) << "(get-interpolant " << n << ")" << endl;

#ifdef PRODUCE_PROOF
  if ( config.produce_inter == 0 )
  {
    opensmt_warning( "Skipping command (get-interpolant) as (produce-interpolants) is not set" );
    return NULL;
  }
  else if ( state == l_False )
  {
    if ( config.verbosity >= 2 )
    {
      cerr << endl << "Calling GetInterpolant with " << n << endl;
    }
    assert( n < interpolants.size( ) );
    if ( config.verbosity >= 2 )
    {
      cerr << "Returning: " << interpolants[ n ] << endl;
    }
    Enode * e = interpolants[ n ];
    // Tries to maximize, remove redundancies etc
    e = egraph.maximize( e );
    // Tries to absorb or
    e = egraph.absorbOr( e );
    // Put into DNF (MCMT only)
    if ( config.tool == MCMT )
      e = egraph.convertIntoDNF( e );

    if ( print_out )
    {
      ostream & out = config.getRegularOut( );
      out << "; Interpolant " << n << endl;
      egraph.dumpFormulaToFile( out, e );
    }

    return e;
  }
  else
  {
    opensmt_warning( "Skipping command (get-interpolant) as formula is not unsat" );
    return NULL;
  }
#else
  (void)print_out;
  opensmt_warning( "You need a version of opensmt compiled with --enable-proof, and produce_inter flag enabled" );
  return NULL;
#endif
}

lbool OpenSMTContext::CheckSAT( )
{
  if ( config.dump_log )
    config.getLogOut( ) << "(check-sat)" << endl;

  if ( config.tool == OPENSMT
    && config.verbosity > 1 )
    cerr << "# OpenSMTContext::Checking satisfiability" << endl;

#ifdef PRODUCE_PROOF
  // Compute interpolants instead
  if ( config.produce_inter != 0 )
  {
    if ( config.term_abstraction )
      return CheckSATInterpTA( );
    else
      return CheckSATInterp( );
  }
#endif 

  // Retrieve the conjunction of the
  // yet unchecked assertions
  Enode * alist = const_cast< Enode * >( egraph.enil );
  for ( ; processed_assertions < active_assertions.size( ) ; processed_assertions ++ )
    alist = egraph.cons( active_assertions[ processed_assertions ],  alist );

  Enode * formula = egraph.mkAnd( alist );
  assert( formula );

  // Static preprocessing if not incremental
  if ( config.incremental == 0 )
  {
    formula = staticPreprocessing( formula );
#ifdef SMTCOMP
    egraph.initializeTheorySolvers( &solver );
#endif
  }
  // Incremental preprocessing
  else
    formula = incrementalPreprocessing( formula );
  
  // Cnfize formula
  state = cnfizer.cnfizeAndGiveToSolver( formula );

  // Solving happens here
  if ( state == l_Undef )
    state = solver.solve( );

  if ( !silent )
  {
    ostream & out = config.getRegularOut( );
    if ( state == l_Undef )
      out << "unknown" << endl;
    else if ( state == l_False )
      out << "unsat" << endl;
    else
      out << "sat" << endl;
  }

  return state;
}

#ifdef PRODUCE_PROOF
lbool OpenSMTContext::CheckSATInterp( )
{
  assert( config.produce_inter != 0 );
  assert( config.incremental != 0 );

  if ( config.logic == UNDEF )
    opensmt_error( "unable to determine logic" );

  /*
  if ( config.logic == QF_UFIDL 
    || config.logic == QF_UFLRA )
  {
    if ( config.sat_lazy_dtc == 0 )
      opensmt_warning( "Overriding option sat_lazy_dtc" );
    config.sat_lazy_dtc = 1;
    config.incremental = 1;
    config.sat_polarity_mode = 4;
  }

  // Purifier for DTC
  if ( config.logic == QF_UFIDL
    || config.logic == QF_UFLRA )
  {
    Purify purifier( egraph, config );
    purifier.doit( assertions );
  }

  // Ite expander
  ExpandITEs expander( egraph, config );
  
  // Top-Level Propagator. It also canonize atoms
  TopLevelProp propagator( egraph, config );

  // Initialize AXDIFF preprocessor
  AXDiffPreproc axdiffpreproc( egraph, sstore, config );
  */

  // Load shared knowledge first
  Enode * alist = const_cast< Enode * >( egraph.enil );
  for ( ; processed_assertions < active_assertions.size( ) ; processed_assertions ++ )
    alist = egraph.cons( active_assertions[ processed_assertions ], alist );

  Enode * formula = egraph.mkAnd( alist );

  // Set Shared partition -- at the moment we put 
  // shared information in the first partition. Can be changed
  ipartitions_t partition = 0;
  setbit( partition, 1 );
  // Remove ites 
  // formula = expander.doit( formula );
  // Canonize atoms
  // formula = propagator.doit( formula );
  // Preprocessing for AX 
  /*
  if ( config.logic == QF_AX
    || config.logic == QF_AXDIFF )
  {
    formula = axdiffpreproc.doit( formula, partition );
  }
  */
  //
  // Extend the colors of uninterpreted symbols to
  // sorrounding terms and predicates
  //
  egraph.finalizeColors( formula, partition );

  // CNFize the input formula and feed clauses to the solver
  state = cnfizer.cnfizeAndGiveToSolver( formula, partition );

  //
  // Now color partitions separately
  //
  for ( size_t in = 0 ; in < active_partitions.size( ) ; in ++ )
  {
    // Get formula
    Enode * formula = active_partitions[ in ];

    // const ipartitions_t partition = SETBIT( in + 1 );
    ipartitions_t partition = 0;
    setbit( partition, in + 1 );
    assert( in != 0 || formula != NULL );
    /*
    // Remove ites 
    formula = expander.doit( formula );
    // Canonize atoms
    cerr << "CANONIZING: " << formula << endl;
    formula = propagator.doit( formula );
    cerr << " CANONIZED: " << formula << endl;
    // Preprocessing for AX 
    if ( config.logic == QF_AX
      || config.logic == QF_AXDIFF )
    {
      formula = axdiffpreproc.doit( formula, partition );
    }
    */
    //
    // Extend the colors of uninterpreted symbols to
    // sorrounding terms and predicates
    //
    egraph.finalizeColors( formula, partition );

    if ( config.dump_formula != 0 )
    {
      char buf[ 32 ];
      sprintf( buf, "presolve_%ld.smt2", in + 1 );
      egraph.dumpToFile( buf, formula );
    }
    // Restore
    active_partitions[ in ] = formula;
  }

  //cerr << "INFEASIBLE TRACE: " << endl;

  //
  // Now give to solver
  //
  for ( size_t in = 0 ; in < active_partitions.size( ) ; in ++ )
  {
    // const ipartitions_t partition = SETBIT( in + 1 );
    ipartitions_t partition = 0;
    setbit( partition, in + 1 );
    // Get partition
    Enode * formula = active_partitions[ in ];
    //cerr << in << " : " << formula << endl;
    // CNFize the input formula and feed clauses to the solver
    state = cnfizer.cnfizeAndGiveToSolver( formula, partition );
  }
  //
  // Solve
  //
  if ( state == l_Undef )
  {
    state = solver.smtSolve( false );
  }
  
  // Retrieve interpolants if false
  if ( state == l_False )
  {
    solver.getInter( interpolants );
    // /*
    if ( config.term_abstraction == 0 )
    {
      cerr << endl;
      for ( size_t i = 0 ; i < interpolants.size( ) ; i ++ )
	cerr << "I" << i << ": " << interpolants[ i ] << endl;
    }
    // */
  }

  // If computation has been stopped, return undef
  if ( opensmt::stop ) state = l_Undef;

  if ( !silent )
  {
    ostream & out = config.getRegularOut( );
    if ( state == l_Undef )
      out << "unknown" << endl;
    else if ( state == l_False )
      out << "unsat" << endl;
    else
      out << "sat" << endl;
  }

  return state;
}

// PLEASE REMOVE AFTER FOUND CORRECT
#define TA_VERB 0

lbool OpenSMTContext::CheckSATInterpTA( )
{
  // Disabling dump log for simplicity
  const int saved_cfg = config.dump_log;
  config.dump_log = 0;

  // cerr << endl << "==== BEGIN TERM ABSTRACTION ===" << endl;

  assert( config.term_abstraction );
  assert( config.produce_inter != 0 );
  assert( config.incremental != 0 );

  if ( config.logic == UNDEF )
    opensmt_error( "unable to determine logic" );

  assert( active_assertions.empty( ) );

  //
  // Given an unsat trace
  //
  // p1
  // p2
  // ...
  // pn
  //
  // consider different cuts, e.g.
  //
  // p1
  // --
  // p2
  // ...
  // pn
  //
  // for each cut abstract as much as possible the 
  // terms inside the first partition, and then move
  // to the next cut
  //

  const size_t max_cuts = active_partitions.size( );

  vector< Enode * > ta_interpolants;
  ta_interpolants.push_back( egraph.mkTrue( ) );
  // Save cuts
  vector< Enode * > saved_partitions;
  saved_partitions.swap( active_partitions );
  // 
  // Iteratively consider cuts
  //
  Enode * a_part = NULL;
  for ( size_t cut = 1 ; cut < max_cuts ; cut ++ )
  {
    assert( active_partitions.empty( ) );

#if TA_VERB
    cerr << endl << "================ PROCESSING CUT: " << cut << endl;
#else
    // cerr << endl << "Simulating " << cut << "th Pre" << endl;
#endif

    // Save colors (nothing is colored)
    egraph.saveColors( );

    list< Enode * > a_part_list, b_part_list;
    // Get A
    if ( a_part )
      a_part_list.push_back( a_part );

    // Adds to a_part only the cut's partition (others are accumulated before)
    a_part_list.push_back( saved_partitions[ cut-1 ] );

    a_part = egraph.mkAnd( egraph.cons( a_part_list ) );
    egraph.colorUF( a_part, 2 );
    egraph.finalizeColors( a_part, 2 );

    // Get B
    for ( size_t in = cut ; in < saved_partitions.size( ) ; in ++ )
      b_part_list.push_back( saved_partitions[ in ] );
    Enode * b_part = egraph.mkAnd( egraph.cons( b_part_list ) );
    egraph.colorUF( b_part, 4 );
    egraph.finalizeColors( b_part, 4 );

#if TA_VERB
    cerr << "  PARTITION A: " << a_part << endl;
    cerr << "  PARTITION B: " << b_part << endl;
#endif

    // Retrieve candidates for term abstraction
    set< Enode * > candidates;

    retrieveCommonTerms( a_part, candidates , 2 );

#if TA_VERB
    cerr << "CANDIDATES ARE  : ";
    string sep = "";
    for ( set< Enode * >::iterator it = candidates.begin( )
	; it != candidates.end( ) 
	; it ++ )
    {
      cerr << sep << *it;
      sep = ", ";
    }
    cerr << endl;
#endif

    // Temporarily disabling
    config.produce_inter = 0;

    // Try to abstract as much as possible here
    for ( set< Enode * >::iterator it = candidates.begin( )
	; it != candidates.end( )
	; it ++ )
    {
      if ( *it == egraph.mkNum( "-1" ) )
	  continue;

      // Saving partition to backtrack later
      Enode * a_part_saved = a_part;

#if TA_VERB
      cerr << "Considering candidate: " << *it << endl;
#endif
      // Creating new symbol to abstract term
      char def_name[ 32 ];
      Enode * arg_def = NULL;
      sprintf( def_name, "TA_%d", egraph.freshSymbolCount( ) );
      egraph.newSymbol( def_name, NULL, (*it)->getRetSort( ) );
      arg_def = egraph.mkVar( def_name );
#if TA_VERB
      cerr << "  Creating new symbol: " << arg_def << endl;
#endif
      // Substituting symbol
      map< Enode *, Enode * > subst;
      subst[ *it ] = arg_def;
      Enode * abs_part = egraph.safeSubstitute( a_part, subst );
#if TA_VERB
      cerr << "  Substitution       : " << abs_part << endl;
#endif

      // a_part = egraph.prepareAssertion( abs_part );
      a_part = abs_part;

      // Save current state
      Push( );

      active_partitions.push_back( egraph.prepareAssertion( a_part ) );
      active_partitions.push_back( egraph.prepareAssertion( b_part ) );

      lbool result = checkSATReduced( );

      active_partitions.clear( );

#if TA_VERB
      if ( result == l_False )
	cerr << "Still false, good !" << endl;
      else 
	cerr << "Too abstract, backtrack !" << endl;
#else
      // if ( result == l_False )
	// cerr << "  Abstracted " << *it << " with " << arg_def << endl;
#endif

      // Restore previous state
      Pop( );

      // Restore what was there before if too coarse
      if ( result == l_True )
	a_part = a_part_saved;
    }

    // Enabling back produce inter
    config.produce_inter = 1;

    // Construct interpolation problem
    assert( active_partitions.empty( ) );
    active_partitions.push_back( egraph.preparePartition( a_part, 2 ) );
    active_partitions.push_back( egraph.preparePartition( b_part, 4 ) );
    assert( active_partitions.size( ) == 2 );

#if TA_VERB
    cerr << "ABSTRACTION DONE FOR CUT " << cut << " NOW COMPUTING INTERPOLANT" << endl;
    cerr << "A: " << active_partitions[ 0 ] << endl;
    cerr << "B: " << active_partitions[ 1 ] << endl;
#endif

    egraph.setNofPartitions( 2 );

    // Save state
    Push( );

    // NOW COMPUTE INTERPOLANTS ON THE MODIFIED PARTITIONS !
    assert( active_assertions.empty( ) );
    state = CheckSATInterp( );
    assert( state == l_False );

    ta_interpolants.push_back( GetInterpolant( 1 ) );

    // Restore state
    Pop( );

    // Decolor everything
    egraph.restoreColors( );

    // Empty partitions again
    active_partitions.clear( );
  }

  ta_interpolants.push_back( egraph.mkFalse( ) );
  interpolants.swap( ta_interpolants );

  // cerr << "Term-abstracted interpolants: " << endl;
  cerr << endl;
  for ( size_t i = 0 ; i < interpolants.size( ) ; i ++ )
    cerr << "I" << i << ": " << interpolants[ i ] << endl;

  // cerr << "==== END TERM ABSTRACTION ===" << endl;
  
  // Restoring dump log 
  config.dump_log = saved_cfg;

  return state;
}

lbool OpenSMTContext::checkSATReduced( )
{
  assert( config.term_abstraction );
  assert( config.incremental != 0 );

  assert( active_assertions.empty( ) );
  
  // Retrieve the conjunction of the
  // yet unchecked assertions
  Enode * alist = const_cast< Enode * >( egraph.enil );
  for ( size_t p = 0 ; p < active_partitions.size( ) ; p ++ )
    alist = egraph.cons( active_partitions[ p ],  alist );

  Enode * formula = egraph.mkAnd( alist );
  assert( formula );

  // Static preprocessing if not incremental
  if ( config.incremental == 0 )
    formula = staticPreprocessing( formula );
  /*
  else
    formula = incrementalPreprocessing( formula );
  */
  
  // Cnfize formula
  state = cnfizer.cnfizeAndGiveToSolver( formula );

  // Solving happens here
  if ( state == l_Undef )
    state = solver.solve( );

  if ( !silent )
  {
    ostream & out = config.getRegularOut( );
    if ( state == l_Undef )
      out << "unknown" << endl;
    else if ( state == l_False )
      out << "unsat" << endl;
    else
      out << "sat" << endl;
  }

  return state;
}
#endif

/*
 * Temporairly disabled for maintenance
 *
lbool OpenSMTContext::CheckSAT( vec< Enode * > & assumptions )
{
  if ( config.dump_log )
    config.getLogOut( ) << "(check-sat)" << endl;
  
  if ( config.tool == OPENSMT
    && config.verbosity > 1 )
    cerr << "# OpenSMTContext::Checking satisfiability" << endl;

  // Retrieve the conjunction of the
  // yet unchecked assertions
  Enode * alist = const_cast< Enode * >( egraph.enil );
  for ( ; processed_assertions < active_assertions.size( ) ; processed_assertions ++ )
    alist = egraph.cons( active_assertions[ processed_assertions ],  alist );

  Enode * formula = egraph.mkAnd( alist );

  if ( config.tool == OPENSMT
    && config.verbosity > 1 )
    cerr << "# OpenSMTContext::Processing: " << formula << endl;

  state = cnfizer.cnfizeAndGiveToSolver( formula );

  if ( state == l_Undef )
    state = solver.solve( assumptions, false );

  if ( !silent )
  {
    ostream & out = config.getRegularOut( );
    if ( state == l_Undef )
      out << "unknown" << endl;
    else if ( state == l_False )
      out << "unsat" << endl;
    else
      out << "sat" << endl;
  }

  return state;
}

lbool OpenSMTContext::CheckSAT( vec< Enode * > & assumptions, unsigned limit )
{
  if ( config.dump_log )
    config.getLogOut( ) << "(check-sat)" << endl;

  if ( config.tool == OPENSMT
    && config.verbosity > 1 )
    cerr << "# OpenSMTContext::Checking satisfiability" << endl;
  
  // Retrieve the conjunction of the
  // yet unchecked assertions
  Enode * alist = const_cast< Enode * >( egraph.enil );
  for ( ; processed_assertions < active_assertions.size( ) ; processed_assertions ++ )
    alist = egraph.cons( active_assertions[ processed_assertions ],  alist );

  Enode * formula = egraph.mkAnd( alist );
  assert( formula );

  // Static Preprocessing if no incrementality
  if ( config.incremental == 0 )
    formula = staticPreprocessing( formula );

  state = cnfizer.cnfizeAndGiveToSolver( formula );

  if ( state == l_Undef )
    state = solver.solve( assumptions, limit, false );

  if ( !silent )
  {
    ostream & out = config.getRegularOut( );
    if ( state == l_Undef )
      out << "unknown" << endl;
    else if ( state == l_False )
      out << "unsat" << endl;
    else
      out << "sat" << endl;
  }

  return state;
}
*/

void OpenSMTContext::Exit( )
{ 
  if ( config.dump_log )
    config.getLogOut( ) << "(exit)" << endl;

  // PrintResult( state, config.status );
}

void OpenSMTContext::PrintResult( const lbool & result, const lbool & config_status )
{
  ostream & out = config.getRegularOut( );
#ifdef SMTCOMP
  (void)config_status;
#else
  fflush( stderr );
  (void)config_status;
  //
  // For testing purposes we return error if bug is found
  //
  if ( config_status != l_Undef
    && result != l_Undef
    && result != config_status )
    out << "error" << endl;
  else
#endif

  if ( silent )
  {
    if ( result == l_True )
      out << "sat" << endl;
    else if ( result == l_False )
      out << "unsat" << endl;
    else if ( result == l_Undef )
      out << "unknown" << endl;
    else
      opensmt_error( "unexpected result" );
  }

  fflush( stdout );

#ifndef SMTCOMP
  if ( config.verbosity )
  {
    //
    // Statistics
    //
    double   cpu_time = cpuTime();
    reportf( "#\n" );
    reportf( "# CPU Time used: %g s\n", cpu_time == 0 ? 0 : cpu_time );
    uint64_t mem_used = memUsed();
    reportf( "# Memory used: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
    reportf( "#\n" );
  }
#endif
}

Enode * OpenSMTContext::ParseString( const char * str )
{
#if defined(__linux__)
  parser_ctx = this;
  FILE * fin = fmemopen( const_cast< char * >( str ), strlen( str ), "r" );
  smt2set_in( fin );
  smt2parse( );
  Enode * ret = egraph.getLastSeen( );
  return ret;
#elif defined(__FreeBSD__) || defined(__OSX__) || defined(__APPLE__)
  opensmt_error( "Not implemented for MAC" );
#else
  opensmt_error( "Not implemented for Windows" );
#endif
}

Enode * OpenSMTContext::staticPreprocessing( Enode * formula )
{
  assert( config.incremental == 0 );

  if ( config.dump_formula != 0 )
  {
    char buf[ 32 ];
    sprintf( buf, "original_%d.smt2", nof_check_sat );
    egraph.dumpToFile( buf, formula );
  }

  // Expand ites
  if ( egraph.hasItes( ) )
  {
    formula = expander.doit( formula );

    if ( config.dump_formula != 0 )
    {
      char buf[ 32 ];
      sprintf( buf, "expanded_%d.smt2", nof_check_sat );
      egraph.dumpToFile( buf, formula );
    }
  }

  // Gather interface terms for DTC
  if ( ( config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
    // Don't use with DTC of course
    && config.sat_lazy_dtc == 1
    // Don't use when dumping interpolants
    && config.sat_dump_rnd_inter == 0 )
  {
    purifier.doit( formula );
  }

  // Ackermanize away functional symbols
  if ( ( config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
    // Don't use with DTC of course
    && config.sat_lazy_dtc == 0
    // Don't use when dumping interpolants
    && config.sat_dump_rnd_inter == 0 )
  {
    Ackermanize ackermanizer( egraph, config );
    formula = ackermanizer.doit( formula );

    if ( config.dump_formula != 0 )
      egraph.dumpToFile( "ackermanized.smt2", formula );
  }

  /*
  // Artificially create a boolean
  // abstraction, if necessary
  if ( config.logic == QF_BV )
  {
    BVBooleanize booleanizer( egraph, config );
    formula = booleanizer.doit( formula );
  }
  */

  if ( config.dump_formula != 0 )
    egraph.dumpToFile( "prepropagated.smt2", formula );

  // Top-Level Propagator. It also canonize atoms
  TopLevelProp propagator( egraph, config );
  // Only if sat_dump_rnd_inter is not set
  if ( config.sat_dump_rnd_inter == 0 )
    formula = propagator.doit( formula );

  if ( config.dump_formula != 0 )
    egraph.dumpToFile( "propagated.smt2", formula );

  AXDiffPreproc2 axdiffpreproc( egraph, sstore, config );
  if ( config.logic == QF_AX
    || config.logic == QF_AXDIFF )
  {
    formula = axdiffpreproc.doit( formula );
    if ( config.dump_formula != 0 )
      egraph.dumpToFile( "axdiffpreproc.smt2", formula );
  }

  // Convert RDL into IDL, also compute if GMP is needed
  // for IDL, UFIDL
  if ( config.logic == QF_RDL 
    || config.logic == QF_IDL
    || config.logic == QF_UFIDL )
  {
    DLRescale rescaler( egraph, config );
    rescaler.doit( formula );
  }

  // If DTC is used, make sure that incrementality 
  // is enabled from this point on
  if ( ( config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
      && config.sat_lazy_dtc != 0 )
  {
    config.incremental = 1;
    config.sat_polarity_mode = 4;
  }

  // Compute polarities
  egraph.computePolarities( formula );

  return formula;
}

Enode * OpenSMTContext::incrementalPreprocessing( Enode * formula )
{
  assert( config.incremental );

  // Convert RDL into IDL, also compute if GMP is needed
  if ( config.logic == QF_RDL 
    || config.logic == QF_AX 
    || config.logic == QF_AXDIFF )
  {
    opensmt_error( "incrementality not supported for this theory (yet)" );
  }

  // Expand ites
  if ( egraph.hasItes( ) )
    formula = expander.doit( formula );

  // Gather interface terms for DTC
  if ( ( config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
    // Don't use with DTC of course
    && config.sat_lazy_dtc == 1 )
  {
    purifier.doit( formula );
  }

  // Ackermanize away functional symbols
  if ( ( config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
    // Don't use with DTC of course
    && config.sat_lazy_dtc == 0 )
  {
    iackermanizer.doit( formula );
  }

  /*
  // Artificially create a boolean
  // abstraction, if necessary
  if ( config.logic == QF_BV )
  {
    BVBooleanize booleanizer( egraph, config );
    formula = booleanizer.doit( formula );
  }
  */

  if ( config.logic != QF_RD )
    formula = ipropagator.doit( formula );

  if ( config.dump_formula != 0 )
  {
    static int prop_count = 0;
    char buf[ 32 ];
    sprintf( buf, "propagated_%d.smt2", prop_count ++ );
    egraph.dumpToFile( buf, formula );
  }

  // Compute polarities
  egraph.computePolarities( formula );

  return formula;
}

void OpenSMTContext::printSplashScreen( )
{
  const int len_pack = strlen( PACKAGE_STRING );
  const char * site = "http://verify.inf.usi.ch/opensmt";
  const int len_site = strlen( site );

  cerr << "#" << endl
    << "# -------------------------------------------------------------------------" << endl
    << "# " << PACKAGE_STRING;

  for ( int i = 0 ; i < 73 - len_site - len_pack ; i ++ )
    cerr << " ";

  cerr << site << endl
    << "# Compiled with gcc " << __VERSION__ << " on " << __DATE__ << endl
    << "# -------------------------------------------------------------------------" << endl
    << "#" << endl;
}

#ifdef PRODUCE_PROOF
// For now, only retrieves constants
void OpenSMTContext::retrieveCommonTerms( Enode * part
                                        , set< Enode * > & terms 
					, const ipartitions_t & mask
					)
{
  assert( part );
  assert( config.term_abstraction );
  assert( config.produce_inter != 0 );

  vector< Enode * > unprocessed_enodes;
  egraph.initDup1( );

  unprocessed_enodes.push_back( part );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup1( enode ) )
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
      if ( !egraph.isDup1( arg ) )
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

    //
    // Change this to select abstraction candidates
    //
    if ( isAB( enode->getIPartitions( ), mask )      // Only Common terms are abstracted
      // && enode->getCar( )->getName( ) == "a_length"
      // && enode->isConstant( )                    
      // && enode == egraph.mkNum( "0" )             
       )           
       terms.insert( enode );

    egraph.storeDup1( enode );
  }

  egraph.doneDup1( );
}
#endif
