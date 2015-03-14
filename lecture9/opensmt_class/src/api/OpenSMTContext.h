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

#ifndef OPENSMT_CONTEXT_H
#define OPENSMT_CONTEXT_H

#include "Egraph.h"
#include "SimpSMTSolver.h"
#include "ExpandITEs.h"
#include "Purify.h"
#include "Tseitin.h"
#include "TopLevelPropInc.h"
#include "AckermanizeInc.h"

class OpenSMTContext
{
public:
  //
  // For executable
  //
  OpenSMTContext( int    argc
                , char * argv[ ] )
    : config_p            ( new Config( OPENSMT, argc, argv ) )
    , config              ( *config_p )
    , sstore_p            ( new SStore( config ) )
    , sstore              ( *sstore_p )
    , egraph_p            ( new Egraph( config, sstore ) )
    , egraph              ( *egraph_p )
    , solver_p            ( new SimpSMTSolver( egraph, config ) )
    , solver              ( *solver_p )
    , expander_p          ( new ExpandITEs( egraph, config ) )
    , expander            ( *expander_p )
    , purifier_p          ( new Purify( egraph, config ) )
    , purifier            ( *purifier_p )
    , iackermanizer_p     ( new AckermanizeInc( egraph, config ) )
    , iackermanizer       ( *iackermanizer_p )
    , ipropagator_p       ( new TopLevelPropInc( egraph, config ) )
    , ipropagator         ( *ipropagator_p )
    , cnfizer_p           ( new Tseitin( egraph, solver, config, sstore ) )
    , cnfizer             ( *cnfizer_p )
    , state               ( l_Undef )
    , init                ( false )
    , processed_assertions( 0 )
#ifdef PRODUCE_PROOF
    , nof_partitions ( 0 )
#endif
    , silent         ( false )
    , nof_check_sat  ( 0 )
  {
#ifndef SMTCOMP
  if ( getConfig( ).verbosity > 1 )
    printSplashScreen( );
#endif

    free_all = true; 
  }
  //
  // For API library
  //
  OpenSMTContext( )
    : config_p             ( new Config( ) )
    , config               ( *config_p )
    , sstore_p             ( new SStore( config ) )
    , sstore               ( *sstore_p )
    , egraph_p             ( new Egraph( config, sstore ) )
    , egraph               ( *egraph_p )
    , solver_p             ( new SimpSMTSolver( egraph, config ) )
    , solver               ( *solver_p )
    , expander_p           ( new ExpandITEs( egraph, config ) )
    , expander             ( *expander_p )
    , purifier_p           ( new Purify( egraph, config ) )
    , purifier             ( *purifier_p )
    , iackermanizer_p      ( new AckermanizeInc( egraph, config ) )
    , iackermanizer        ( *iackermanizer_p )
    , ipropagator_p        ( new TopLevelPropInc( egraph, config ) )
    , ipropagator          ( *ipropagator_p )
    , cnfizer_p            ( new Tseitin( egraph, solver, config, sstore ) )
    , cnfizer              ( *cnfizer_p )
    , state                ( l_Undef )
    , init                 ( false )
    , processed_assertions ( 0 )
#ifdef PRODUCE_PROOF
    , nof_partitions ( 0 )
#endif
    , silent         ( true )
    , nof_check_sat  ( 0 )
  { 
    free_all = true;
  }
  //
  // For use as MCMT solver: it does not create new
  // egraph or sort store, but it reuses those already
  // created for MCMT, so that sharing is maximized
  //
  OpenSMTContext( Config & c_ 
                , SStore & s_
		, Egraph & e_
		)
    : config               ( c_ )
    , sstore               ( s_ )
    , egraph               ( e_ )
    , solver_p             ( new SimpSMTSolver( egraph, config ) )
    , solver               ( *solver_p )
    , expander_p           ( new ExpandITEs( egraph, config ) )
    , expander             ( *expander_p )
    , purifier_p           ( new Purify( egraph, config ) )
    , purifier             ( *purifier_p )
    , iackermanizer_p      ( new AckermanizeInc( egraph, config ) )
    , iackermanizer        ( *iackermanizer_p )
    , ipropagator_p        ( new TopLevelPropInc( egraph, config ) )
    , ipropagator          ( *ipropagator_p )
    , cnfizer_p            ( new Tseitin( egraph, solver, config, sstore ) )
    , cnfizer              ( *cnfizer_p )
    , state                ( l_Undef )
    , init                 ( false )
    , processed_assertions ( 0 )
#ifdef PRODUCE_PROOF
    , nof_partitions ( 0 )
#endif
    , silent         ( true )
    , nof_check_sat  ( 0 )
  { 
    free_all = false;
  }

  ~OpenSMTContext( )
  {
    assert( !free_all || config_p );
    assert( !free_all || sstore_p ); 
    assert( !free_all || egraph_p );
    assert( solver_p );
    assert( cnfizer_p );
    delete cnfizer_p;
    delete solver_p;
    if ( free_all )
    {
      delete egraph_p;
      delete sstore_p;
      delete config_p;
      egraph_p = NULL;
      sstore_p = NULL;
      config_p = NULL;
    }
  }

  //======================================================================
  //
  // Communication API
  //
  void          SetLogic	     ( const logic_t );                  // Set logic
  void          SetLogic	     ( const char * );                   // Set logic
  void          SetOption            ( const char * );                   // Set option
  void          SetOption            ( const char *, const char * );     // Set option
  void          SetInfo              ( const char * );                   // Set info
  void          SetInfo              ( const char *, const char * );     // Set info
  void          DeclareSort          ( const char *, const int );        // Declares a new sort
  void          DeclareSubrange      ( Snode *                           // Declares a range
                                     , const int                         // for variables of this type
				     , const int );                      
  void          DeclareFun           ( const char *, Snode *, Snode * ); // Declares a new function symbol
  void          DefineFun            ( const char *, Enode *, Enode * ); // Shortcut for an expression

  void          Push                 ( );
  void          Pop                  ( );
  void          Push                 ( unsigned );
  void          Pop                  ( unsigned );
  void          Reset                ( );
#ifndef SMTCOMP
  inline void   PrintModel           ( ostream & os ) { solver.printModel( os ); egraph.printModel( os ); }
#endif

  void          Assert               ( Enode *, const bool = false );         // Pushes assertion 
  lbool         CheckSAT             ( );                                     // Command for (check-sat)
  // lbool         CheckSAT             ( vec< Enode * > & );                    // For PB/CT
  // lbool         CheckSAT             ( vec< Enode * > &, unsigned );          // For PB/CT
  void          Exit                 ( );                                     // Command for (exit)

  void          AssertPartition      ( Enode *, const unsigned );             // Pushes partition for interpolation
  void          AssertPartition      ( Enode * );                             // Pushes partition for interpolation
  lbool         CheckSATInterp       ( );                                     // Command for (check-sat) when interpolants
  lbool         CheckSATInterpTA     ( );                                     // Command for (check-sat) when interpolants
  void          GetProof             ( );
  void          GetModel             ( );
  void          GetInterpolants      ( );
  Enode *       GetInterpolant       ( const unsigned, const bool = false );

  //
  // Misc
  //
  Enode *       ParseString          ( const char * );
  void          PrintResult          ( const lbool &
                                     , const lbool & = l_Undef );

  //======================================================================
  //
  // Term Creation API
  //
  //
  // Core functions
  //
  inline Enode * mkTrue      ( )                 { return egraph.mkTrue( ); }       
  inline Enode * mkFalse     ( )                 { return egraph.mkFalse( ); }       
  inline Enode * mkAnd       ( Enode * e )       { assert( e ); return egraph.mkAnd     ( e ); }
  inline Enode * mkOr        ( Enode * e )       { assert( e ); return egraph.mkOr      ( e ); }
  inline Enode * mkNot       ( Enode * e )       { assert( e ); return egraph.mkNot     ( e ); }
  inline Enode * mkImplies   ( Enode * e )       { assert( e ); return egraph.mkImplies ( e ); }
  inline Enode * mkXor       ( Enode * e )       { assert( e ); return egraph.mkXor     ( e ); }
  inline Enode * mkEq        ( Enode * e )       { assert( e ); return egraph.mkEq      ( e ); }
  inline Enode * mkIte       ( Enode * e )       { assert( e ); return egraph.mkIte     ( e ); }
  inline Enode * mkDistinct  ( Enode * e )       { assert( e ); return egraph.mkDistinct( e ); }
  //
  // Arithmetic functions
  //
  inline Enode * mkPlus      ( Enode * e )       { assert( e ); return egraph.mkPlus  ( e ); }
  inline Enode * mkMinus     ( Enode * e )       { assert( e ); return egraph.mkMinus ( e ); }
  inline Enode * mkTimes     ( Enode * e )       { assert( e ); return egraph.mkTimes ( e ); }
  inline Enode * mkUminus    ( Enode * e )       { assert( e ); return egraph.mkUminus( e ); }
  inline Enode * mkDiv       ( Enode * e )       { assert( e ); return egraph.mkDiv   ( e ); }
  inline Enode * mkLeq       ( Enode * e )       { assert( e ); return egraph.mkLeq   ( e ); }
  inline Enode * mkLt        ( Enode * e )       { assert( e ); return egraph.mkLt    ( e ); }
  inline Enode * mkGeq       ( Enode * e )       { assert( e ); return egraph.mkGeq   ( e ); }
  inline Enode * mkGt        ( Enode * e )       { assert( e ); return egraph.mkGt    ( e ); }

  inline Enode * mkCostBound ( Enode * e )       { assert( e ); return egraph.mkCostBound( e ); }
  inline Enode * mkCostIncur ( Enode * e )       { assert( e ); return egraph.mkCostIncur( e ); }
                                             
  inline Enode * mkCons   ( Enode * car
                          , Enode * cdr = NULL )        
  { 
    assert( car ); 
    return cdr == NULL ? egraph.cons( car ) : egraph.cons( car, cdr ); 
  }

  inline Enode * mkCons   ( list< Enode * > & l )            { return egraph.cons( l ); }

  inline Snode * mkCons   ( Snode * car
                          , Snode * cdr = NULL )        
  { 
    assert( car ); 
    return cdr == NULL ? sstore.cons( car ) : sstore.cons( car, cdr ); 
  }

  inline Snode * mkCons   ( list< Snode * > & l )            { return sstore.cons( l ); }

  inline void    mkBind   ( const char * v, Enode * t )      { assert( v ); assert( t ); egraph.mkDefine( v, t ); }
                                                        
  inline Enode * mkVar    ( const char * n, bool m = false ) { assert( n ); return egraph.mkVar( n, m ); }
  inline Enode * mkStore  ( Enode * a, Enode * i, Enode * e ){ assert( a && i && e ); return egraph.mkStore( a, i, e ); }
  inline Enode * mkSelect ( Enode * a, Enode * i )           { assert( a && i ); return egraph.mkSelect( a, i ); }
  inline Enode * mkDiff   ( Enode * a, Enode * b )           { assert( a && b ); return egraph.mkDiff( a, b ); }
  inline Enode * mkFun    ( const char * n, Enode * a )      { assert( n ); return egraph.mkFun( n, a ); }
  inline Enode * mkNum    ( const char * n )                 { assert( n ); return egraph.mkNum( n ); }
  inline Enode * mkNum    ( const Real & r )                 { return egraph.mkNum( r ); }

  inline Enode * mkRDCons ( Enode * x, Enode * y )           { return egraph.mkRDCons( x, y ); }
  inline Enode * mkRDCar  ( Enode * x )                      { return egraph.mkRDCar( x ); }
  inline Enode * mkRDCdr  ( Enode * x )                      { return egraph.mkRDCdr( x ); }

  //======================================================================
  //
  // Sort Creation API
  //
  
  inline Snode * mkSortBool  ( )           { return sstore.mkBool  ( ); }
  inline Snode * mkSortInt   ( )           { return sstore.mkInt   ( ); }
  inline Snode * mkSortReal  ( )           { return sstore.mkReal  ( ); }
  inline Snode * mkSortCost  ( )           { return sstore.mkCost  ( ); }

  inline Snode * mkSort      ( Snode * a )      { return sstore.mkDot( a ); }
  inline Snode * mkSortVar   ( const char * n ) { return sstore.mkVar( n ); }

  //======================================================================
  //
  // Getty functions
  //
  inline Config &    getConfig    ( )           { return config; }
  inline unsigned    getLearnts   ( )           { return solver.nLearnts( ); }
  inline unsigned    getDecisions ( )           { return solver.decisions; }
  inline lbool       getStatus    ( )           { return state; }
#ifndef SMTCOMP
  inline lbool       getModel     ( Enode * a ) { return solver.getModel( a ); } 
#endif

  //======================================================================
  //
  // Setty functions
  //
  inline void        setPolarityMode ( unsigned m ) { assert( m <= 6 ); config.sat_polarity_mode = m; }

private:

  void               printSplashScreen        ( );               // OpenSMT splash screen
  void               loadCustomSettings       ( );               // Loads custom settings for SMTCOMP
  Enode *            staticPreprocessing      ( Enode * );       // Preprocess formula statically (old)
  Enode *            incrementalPreprocessing ( Enode * );       // Preprocess formula incrementally (new)
#ifdef PRODUCE_PROOF
  void               retrieveCommonTerms   ( Enode *
                                           , set< Enode * > &
					   , const ipartitions_t & );
  lbool              checkSATReduced       ( );                  // Command for (check-sat) when interpolants
#endif

  Config *           config_p;                                   // Pointer to config
  Config &           config;                                     // Reference to config
  SStore *           sstore_p;                                   // Pointer to SStore
  SStore &           sstore;                                     // Reference to SStore
  Egraph *           egraph_p;                                   // Pointer to egraph
  Egraph &           egraph;                                     // Reference to egraph
  SimpSMTSolver *    solver_p;                                   // Pointer to solver
  SimpSMTSolver &    solver;                                     // Reference to solver
  ExpandITEs *       expander_p;                                 // Pointer to expander
  ExpandITEs &       expander;                                   // Reference to expander
  Purify *           purifier_p;                                 // Pointer to purifier
  Purify &           purifier;                                   // Reference to purifier
  AckermanizeInc *   iackermanizer_p;                            // Pointer to ackermanizer
  AckermanizeInc &   iackermanizer;                              // Reference to ackermanizer
  TopLevelPropInc *  ipropagator_p;                              // Pointer to incremental propagator
  TopLevelPropInc &  ipropagator;                                // Reference to incremental propagator
  Tseitin *          cnfizer_p;                                  // Pointer to cnfizer
  Tseitin &          cnfizer;                                    // Reference to cnfizer
                                                                 
  lbool              state;                                      // Current state of the solver
  bool               init;                                       // Initialize
  bool               model_computed;
  bool               free_all;                                   // Should free config, egraph and sstore ?
  vector< Enode * >  active_assertions;                          // Stack of active assertions
  size_t             processed_assertions;                       // How many assertions have been processed
#ifdef PRODUCE_PROOF
  vector< Enode * >  active_partitions;                          // Stack of active partitions, for interpolation
#endif

  map< Snode *, Pair( int ) > sort_to_range;                     // Holds info about subrange for custom arith types

  vector< size_t >   undo_stack_assertions;                      // For backtracking
  vector< size_t >   undo_proc_assertions;                       // For backtracking

#ifdef PRODUCE_PROOF
  vector< Enode * >  interpolants;                               // Stores interpolants
  unsigned           nof_partitions;                             // Counts partitions based on
#endif

  const bool         silent;                                     // Dont print sat/unsat
  unsigned           nof_check_sat;                              // Keep track of check-sat number
};

#endif
