/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef MCMT_CONTEXT_H
#define MCMT_CONTEXT_H

#define BACKWARD_INTERPOLANTION

#include "Egraph.h"
#include "MC.h"
#include "Yices.h"
#include "OpenSMT.h"

class MCMTContext
{
public:

  MCMTContext( int    argc
	     , char * argv[ ] )
    : config_p     ( new Config( MCMT, argc, argv ) )
    , config       ( *config_p )
    , sstore_p     ( new SStore( config ) )
    , sstore       ( *sstore_p )
    , egraph_p     ( new Egraph( config, sstore ) )
    , egraph       ( *egraph_p )
#if USE_OPENSMT
    , solver_p     ( new OpenSMT( "opensmt", config, egraph, sstore ) )
    , solver       ( *solver_p )
    , int_solver_p ( solver_p )
    , int_solver   ( *solver_p )
#elif USE_YICES
    , solver_p     ( new Yices( "yices", config, egraph ) )
    , solver       ( *solver_p )
    , int_solver_p ( new OpenSMT( "opensmt", config, egraph, sstore ) )
    , int_solver   ( *int_solver_p )
#endif
    , mc_p         ( new MC( config, egraph, sstore, solver , int_solver , false /*, mc_p_i */ ) )
    , mc           ( *mc_p )
  { 
    // Assume incrementality
    assert( config.incremental == 1 );
    // Make sure booleans are not preprocessed
    config.sat_preprocess_booleans = 0;
    // Disable printing of success
    // config.print_success = 0;
    // Set array plus integer logic
    int_solver.SetOption( ":print-success", "false" );
    // Set array plus integer logic
    int_solver.SetLogic( QF_AXLIA );
    // Set interpolation
    int_solver.SetOption( ":produce-interpolants", "true" );
    // Do not split equalities
    // int_solver.SetOption( ":split-equalities", "false" );
    // Set interpolant strenght
    int_solver.SetOption( ":proof-set-inter-algo", "2" );
    // Disable gaussian elimination
    int_solver.SetOption( ":lra-gaussian-elim", "0" );
    // Initializes predefined Index Variables
    mc.initializeIndexVariables( );
  }

  ~MCMTContext( )
  {
    assert( config_p );
    assert( sstore_p ); 
    assert( egraph_p );
    assert( solver_p );
    assert( int_solver_p );
    assert( mc_p );
    delete mc_p;
    delete solver_p;
    if ( solver_p != int_solver_p )
    {
      delete int_solver_p;
    }
    delete egraph_p;
    delete sstore_p;
    delete config_p;
  }

  //
  // Execute recorded commands
  //
  int           executeCommands      ( );

  //======================================================================
  //
  // Communication API
  //
  void            SetLogic	       ( logic_t ) { }            // Set logic of index datatype
  void            SetLogic	       ( const char * ) { }       // Set logic
  void            SetOption            ( const char * ) { }       // Set option
  void            SetInfo              ( const char * ) { }       // Set info
  void            DeclareSort          ( const char *, int );     // Declares a new sort
  void            DeclareFun           ( const char *
                                       , Snode *
				       , Snode * );               // Declares a new function symbol

  inline void     Push                 ( ) { mc.pushBacktrackPoint( ); }
  inline void     Pop                  ( ) { mc.popBacktrackPoint( ); }
  inline void     Reset                ( ) { mc.reset( ); }
		  
  inline status_t CheckSafety          ( ) { return mc.checkSafety( ); }
  inline void     GenerateInvariants   ( ) { mc.generateInvariants( ); }
  lbool           CheckSAT             ( );
  void            Exit                 ( ) { mc.exit( ); } 

  void            Assert               ( Enode * );
  void            GetProof             ( );
  void            GetInterpolants      ( );

  void            PrintResult          ( );
  //
  // MCMT actions done immediately
  //
  void  DeclareIntVar         ( char * );
  void  DeclareNatVar         ( char * );
  void  DeclareRealVar        ( char * );
  void  DeclareLocal          ( char *, char * );
  void  DeclareGlobal         ( char *, char * );
  void  DefineType            ( char *, int, int );               // Command for (define-type)
  void  DeclareIndexVar       ( char * );
  // 
  // MCMT actions saved for later use
  //
  void  addInitial            ( Enode *, Enode *
			      , Enode *, Enode *
			      , Enode * );
  void  addSystemAxiom        ( Enode *, Enode *
			      , Enode *, Enode *
			      , Enode * );
  void  addUnsafe             ( Enode *, Enode *, Enode *, Enode *, Enode * );
  void  addSuggested          ( Enode *, Enode *, Enode *, Enode *, Enode * );
  void  addTransition         ( Enode *
			      , Enode *
			      , Enode *
			      , Enode *
			      , vector< Enode * > &
			      , vector< Transition::Case * > &
                              , bool );                           // Command for (transition ...)     
  void  addCheckSafety        ( );                                // Command for (check-safety)
  void  addGenerateInvariants ( );                                // Command for (check-safety)
  void  addPush               ( int );                            // Command for (push ...)
  void  addPop                ( int );                            // Command for (pop ...)
  void  addExit               ( );                                // Command for (exit)
  void  setAbstract           ( char * );                         // Set abstract variable
  void  setAbstractTransition ( unsigned );                       // Set abstract transition
  //
  // Kept for the moment but useless
  //
  void  addAssert             ( Enode * );                        // Stub
  void  addCheckSAT           ( );                                // Stub
  void  addGetProof           ( );                                // Stub
  
  //======================================================================
  //
  // Term Creation API
  //
  //
  // Core functions
  //
  inline Enode * mkTrue     ( )                  { return egraph.mkTrue( ); }       
  inline Enode * mkFalse    ( )                  { return egraph.mkFalse( ); }       
  inline Enode * mkAnd      ( Enode * e )        { assert( e ); return egraph.mkAnd     ( e ); }
  inline Enode * mkOr       ( Enode * e )        { assert( e ); return egraph.mkOr      ( e ); }
  inline Enode * mkNot      ( Enode * e )        { assert( e ); return egraph.mkNot     ( e ); }
  inline Enode * mkImplies  ( Enode * e )        { assert( e ); return egraph.mkImplies ( e ); }
  inline Enode * mkXor      ( Enode * e )        { assert( e ); return egraph.mkXor     ( e ); }
  inline Enode * mkEq       ( Enode * e )        { assert( e ); return egraph.mkEq      ( e ); }
  inline Enode * mkIte      ( Enode * e )        { assert( e ); return egraph.mkIte     ( e ); }
  inline Enode * mkDistinct ( Enode * e )        { assert( e ); return egraph.mkDistinct( e ); }
  //
  // Arithmetic functions
  //
  inline Enode * mkPlus   ( Enode * e )            { assert( e ); return egraph.mkPlus  ( e ); }
  inline Enode * mkMinus  ( Enode * e )            { assert( e ); return egraph.mkMinus ( e ); }
  inline Enode * mkTimes  ( Enode * e )            { assert( e ); return egraph.mkTimes ( e ); }
  inline Enode * mkUminus ( Enode * e )            { assert( e ); return egraph.mkUminus( e ); }
  inline Enode * mkDiv    ( Enode * e )            { assert( e ); return egraph.mkDiv   ( e ); }
  inline Enode * mkLeq    ( Enode * e )            { assert( e ); return egraph.mkLeq   ( e ); }
  inline Enode * mkLt     ( Enode * e )            { assert( e ); return egraph.mkLt    ( e ); }
  inline Enode * mkGeq    ( Enode * e )            { assert( e ); return egraph.mkGeq   ( e ); }
  inline Enode * mkGt     ( Enode * e )            { assert( e ); return egraph.mkGt    ( e ); }
  inline Enode * mkSelect ( Enode * e, Enode * i ) 
  { 
    assert( e ); 
    assert( i );
    return egraph.mkSelect( e, i ); 
  }
                                             
  inline Enode * mkCons   ( Enode * car
                          , Enode * cdr = NULL )        
  { 
    assert( car ); 
    return cdr == NULL ? egraph.cons( car ) : egraph.cons( car, cdr ); 
  }

  inline Enode * mkCons   ( list< Enode * > & l )            { return egraph.cons( l ); }
  inline Snode * mkCons   ( list< Snode * > & l )            { return sstore.cons( l ); }

  inline void    mkBind   ( const char * v, Enode * t )      { assert( v ); assert( t ); egraph.mkDefine( v, t ); }
                                                        
  inline Enode * mkVar    ( const char * n, bool m = false ) { assert( n ); return egraph.mkVar( n, m ); }
  inline Enode * mkFun    ( const char * n, Enode * a )      { assert( n ); return egraph.mkFun( n, a ); }
  inline Enode * mkNum    ( const char * n )                 { assert( n ); return egraph.mkNum( n ); }
  inline Enode * mkNum    ( const Real & r )                 { return egraph.mkNum( r ); }

  //======================================================================
  //
  // Sort Creation API
  //
  
  inline Snode * mkSortBool  ( ) { return sstore.mkBool  ( ); }
  inline Snode * mkSortInt   ( ) { return sstore.mkInt   ( ); }
  inline Snode * mkSortReal  ( ) { return sstore.mkReal  ( ); }
  inline Snode * mkSortArray ( ) { assert( false ); return sstore.mkVar( "Array" ); }
  inline Snode * mkSortElem  ( ) { return sstore.mkVar( "Elem" ); }
  inline Snode * mkSortIndex ( ) { return sstore.mkVar( "Index" ); }

  inline Snode * mkSort      ( Snode * a )      { return sstore.mkDot( a ); }
  inline Snode * mkSortVar   ( const char * n ) { return sstore.mkVar( n ); }

  inline Config & getConfig  ( ) { return config; }

  int    execute                 ( ); // Execute list of parsed commands
  
private:

  Config *              config_p;       // Pointer to config
  Config &              config;         // Reference to config
  SStore *              sstore_p;       // Pointer to SStore
  SStore &              sstore;         // Reference to SStore
  Egraph *              egraph_p;       // Pointer to egraph
  Egraph &              egraph;         // Reference to egraph
#if USE_OPENSMT                       
  AbstractSolverInt *   solver_p;       // Pointer to solver
  AbstractSolverInt &   solver;         // Reference to solver
#elif USE_YICES                       
  AbstractSolver *      solver_p;       // Pointer to solver
  AbstractSolver &      solver;         // Reference to solver
#endif
  AbstractSolverInt *   int_solver_p;   // Pointer to solver
  AbstractSolverInt &   int_solver;     // Reference to solver
  MC *                  mc_p;           // Pointer to model checker
  MC &                  mc;             // Reference to model checker
                                 
  typedef enum                   
  {                              
      CMD_UNDEF                  // undefined command
    , SET_LOGIC                  // (set-logic)
    , SET_OPTION                 // (set-option)  
    , SET_INFO                   // (set-info)
    , DECLARE_SORT               // (declare-sort)
    , DEFINE_SORT                // (define-sort)
    , DECLARE_FUN                // (declare-fun)
    , DEFINE_FUN                 // (define-fun)
    , PUSH                       // (push)
    , POP                        // (pop)
    , ASSERT                     // (assert)
    , CHECK_SAFETY               // (check-safety)
    , GENERATE_INVARIANTS        // (check-safety)
    , EXIT                       // (exit)
  } command_name_t;                   
  //
  // Data structure to store commands
  // (for script use only)
  //
  struct Command
  {
    Command( )                   
     : command( CMD_UNDEF )
     , enode     ( NULL )
     , sort_arg  ( NULL )
     , sort_ret  ( NULL )
    { }

    command_name_t command;
    Enode *        enode;
    Snode *        sort_arg;
    Snode *        sort_ret;
    char           str[256];
    int            num;
  };
  void    loadCustomSettings ( );     // Loads custom settings for SMTCOMP
                                      
  vector< Command >  command_list;    // Store commands to execute
  //set< string >      index_vars;      // For retrocomp. store index variables
};

#endif
