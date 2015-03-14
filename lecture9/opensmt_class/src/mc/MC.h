/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef MC_H
#define MC_H

#define USE_OPENSMT 0
#define USE_YICES   1

#if !(USE_OPENSMT + USE_YICES == 1)
#error "Exactly one solver must be selected"
#endif

#include "Global.h"
#include "Egraph.h"
#include "AbstractSolver.h"
#include "Transition.h"
#include "Node.h"
#include "Config.h"
#include "Container.h"
#include "InvariantContainer.h"
#include "Structures.h"

#define EXT_VAR "z%d"

class MC
{
public:
  
  MC( Config            & c_ 
    , Egraph            & e_ 
    , SStore            & ss_
    , AbstractSolver    & s_
    , AbstractSolverInt & i_s_
    , bool                i_ )
//    , MC              * mc_i_ )
    : nodes_univ_identifier     ( 0 )
    , container_p               ( new Container( e_, c_ ) )
    , container                 ( *container_p )
    , unsafe                    ( 0 )
    , initial                   ( NULL )
    , stoppingFailure           ( false )
    , config                    ( c_ )
    , egraph                    ( e_ )
    , sstore                    ( ss_ )
    , solver                    ( s_ )
    , i_solver                  ( i_s_ )
    , status                    ( UNKNOWN )
    , transition_preprocessing  ( false )
    , initialized               ( false )
    , invariants                ( i_ )
    , discovered_invariants     ( 0 )
//    , mc_i                      ( mc_i_ )
    , next_candidate            ( 0 )
    , unsafe_node               ( NULL )
    , number_of_executions      ( 0 )
    , last_node                 ( NULL )
    , cegar_loops               ( 0 )
    , var_id                    ( 0 )
  {
    if ( config.report_tex )
    {
       latex_file.open ("latex_report.tex");
    }
    if ( config.report )
    {
       log_file.open ("report.log");
       graphviz.open ("report.gv");
       graphviz << "digraph finite_state_machine {\n\trannkdir=N;\n\tnode [shape = circle];\n";
    }
    simplified = 0;  
  }

  ~MC( )
  { 
    while( !array_vars.empty( ) )
    {
      delete array_vars.back( );
      array_vars.pop_back( );
    }
    
    if ( config.report_tex )
    {
      latex_file.close();
    }
    if ( config.report )
    {
      log_file.close();
      graphviz << "}";
      graphviz.close();

    }

    if ( !invariants )
    {
      while( !transitions.empty( ) )
      {
        delete transitions.back( );
        transitions.pop_back( );
      }
    }

    while( !system_axioms.empty( ) )
    {
      delete system_axioms.back( );
      system_axioms.pop_back( );
    }


    assert( container_p );
    delete container_p;
  }

  struct SystemAxiom
  {
    Enode * s_ax;		 // the system axiom
    vector < Enode* > s_ax_vars; // variables of this system axiom
  };

  void                                  initializeDataStructures  ( );
  void                                  initializeIndexVariables  ( );
  unsigned                              getExCounter              ( );
  unsigned                              getNodes                  ( );
  unsigned                              getDeletedNodes           ( );
  unsigned                              getCoveredNodes           ( );
  unsigned                              getDepth                  ( );
  inline unsigned                       getInvariants             ( ) { return discovered_invariants; }
  inline vector < Enode * > &           getSuggestedInvariants    ( ) { return suggested_invariants; }
  inline vector < ArrayVar * > &        getArrayVarsList          ( ) { return array_vars; }
                                            
  void                                  defineType                ( char *, int, int );
  void                                  declareIntVar             ( char * );
  void                                  declareRealVar            ( char * );
                                        
  // void                                  declareLocal              ( char *, char * );
  // void                                  declareGlobal             ( char *, char * );
  void                                  declareLocal              ( char *, Snode * );
  void                                  declareGlobal             ( char *, Snode * );
                                                                  
  void                                  declareInitial            ( Enode *, Enode *
  		                                                  , Enode *, Enode * 
  		                                                  , Enode * );

  void                                  declareSystemAxiom        ( Enode *, Enode *
  		                                                  , Enode *, Enode * 
  		                                                  , Enode * );

  void                                  declareTransition         ( Enode *
                                                                  , Enode *
                                                                  , Enode *
                                                                  , Enode *
		                                                  , vector< Enode * > &
		                                                  , vector< Transition::Case * > &
                                                                  , bool );

  void                                  declareUnsafe             ( Enode * , Enode *
                                                                  , Enode * , Enode *
                                                                  , Enode * );
  void                                  defineUnsafeConfigs       (  ); // defines unsafe configurations in smt ctx
  void                                  declareSuggested          ( Enode * , Enode *
                                                                  , Enode * , Enode *
                                                                  , Enode * );
                                                                  
                                                                  
void                                  pushBacktrackPoint        ( );
  void                                  popBacktrackPoint         ( );
  status_t                              checkSafety               ( );
  void                                  exit                      ( );
                                                                  
  inline status_t                       getStatus                 ( ) { return status; }

  bool                                  checkFixpoint             ( Node * , vector < Node * > & );
  bool                                  checkFixpoint             ( Node * , set < Node * > & );
  bool                                  checkFixpoint             ( Node * , Node * = NULL );
  bool                                  checkAbstractFixpoint     ( Node * , Node * = NULL , bool = false );
                                                                  
  Enode *                               checkCondition            ( Enode *, Enode *
                                                                  , Enode *, Enode *
		                                                  , Enode *, Enode *
		                                                  , Enode *, Enode * );
  Enode *                               createPreimage            ( list< Enode * > & 
                                                                  , Enode * , Enode *
		                                                  , Enode * , Enode *
		                                                  , Enode * );
                                                                  
  Enode *                               simplify                  ( Enode * );
                                                                  
  bool                                  checkCompatible           ( Node *, Enode *, vector< Enode * > & );
                                                                  
  void                                  assertSystemAxioms        ( );
  void                                  declareIndexVar           ( char * );
  Enode *                               getNewIndexVariable       ( vector < Enode * > & );
  Enode *                               getNewIndexVariable       ( vector < Enode * > & , Enode * );
  void                                  declareIndexVarInSolver   ( char * );
  void                                  transitionsPreprocessing  ( );
                                        
  int                                   simplified;  // temporary variable used for pretty printing
  bool                                  stoppingFailureAdopted    ( ) { return stoppingFailure; }
  void                                  deleteNode                ( Node * );

  bool                                  checkSafetyUnsafe         ( );



  // used for invariant search to reset all 
  void                                  reset                     ( );
  void                                  checkInvariant            ( );



  /* ******************************************************************************************************
   *    INVARIANT GENERATION
   * ******************************************************************************************************/
  
  //
  void                                  generateInvariants        ( );
  unsigned                              getNumberOfExecutions     ( ) { return number_of_executions; };




  /* ******************************************************************************************************
   *    LAZY ABSTRACTION
   * ******************************************************************************************************/
  void                                  setAbstract                     ( char * );
  void                                  setAbstractTransition           ( unsigned );
  void                                  cleanUnsafe                     (  );
  unsigned                              getCegarLoops                   (  ) { return cegar_loops; }
  void                                  fixCoveredChildren              ( Node * );
  void                                  fixCoveredParentForLock         ( Node * );
  void                                  checkChildren                   ( Node * );
  void                                  checkCoveredParentForLock       ( Node * );
  void                                  checkCoveredAncestorsForLock    ( Node * );

#ifdef PEDANTIC_DEBUG
  void                                  checkInterpolant          ( Enode * );
#endif


private:                                
  unsigned                              nodes_univ_identifier;
  
  int                                   assertAllCombinations ( Enode * 
                                                              , vector< Enode *> & 
                                                              , vector <Enode *> &
                                                              , bool );
                                        
  void                                  assertAllCombinationsWithRepetitions ( Enode *
                                                                             , vector< Enode * > & 
                                                                             , vector < Enode * > &
                                                                             , vector < Enode * > & );

  int                                   assertAllCombinationsWithRepetitions ( Enode * 
                                                                             , vector< Enode *> &
                                                                             , vector <Enode *> &
                                                                             , bool );
  
  int                                   assertAllCombinationsWithRepetitions ( Enode * 
                                                                             , vector< Enode *> &
                                                                             , vector <Enode *> &
                                                                             , bool
                                                                             , AbstractSolver & );
                                        
  int                                   assertSuitableCombinations          ( Node * , Node * , bool );
  int                                   assertSuitableAbstractCombinations  ( Node * , Node * , bool );
                                        
  void                                  buildMaps ( vector < Enode * > & 
                                                   , map < Enode * , Enode * > &  
                                                   , map < Enode * , set < Enode * > > &
                                                   , set < Enode * > & 
                                                   );
                                        
  bool                                  canHelpInFixpoint ( Enode * , Enode * );
  
  void                                  autoTest( );




  /* Functions for preimage computation */
  
  void                                  computePreimages       ( vector < Node * > &
                                                               , Node * 
                                                               , Transition *
                                                               , bool = false );

  void                                  buildFormula           ( vector < Node * > &
                                                               , Enode *
                                                               , Enode *
                                                               , Node * 
                                                               , Transition *
                                                               , bool = false );
 
  void                                  buildFormulaBody       ( vector < Node * > &
                                                               , Enode *
                                                               , Enode *
                                                               , vector < Enode * > &
                                                               , vector < unsigned > &
                                                               , list < Enode * > & 
                                                               , size_t 
                                                               , Node * 
                                                               , Transition *
                                                               , bool = false );
                                                               
  bool                                  checkCase              ( Enode * 
                                                               , vector< Enode * > & 
                                                               , vector< Enode * > & 
                                                               , list < Enode * > & ); 
                                                               
  bool                                  checkUpdates           ( Enode *  
                                                               , Node * 
                                                               , vector < Enode * > & );
                                                               
  Enode *                               getUpdatedLabel        ( vector < Enode * > & 
                                                               , vector < unsigned > & 
                                                               , Enode * 
                                                               , Transition * );

  bool                                  checkIdenticalUpdates  ( vector< unsigned > &
                                                               , Transition * t );







  void                                  retrieveLits ( Enode *, vector< Enode * > & );
  void                                  retrieveVars ( Enode *, vector< Enode * > & );
                                        
  Enode *                               addLiteral ( Enode * , Enode *
                                                   , Enode * 
			                       	   , Enode * );
  Enode *                               updateLabel ( Enode *
                                                    , vector< Enode * > &
			                       	    , vector< Enode * > & );
  bool                                  checkInitialIntersection     ( Node * );
  bool                                  isSat                        ( Enode * n );
  bool                                  isSat                        ( Node * n );
  Enode *                               newExtVar         ( Node * , int increment );
                                        
  void                                  latexNode          ( Node * );
  void                                  latexFormula       ( Enode * , bool );
                                        
  bool                                  checkLogicalEquivalence       ( Enode * , Enode * );
  void                                  simplifyPreimages             ( vector < Node * > & );
                                        
  bool                                  checkSubsumption              ( Node * , list< Node *>& );
  bool                                  checkSubsumption              ( Node * , vector< Node *>& );
                                        
  bool                                  checkValidImplication         ( Node * , Node * );
  bool                                  checkValidImplication         ( Enode * , Enode * );
  bool                                  checkValidImplication         ( Node * , vector < Node * > & );
                                        
  Container *                           container_p;                  // Pointer to container
  Container &                           container;                    // Container for all the nodes computed
                                                                      
  unsigned                              unsafe;                       // number of unsafe formulae
  Enode *                               initial;                      // Initial state
  vector < Enode * >                    initial_vars;                 // Initial state
  vector< Transition * >                transitions;                  // Set of transitions
  vector< Enode* >                      variables;                    // Set of variables declared
  vector< Enode* >                      z_variables;                  // Set of variables of the kind 'zN'
  bool                                  stoppingFailure;              // stoppingFailureModel?
                                                                     
  Config &                              config;                       // Configure
  Egraph &                              egraph;                       // Egraph
  SStore &                              sstore;                       // Sort Store
  AbstractSolver &                      solver;                       // Reference to a solver
  AbstractSolverInt &                   i_solver;                     // Reference to a solver for interpolation
  status_t                              status;                       // Current status
  bool                                  transition_preprocessing;     // prevent to do it twice or more times
                                        
  set< Enode * >                        index_vars;                   // For retrocomp. store index variables
                                        
  void                                  instantiate                   ( Node * 
                                                                      , const vector < Enode * > & 
                                                                      , vector < unsigned > & 
                                                                      , bool );

  void inline                           createDefinition              ( Node * n ) { solver.Define( n, array_vars ); }

                                        
  void                                  retrieveSystemAxiom ( Node * );

  // TODO Questa e' una porcata ma funziona:
  // Otteniamo un "cubo" dove per ogni riga c'e' l'update in funzione
  // della variabile 'j' istanziata, e per ogni colonna ci sono gli update
  // per un dato caso.
  vector< vector< vector< Enode * > > > sources;
  vector< vector< vector< Enode * > > > updates;



  // matrix of preinstantiated vectors used in the preimage computation
  vector < vector < Enode * > >         array_index_matrix; // [ Z VAR ID ][ ARRAY ID ]


  vector < SystemAxiom * >              system_axioms; // Set of system axioms
  vector < ArrayVar * >                 array_vars;    // Set of array variables
                                                                                
/*
  void                                  computePreimages  ( Node * , Transition * );
  void                                  buildFormula ( size_t 
                                                     , Enode * 
                                                     , Enode * , Enode *
                                                     , Enode * , Enode *
                                                     , Transition *
                                                     , Node *
                                                     , bool
                                                     , Enode *
                                                     , size_t
                                                     , vector < Enode * > &
                                                     , vector < Enode * > &
                                                     , vector < Enode * > &
                                                     , list < Enode * > &
                                                     , vector < unsigned > &
                                                     );
 
  void                                  retrieveUpdatedEnodes( Node *
                                                             , Enode *
                                                             , Transition *
                                                             , vector< vector< Enode * > > &
                                                             , vector< vector < Enode * > > & );
                                        
  void                                  retrieveLocalUpdates ( Transition::Case * 
                                                             , Node * 
                                                             , Enode * 
                                                             , Enode * 
                                                             , vector < Enode * > &
                                                             , vector < Enode * > & );
*/
                                        
  ofstream                              latex_file;
  ofstream                              log_file;
  ofstream                              graphviz;
  ofstream                              abs_graphviz;
  ofstream                              abs_log_file;
                                        
  void                                  initializeSolver( );
  bool                                  initialized;

  
  // invariant search
  void                                   newUnsafe ( Enode * );
  void                                   addAvNode ( Node * );
  list < Node * > &                      getAvList ( );
  vector < Enode * >                     candidate_invariants;
  vector < Enode * >                     suggested_invariants;
  bool                                   invariants;
  unsigned                               discovered_invariants;
//  MC *                                   mc_i;
  unsigned                               next_candidate;
  Node *                                 unsafe_node;
  
  // counterexample and functions to work on it
  vector < Enode * >                     counterexample;
  void getCE                             ( Node * 
                                         , vector < Enode * > & 
                                         , vector < Enode * > & 
                                         , vector < Enode * > & );
  void printCE                           ( vector < Enode * > & 
                                         , ostream & os );

  

  




  /* ******************************************************************************************************
   *    INVARIANT GENERATION
   * ******************************************************************************************************/
  
  unsigned                               number_of_executions;     // statistics
  Node *                                 last_node;                // last node of the trace, used to find the 





  



  /* ******************************************************************************************************
   *    LAZY ABSTRACTION
   * ******************************************************************************************************/
  
  unsigned                               cegar_loops;                       // number of refinements 
  void                                   cleanAbstractLabel                 ( Node * , bool = false );
  Enode *                                cleanAbstractLabel                 ( Enode * , bool = false );
  void                                   setUpPredicates                    (  );
  vector < Enode * >                     useful_predicates;
  void                                   refineNodes                        ( vector < Enode * > &
                                                                            , Node * 
                                                                            , vector < Enode * > &
                                                                            , vector < Enode * > & );
  void                                   updateCoveringRelation             ( Node * , vector< Node * > & );
  void                                   checkCovering                      ( Node * );
  bool                                   CounterexampleIsFeasible           ( vector < Enode * > & 
                                                                            , vector < Enode * > &
                                                                            , vector < Enode * > &
                                                                            , vector < Enode * > & );
  bool                                   isTermAbstracted                   ( Enode * );
  bool                                   existMixedLiteralsInFormula        ( Enode * );
  bool                                   existMixedLiterals                 ( );
  Enode *                                cleanFormulaFromConcreteArrays     ( Enode * );
  Enode *                                getIndexedFormula                  ( Enode * 
                                                                            , int 
                                                                            , vector < Enode * > & 
                                                                            , vector < Enode * > & );
  Enode *                                getArrayVar                        ( ArrayVar * , int );
  Enode *                                instantiateInitial                 ( vector < Enode * > & );
  Enode *                                instantiateUnsafe                  ( Enode * , vector< Enode * > & );
  Enode *                                getTransitionFormula               ( Transition * 
                                                                            , Node * 
                                                                            , vector < Enode * > & 
                                                                            , vector < unsigned > & 
                                                                            , int 
                                                                            , vector < Enode * > & 
                                                                            , vector < Enode * > & );
  Enode *                                abstractArithmeticLiterals         ( Enode * ); 
  Enode *                                getTransitionUpdate                ( Transition * 
                                                                            , Node * 
                                                                            , vector < Enode * > & 
                                                                            , vector < unsigned > & 
                                                                            , int 
                                                                            , vector < Enode * > & 
                                                                            , vector < Enode * > & );
  vector < Node * >                      parent_cover; // tmp vector used in the fixpoint test to keep the covered nodes
  unsigned                               var_id; // used to abstract arithmetic terms





















  vector < Enode * > simplify_origs;
  vector < Enode * > simplify_dests;



};

#endif
