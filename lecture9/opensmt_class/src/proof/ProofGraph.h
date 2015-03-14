/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>
      , Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

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

#ifdef PRODUCE_PROOF

#ifndef PROOFGRAPH_H
#define PROOFGRAPH_H

//TODO remove
//#define PRODUCE_PROOF 1

#include "ProofGlobal.h"
#include "Proof.h"
#include "Enode.h"
#include "CoreSMTSolver.h"
#include <deque>
#include <algorithm>
#include <limits>
#include <bitset>

#define ENABLE_SAFE_VARIABLES 0
#define CHECK // For general checking

// Predetermined max size of visit vectors
// #define SIZE_BIT_VECTOR 10000000
#define SIZE_BIT_VECTOR 100000

// Types of clauses
// NB: CLADERIVED are distinct from CLALEARNED during solving, 
// that are the root of the initial subproofs
enum clause_type 
{ 
   CLAORIG
 , CLALEMMA
 , CLAAXIOM
 , CLALEARNT   
 , CLAMAGENTA
 , CLADERIVED 
};

// Types of rules
enum rul_type 
{ 
   rA1
 , rA2
 , rA2u
 , rB2k
 , rB3
 , rB1
 , rB2
 , rA1B
 , rA2B
 , rA1undo
 , rB
 , rNO
 , ru       // Push down unit clauses
 , ru2
 , rb       // Push down original clauses
 , rp       // Good/bad pivot rule
 , rANY
};

// Rules applicability info
// Five nodes context plus type of applicable rule
struct RuleContext 
{
  RuleContext ( )
    : type( rNO )
    , cv1 ( -1 )
    , cv2 ( -1 )
    , cw  ( -1 )
    , cv3 ( -1 )
    , cv  ( -1 ) 
  { }

  ~RuleContext ( ) { }

  inline void reset( ) 
  { 
    type = rNO; 
    cv1 = -1;
    cv2 = -1;
    cw = -1;
    cv3 = -1; 
    cv = -1;
  }

  rul_type   type;
  clauseid_t cv1;
  clauseid_t cv2;
  clauseid_t cw;
  clauseid_t cv3;
  clauseid_t cv;
};

//
// Resolution proof graph element
//
// FIXME: check if variables HAVE TO be public
// if not make the private
struct ProofNode
{
  ProofNode  ( ) 
    : ant1               ( NULL )
    , ant2               ( NULL )
    , max_dist_sink      ( 0 )
    , min_dist_sink      ( std::numeric_limits<int>::max( ) )
    , partial_interp     ( NULL )
    , partition_mask     ( 0 )
    , num_nodes_subproof ( 0 )
  { }

  ~ProofNode ( ) { }

  //
  // Getty methods
  //
  inline clauseid_t            getId                  ( ) const { return id; }
  inline vector< Lit > &       getClause              ( )       { return clause; }
  inline size_t                getClauseSize          ( ) const { return clause.size( ); }
  inline Var                   getPivot               ( ) const { return pivot; }
  inline ProofNode *           getAnt1                ( ) const { return ant1; }
  inline ProofNode *           getAnt2                ( ) const { return ant2; }
  inline clause_type           getType                ( ) const { return type; }
  inline Enode *               getPartialInterpolant  ( ) const { return partial_interp; }
  inline const ipartitions_t & getInterpPartitionMask ( ) const { return partition_mask; }
  inline size_t                getNumResolvents       ( ) const { return res.size( ); }
  // FIXME: check what this function is actually doing
  inline set< ProofNode * > &  getResolvents          ( )       { return res; }
#if ENABLE_SAFE_VARIABLES
  inline set< Var > &          getSafeVars    	      ( )       { return safe_vars; }
#endif
  inline int		       getNumNodesSubproof    ( )       { return num_nodes_subproof; }
  //
  // Setty methods
  //
  inline void                  setId                  ( clauseid_t new_id )            { id = new_id; }
  inline void                  setPivot               ( Var new_pivot )                { pivot = new_pivot; }
  inline void                  setAnt1                ( ProofNode * a1 )               { ant1 = a1; }
  inline void                  setAnt2                ( ProofNode * a2 )               { ant2 = a2; }
  inline void                  setType                ( clause_type new_type )         { type = new_type; }
  inline void                  setPartialInterpolant  ( Enode * new_part_interp )      { partial_interp = new_part_interp; }
  inline void                  setInterpPartitionMask ( const ipartitions_t & new_part_mask) { partition_mask = new_part_mask; }
  inline void                  addResolvent           ( ProofNode * resol )            { res.insert( resol ); }
  inline void                  removeResolvent        ( ProofNode * resol )            { res.erase( resol ); }
  inline void				   setNumNodesSubproof    ( int i )       				   { num_nodes_subproof = i; }
  //
  // Test methods
  //
  inline bool           isLeaf(){ assert((ant1==NULL && ant2==NULL) || (ant1!=NULL && ant2!=NULL)); return (ant1==NULL);}
  //
  // Data
  //
  clauseid_t         id;                 // id
  vector< Lit >      clause;             // Clause
  Var                pivot;              // Non-leaf node pivot
  set< ProofNode * > res;                // Outgoing edges
  ProofNode *        ant1;               // Edges to antecedents
  ProofNode *        ant2;               // Edges to antecedents 
  clause_type        type;
  int                max_dist_sink;      // Maximal path to sink
  int                min_dist_sink;      // Minimal path to sink
  Enode *            partial_interp;     // Stores partial interpolant
  ipartitions_t      partition_mask;     // Stores mask
  int				 num_nodes_subproof; // Number of nodes in rooted subproof ( overestimate in case of DAG )
#if ENABLE_SAFE_VARIABLES
  set< Var >         safe_vars;          // Set of variables resolved along all the paths from the node to the root
#endif
};

class CoreSMTSolver;
class Proof;

class ProofGraph
{
public:

  ProofGraph ( Config &        c
             , CoreSMTSolver & s
             , THandler *      th
             , Egraph &        e
             , Proof &         t
             , set< int > &    a
             , int             f
             , clauseid_t      g = clause_id_null
             , int             n = -1 )
    : config   ( c )
    , solver   ( s )
    , thandler ( th )
    , egraph   ( e )
  {
    buildProofGraph( t, a, f, g, n );
    if ( useRandomSeed( ) )
    {
      /*
      if ( verbose( ) )
      {
	cout << "# Using random transformation seed" << endl;
      }
      */
      // Initialize random seed
      srand ( time( NULL ) );
    }
    else
    {
      /*
      if ( verbose( ) )
      {
	cout << "# Using default transformation seed" << endl;
      }
      */
      // Initialize random seed
      srand ( 1 );
    }
  }

  ~ProofGraph ( );

  void           handleProof		       ( );
  void           handleProofInter	       ( );
  void           initializeLightVarSet         ( set< Var > & );
  void           produceSequenceInterpolants   ( vector< Enode * > & );
  Enode *        produceMiddleInterpolant      ( );

  void           printProofAsDotty             ( ostream &, bool );

  inline int     verbose                       ( ) const { return config.verbosity; }
  inline int     reorderPivots                 ( ) const { return config.proof_reorder_pivots; }
  inline int     reduceProof                   ( ) const { return config.proof_reduce; }
  inline int     reduceProofWhileReordering    ( ) const { return config.proof_reduce_while_reordering; }
  inline int     produceInterpolants           ( ) const { return config.produce_inter; }
  inline int     printProofSMT                 ( ) const { return config.print_proofs_smtlib2; }
  inline int     printProofDotty               ( ) const { return config.print_proofs_dotty; }
  inline double  ratioReductionSolvingTime     ( ) const { return config.proof_ratio_red_solv; }
  inline double  reductionTime                 ( ) const { return config.proof_red_time; }
  inline double  reductionLoops                ( ) const { return config.proof_red_trans; }
  inline int     numGraphTraversals            ( ) { return config.proof_num_graph_traversals; }
  inline int     removeMixedPredicates         ( ) { return config.proof_remove_mixed; }
  inline int     numABMixedPredicates          ( ) { return light_vars.size(); }
  inline size_t  graphSize                     ( ) const { return graph.size( ); }
  inline int     useRandomSeed                 ( ) const { return config.proof_random_seed; }

  void           printBits                     ( const ipartitions_t & ) const;
  // 
  // Main routines
  //
  void           transfProofForReduction       ( );
  void           transfProofForInterpolation   ( );
  double         doIt                          ( double );
  double         doReduction                   ( double );
  double         doReduction2                  ( double );
  double         doReorderingForInterpolation  ( );
  //
  // Build et al.
  //
  void           buildProofGraph               ( Proof &, set< int > &, int, clauseid_t, int );
  int            cleanProofGraph               ( );                        // Removes proof leftovers
  void           dupliClause                   ( clauseid_t, clauseid_t ); // Clause duplications
  ProofNode *    cloneProofNode                ( clauseid_t );             // Clone node
  void           splitClause                   ( clauseid_t );             // Clause multiplication (?) FIXME
  void           treefyProofGraph              ( );                        // Turn graph into tree (crazy?) FIXME
  void           removeNode                    ( clauseid_t );             // Turn into node destructor (?) FIXME
  void           removeTree                    ( clauseid_t );             // Remove useless subproof
  bool           magentification               ( clauseid_t );             // Magentification
  void           systematicMagentification     ( );
  //
  // Check et al.
  //
  void           checkClauseSorting                 ( clauseid_t );
  void           checkClause                        ( clauseid_t );
  void           checkProof                         ( );
  void           checkClauseDuplicates              ( );
  void           checkNormality                     ( );
  void           checkPivotOrdering                 ( bool( ProofGraph::*ordered ) ( RuleContext & ) ); // FIXME: check this
  bool           pushUpLightVarCriterionWeakOrdered ( RuleContext & );
  void           checkMagentification               ( );
  void           checkTreefication                  ( );
  //
  // Auxiliary
  //
  bool           mergeClauses          ( vector< Lit > &, vector< Lit > &, vector< Lit > &, Var );
  inline bool    litLess               ( Lit & l1, Lit & l2 ) { return var(l1) <= var(l2); }
  inline bool    litEq                 ( Lit & l1, Lit & l2 ) { return (var(l1) == var(l2) && sign(l1) == sign(l2)); }
  void           normalizeProof        ( );
  bool           binSearch             ( vector< Lit > &, Var, bool & );
  void           getGraphInfo          ( );
  void           topolSortingVec       ( vector< clauseid_t > & );
  void           invTopolSortingVec    ( vector< clauseid_t > & );
  void           topolSortingList      ( list< clauseid_t > & );
  void           visitProofChains      ( );
  string         printRuleType         ( rul_type );
  string         printClauseType       ( clause_type );
  void           printProofNode        ( clauseid_t );
  void           printContext          ( RuleContext & );
  void           printClause           ( ProofNode * );
  void           printClause           ( ProofNode *, ostream & );
  void           printSMTClause        ( ProofNode *, ostream & );
  void           printStatus           ( );
  bool           findPivotInSubproof   ( Var, clauseid_t );
  void           restoreAntPolarity    ( clauseid_t, Var );
  inline ProofNode* getNode			   ( clauseid_t id ) { assert( id>=0 ); return graph[ id ]; }
#if ENABLE_SAFE_VARIABLES
  void           calcSafeVarsSets  ( );
#endif
  
  inline bool    isSwapRule            ( rul_type rt ) const { return ( rt==rA1 || rt==rA1B || rt==rA1undo 
                                                                     || rt==rA2 || rt==rA2B || rt==rA2u 
								     || rt==rB2k ); }
  inline bool    isCutRule             ( rul_type rt ) const { return (rt==rB1 || rt==rB2 || rt==rB3); }
  //
  // Interpolation
  //
  Enode *        setPartialInterp                         ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  Enode *        getPartialInterp                         ( ProofNode *, int );
  Enode *        setInterpPudlakLeaf                      ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  Enode *        setInterpPudlakNonLeaf                   ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  Enode *        setInterpMcMillanNonLeaf                 ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  Enode *        setInterpMcMillanLeaf                    ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  Enode *        setInterpMcMillanPrimeLeaf               ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  Enode *        setInterpMcMillanPrimeNonLeaf            ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  Enode *        partialInterpolantWithNelsonOppen        ( ProofNode * );
  void           restrictClauseToAB                       ( ProofNode *, const ipartitions_t &, const ipartitions_t &, vector< Lit > & );
  icolor_t       getVarColor                              ( Var        , const ipartitions_t &, const ipartitions_t & );
  icolor_t       getClauseColor                           ( ProofNode *, const ipartitions_t &, const ipartitions_t & );
  // FIXME: returning a set ?
  set< Enode * > getPredicatesSetFromInterpolantIterative ( Enode * );
  int            getComplexityInterpolantIterative        ( Enode *, bool );
  void           topolSortingEnode                        ( vector< Enode * > &, Enode * );
  bool           usingMcMillanInterpolation               ( ) { return ( config.proof_set_inter_algo == 0 ); }
  bool           usingPudlakInterpolation                 ( ) { return ( config.proof_set_inter_algo == 1 ); }
  bool           usingMcMillanPrimeInterpolation          ( ) { return ( config.proof_set_inter_algo == 2 ); }
  //
  // Transformation
  //
  bool           ruleApply                                ( RuleContext & );
  bool           getApplContext                           ( clauseid_t, clauseid_t, RuleContext & );
  //
  // Heuristics
  //
  bool           trivialApplicationCriterion                   ( RuleContext &, bool );
  bool           ARulesInterpolationApplicationCriterionWeak   ( RuleContext &, bool );
  bool           ARulesInterpolationApplicationCriterionStrong ( RuleContext &, bool );
  bool           ARulesReductionApplicationCriterionTree       ( RuleContext &, bool );
  short          contextChoiceCriterion                        ( RuleContext &
                                                               , RuleContext &
							       , bool(ProofGraph::*allowSwap)(RuleContext&, bool)
							       , bool(ProofGraph::*allowCut)(RuleContext&, bool)
							       , bool
							       , bool);
  bool           allowCutRule                                  ( RuleContext &, bool );
  bool           allowSwapRule                                 ( RuleContext &, bool );
  bool           allowRuleInterpolation                        ( RuleContext &, bool );
  short          handleRuleApplication                         ( RuleContext &
                                                               , RuleContext &
							       , bool(ProofGraph::*allowSwap)(RuleContext &, bool)
							       , bool(ProofGraph::*allowCut)(RuleContext &, bool)
							       , bool
							       , bool );
  // Randomize application of rules
  inline bool    randomApplicationSwap                         ( ) { return ( config.proof_random_swap_application == 1 ); }
  inline bool    randomApplicationCut                          ( ) { return false; }
  inline bool    additionalRandomization                       ( ) { return ( config.proof_random_context_analysis == 1 ); }
  //
  // Strategies
  //
  void           transformAndRestructureOnTheFly               ( double, bool, int );
  double         recyclePivotsIter                             ( );
  double         doTransformationLoop                          ( bool &
                                                               , bool(ProofGraph::*allowSwap)(RuleContext &, bool)
							       , bool(ProofGraph::*allowCut)(RuleContext &, bool)
							       , bool, bool, bool, bool );
  void           alternateARulesRecyclePivots                  ( const double );
  void           applyRandomRule                               ( );

private:

  Config &              config;
  CoreSMTSolver &       solver;
  THandler *            thandler;
  Egraph &              egraph;

  vector< ProofNode * >          graph;                       // Graph
  double                         building_time;               // Time spent building graph
  std::bitset< SIZE_BIT_VECTOR > visited;                     // Bitsets used for graph visits
  std::bitset< SIZE_BIT_VECTOR > visited2;
  set< Var >                     light_vars;                  // Set of light variables that can be pushed up
  clauseid_t                     root;                        // Proof root

  int num_vars_limit;                                         // Number of variables nominal
  int num_vars_actual;                                        // Number of variables actual
  int A1, A2, A2U, B1, B2, B2K, B3, A1B, A2B, A1Undo;         // Info on number of applied rules

  int    num_nodes;                                           // Info on graph dimension
  int    num_edges;
  int    num_unary;
  int    num_leaves;
  double avg_num_res_unary;
  int    diameter;                                            // Max length over min paths leaf->root
  
  double av_cla_size;                                         // Info on clauses
  double var_cla_size;
  int    max_cla_size;
  double avg_num_res;
  double var_num_res;
  int    max_num_res;
  int    dim_unsat_core;
  
  int num_dup;                                                // Count node duplications made while applying rules
  int num_node_add_A1;                                        // Count addition of nodes due to A1 applications
};

#endif
#endif
