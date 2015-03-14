/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

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

#ifndef CONFIG_H
#define CONFIG_H

#include "Global.h"
#include "SolverTypes.h"

//
// Holds informations about the configuration of the solver
//
struct Config
{
  //
  // For standard executable
  //
  Config ( const tool_t tool_
         , int    argc
	 , char * argv[ ] )
    : filename ( argv[ argc - 1 ] )
    , rocset   ( false )
    , docset   ( false )
  {
    initializeConfig( );
    tool = tool_;
    // Parse command-line options
    parseCMDLine( argc, argv );
  }
  //
  // For API
  //
  Config ( )
  {
    initializeConfig( );
  }

  ~Config ( ) 
  { 
    if ( produce_stats )  stats_out.close( );
    if ( dump_log )       log_out.close( );
    if ( rocset )         out.close( );
    if ( docset )         err.close( );
  }

  void initializeConfig ( );

  void parseConfig         ( char * );
  void parseCMDLine        ( int argc, char * argv[ ] );
  void parseOpenSMTCMDLine ( int argc, char * argv[ ] );
  void parseMCMTCMDLine    ( int argc, char * argv[ ] );
  void printHelp           ( );
  void printConfig         ( ostream & out );

  inline bool      isInit      ( ) { return logic != UNDEF; }

  inline ostream & getStatsOut     ( ) { assert( produce_stats ); return stats_out; }
  inline ostream & getLogOut       ( ) { assert( dump_log ); return log_out; }
  inline ostream & getRegularOut   ( ) { return rocset ? out : cout; }
  inline ostream & getDiagnosticOut( ) { return docset ? err : cerr; }

  inline void setProduceModels  ( const bool s = true ) { produce_models = s ? 1 : 0 ; }  
  inline void setProduceProofs  ( const bool s = true ) { print_proofs_smtlib2 = s ? 1 : 0; }
  inline void setProduceInter   ( const bool s = true ) { produce_inter = s ? 1 : 0; }
  inline void setSplitEqualities( const bool s = true ) { split_equalities = ( s ? 1 : 0 ); }
  inline void setInterAlgo      ( const int s )         { proof_set_inter_algo = s; }  
  inline void setLraGaussianElim( const int s )         { lra_gaussian_elim = s; }

  inline void setRegularOutputChannel( const char * attr )
  {
    if ( strcmp( attr, "stdout" ) != 0 && !rocset )
    {
      out.open( attr );
      if( !out ) 
	opensmt_error2( "can't open ", attr );
      rocset = true;
    }
  }

  inline void setDiagnosticOutputChannel( const char * attr )
  {
    if ( strcmp( attr, "stderr" ) != 0 && !rocset )
    {
      err.open( attr );
      if( !err ) 
	opensmt_error2( "can't open ", attr );
      rocset = true;
    }
  }

  tool_t       tool;                                               // Which tool is this, OPENSMT or MCMT ?
  const char * filename;                                           // Holds the name of the input filename
  logic_t      logic;                                              // SMT-Logic under consideration
  lbool	       status;                                             // Status of the benchmark
  int          incremental;                                        // Incremental solving
  int          produce_stats;                                      // Should print statistics ?
  int          print_stats;                                        // Should print statistics ?
  int          produce_models;                                     // Should produce models ?
  int          produce_proofs;                                     // Should produce proofs ?
  int          print_proofs_smtlib2;                               // Should print proofs ?
  int 	       print_proofs_dotty;	                           // Should print proofs ?
  int          produce_inter;                                      // Should produce interpolants ?
  bool         rocset;                                             // Regular Output Channel set ?
  bool         docset;                                             // Diagnostic Output Channel set ?
  int          dump_formula;                                       // Dump input formula
  int          dump_log;                                           // Dump logfile as smtlib2 script
  int          verbosity;                                          // Verbosity level
  int          print_success;                                      // Print sat/unsat
  int          certification_level;                                // Level of certification
  char         certifying_solver[256];                             // Executable used for certification
  int          split_equalities;                                   // Split arithmetic equalities
  // SAT-Solver related parameters                                 
  int          sat_theory_propagation;                             // Enables theory propagation from the sat-solver
  int          sat_polarity_mode;                                  // Polarity mode
  double       sat_initial_skip_step;                              // Initial skip step for tsolver calls
  double       sat_skip_step_factor;                               // Increment for skip step
  int          sat_restart_first;                                  // First limit of restart
  double       sat_restart_inc;                                    // Increment of limit
  int          sat_use_luby_restart;                               // Use luby restart mechanism
  int          sat_learn_up_to_size;                               // Learn theory clause up to size
  int          sat_temporary_learn;                                // Is learning temporary
  int          sat_preprocess_booleans;                            // Activate satelite (on booleans)
  int          sat_preprocess_theory;                              // Activate theory version of satelite
  int          sat_centrality;                                     // Specify centrality parameter
  int          sat_trade_off;                                      // Specify trade off
  int          sat_minimize_conflicts;                             // Conflict minimization: 0 none, 1 bool only, 2 full
  int          sat_dump_cnf;                                       // Dump cnf formula
  int          sat_dump_rnd_inter;                                 // Dump random interpolant
  int          sat_lazy_dtc;                                       // Activate dtc
  int          sat_lazy_dtc_burst;                                 // % of eij to generate
  int	       sat_reduce_proof;	                           // Enable proof reduction
  int 	       sat_reorder_pivots;	                           // Enable pivots reordering for interpolation
  double       sat_ratio_red_time_solv_time;                       // Reduction time / solving time for each global loop
  double       sat_red_time;                                       // Reduction time for each global loop
  int	       sat_num_glob_trans_loops;                           // Number of loops recycle pivots + reduction
  int	       sat_remove_mixed;                                   // Compression of AB-mixed subtrees
  // Proof manipulation parameters                                 
  int          proof_reduce;                                       // Enable proof reduction
  double       proof_ratio_red_solv;                               // Ratio reduction time solving time for each global loop
  double       proof_red_time;                                     // Reduction time for each global loop
  int	       proof_num_graph_traversals;                         // Number of graph traversals in each global loop
  int          proof_red_trans;                                    // Number of reduction transformations loops
  int          proof_reorder_pivots;                               // Enable pivot reordering
  int 	       proof_reduce_while_reordering;                      // Enable reduction during reordering
  int	       proof_random_context_analysis;                      // Examine a context with 50% probability
  int 	       proof_random_swap_application;                      // Apply a chosen A1,A2,B2k rule with 50% probability
  int          proof_remove_mixed;                                 // Enable removal of mixed predicates
  int          proof_set_inter_algo;                               // 0,1,2 to use McMillan,Pudlak or McMillan' method
  int          proof_certify_inter;                                // Check interpolants
  int	       proof_random_seed;	                           // Randomly initialize seed for transformation
  // UF-Solver related parameters                                  
  int          uf_disable;                                         // Disable the solver
  int          uf_theory_propagation;                              // Enable theory propagation
  // BV-Solver related parameters                                  
  int          bv_disable;                                         // Disable the solver
  int          bv_theory_propagation;                              // Enable theory propagation
  // DL-Solver related parameters                                  
  int          dl_disable;                                         // Disable the solver
  int          dl_theory_propagation;                              // Enable theory propagation
  // LRA-Solver related parameters                                 
  int          lra_disable;                                        // Disable the solver
  int          lra_theory_propagation;                             // Enable theory propagation
  int          lra_poly_deduct_size;                               // Used to define the size of polynomial to be used for deduction; 0 - no deduction for polynomials
  int          lra_trade_off;                                      // Trade-off value for DL preprocessing
  int          lra_gaussian_elim;                                  // Used to switch on/off Gaussian elimination in LRA
  int          lra_integer_solver;                                 // Flag to require integer solution for LA problem
  int          lra_check_on_assert;                                // Probability (0 to 100) to run check when assert is called

  // MCMT Options go here                                          
  bool         auto_test;                                          // Auto test at the end of the search if the system is safe
  unsigned     node_limit;                                         // Stop state space exploration after N nodes
  unsigned     depth_limit;                                        // Stop state space exploration when depth N is reached
  bool         report_tex;                                         // Print report in two files: report.tex and report.dot
  bool         flex_fix_point;                                     // Flexible instantiation for fix-point checks
  bool         predicate_abstr;                                    // Enable index and predicate abstraction in invariant search
  bool         constant_abstr;                                     // Enable constant abstraction in invariant search
  bool         log;                                                // Print the log of the proof obligations generated
  int          weak_fix_point;                                     // Enable an incomplete heuristics for fix-point cheks after node N
  int          incr_fix_point;                                     // Set how many new configurations should be considered for incremental fix-point checks
  int          fix_point_strategy;                                 // Can be backward or forward
  bool         breadth_search;                                     // Enable breadth-first exploration of state space
  bool         depth_search;                                       // Enable breadth-first exploration of state space
  int          simpl_level;                                        // Set the simplification level
  int          e_simpl_level;                                      // Simplification level within the egraph
  bool         full_inv_search;                                    // Enables one/two variables invariant search, plus dynamic predicate and constant abstraction
  bool         parsing_tests;                                      // Just do parsing 
  bool         simplify_preimages;                                 // Simplify preimages 
  bool         report;                                             // Print out in "report.log" the list of unsafe nodes
  bool         abstraction_report;                                 // export dot log
  bool         s_efp;                                              // Eager fixpoint
  bool         s_lfp;                                              // Lazy fixpoint removal
  bool         optimization;                                       // Optimization
  int          fix_point_period;                                   // Fix Point Period
  int          check_compatible;                                   // Check compatible
  bool         iterative;                                          // Check compatible
  bool         invariant_pattern;                                  // Pattern-based invariant search
  bool         global_invariant;                                   // Pattern-based invariant search
  bool         classic_invariant;                                  // Pattern-based invariant search
  unsigned     invariant_nodes;                                    // Maximum number of nodes that can be generates while we are searching for invariants
  bool         counterexample;                                     // Counterexample retrieval
  bool         generate_invariants;                                // Generate invariants
  unsigned     stop_for_debug;                                     // Stop at this node
                                                                   
  bool         abstraction;                                        // Abstraction (this is NOT an "user" option)
  unsigned     abstraction_power;                                  // Abstraction power (different level of abstraction)
  unsigned     abstraction_locking;                                // Locking (different levels)
  int          abstraction_limit;                                  // Maximum number of abstractions (-1 = unbounded) 
  int          abstraction_refinement_depth;                       // Different layers of refinement depth
  bool         abstract_unsafe;                                    // Abstract unsafe configurations?
  bool         abstract_transitions;                               // Abstract transitions (there must be the "abstract_transition" keyword for at most 1 transition
  bool         term_abstraction;                                   // Enables/Disables term abstraction
  unsigned     starting_interp_algo;                               // Starting interpolation algorithm
  int          abstraction_arithmetic;                             // Abstract   T + 1  with  T + n  , where 'n' is a new int variable

private:

  ofstream     stats_out;                                          // File for statistics
  ofstream     log_out;                                            // File for log
  ofstream     out;                                                // Regular output channel
  ofstream     err;                                                // Diagnostic output channel
};
#endif
