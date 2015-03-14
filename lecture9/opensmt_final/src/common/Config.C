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

#include "Config.h"

void
Config::initializeConfig( )
{
  // Set Global Default configuration
  tool                                    = TOOL_UNDEF;
  logic                                   = UNDEF;
  status                                  = l_Undef;
  incremental                             = 1;
  produce_stats                           = 0;
  produce_models                          = 0;
  print_stats                             = 0;
  print_proofs_smtlib2                    = 0;
  print_proofs_dotty	                  = 0;
  produce_inter                           = 0;
  dump_formula                            = 0;
  dump_log                                = 0;
  verbosity                               = 1;
  print_success                           = 1;
  certification_level                     = 0;       
  strcpy( certifying_solver, "tol_wrapper.sh" ); 
  split_equalities                        = 1;
  // Set SAT-Solver Default configuration
  sat_theory_propagation                  = 1;
  sat_polarity_mode                       = 0;
  sat_initial_skip_step                   = 1;
  sat_skip_step_factor                    = 1;
  sat_restart_first                       = 100;
  sat_restart_inc                         = 1.1;
  sat_use_luby_restart                    = 0;
  sat_learn_up_to_size                    = 0;
  sat_temporary_learn                     = 1;
  sat_preprocess_booleans                 = 0;
  sat_preprocess_theory                   = 0;
  sat_centrality                          = 18;
  sat_trade_off                           = 8192;
  sat_minimize_conflicts                  = 1;
  sat_dump_cnf                            = 0;
  sat_dump_rnd_inter                      = 0;
  sat_lazy_dtc                            = 0;
  sat_lazy_dtc_burst                      = 1;
  // UF-Solver Default configuration
  uf_disable                              = 0;
  uf_theory_propagation                   = 1;
  // BV-Solver Default configuration
  bv_disable                              = 0;
  bv_theory_propagation                   = 1;
  // DL-Solver Default configuration
  dl_disable                              = 0;
  dl_theory_propagation                   = 1;
  // LRA-Solver Default configuration
  lra_disable                             = 0;
  lra_theory_propagation                  = 1;
  lra_poly_deduct_size                    = 0;
  lra_gaussian_elim                       = 1;
  lra_integer_solver                      = 0;
  lra_check_on_assert                     = 0;
  // Proof parameters                     
  proof_reduce                            = 0;
  proof_ratio_red_solv                    = 0;
  proof_red_time                          = 0;
  proof_num_graph_traversals              = 0;
  proof_red_trans                         = 0;
  proof_reorder_pivots                    = 0;
  proof_reduce_while_reordering           = 0;
  proof_random_context_analysis           = 0;
  proof_random_swap_application           = 0;
  proof_remove_mixed                      = 0;
  proof_set_inter_algo                    = 1;
  proof_certify_inter                     = 0;
  proof_random_seed	                  = 0;
  // MCMT related options                 
  auto_test                               = false;
  node_limit                              = 50000;
  depth_limit                             = 0;
  report_tex                              = false;
  flex_fix_point                          = false;
  verbosity                               = 1;
  predicate_abstr                         = false;
  constant_abstr                          = false;
  log                                     = false;
  weak_fix_point                          = 0;
  incr_fix_point                          = 0;
  fix_point_strategy                      = FORWARD;
  breadth_search                          = false;
  depth_search                            = false;
  simpl_level                             = 0;
  e_simpl_level                           = 1;
  simplify_preimages                      = false;
  full_inv_search                         = false;
  parsing_tests                           = false;
  report                                  = false;
  s_efp                                   = false;
  s_lfp                                   = false;
  optimization                            = false;
  fix_point_period                        = 10;
  check_compatible                        = 1;
  iterative                               = false;
  classic_invariant                       = false;
  invariant_pattern                       = false;
  global_invariant                        = false;
  counterexample                          = false;
  generate_invariants                     = false;
  invariant_nodes                         = 10;
  stop_for_debug                          = 0;
  abstraction                             = false;
  term_abstraction                        = false;
  abstraction_power                       = 0;
  abstract_unsafe                         = false;
  abstract_transitions                    = false;
  abstraction_report                      = false;
  abstraction_locking                     = 2;
  abstraction_limit                       = -1;
  abstraction_refinement_depth            = -1;
  starting_interp_algo                    = 0;
}

void Config::parseConfig ( char * f )
{
  FILE * filein = NULL;
  // Open configuration file
  if ( ( filein = fopen( f, "rt" ) ) == NULL )
  {
    // No configuration file is found. Print out
    // the current configuration
    cerr << "# WARNING: No configuration file " << f << ". Dumping default setting to " << f << endl;
    ofstream fileout( f );
    printConfig( fileout );
    fileout.close( );
  }
  else
  {
    int line = 0;

    while ( !feof( filein ) )
    {
      line ++;
      char buf[ 128 ];
      char * res = fgets( buf, 128, filein );
      (void)res;
      // Stop if finished
      if ( feof( filein ) )
	break;
      // Skip comments
      if ( buf[ 0 ] == '#' )
	continue;

      char tmpbuf[ 32 ];

      // GENERIC CONFIGURATION
	   if ( sscanf( buf, "incremental %d\n"                   , &incremental )                    == 1 );
      else if ( sscanf( buf, "produce_stats %d\n"                 , &produce_stats )                  == 1 );
      else if ( sscanf( buf, "print_stats %d\n"                   , &print_stats )                    == 1 );
      else if ( sscanf( buf, "print_proofs_smtlib2 %d\n"          , &print_proofs_smtlib2 )           == 1 );
      else if ( sscanf( buf, "print_proofs_dotty %d\n"            , &print_proofs_dotty )             == 1 );
      else if ( sscanf( buf, "produce_models %d\n"                , &produce_models )                 == 1 )
      {
#ifndef PRODUCE_PROOF
	if ( produce_proofs != 0 )
	  opensmt_error( "You must configure code with --enable-proof to produce proofs" );
#endif
      }
      else if ( sscanf( buf, "produce_inter %d\n"                 , &produce_inter )                  == 1 )
      {
#ifndef PRODUCE_PROOF
	if ( produce_inter != 0 )
	  opensmt_error( "You must configure code with --enable-proof to produce interpolants" );
#endif
      }
      else if ( sscanf( buf, "regular_output_channel %s\n"        , tmpbuf )                          == 1 )
	setRegularOutputChannel( tmpbuf );
      else if ( sscanf( buf, "diagnostic_output_channel %s\n"     , tmpbuf )                          == 1 )
	setDiagnosticOutputChannel( tmpbuf );                                                         
      else if ( sscanf( buf, "dump_formula %d\n"                  , &dump_formula )                   == 1 );
      else if ( sscanf( buf, "dump_log %d\n"                      , &dump_log )                       == 1 );
      else if ( sscanf( buf, "verbosity %d\n"                     , &verbosity )                      == 1 );
      else if ( sscanf( buf, "print_success %d\n"                 , &print_success )                  == 1 );
      else if ( sscanf( buf, "certification_level %d\n"           , &certification_level )            == 1 );
      else if ( sscanf( buf, "certifying_solver %s\n"             , certifying_solver )               == 1 );
      else if ( sscanf( buf, "split_equalities %d\n"              , &split_equalities )               == 1 );
      // SAT SOLVER CONFIGURATION                                                                     
      else if ( sscanf( buf, "sat_theory_propagation %d\n"        , &(sat_theory_propagation))        == 1 );
      else if ( sscanf( buf, "sat_polarity_mode %d\n"             , &(sat_polarity_mode))             == 1 );
      else if ( sscanf( buf, "sat_initial_skip_step %lf\n"        , &(sat_initial_skip_step))         == 1 );
      else if ( sscanf( buf, "sat_skip_step_factor %lf\n"         , &(sat_skip_step_factor))          == 1 );
      else if ( sscanf( buf, "sat_restart_first %d\n"             , &(sat_restart_first))             == 1 );
      else if ( sscanf( buf, "sat_restart_increment %lf\n"        , &(sat_restart_inc))               == 1 );
      else if ( sscanf( buf, "sat_use_luby_restart %d\n"          , &(sat_use_luby_restart))          == 1 );
      else if ( sscanf( buf, "sat_learn_up_to_size %d\n"          , &(sat_learn_up_to_size))          == 1 );
      else if ( sscanf( buf, "sat_temporary_learn %d\n"           , &(sat_temporary_learn))           == 1 );
      else if ( sscanf( buf, "sat_preprocess_booleans %d\n"       , &(sat_preprocess_booleans))       == 1 );
      else if ( sscanf( buf, "sat_preprocess_theory %d\n"         , &(sat_preprocess_theory))         == 1 );
      else if ( sscanf( buf, "sat_centrality %d\n"                , &(sat_centrality))                == 1 );
      else if ( sscanf( buf, "sat_trade_off %d\n"                 , &(sat_trade_off))                 == 1 );
      else if ( sscanf( buf, "sat_minimize_conflicts %d\n"        , &(sat_minimize_conflicts))        == 1 );
      else if ( sscanf( buf, "sat_dump_cnf %d\n"                  , &(sat_dump_cnf))                  == 1 );
      else if ( sscanf( buf, "sat_dump_rnd_inter %d\n"            , &(sat_dump_rnd_inter))            == 1 );
      else if ( sscanf( buf, "sat_lazy_dtc %d\n"                  , &(sat_lazy_dtc))                  == 1 );
      else if ( sscanf( buf, "sat_lazy_dtc_burst %d\n"            , &(sat_lazy_dtc_burst))            == 1 );
      // PROOF PRODUCTION CONFIGURATION                                                               
      else if ( sscanf( buf, "proof_reduce %d\n"                  , &(proof_reduce))                  == 1 );
      else if ( sscanf( buf, "proof_random_seed %d\n"             , &(proof_random_seed))             == 1 );
      else if ( sscanf( buf, "proof_ratio_red_solv %lf\n"         , &(proof_ratio_red_solv))          == 1 );
      else if ( sscanf( buf, "proof_red_time %lf\n"               , &(proof_red_time))                == 1 );
      else if ( sscanf( buf, "proof_num_graph_traversals %d\n"    , &(proof_num_graph_traversals))    == 1 );
      else if ( sscanf( buf, "proof_red_trans %d\n"               , &(proof_red_trans))               == 1 );
      else if ( sscanf( buf, "proof_reorder_pivots %d\n"          , &(proof_reorder_pivots))          == 1 );
      else if ( sscanf( buf, "proof_reduce_while_reordering %d\n" , &(proof_reduce_while_reordering)) == 1 );
      else if ( sscanf( buf, "proof_random_context_analysis %d\n" , &(proof_random_context_analysis)) == 1 );
      else if ( sscanf( buf, "proof_random_swap_application %d\n" , &(proof_random_swap_application)) == 1 );
      else if ( sscanf( buf, "proof_remove_mixed %d\n"            , &(proof_remove_mixed))            == 1 );
      else if ( sscanf( buf, "proof_set_inter_algo %d\n"          , &(proof_set_inter_algo))          == 1 );
      else if ( sscanf( buf, "proof_certify_inter %d\n"           , &(proof_certify_inter))           == 1 );
      // EUF SOLVER CONFIGURATION                                                                     
      else if ( sscanf( buf, "uf_disable %d\n"                    , &(uf_disable))                    == 1 );
      else if ( sscanf( buf, "uf_theory_propagation %d\n"         , &(uf_theory_propagation))         == 1 );
      // BV SOLVER CONFIGURATION                                                                            
      else if ( sscanf( buf, "bv_disable %d\n"                    , &(bv_disable))                    == 1 );
      else if ( sscanf( buf, "bv_theory_propagation %d\n"         , &(bv_theory_propagation))         == 1 );
      // DL SOLVER CONFIGURATION                                                                            
      else if ( sscanf( buf, "dl_disable %d\n"                    , &(dl_disable))                    == 1 );
      else if ( sscanf( buf, "dl_theory_propagation %d\n"         , &(dl_theory_propagation))         == 1 );
      // LRA SOLVER CONFIGURATION                                                                           
      else if ( sscanf( buf, "lra_disable %d\n"                   , &(lra_disable))                   == 1 );
      else if ( sscanf( buf, "lra_theory_propagation %d\n"        , &(lra_theory_propagation))        == 1 );
      else if ( sscanf( buf, "lra_poly_deduct_size %d\n"          , &(lra_poly_deduct_size))          == 1 );
      else if ( sscanf( buf, "lra_gaussian_elim %d\n"             , &(lra_gaussian_elim))             == 1 );
      else if ( sscanf( buf, "lra_integer_solver %d\n"            , &(lra_integer_solver))            == 1 );
      else if ( sscanf( buf, "lra_check_on_assert %d\n"           , &(lra_check_on_assert))           == 1 );
      // MCMT related options
      else if ( sscanf( buf, "node_limit %d\n"                    , &(node_limit))                    == 1 );
      else if ( sscanf( buf, "depth_limit %d\n"                   , &(depth_limit))                   == 1 );
      else if ( sscanf( buf, "verbosity %d\n"                     , &(verbosity))                     == 1 );      
      else if ( sscanf( buf, "simpl_level %d\n"                   , &(simpl_level))                   == 1 );      
      else if ( sscanf( buf, "e_simpl_level %d\n"                 , &(e_simpl_level))                 == 1 );      
      else if ( sscanf( buf, "fix_point_strategy %d\n"            , &(fix_point_strategy))            == 1 );
      else if ( sscanf( buf, "fix_point_period %d\n"              , &(fix_point_period))              == 1 );
      else if ( sscanf( buf, "check_compatible %d\n"              , &(check_compatible))              == 1 );
      else if ( sscanf( buf, "invariant_nodes %d\n"               , &(invariant_nodes))               == 1 );
      else if ( (report_tex            = (strcmp( buf, "tex\n" )                      == 0)) );
      else if ( (flex_fix_point        = (strcmp( buf, "flex_fix_point\n" )           == 0)) );
      else if ( (predicate_abstr       = (strcmp( buf, "predicate_abstr\n" )          == 0)) );
      else if ( (constant_abstr        = (strcmp( buf, "constant_abstr\n" )           == 0)) ); 
      else if ( (log                   = (strcmp( buf, "log\n" )                      == 0)) );
      else if ( (weak_fix_point        = (strcmp( buf, "weak_fix_point\n" )           == 0)) );
      else if ( (incr_fix_point        = (strcmp( buf, "incr_fix_point\n" )           == 0)) ); 
      else if ( (breadth_search        = (strcmp( buf, "breadth_search\n" )           == 0)) );
      else if ( (breadth_search        = (strcmp( buf, "depth_search\n" )             == 0)) );
      else if ( (full_inv_search       = (strcmp( buf, "full_inv_search\n" )          == 0)) );
      else if ( (parsing_tests         = (strcmp( buf, "parsing_tests\n" )            == 0)) );  
      else if ( (simplify_preimages    = (strcmp( buf, "simplify_preimages\n" )       == 0)) );  
      else if ( (report                = (strcmp( buf, "report\n" )                   == 0)) );  
      else if ( (optimization          = (strcmp( buf, "optimization\n" )             == 0)) ); 
      else if ( (iterative             = (strcmp( buf, "iterative\n" )                == 0)) ); 
      else if ( (invariant_pattern     = (strcmp( buf, "invariant_pattern\n" )        == 0)) ); 
      else if ( (classic_invariant     = (strcmp( buf, "invariant\n" )                == 0)) ); 
      else if ( (counterexample        = (strcmp( buf, "counterexample\n" )           == 0)) ); 
      else if ( (generate_invariants   = (strcmp( buf, "generate_invariants\n" )      == 0)) ); 
      else
      {
	opensmt_error2( "unrecognized option ", buf );
      }
    }

    if ( invariant_pattern || classic_invariant )
    {
      global_invariant = true;
    }

    // Close
    fclose( filein );
  }

  if ( produce_stats ) stats_out.open( ".stats.out" );
  if ( dump_log )      log_out.open( ".opensmt_log.smt2" );
}

void Config::printConfig ( ostream & out )
{
  out << "#" << endl;
  out << "# OpenSMT/MCMT Configuration File" << endl;
  out << "# . Options may be written in any order" << endl;
  out << "# . Unrecognized options will throw an error" << endl;
  out << "# . Use '#' for line comments" << endl;
  out << "# . Remove this file and execute opensmt to generate a new copy with default values" << endl;
  out << "#" << endl;
  out << "# GENERIC CONFIGURATION" << endl;
  out << "#" << endl;
  out << "# Enables incrementality (SMT-LIB 2.0 script-compatible)" << endl;
  out << "incremental "             << incremental << endl;
  out << "# Regular output channel " << endl;
  out << "regular_output_channel stdout" << endl;
  out << "# Diagnostic output channel " << endl;
  out << "diagnostic_output_channel stderr" << endl;
  out << "# Prints statistics in stats.out" << endl;
  out << "produce_stats "           << produce_stats << endl;
  out << "# Prints statistics to screen" << endl;
  out << "print_stats "             << print_stats << endl;
  out << "# Prints models" << endl;
  out << "produce_models "          << produce_models << endl;
  out << "# Prints proofs"  << endl;
  out << "print_proofs_smtlib2 "    << print_proofs_smtlib2 << endl;
  out << "print_proofs_dotty "      << print_proofs_dotty << endl;
  out << "# Prints interpolants" << endl;
  out << "produce_inter "           << produce_inter << endl;
  out << "# Dumps input formula (debugging)" << endl;
  out << "dump_formula "            << dump_formula << endl;
  out << "# Dumps a log in smtlib2 format" << endl;
  out << "dump_log "                << dump_log << endl;
  out << "# Choose verbosity level" << endl;
  out << "verbosity "               << verbosity << endl;
  out << "# Print success" << endl;
  out << "print_success "           << print_success << endl;
  out << "# Choose certification level" << endl;
  out << "# 0 - don't certify" << endl;
  out << "# 1 - certify conflicts" << endl;
  out << "# 2 - certify conflicts, deductions " << endl;
  out << "# 3 - certify conflicts, deductions, theory calls " << endl;
  out << "certification_level "     << certification_level << endl;
  out << "certifying_solver "       << certifying_solver << endl;
  out << "# Activates/deactivates splitting of equalities for arithmetic" << endl;
  out << "split_equalities "        << split_equalities << endl;
  out << "#" << endl;
  out << "# SAT SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "# Enables theory propagation" << endl;
  out << "sat_theory_propagation "  << sat_theory_propagation << endl;
  out << "# Polarity mode for TAtoms and BAtoms" << endl;
  out << "# 0 - all true" << endl;
  out << "# 1 - all false" << endl;
  out << "# 2 - all random" << endl;
  out << "# 3 - heuristic TAtoms, true BAtoms" << endl;
  out << "# 4 - heuristic TAtoms, false BAtoms" << endl;
  out << "# 5 - heuristic TAtoms, random BAtoms" << endl;
  out << "sat_polarity_mode "       << sat_polarity_mode << endl;
  out << "# Initial and step factor for theory solver calls" << endl;
  out << "sat_initial_skip_step "   << sat_initial_skip_step << endl;
  out << "sat_skip_step_factor "    << sat_skip_step_factor << endl;
  out << "# Initial and increment conflict limits for restart" << endl;
  out << "sat_restart_first "       << sat_restart_first << endl;
  out << "sat_restart_increment "   << sat_restart_inc << endl;
  out << "sat_use_luby_restart "    << sat_use_luby_restart << endl;
  out << "# Learn theory-clauses up to the specified size (0 learns nothing)" << endl;
  out << "sat_learn_up_to_size "    << sat_learn_up_to_size << endl;
  out << "sat_temporary_learn "     << sat_temporary_learn << endl;
  out << "# Preprocess variables and clauses when possible" << endl;
  out << "sat_preprocess_booleans " << sat_preprocess_booleans << endl;
  out << "sat_preprocess_theory "   << sat_preprocess_theory << endl;
  out << "sat_centrality "          << sat_centrality << endl;
  out << "sat_trade_off "           << sat_trade_off << endl;
  out << "sat_minimize_conflicts "  << sat_minimize_conflicts << endl;
  out << "sat_dump_cnf "            << sat_dump_cnf << endl;
  out << "sat_dump_rnd_inter "      << sat_dump_rnd_inter << endl;
  out << "sat_lazy_dtc "            << sat_lazy_dtc << endl;
  out << "sat_lazy_dtc_burst "      << sat_lazy_dtc_burst << endl;
  out << "#" << endl;
  out << "# PROOF TRANSFORMER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "# Enable reduction" << endl;
  out << "proof_reduce "             << proof_reduce << endl;
  out << "# Randomly initialize seed for transformation" << endl;
  out << "proof_random_seed "     << proof_random_seed << endl;
  out << "# Reduction timeout w.r.t. solving time for each global iteration" << endl;
  out << "proof_ratio_red_solv "     << proof_ratio_red_solv << endl;
  out << "# Reduction timeout for each global iteration" << endl;
  out << "proof_red_time "           << proof_red_time << endl;
  out << "# Number of graph traversals for each global iteration" << endl;
  out << "proof_num_graph_traversals "   << proof_num_graph_traversals << endl;
  out << "# Number of reduction global iterations" << endl;
  out << "proof_red_trans "          << proof_red_trans << endl;
  out << "# Enable pivot reordering for interpolation" << endl;
  out << "proof_reorder_pivots "     << proof_reorder_pivots << endl;
  out << "proof_reduce_while_reordering "     << proof_reduce_while_reordering << endl;
  out << "# Randomize examination rule contexts" << endl;
  out << "proof_random_context_analysis " << proof_random_context_analysis << endl;
  out << "# Randomize application rules A1,A2,B2k" << endl;
  out << "proof_random_swap_application " << proof_random_swap_application << endl;
  out << "# Delete AB-mixed subtrees" << endl;
  out << "proof_remove_mixed "       << proof_remove_mixed << endl;
  out << "# Set to 0,1,2 to use McMillan, Pudlak or McMillan' interpolation algorithm" << endl;
  out << "proof_set_inter_algo "      << proof_set_inter_algo << endl;
  out << "# Choose certification level for interpolants" << endl;
  out << "# 0 - don't certify" << endl;
  out << "# 1 - certify final interpolant" << endl;
  out << "# 2 - certify final and theory interpolants" << endl;
  out << "proof_certify_inter "      << proof_certify_inter << endl;
  out << "#" << endl;
  out << "# EUF SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "uf_disable "               << uf_disable << endl;
  out << "uf_theory_propagation "    << uf_theory_propagation << endl;
  out << "#" << endl;
  out << "# BITVECTOR SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "bv_disable "               << bv_disable << endl;
  out << "bv_theory_propagation "    << bv_theory_propagation << endl;
  out << "#" << endl;
  out << "# DIFFERENCE LOGIC SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "dl_disable "               << dl_disable << endl;
  out << "dl_theory_propagation "    << dl_theory_propagation << endl;
  out << "#" << endl;
  out << "# LINEAR RATIONAL ARITHMETIC SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "lra_disable "              << lra_disable << endl;
  out << "lra_theory_propagation "   << lra_theory_propagation << endl;
  out << "lra_poly_deduct_size "     << lra_poly_deduct_size << endl;
  out << "lra_gaussian_elim "        << lra_gaussian_elim << endl;
  out << "lra_check_on_assert "      << lra_check_on_assert << endl;
  out << "#" << endl;
  out << "# MCMT OPTIONS" << endl;
  out << "#" << endl;
  out << "# . Options may be written in any order"       << endl;
  out << "# . Unrecongnized options will throw an error" << endl;
  out << "# . Use '#' for line comments"                 << endl;
  out << "# . Remove this file and execute mcmt to generate a new copy with default values" << endl;
  out << "node_limit 50000" << endl;
  out << "depth_limit 0" << endl;
  out << "# tex" << endl;
  out << "# flex_fix_point" << endl;
  // out << "inv_search" << endl;
  out << "# predicate_abstr" << endl;
  out << "# constant_abstr" << endl;
  out << "# log" << endl;
  out << "weak_fix_point" << endl;
  out << "incr_fix_point" << endl;
  out << "# Set the fix-point strategy:" << endl;
  out << "#   1 -> Backward (default)" << endl;
  out << "#   2 -> Forward" << endl;
  out << "fix_point_strategy 1" << endl;
  out << "# breadth_search" << endl;
  out << "# depth_search" << endl;
  out << "simpl_level 0" << endl;
  out << "# full_inv_search" << endl;
  out << "# parsing_tests" << endl;
  out << "# simplify_preimages" << endl;
  out << "# check_compatible 1" << endl;
  out << "# iterative" << endl;
  out << "# Pattern-based invariant search" << endl;
  out << "# invariant_pattern" << endl;
  out << "# counterexample" << endl;
  out << "# invariants" << endl;
  out << "# invariant_nodes 15" << endl;
  out << "# generate_invariants" << endl;
}

void
Config::parseCMDLine( int argc
                       , char * argv[ ] )
{
  assert( tool != TOOL_UNDEF );
  if ( tool == OPENSMT )
    parseOpenSMTCMDLine( argc, argv );
  else if ( tool == MCMT )
    parseMCMTCMDLine( argc, argv );
  else
    opensmt_error( "Uknown tool" );
}

void
Config::parseOpenSMTCMDLine( int argc
                              , char * argv[ ] )
{
  char config_name[ 64 ];
  for ( int i = 1 ; i < argc - 1 ; i ++ )
  {
    const char * buf = argv[ i ];
    // Parsing of configuration options
    if ( sscanf( buf, "--config=%s", config_name ) == 1 )
    {
      parseConfig( config_name );
      break;
    }      
    else if ( strcmp( buf, "--help" ) == 0 
	   || strcmp( buf, "-h" )     == 0 )
    {
      printHelp( );
      exit( 1 );
    }
    else
    {
      printHelp( );
      opensmt_error2( "unrecognized option", buf );
    }
  }

  if ( dump_log ) log_out.open( ".opensmt_log.smt2" );
}

void
Config::parseMCMTCMDLine( int argc
                           , char * argv[ ] )
{
  char config_name[ 64 ];
  for ( int i = 1 ; i < argc - 1 ; i ++ )
  {
    const char * buf = argv[ i ];
    // Parsing of configuration options
         if ( sscanf( buf, "--node_limit=%d"          , &(node_limit))                         == 1 
           || sscanf( buf, "-d%d"                     , &(node_limit))                         == 1 );
    else if ( sscanf( buf, "--depth_limit=%d"         , &(depth_limit))                        == 1 
	   || sscanf( buf, "-D%d"                     , &(depth_limit))                        == 1 );
    else if ( sscanf( buf, "--verbosity=%d"           , &(verbosity))                          == 1
           || sscanf( buf, "-v%d"                     , &(verbosity))                          == 1 );      
    else if ( sscanf( buf, "--simpl_level=%d"         , &(simpl_level))                        == 1
	   || sscanf( buf, "-S%d"                     , &(simpl_level))                        == 1 );
    else if ( sscanf( buf, "--e_simpl_level=%d"       , &(e_simpl_level))                      == 1 
           || sscanf( buf, "-E%d"                     , &(e_simpl_level))                      == 1 );      
    else if ( sscanf( buf, "--fix_point_period=%d"    , &(fix_point_period))                   == 1 
           || sscanf( buf, "-fpp%d"                   , &(fix_point_period))                   == 1 );      
    else if ( sscanf( buf, "--check_compatible=%d"    , &(check_compatible))                   == 1 
           || sscanf( buf, "-cc%d"                    , &(check_compatible))                   == 1 );      
    else if ( sscanf( buf, "--invariant_nodes=%d"     , &(invariant_nodes))                    == 1 
           || sscanf( buf, "-in%d"                    , &(invariant_nodes))                    == 1 );      
    else if ( sscanf( buf, "--abstraction_power=%d"   , &(abstraction_power))                  == 1 
           || sscanf( buf, "-ap%d"                    , &(abstraction_power))                  == 1 );      
    else if ( sscanf( buf, "--abstraction_limit=%d"   , &(abstraction_limit))                  == 1 
           || sscanf( buf, "-alim%d"                  , &(abstraction_limit))                  == 1 );      
    else if ( sscanf( buf, "--refinement_depth=%d"    , &(abstraction_refinement_depth))       == 1 
           || sscanf( buf, "-rd%d"                    , &(abstraction_refinement_depth))       == 1 );      
    else if ( sscanf( buf, "--abs_locking=%d"         , &(abstraction_locking))                == 1 
           || sscanf( buf, "-al%d"                    , &(abstraction_locking))                == 1 );      
    else if ( sscanf( buf, "--start_interp_algo=%d"   , &(starting_interp_algo))               == 1 
           || sscanf( buf, "-sia%d"                   , &(starting_interp_algo))               == 1 );      
    else if ( sscanf( buf, "--stop-for-debug=%d"      , &(stop_for_debug))                     == 1 
           || sscanf( buf, "-sfd%d"                   , &(stop_for_debug))                     == 1 );      
    else if ( strcmp( buf, "--tex" ) == 0 )
      report_tex = true;
    else if ( strcmp( buf, "--flex_fix_point" ) == 0 )
      flex_fix_point = true;
    else if ( strcmp( buf, "--predicate_abstr" ) == 0)
      predicate_abstr = true;
    else if ( strcmp( buf, "--constant_abstr" ) == 0)
      constant_abstr = true;
    else if ( strcmp( buf, "--yices-log" )                                  == 0
           || strcmp( buf, "-y" )                                           == 0)   
      log = true;                                                           
    else if ( strcmp( buf, "--opensmt-log" )                                == 0
           || strcmp( buf, "--olog" )                                       == 0    
           || strcmp( buf, "-ol" )                                          == 0 )   
      dump_log = 1;                                                           
    else if ( strcmp( buf, "--weak_fix_point" ) == 0 )                      
      weak_fix_point = true;                                                
    else if ( strcmp( buf, "--incr_fix_point" )                             == 0)  
      incr_fix_point = true;                                                
    else if ( strcmp( buf, "-bs" )                                          == 0
           || strcmp( buf, "--breadth_search" )                             == 0)   
      breadth_search = true;                                                
    else if ( strcmp( buf, "-at" )                                          == 0
           || strcmp( buf, "--auto-test" )                                  == 0)   
      auto_test = true;                                                           
    else if ( strcmp( buf, "-ds" )                                          == 0
           || strcmp( buf, "--depth_search" )                               == 0)   
      depth_search = true;                                                           
    else if ( strcmp( buf, "--full_inv_search" )                            == 0) 
      full_inv_search = true;                                               
    else if ( strcmp( buf, "--parsing_tests" )                              == 0)   
      parsing_tests = true;                                                 
    else if ( strcmp( buf, "--simplify_preimages" )                         == 0 
           || strcmp( buf, "-sp" )                                          == 0)   
      simplify_preimages = true;                                            
    else if ( strcmp( buf, "--abstraction_report" )                         == 0
           || strcmp( buf, "-ar" )                                          == 0)   
      abstraction_report = true;                                                        
    else if ( strcmp( buf, "--term_abstraction" )                           == 0
           || strcmp( buf, "-ta" )                                          == 0)   
      term_abstraction = true;                                                        
    else if ( strcmp( buf, "--abstract_unsafe" )                            == 0
           || strcmp( buf, "-au" )                                          == 0)   
      abstract_unsafe = true;                                                        
    else if ( strcmp( buf, "--abstraction_arithmetic" )                     == 0
           || strcmp( buf, "-arh" )                                         == 0)   
      { abstraction_arithmetic = true; abstraction = true; }                                                    
    else if ( strcmp( buf, "--report" )                                     == 0
           || strcmp( buf, "-r" )                                           == 0)   
      report = true;                                                        
    else if ( strcmp( buf, "-no_efp" )                                      == 0
           || strcmp( buf, "--suppress_eager_fixpoint" )                    == 0)   
      s_efp = true;                                                           
    else if ( strcmp( buf, "-no_lfp" )                                      == 0
           || strcmp( buf, "--suppress_lazy_fixpoint")                      == 0)   
      s_lfp = true;                                                         
    else if ( strcmp( buf, "-o" )                                           == 0
           || strcmp( buf, "--optimization")                                == 0)   
      optimization = true;                                                  
    else if ( strcmp( buf, "-it" )                                           == 0
           || strcmp( buf, "--iterative")                                    == 0)   
      iterative = true;                                                     
    else if ( strcmp( buf, "-i" )                                           == 0
           || strcmp( buf, "--invariant")                                   == 0)   
    { classic_invariant = true; global_invariant = true; }                 
    else if ( strcmp( buf, "-ip" )                                           == 0
           || strcmp( buf, "--invariant_pattern")                            == 0)   
    { invariant_pattern = true; global_invariant = true; }                 
    else if ( strcmp( buf, "-ce" )                                           == 0
           || strcmp( buf, "--counterexample")                               == 0)   
      counterexample = true;                                                
    else if ( strcmp( buf, "-gi" )                                           == 0
           || strcmp( buf, "--generate_invariants")                          == 0)   
      generate_invariants = true;
    else if ( sscanf( buf, "--config=%s", config_name ) == 1 )
    {
      parseConfig( config_name );
      break;
    }      
    else if ( strcmp( buf, "--help" ) == 0 
	   || strcmp( buf, "-h" )     == 0 )
    {
      printHelp( );
      exit( 1 );
    }
    else
    {
      printHelp( );
      mcmt_error2( "unrecognized option", buf );
    }
  }

  if ( dump_log ) log_out.open( ".opensmt_log.smt2" );
}

void Config::printHelp( )
{
  const char opensmt_help_string[] 
    = "Usage: ./opensmt [OPTION] filename\n"
      "where OPTION can be\n"
      "  --help [-h]                                   print this help\n"
      "  --config=<filename>                           use configuration file <filename>\n";
                                                       
  const char mcmt_help_string[]                        
    = "Usage: ./mcmt [OPTION] filename\n"              
      "where OPTION can be\n"                          
      "  --help [-h]                                   print this help\n"
      "  --config=<filename>                           use configuration file <filename>\n"
      "  --auto-test [-at]                             automatic test feature\n" 
      "  --node_limit=N  [-dN]                         stop state space exploration after N nodes (N is a positive integer,\n" 
      "                                                default is 50000)\n"
      "  --depth_limit=N [-DN]                         stop state space exploration when depth N is reached (bounded model\n" 
      "                                                checking mode)\n"
      "  --resume [-e]                                 resume previous state space exploration\n"
      "  --tex [-t]                                    print report in two files: report.tex (containing the list of nodes in LaTex)\n" 
      "                                                and report.dot (containing the graph of the search space in Dot format)\n"
      "  --flex_fix_point [-f]                         flexible instantiation for fix-point checks (user can also specify in the\n" 
      "                                                input file depth and number of variables to be fixed - expert users only)\n" 
      "  --verbosity [-v]                              set verbosity level (1 default, 0 silent)\n"
      "  --predicate_abstr [-a]                        enable index and predicate abstraction in invariant search (user can specify an\n" 
      "                                                abstract signature in the input file)\n"
      "  --constant_abstr [-c]                         constant abstraction in invariant search\n"
      "  --log [-y]                                    printf the log of the proof obligations generated for Yices\n" 
      "                                                (in the file .yices-log)\n"
      "  --olog [-ol]                                  printf the log of the proof obligations generated for OpenSMT\n" 
      "                                                (in the file .opensmt_log.smt2)\n"
      "  --weak_fix_point [-wN]                        enable an incomplete heuristics for fix-point checks after node N (expert\n" 
      "                                                users only)\n"
      "  --incr_fix_point=N [-pN]                      set how many new configurations should be considered for incremental\n" 
      "                                                fix-point checks\n"
      "  --breadth_search [-bs]                        enable breadth-first exploration of state space\n"
      "  --depth_search [-ds]                          enable depth-first exploration of state space\n"
      "  --simpl_level=N [-SN]                         set the simplification level\n" 
      "                                                N=0: none, N=1 : lazy, N=2 : eager,\n" 
      "                                                N=3: eager+eager real quantifier elimination\n"
      "  --e_simpl_level=N [-EN]                       set the egraph simplification level\n" 
      "                                                N=0: naively remove duplicates in ands\n"
      "                                                N=1: aggressively remove duplicates in ands\n"
      "  --full_inv_search [-I]                        enables one/two variables invariant search, plus dynamic predicate and constant\n" 
      "                                                abstraction\n"
      "  --parsing_tests   [-P]                        just do parsing tests on formulae (Yices executable required in the shell path)\n"
      "  --simplify_preimages [-sp]                    simplifies the preimages when generated, deleteting unuseful ones\n"
      "  --report [-r]                                 write a report of nodes in the file report.log\n"
      "  --suppress_eager_fixpoint [-no_efp]           suppress the eager fixpoint (i.e. a fixpoint test is performed BEFORE\n"
      "                                                enter the node in the ToBeVisited list).\n"
      "  --suppress_lazy_fixpoint [-no_lfp]            suppress the lazy fixpoint (enabled by default)\n"
      "  --optimization [-o]                           enables optimization features\n"
      "  --fix_point_period=N [-fppN]                  Change the number of assertions before calling the SMT-solver (default is 10)\n"
      "  --check_compatible=N [-ccN]                   N=1 : simpliest (and less precise) check of transition compatibility (default)\n"
      "                                                N=2 : more precise check of compatibility\n"
      "  --iterative [-it]                             Iterative version\n"
      "  --counterexample [-ce]                        Get the counterexample unsafety is detected\n"
      "  --invariant [-i]                              \"Old-style\" invariant search\n"
      "  --invariant_nodes=N [-inN]                    Can generate at most N nodes while checking candidate invariants\n"
      "  --invariant_pattern [-ip]                     Pattern-based invariant search\n"
      "  --generate_invariants [-gi]                   Generate invariants\n"
      "\n  LAZY ABSTRACTION OPTIONS -- these options work only with abstraction!\n"
      "  --abstraction_power=N [-apN]                  Different levels of abstraction power\n"
      "                                                N=0: minimum power (default)\n"
      "                                                N=1: maximum\n"
      "  --term_abstraction [-ta]                      Enables term abstraction\n"
      "  --abstract_unsafe [-au]                       Abstract all the unsafe configurations (default=no)\n"
      "  --abstraction_report [-ar]                    Produces a graphviz+log before every refinement\n"
      "  --abstraction_limit=N [-alimN]                Maximum number of abstractions (-1 = unbounded, default)\n"
      "  --abstraction_locking=N [-alN]                Enables lock features:\n"
      "                                                N=0: no locking\n"
      "                                                N=1: check with parents\n"
      "                                                N=2: check with nodes previously generated (default)\n"
      "  --refinement_depth=N [-rdN]                   Change the depth of the refinement:\n"
      "                                                N=-1: refines all the nodes on the trace (default)\n"
      "                                                N=1,2,3...: refines up to the last but N nodes of the trace\n"
      "  --start_interp_algo=N [-siaN]                 Change the first interpolation algorhtm (0,1,2)\n"
      "  --abstraction_arithmetic [-arh]               Abstract arithmetic literals\n"
      "\n"
      "Transitions to be accelerated can be specified in the input file\n";
  
  assert( tool != TOOL_UNDEF );
  if ( tool == OPENSMT )
    cerr << opensmt_help_string;
  else if ( tool == MCMT )
    cerr << mcmt_help_string;
  else
    opensmt_error( "Unknown tool" );
}
