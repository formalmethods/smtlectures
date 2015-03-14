/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

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

#include "ProofGraph.h"

// Outputs original proof in dotty format, if reduction enabled also outputs reduced proof in dotty format
void ProofGraph::handleProof( )
{
#ifndef OPTIMIZE
  checkProof();
  cleanProofGraph();
  checkProof();
#endif

  assert( produceInterpolants( ) == 0);
  assert( printProofDotty( ) == 1 
      || reduceProof( ) == 1 );

  //Print propositional skeleton or full proof
  const bool skeleton=false;
  if ( printProofDotty() == 1 )
  {
    //Print original proof
	if( verbose() > 0 ) cerr << "# Outputting dotty proof" << endl;
    ofstream dotty( "proof.dot" );
    printProofAsDotty( dotty, skeleton  );
  }

  if( reduceProof() > 0 )
  {
    //Reduce proof
    transfProofForReduction();

    if( printProofDotty() == 1 )
    {
      //Print reduced proof
      if( verbose() > 0 ) cerr << "# Outputting dotty proof reduced" << endl;
      ofstream dottyred( "proof_reduced.dot" );
      printProofAsDotty( dottyred, skeleton );
    }
    //TODO should return reduced proof in SMTLib2 format!
  }
}

// Manipulates proofs and generates sequence of interpolants
void ProofGraph::handleProofInter( )
{
#ifndef OPTIMIZE
  checkProof();
  cleanProofGraph();
  checkProof();
#endif

  assert( produceInterpolants() == 1);

  // Print propositional skeleton or full proof
  const bool skeleton = false;
  if( printProofDotty() == 1 )
  {
    //Print original proof
	if( verbose() > 0 ) cerr << "# Outputting dotty proof" << endl;
    ofstream dotty( "proof.dot" );
    printProofAsDotty( dotty, skeleton );
  }

  // Potential proof reduction phase before interpolation phase
  if( reduceProof( ) > 0 )
  {
    //Reduce proof
    transfProofForReduction();

    if( printProofDotty() == 1 )
    {
      //Print reduced proof
      if( verbose() > 0 ) cerr << "# Outputting dotty proof reduced" << endl;
      ofstream dottyred( "proof_reduced.dot" );
      printProofAsDotty( dottyred, skeleton );
    }
  }
  
    // Retrieve ABmixed atoms
  solver.getMixedAtoms( light_vars ); 

  // Interpolation phase
  // Makes sense to reorder proof only if there are AB-mixed predicates;
  // notice that attempts to reduction can be embedded inside reordering procedure
  if ( !light_vars.empty( ) )
  {
    transfProofForInterpolation( );

    if( printProofDotty() == 1 )
    {
      //Print reordered proof
      if( verbose() > 0 ) cerr << "# Outputting dotty proof reordered" << endl;
      ofstream dottyre( "proof_reordered.dot" );
      printProofAsDotty( dottyre, skeleton );
    }
  }
}

void ProofGraph::transfProofForReduction( )
{
  assert( reduceProof() > 0 );
  // Time left for transformation
  double solvingTime = cpuTime( );

  size_t size=0;
  int numnodes=0;
  int numedges=0;
  int numleaves=0;
  int numvars=0;
  double avgdeg=0;
  int dia=0;
  int maxclasize=0;
  double avgclasize=0;
  int unsatcoredim=0;
  int numunary=0;
  double avgnumresunary=0;
  double avgnumres=0;
  int maxnumres=0;
  double varnumres=0;
  double varclasize=0;

  if ( verbose() )
  {
    getGraphInfo( );

    size = graph.size( );
    numnodes = num_nodes;
    numedges = num_edges;
    numleaves = num_leaves;
    numvars = num_vars_actual;
    avgdeg = (double)numedges / (double)numnodes;
    dia = diameter;
    maxclasize = max_cla_size;
    avgclasize = av_cla_size;
    unsatcoredim = dim_unsat_core;
    numunary = num_unary;
    avgnumresunary = avg_num_res_unary;
    avgnumres = avg_num_res;
    maxnumres = max_num_res;
    varnumres = var_num_res;
    varclasize = var_cla_size;
  }

  double time=0;

  time = doReduction( solvingTime );

#ifndef OPTIMIZE
  checkProof();
  cleanProofGraph( );
  checkProof();
#endif

  if ( verbose() > 0 )
  {
    getGraphInfo( );

    double perc_nodes=(((double)num_nodes-(double)numnodes)/(double)numnodes)*100;
    double perc_edges=(((double)num_edges-(double)numedges)/(double)numedges)*100;
    double perc_leaves=(((double)num_leaves-(double)numleaves)/(double)numleaves)*100;
    double perc_unsatcore=(((double)dim_unsat_core-(double)unsatcoredim)/(double)unsatcoredim)*100;
    cerr << "#" << endl;
    cerr << "# ------------------------------------" << endl;
    cerr << "# PROOF GRAPH REDUCTION STATISTICS    " << endl;
    cerr << "# ------------------------------------" << endl;
    cerr << "# Structural properties" << endl;
    cerr << "# ---------------------" << endl;
    cerr << "# Light variables............: ";
    fprintf( stderr, "%-10ld\n", light_vars.size( ) );
    cerr << "# Nominal num proof variables: ";
    fprintf( stderr, "%-10d\n", num_vars_limit );
    cerr << "# Actual num proof variables.: ";
    fprintf( stderr, "%-10d %-10d\n", numvars, num_vars_actual );
    cerr << "# Nodes......................: ";
    fprintf( stderr, "%-10d %-10d\n", numnodes, num_nodes );
    cerr << "# Nodes variation............: ";
    fprintf( stderr, "%-9.2f %%\n", perc_nodes );
    cerr << "# Leaves.....................: ";
    fprintf( stderr, "%-10d %-10d\n", numleaves, num_leaves );
    cerr << "# Leaves variation...........: ";
    fprintf( stderr, "%-9.2f %%\n", perc_leaves );
    cerr << "# Unsat core.................: ";
    fprintf( stderr, "%-10d %-10d\n", unsatcoredim, dim_unsat_core );
    cerr << "# Unsat core variation.......: ";
    fprintf( stderr, "%-9.2f %%\n", perc_unsatcore );
    cerr << "# Edges......................: ";
    fprintf( stderr, "%-10d %-10d\n", numedges, num_edges );
    cerr << "# Edges variation............: ";
    fprintf( stderr, "%-9.2f %%\n", perc_edges );
    cerr << "# Graph vector size..........: ";
    fprintf( stderr, "%-10ld %-10ld\n", size, graph.size( ) );
    cerr << "# Average degree.............: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", avgdeg, (double)num_edges / (double)num_nodes );
    cerr << "# Diameter...................: ";
    fprintf( stderr, "%-10d %-10d\n", dia, diameter );
    cerr << "# Unary clauses..............: ";
    fprintf( stderr, "%-10d %-10d\n", numunary, num_unary );
    cerr << "# Max clause size............: ";
    fprintf( stderr, "%-10d %-10d\n", maxclasize, max_cla_size );
    cerr << "# Average clause size........: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", avgclasize, av_cla_size );
    cerr << "# Variance clause size.......: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", varclasize, var_cla_size );
    cerr << "# Max num res................: ";
    fprintf( stderr, "%-10d %-10d\n", maxnumres, max_num_res );
    cerr << "# Average num res............: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", avgnumres, avg_num_res );
    cerr << "# Avg num res unary clauses..: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", avgnumresunary, avg_num_res_unary );
    cerr << "# Variance num res...........: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", varnumres, var_num_res );
    cerr << "# -------------------------" << endl;
    cerr << "# Transformation statistics" << endl;
    cerr << "# -------------------------" << endl;
    cerr << "# Graph building time........: " << building_time << " s" << endl;
    cerr << "# Transformation time........: " << time << " s" << endl;
    cerr << "# Duplications...............: " << num_dup << endl;
    cerr << "# Node additions due to A1...: " << num_node_add_A1 << endl;
    cerr << "# ---------------------------" << endl;
    cerr << "# Rules application statistics" << endl;
    cerr << "# ---------------------------" << endl;
    cerr << "# A1.........................: " << A1 << endl;
    cerr << "# A1 undo....................: " << A1Undo << endl;
    cerr << "# A1 to B....................: " << A1B << endl;
    cerr << "# A2.........................: " << A2 << endl;
    cerr << "# A2 to B....................: " << A2B << endl;
    cerr << "# A2 unary...................: " << A2U << endl;
    cerr << "# B1.........................: " << B1 << endl;
    cerr << "# B2.........................: " << B2 << endl;
    cerr << "# B2 killer..................: " << B2K << endl;
    cerr << "# B3.........................: " << B3 << endl;
    cerr << "# ---------------------------" << endl;
  }
}

void ProofGraph::transfProofForInterpolation( )
{
  assert( produceInterpolants( ) > 0 );
  assert( !light_vars.empty( ) );

  size_t size=0;
  int numnodes=0;
  int numedges=0;
  int numleaves=0;
  int numvars=0;
  double avgdeg=0;
  int dia=0;
  int maxclasize=0;
  double avgclasize=0;
  int unsatcoredim=0;
  int numunary=0;
  double avgnumresunary=0;
  double avgnumres=0;
  int maxnumres=0;
  double varnumres=0;
  double varclasize=0;

  if ( verbose() )
  {
    getGraphInfo( );

    size = graph.size( );
    numnodes=num_nodes;
    numedges=num_edges;
    numleaves=num_leaves;
    numvars=num_vars_actual;
    avgdeg=(double)numedges / (double)numnodes;
    dia=diameter;
    maxclasize=max_cla_size;
    avgclasize=av_cla_size;
    unsatcoredim=dim_unsat_core;
    numunary=num_unary;
    avgnumresunary=avg_num_res_unary;
    avgnumres=avg_num_res;
    maxnumres=max_num_res;
    varnumres=var_num_res;
    varclasize=var_cla_size;
  }

  double time=0;

  if ( reorderPivots( ) > 0 )
    time = doReorderingForInterpolation( );
  else
  {
    opensmt_error( "Cannot produce interpolants because of AB-mixed predicates. Please enable pivot reordering in config file" );
  }


#ifndef OPTIMIZE
  checkProof();
  cleanProofGraph( );
  checkProof();
#endif
  if ( verbose() > 0 )
  {
    getGraphInfo( );

    double perc_nodes=(((double)num_nodes-(double)numnodes)/(double)numnodes)*100;
    double perc_edges=(((double)num_edges-(double)numedges)/(double)numedges)*100;
    double perc_leaves=(((double)num_leaves-(double)numleaves)/(double)numleaves)*100;
    double perc_unsatcore=(((double)dim_unsat_core-(double)unsatcoredim)/(double)unsatcoredim)*100;
    cerr << "#" << endl;
    cerr << "# ------------------------------------" << endl;
    cerr << "# PROOF GRAPH INTERPOLATION STATISTICS    " << endl;
    cerr << "# ------------------------------------" << endl;
    cerr << "# Structural properties" << endl;
    cerr << "# ---------------------" << endl;
    cerr << "# Light variables............: ";
    fprintf( stderr, "%-10ld\n", light_vars.size( ) );
    cerr << "# Nominal num proof variables: ";
    fprintf( stderr, "%-10d\n", num_vars_limit );
    cerr << "# Actual num proof variables.: ";
    fprintf( stderr, "%-10d %-10d\n", numvars, num_vars_actual );
    cerr << "# Nodes......................: ";
    fprintf( stderr, "%-10d %-10d\n", numnodes, num_nodes );
    cerr << "# Nodes variation............: ";
    fprintf( stderr, "%-9.2f %%\n", perc_nodes );
    cerr << "# Leaves.....................: ";
    fprintf( stderr, "%-10d %-10d\n", numleaves, num_leaves );
    cerr << "# Leaves variation...........: ";
    fprintf( stderr, "%-9.2f %%\n", perc_leaves );
    cerr << "# Unsat core.................: ";
    fprintf( stderr, "%-10d %-10d\n", unsatcoredim, dim_unsat_core );
    cerr << "# Unsat core variation.......: ";
    fprintf( stderr, "%-9.2f %%\n", perc_unsatcore );
    cerr << "# Edges......................: ";
    fprintf( stderr, "%-10d %-10d\n", numedges, num_edges );
    cerr << "# Edges variation............: ";
    fprintf( stderr, "%-9.2f %%\n", perc_edges );
    cerr << "# Graph vector size..........: ";
    fprintf( stderr, "%-10ld %-10ld\n", size, graph.size( ) );
    cerr << "# Average degree.............: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", avgdeg, (double)num_edges / (double)num_nodes );
    cerr << "# Diameter...................: ";
    fprintf( stderr, "%-10d %-10d\n", dia, diameter );
    cerr << "# Unary clauses..............: ";
    fprintf( stderr, "%-10d %-10d\n", numunary, num_unary );
    cerr << "# Max clause size............: ";
    fprintf( stderr, "%-10d %-10d\n", maxclasize, max_cla_size );
    cerr << "# Average clause size........: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", avgclasize, av_cla_size );
    cerr << "# Variance clause size.......: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", varclasize, var_cla_size );
    cerr << "# Max num res................: ";
    fprintf( stderr, "%-10d %-10d\n", maxnumres, max_num_res );
    cerr << "# Average num res............: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", avgnumres, avg_num_res );
    cerr << "# Avg num res unary clauses..: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", avgnumresunary, avg_num_res_unary );
    cerr << "# Variance num res...........: ";
    fprintf( stderr, "%-10.2f %-10.2f\n", varnumres, var_num_res );
    cerr << "# -------------------------" << endl;
    cerr << "# Transformation statistics" << endl;
    cerr << "# -------------------------" << endl;
    cerr << "# Graph building time........: " << building_time << " s" << endl;
    cerr << "# Transformation time........: " << time << " s" << endl;
    cerr << "# Duplications...............: " << num_dup << endl;
    cerr << "# Node additions due to A1...: " << num_node_add_A1 << endl;
    cerr << "# ---------------------------" << endl;
    cerr << "# Rules application statistics" << endl;
    cerr << "# ---------------------------" << endl;
    cerr << "# A1.........................: " << A1 << endl;
    cerr << "# A1 undo....................: " << A1Undo << endl;
    cerr << "# A1 to B....................: " << A1B << endl;
    cerr << "# A2.........................: " << A2 << endl;
    cerr << "# A2 to B....................: " << A2B << endl;
    cerr << "# A2 unary...................: " << A2U << endl;
    cerr << "# B1.........................: " << B1 << endl;
    cerr << "# B2.........................: " << B2 << endl;
    cerr << "# B2 killer..................: " << B2K << endl;
    cerr << "# B3.........................: " << B3 << endl;
    cerr << "# ---------------------------" << endl;
  }
}


// Performs reduction
double ProofGraph::doReduction(double solving_time)
{
  if(  ( ratioReductionSolvingTime() > 0 && reductionTime() > 0) ||
      ( ratioReductionSolvingTime() > 0 && numGraphTraversals() > 0) ||
      ( reductionTime() > 0 && numGraphTraversals() > 0) ||
      ( ratioReductionSolvingTime() == 0 && reductionTime() == 0 && numGraphTraversals() == 0)   )
    opensmt_error( "Please choose either ratio or time for reduction or number of proof traversals in config file" );
  if ( reductionLoops() == 0 )
    opensmt_error( "Please set number of global reduction loops to at least 1 in config file" );

  size_t num_non_null;
  if ( verbose() > 0 )
  {
    num_non_null=0;
    for(size_t i=0;i<graph.size();i++)
      if(graph[i]!=NULL) num_non_null++;

    cerr << "#" << endl << "# Estimate of memory used before transformation" << endl;
    cerr << "# Size graph vector: " << graph.size() << " Memory for vector: " <<
      (graph.size()*sizeof(ProofNode*)) << endl;
    cerr << "# Nonnull nodes: " << num_non_null
      << " Memory for nodes: " << (num_non_null*sizeof(ProofNode))<< endl;
    cerr << "# Memory for visit vectors (preallocated): " << sizeof(std::bitset<SIZE_BIT_VECTOR>)*2 << endl << "#" << endl;
  }

  //alternateARulesRecyclePivots(120);
  //return 0;
  //treefyProofGraph();

  //Transformation time calculation
  double time_init=0;
  double time_end=0;
  double red_time=0;
  //Number of inner transformation loops
  //-1 for exhaustiveness
  int num_transf_loops=0;
  //Number of outer transformation loops
  //useful for alternation with recycle pivots
  int num_global_reduction_loops=0;
  // Time available for transformations
  // -1 for exhaustiveness
  double ratio;
  //Flag to enable transformations
  //Set to false in reduction if doing only recycle pivots and reconstruction
  bool do_transf=true;

  if( ratioReductionSolvingTime() > 0)
  {
    // Ratio transformation time/solving time
    ratio=ratioReductionSolvingTime();
    red_time=ratio*solving_time;
    num_transf_loops=-1;
  }
  else if( reductionTime() > 0)
  {
    red_time=reductionTime();
    num_transf_loops=-1;
  }
  else if( numGraphTraversals() > 0)
  {
    num_transf_loops = numGraphTraversals();
    red_time=-1;
  }

  //For each outer loop, recycle pivots algorithm is executed, followed by a certain
  //number of transformation loops, or by a single restructuring loop

  //Each global loop is given an equal fraction of available time
  num_global_reduction_loops=reductionLoops();
  if ( verbose() > 0 )
  {
    cerr << "# Compressing proof, " << num_global_reduction_loops << " global iteration(s) " << endl;
    if( ratioReductionSolvingTime() > 0 || reductionTime() > 0)
      cerr << "# each with timeout " << red_time << " sec(s) " << endl;
    else if ( numGraphTraversals() > 0 )
      cerr << "# each consisting of " << num_transf_loops << " graph traversal(s) "<< endl;
    cerr << "#" << endl;
  }

  double recycle_time=0,i_time=0;

  if( ratioReductionSolvingTime() > 0 || reductionTime() > 0)
  {
    time_init=cpuTime();
    for(int k=0;k<num_global_reduction_loops;k++)
    {
      i_time=cpuTime();
      // Remember that recycle pivots needs a restructuring phase after its execution
      recyclePivotsIter();
      recycle_time=cpuTime()-i_time;

      // Restructure graph, in case do also transformations
      assert(num_transf_loops == -1);
      assert(red_time - recycle_time > 0);
      // Available time = global loop timeout - time used for recycle pivots
      transformAndRestructureOnTheFly(red_time-recycle_time,do_transf,num_transf_loops);
    }
    time_end=cpuTime();
  }
  else if( numGraphTraversals() >0 )
  {
    time_init=cpuTime();
    for(int k=0;k<num_global_reduction_loops;k++)
    {
      // Remember that recycle pivots needs a restructuring phase after its execution
      recyclePivotsIter();

      // Restructure graph, in case do also transformations
      assert(red_time == -1);
      assert(num_transf_loops > 0);
      transformAndRestructureOnTheFly(red_time,do_transf,num_transf_loops);
    }
    time_end=cpuTime();
  }

  if ( verbose() > 0 )
  {
    num_non_null=0;
    for(size_t i=0;i<graph.size();i++)
      if(graph[i]!=NULL) num_non_null++;

    cerr << "#" << endl << "# Estimate of memory used after transformation" << endl;
    cerr << "# Size graph vector: " << graph.size() << " Memory for vector: " <<
      (graph.size()*sizeof(ProofNode*)) << endl;
    cerr << "# Nonnull nodes: " << num_non_null
      << " Memory for nodes: " << (num_non_null*sizeof(ProofNode))<< endl;
    cerr << "# Memory for visit vectors (preallocated): " << sizeof(std::bitset<SIZE_BIT_VECTOR>)*2 << endl;
  }

  return time_end-time_init;
}

// Performs reordering for interpolation, in case combined with reduction
double ProofGraph::doReorderingForInterpolation()
{
  size_t num_non_null;
  if ( verbose() > 0 )
  {
    num_non_null=0;
    for(size_t i=0;i<graph.size();i++)
      if(graph[i]!=NULL) num_non_null++;

    cerr << "#" << endl << "# Estimate of memory used before transformation" << endl;
    cerr << "# Size graph vector: " << graph.size() << " Memory for vector: " <<
      (graph.size()*sizeof(ProofNode*)) << endl;
    cerr << "# Nonnull nodes: " << num_non_null
      << " Memory for nodes: " << (num_non_null*sizeof(ProofNode))<< endl;
    cerr << "# Memory for visit vectors (preallocated): " << sizeof(std::bitset<SIZE_BIT_VECTOR>)*2 << endl << "#" << endl;
  }
  if ( verbose() > 0 )
  {
    cerr << "# Reordering pivots for interpolation" << endl;
    cerr << "#" << endl;
  }

  //Transformation time calculation
  double time_init=0;
  double time_end=0;
  //Number of inner transformation loops
  //-1 for exhaustiveness
  int num_transf_loops=-1;
  //Number of outer transformation loops
  //useful for alternation with recycle pivots if reduction enabled
  int num_global_loops=0;
  //Flag to enable transformations
  bool do_transf=true;
  double leftTime=-1;

  // Combine reordering and reduction
  if( reduceProofWhileReordering() )
  {
    num_global_loops = reductionLoops();
    if ( verbose() > 0 )
    {
      cerr << "# Compressing proof, " << num_global_loops << " global iteration(s) " << endl;
      cerr << "#" << endl;
    }
    time_init=cpuTime();
    for(int k=0;k<num_global_loops;k++)
    {
      // Remember that recycle pivots needs a restructuring phase after its execution
      recyclePivotsIter();
      // Reorder pivots, restructure graph and do transformations
      transformAndRestructureOnTheFly(leftTime,do_transf,num_transf_loops);
    }
    time_end=cpuTime();
  }
  // Do plain reordering
  else
  {
    time_init=cpuTime();
    // Reorder pivots
    transformAndRestructureOnTheFly(leftTime,do_transf,num_transf_loops);
    time_end=cpuTime();
  }

#ifdef CHECK
  bool (ProofGraph::*ordering)(RuleContext&)=&ProofGraph::pushUpLightVarCriterionWeakOrdered;
  checkPivotOrdering(ordering);
#endif

  // Remove AB-mixed subtrees from proof
  if ( removeMixedPredicates( ) > 0 )
  {
	if( verbose() > 0 ) cerr << "# Performing magentification" << endl;
    systematicMagentification( );
    time_end=cpuTime();
#ifdef CHECK
    checkMagentification( );
    checkPivotOrdering(ordering);
#endif
  }

  if ( verbose() > 0 )
  {
    num_non_null=0;
    for(size_t i=0;i<graph.size();i++)
      if(graph[i]!=NULL) num_non_null++;

    cerr << "#" << endl << "# Estimate of memory used after transformation" << endl;
    cerr << "# Size graph vector: " << graph.size() << " Memory for vector: " <<
      (graph.size()*sizeof(ProofNode*)) << endl;
    cerr << "# Nonnull nodes: " << num_non_null
      << " Memory for nodes: " << (num_non_null*sizeof(ProofNode))<< endl;
    cerr << "# Memory for visit vectors (preallocated): " << sizeof(std::bitset<SIZE_BIT_VECTOR>)*2 << endl;
  }

  return time_end-time_init;
}

#endif
