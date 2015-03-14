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

//
// This is an empty solver to be used as a template for the 
// development of ordinary theory solvers. 
//

#include "SOSolver.h"

SOSolver::SOSolver( const int           i
                        , const char *        n
	                , Config &            c
	                , Egraph &            e
			, SStore &            t
	                , vector< Enode * > & x
	                , vector< Enode * > & d
                        , vector< Enode * > & s )
  : OrdinaryTSolver ( i, n, c, e, t, x, d, s )
{ 
  // Here Allocate External Solver

}

SOSolver::~SOSolver( )
{
  // Here Deallocate External Solver

}

//
// The solver is informed of the existence of
// atom e. It might be useful for initializing
// the solver's data structures. This function is 
// called before the actual solving starts.
// 
lbool SOSolver::inform( Enode * e )  
{ 
  (void)e;
  assert( e );
  assert( belongsToT( e ) );
  return l_Undef;
}

// 
// Asserts a literal into the solver. If by chance
// you are able to discover inconsistency you may
// return false. The real consistency state will
// be checked with "check"
//
bool SOSolver::assertLit ( Enode * e, bool reason )
{
  lbool sign = e->getPolarity( ); 

  if ( sign == l_False )
    return true;

  Enode * from = e->get1st( );

  adj_list[ from ].push_back( e );
  used_constr.push_back( e );

  (void)e;
  (void)reason;
  assert( e );
  assert( belongsToT( e ) );
  return true;
}

//
// Saves a backtrack point
// You are supposed to keep track of the
// operations, for instance in a vector
// called "undo_stack_term", as happens
// in EgraphSolver
//
void SOSolver::pushBacktrackPoint ( )
{
  backtrack_points.push_back( used_constr.size( ) );
}

//
// Restore a previous state. You can now retrieve
// the size of the stack when you pushed the last
// backtrack point. You have to implement the 
// necessary backtrack operations 
// (see for instance backtrackToStackSize( )
// in EgraphSolver)
// Also make sure you clean the deductions you
// did not communicate
//
void SOSolver::popBacktrackPoint ( )
{
  assert( !backtrack_points.empty( ) );
  const size_t new_size = backtrack_points.back( );
  backtrack_points.pop_back( );

  while ( new_size < used_constr.size( ) )
  {
    Enode * e = used_constr.back( );
    Enode * from = e->get1st( );
    Enode * to   = e->get2nd( );
    assert( adj_list[ from ].back( ) == e );
    adj_list[ from ].pop_back( );
    used_constr.pop_back( );
  }
}

//
// Check for consistency. If flag is
// set make sure you run a complete check
//
bool SOSolver::check( bool complete )    
{ 
  for ( map< Enode *, vector< Enode * > >::iterator it = adj_list.begin( )
      ; it != adj_list.end( )
      ; it ++ )
  {
    // Make sure seen is cleared
    seen.clear( );
    // Make sure parent relationship is cleared
    parent_edge.clear( );
    // Retrieve from node
    Enode * from = it->first;
    // Check if there is any cycle
    const bool cycle_found = findCycle( from ); 

    if ( cycle_found )
      return false;
  }

  (void)complete;
  // Here check for consistency
  return true;
}

bool SOSolver::findCycle( Enode * from )
{
  // Node already seen, cycle !
  if ( seen.find( from ) != seen.end( ) )
  {
    computeExplanation( from );
    return true;
  }

  seen.insert( from );

  // Otherwise explore the outgoing edges
  vector< Enode * > & adj_list_from = adj_list[ from ];

  for ( size_t i = 0 ; i < adj_list_from.size( ) ; i ++ )
  {
    // Set parent
    parent_edge[ adj_list_from[ i ]->get2nd( ) ] = adj_list_from[ i ];
    // Depth-first search continues
    const bool cycle_found = findCycle( adj_list_from[ i ]->get2nd( ) );
    // Interrupt if cycle found
    if ( cycle_found ) 
      return true;
  }

  seen.erase( from );

  return false;
}

void SOSolver::computeExplanation( Enode * from )
{
  assert( explanation.empty( ) );
  Enode * x = from;
  do
  {
    x = parent_edge[ x ]->get1st( );
    explanation.push_back( parent_edge[ x ] );
  }
  while( x != from );
}

//
// Return true if the enode belongs
// to this theory. You should examine
// the structure of the node to see
// if it matches the theory operators
//
bool SOSolver::belongsToT( Enode * e )
{
  (void)e;
  assert( e );
  return true;
}

//
// Copy the model into enode's data
//
void SOSolver::computeModel( )
{
}

#ifdef PRODUCE_PROOF
Enode * SOSolver::getInterpolants( )
{
  return NULL;
}
#endif
