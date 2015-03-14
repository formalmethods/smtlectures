/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2011, Roberto Bruttomesso

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

#include "RDSolver.h"

RDSolver::RDSolver( const int           i
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

RDSolver::~RDSolver( )
{
  // Here Deallocate External Solver
}

//
// The solver is informed of the existence of
// atom e. It might be useful for initializing
// the solver's data structures. This function is 
// called before the actual solving starts.
// 
lbool RDSolver::inform( Enode * e )  
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
bool RDSolver::assertLit ( Enode * e, bool reason )
{
  (void)e;
  (void)reason;
  assert( e );
  assert( belongsToT( e ) );

  cerr << "Receiving Literal " << e << endl;

  assert( e->hasPolarity( ) );
  const bool polarity = e->getPolarity( ) == l_True; 

  cerr << "with polarity " << polarity << endl;

  cerr << "e->get1st( ): " << e->get1st( ) << endl;
  cerr << "e->get2nd( ): " << e->get2nd( ) << endl;

  cerr << "e->isEq( ): " << e->isEq( ) << endl;
  cerr << "e->isRDCons( ): " << e->isRDCons( ) << endl;
  cerr << "e->isRDCar( ): " << e->isRDCar( ) << endl;
  cerr << "e->isRDCdr( ): " << e->isRDCdr( ) << endl;

  if ( e->get2nd( )->isRDCar( ) )
    cerr << "Ho trovato un car: " << e->get2nd( ) << endl;

  if ( e->get1st( )->isVar( ) )
    cerr << "Ho trovato una variabile: " << e->get1st( ) << endl;

  return true;
}

//
// Saves a backtrack point
// You are supposed to keep track of the
// operations, for instance in a vector
// called "undo_stack_term", as happens
// in EgraphSolver
//
void RDSolver::pushBacktrackPoint ( )
{
  cerr << "Asked to set a backtrack point" << endl;
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
void RDSolver::popBacktrackPoint ( )
{
  cerr << "Asked to pop a backtrack point" << endl;
}

//
// Check for consistency. If flag is
// set make sure you run a complete check
//
bool RDSolver::check( bool complete )    
{ 
  (void)complete;

  cerr << "Asked to check satisfiability" << endl;

  // Here check for consistency
  return true;
}

//
// Return true if the enode belongs
// to this theory. You should examine
// the structure of the node to see
// if it matches the theory operators
//
bool RDSolver::belongsToT( Enode * e )
{
  (void)e;
  assert( e );

  if ( e->isNot( ) )
    e = e->get1st( );

  if ( !e->isEq( ) )
   return false; 


  if ( !e->get1st( )->isRDCons( )
    && !e->get1st( )->isRDCar ( )
    && !e->get1st( )->isRDCdr ( ) 
    && !e->get1st( )->isVar( ) )
    return false;

  if ( !e->get2nd( )->isRDCons( )
    && !e->get2nd( )->isRDCar ( )
    && !e->get2nd( )->isRDCdr ( ) 
    && !e->get2nd( )->isVar( ) )
    return false;

  return true;
}

//
// Copy the model into enode's data
//
void RDSolver::computeModel( )
{
}

#ifdef PRODUCE_PROOF
Enode * RDSolver::getInterpolants( )
{
  return NULL;
}
#endif
