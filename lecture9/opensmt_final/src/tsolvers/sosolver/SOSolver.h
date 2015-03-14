/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2008-2010, Roberto Bruttomesso

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

#ifndef SOSOLVER_H
#define SOSOLVER_H

#include "TSolver.h"

class SOSolver : public OrdinaryTSolver
{
public:

  SOSolver( const int           
          , const char *        
	  , Config &         
	  , Egraph &            
	  , SStore &
	  , vector< Enode * > & 
	  , vector< Enode * > & 
          , vector< Enode * > & );

  ~SOSolver ( );

  lbool               inform              ( Enode * );
  bool                assertLit           ( Enode *, bool = false );
  void                pushBacktrackPoint  ( );
  void                popBacktrackPoint   ( );
  bool                check               ( bool );
  bool                belongsToT          ( Enode * );
  void                computeModel        ( );
#ifdef PRODUCE_PROOF
  Enode *             getInterpolants     ( );
#endif

private:

  bool                findCycle           ( Enode * );  // Find a cycle starting from a node
  void                computeExplanation  ( Enode * );  // Fill explanation
 
  map< Enode *, vector< Enode * > > adj_list;           // Graph representation by means of adj list
  set< Enode * >                    seen;               // Cache to be used inside findCycle
  vector< Enode * >                 used_constr;        // List of constraints used
  vector< size_t >                  backtrack_points;   // Track sizes for used_constr 
  map< Enode *, Enode * >           parent_edge;        // Holds parent relationship for conflict
};

#endif
