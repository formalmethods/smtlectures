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

#ifndef TOP_LEVEL_PROP_INC_H
#define TOP_LEVEL_PROP_INC_H

#include "Global.h"
#include "Otl.h"
#include "Egraph.h"

class TopLevelPropInc
{
public:

  TopLevelPropInc ( Egraph & egraph_, Config & config_ )
    : status      ( true )
    , egraph      ( egraph_ )
    , config      ( config_ )
  { }

  virtual ~TopLevelPropInc( ) { }

  Enode * doit ( Enode * ); // Main routine

  void pushBacktrackPoint( ); // To handle incrementality
  void popBacktrackPoint ( ); // To handle incrementality

private:

  void    retrieveTopLevelEqs             ( Enode *
                                          , vector< Enode * > & 
					  , vector< Enode * > &
					  , list< Enode * > &  );
  bool    produceSubstitutions            ( vector< Enode * > &
                                          , vector< Enode * > & );
  bool    contains                        ( Enode *, Enode * );
  Enode * substitute                      ( Enode * );
  Enode * splitEqs                        ( Enode * );
  void    backwardSubstitute              ( Enode * );

  void    printSubstitutions              ( );

  typedef enum
  {
    ADD_SUBST
  , SUBSTITUTION
  , ADD_FORMULA
  , STATUS_FALSE
  } oper_t;

  map< Enode *, Enode * > all_substitutions;
  vector< Enode * >       all_formulae;

  vector< size_t >  backtrack_points;
  vector< oper_t >  undo_stack_oper;
  vector< Enode * > undo_stack_lhs;
  vector< Enode * > undo_stack_rhs;

  bool status;
  
  Egraph & egraph; // Reference to Egraph
  Config & config; // Reference to Config
};

#endif
