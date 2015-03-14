/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef SMTCOMP

#ifndef Invariant_H
#define Invariant_H

#include "Global.h"
#include "Egraph.h"
#include "AbstractSolver.h"
#include "Transition.h"
#include "Config.h"
#include "Node.h"

#define FORMULAS          3

/* This class contains all the algorithm used to generate candidate invariants. */

class Invariant
{
public:

  Invariant ( Egraph           & e_
    , list < Node * >    & l )
    : egraph           ( e_ )
    , nodes            ( l )
  { }

  ~Invariant ( )
  { }

  // different methods used to generate invariant
  void basic_guess                    ( vector < Enode * > & );
  void pattern_guess                  ( vector < Enode * > & );

private:
    
  Egraph &               egraph;            // Egraph
  
  list < Node * >        nodes;             // list of the nodes on which we need to perform the invariant guessing

};

#endif // Invariant_H

#endif
