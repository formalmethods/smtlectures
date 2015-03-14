/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef ABSTRACT_SOLVER_H
#define ABSTRACT_SOLVER_H

#include "Global.h"
#include "Enode.h"
#include "Node.h"
#include "Config.h"
#include "Structures.h"

// Forwards declaration
class Node;

//
// This is a public interface that any solver has to respect
//

class AbstractSolver
{
public:

  AbstractSolver ( const char * name_
		 , Config &     c_ 
		 , Egraph &     e_
		 )
    : name         ( string( name_ ) )
    , config       ( c_ )
    , egraph       ( e_ )
    , calls        ( 0 )
  { }

  virtual ~AbstractSolver( ) { }

  virtual void     DeclareInitial     ( Enode *
                                      , const vector< Enode * > & 
				      , const vector< ArrayVar * > &
				      ) = 0;
  virtual void     Declare            ( const char *, Snode *, Snode * ) = 0;

  virtual void     DeclareIndexVar    ( const char *
                                      , const vector< Enode * > &
				      , const vector< ArrayVar * > & ) = 0;

  virtual void     DefineType         ( char *, int, int ) = 0;

  virtual void     Push               ( ) = 0;

  virtual void     Pop                ( ) = 0;

  virtual lbool    Check              ( ) = 0;

  virtual void     Assert             ( Enode *, const bool neg = false ) = 0;

  virtual void     Define             ( Node *, vector< ArrayVar * > & ) = 0;
  
  virtual void     Comment            ( const char * ) = 0;
  
  virtual void     Instantiate        ( Node *
                                      , const vector< ArrayVar * > &
                                      , const vector< Enode * > &
				      , const vector< unsigned > &
				      , const bool ) = 0;
  
  virtual void     InstantiateInitial ( const size_t 
                                      , const vector< ArrayVar * > &
			              , const vector< Enode * > &
			              , unsigned * ) = 0;

  inline unsigned     getCalls       ( ) { return calls; }

  inline const char * getName        ( ) { return name.c_str( ); }

  virtual void        SetLogic       ( const logic_t ) { }               // Overload if necessary
  virtual void        SetOption      ( const char *, const char * ) { }  // Overload if necessary

protected:

  const string        name;
  Config &            config;
  Egraph &            egraph;
  unsigned            calls;
};

class AbstractSolverInt : public AbstractSolver
{
public:

  AbstractSolverInt ( const char * name_
		    , Config &     c_ 
		    , Egraph &     e_
		    )
    : AbstractSolver( name_, c_, e_ )
  { }

  virtual ~AbstractSolverInt( ) { }

  virtual void    AssertInt   ( Enode *, const unsigned )     = 0;  // Communicates a partition
  virtual Enode * GetInt      ( const unsigned )              = 0;  // Retrieves n-th interpolant
};

#endif
