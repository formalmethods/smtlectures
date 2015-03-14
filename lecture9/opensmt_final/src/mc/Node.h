/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef NODE_H
#define NODE_H

#include "Global.h"
#include "Egraph.h"
#include "Enode.h"
#include "AbstractSolver.h"
#include "Transition.h"
#include "Config.h"
#include "Formula.h"

/* This class is used as a container for all the nodes generated
 * by the backward reachability procedure.
 * For now consists of two lists of States objects:
 *  - TBV (To Be Visited) is the list where a new node is inserted
 *  - AV (Already Visited) is the list where an old node already
 *    expanded with 'pre' is inserted */

class Node
{
public:
  Node ( Egraph & e , unsigned & nodes_univ_ids )
    : identifier         ( nodes_univ_ids++ )
#ifdef PEDANTIC_DEBUG    
    , explored           ( false )
#endif                   
    , egraph             ( e )
    , id                 ( -1 )
    , label              ( NULL )
    , abstract_label     ( NULL )
    , deleted            ( false )
    , v1                 ( NULL )
    , v2                 ( NULL )
    , depth              ( 0 )
    , redefinition       ( 0 )
    , is_unsafe          ( false )
    , initial_check      ( false )
    , unsafe             ( 0 )
    , invariant          ( false )
    , abstracted         ( false )
    , covered            ( false )
    , covers             ( false )
    , locked             ( false )
  { }
  
  ~Node ( )
  {
    delete label;
  }

  inline Enode *                    getLabel                     (  ) { assert( label ); return label->getFormula( ); }    
  inline Enode *                    getAbstractLabel             (  ) { assert( abstract_label ); return abstract_label->getFormula( ); }    
  void                              setLabel                     ( Enode * );              
  void                              setAbstractLabel             ( Enode * );              
  inline Formula *                  getFormula                   (  ) { return label; }    
  inline Formula *                  getAbstractFormula           (  ) { return abstract_label; }    
  inline Node *                     getParent                    (  ) { return parent; }
  void                              setParent                    ( Node * );             
  Enode *                           getVar                       ( int );
  void                              setVar                       ( int , Enode * );
  inline Transition *               getParentTransition          (  ) { return parent_transition; }
  void                              setParentTransition          ( Transition * );
  inline int                        getId                        (  ) { return id; }
  inline void                       setId                        ( int i ) { id = i; }
  inline bool                       isUnsafe                     (  ) { return is_unsafe; }
  unsigned                          getUnsafe                    (  ) { return unsafe; }
  void                              setUnsafe                    ( unsigned i ) { unsafe = i; is_unsafe = true; parent = NULL; }
  unsigned                          getRedefinition              (  ) { return redefinition; }
  void                              setRedefinition              ( unsigned i ) { redefinition = i; }
  unsigned                          getDepth                     (  ) { return depth; }
  void                              setDepth                     ( unsigned d ) { depth = d; }
  bool                              isDeleted                    (  ) { return deleted; }
  void                              initialDone                  (  ) { initial_check = true; }
  bool                              initialToCheck               (  ) { return !initial_check; }
  void                              Delete                       (  ) { deleted = true; }
  void                              setInvariant                 ( bool d ) { invariant = d; }
  bool                              isInvariant                  (  ) { return invariant; }
                                                                 
  Enode *                           getValue                     ( Enode * , Enode * , bool );
  Enode *                           getAbstractValue             ( Enode * , Enode * , bool );
  void                              printHistory                 (  );
                                                                
  vector < Enode * > &              getLabelVars                 (  ) { return label->getVariables( ); }
  //vector < Enode * > &              getLiterals                  (  ) { return label->getLiterals(); }    
  unsigned                          getMaxId                     (  ) { return label->getVarMaxId( ); }
  void                              addParent                    ( Node * n ) { assert( n ); parents.insert( n ); }
  bool                              hasParent                    ( Node * );
  void                              addChild                     ( Node * );
  void                              addChildren                  ( vector < Node * > & );
  void                              clearChildren                (  ) { children.clear( ); }
  void                              addDescendant                ( Node * );
  void                              addDescendants               ( vector < Node * > & );
  set < Node * > &                  getChildren                  (  ) { return children; }
  set < Node * > &                  getDescendants               (  ) { return descendants; }
  bool                              hasChild                     ( Node * );
  unsigned                          getCaseVar                   ( unsigned v ) { assert( v < cases.size( ) ); return cases[ v ]; }
  vector < unsigned > &             getCases                     (  ) { return cases; }
  void                              setCaseVar                   ( unsigned v , unsigned c );
  void                              setCases                     ( vector < Enode * > & , vector < unsigned > & );
  
  bool                              isOnPath                     ( Node * ); // check if the nodes has between its descendants the argument
                                    
  
  inline bool                       operator==                   ( const Node &n ) { return identifier == n.identifier; }
  inline bool                       operator!=                   ( const Node &n ) { return identifier != n.identifier; }
                                    
  unsigned                          identifier;                 // univocal identifier
                                    
                                    
                                    
  /******************************************** LAZY ABSTRACTION *********************************/
  void                              addCoveringParent            ( Node * n ) { assert( n ); covering_parents.insert( n ); }
  void                              addCoveringParents           ( vector < Node * > & v ) { covering_parents.insert( v.begin( ) , v.end( ) ); }
  void                              addCoveringParents           ( set < Node * > & v ) { covering_parents.insert( v.begin( ) , v.end( ) ); }
  set< Node *> &                    getCoveringParents           (  ) { return covering_parents; }
  void                              clearCoveringParents         (  ) { covering_parents.clear( ); }
  void                              removeCoveringParent         ( Node * n ) { covering_parents.erase( n ); if ( covering_parents.empty( ) ) covered = false; }
  void                              refineKinship                ( Node * );
  void                              deleteHierarchy              (  );
  void                              printCoveringRelation        (  );
  void                              printChildren                (  );
  void                              printDescendants             (  );
  void                              addCoveredChild              ( Node * n ) { assert( n ); covered_children.insert( n ); }
  void                              addCoveredChildren           ( vector < Node * > & v ) { covered_children.insert( v.begin( ) , v.end( ) ); }
  set< Node *> &                    getCoveredChildren           (  ) { return covered_children; }
  void                              clearCoveredChildren         (  ) { covered_children.clear( ); }
  void                              removeCoveredChild           ( Node * n ) { covered_children.erase( n ); }
  void                              informCoveringParentsImFree  (  );
  bool                              isCovered                    (  ) { return covered; }
  void                              setCovered                   ( bool c ) { if ( id == 2 && !c ) cerr << "\n\nNODE2 IS UNCOVERED!!!\n\n"; covered = c; }
  void                              uncoverChildren              (  );
  void                              lock                         (  ) { locked = true; }
  void                              unlock                       (  ) { locked = false; }
  bool                              isLocked                     (  ) { return locked; }
  void                              lockChildren                 (  ) ;
  set< Node * > &                   getLockedChildren            (  ) { return locked_children; }
  void                              addLockedChild               ( Node * n ) { locked_children.insert( n ); }
  inline void                       setAbstracted                ( bool abs ) { abstracted = abs; }
  inline bool                       getAbstracted                (  ) { return abstracted; }

#ifdef PEDANTIC_DEBUG
  void                              checkParents                 ( Node * );
  void                              checkCovering                (  );
  void                              checkLabel                   (  );
  void                              checkDescendants             (  );
  void                              checkLockedNode              (  );
  bool                              explored;
#endif

private:                            
                                    
  Egraph &                          egraph;
                                    
  int                               id;                         // id of this node
  Formula *                         label;                      // Formula representing this node
  Formula *                         abstract_label;             // Formula representing this node
  bool                              deleted;                    // True if this node has been deleted
                                                                
  Enode * 	                    v1;	                        // Variable of the label used to generate this node (mapped to the first variable of the transition)
  Enode *	                    v2;	                        // Variable of the label used to generate this node (mapped to the second variable of the transition)
                                                                
  Node *                            parent;                     // Node from which this node has been computed
  Transition *                      parent_transition;          
  int                               depth;                      
  unsigned                          redefinition;               // Used to redefine the formula.
  bool                              is_unsafe;                  // tells if the node is an unsafe formula
  bool                              initial_check;               
  unsigned                          unsafe;                     // number of unsafe configuration
                                                                
  bool                              invariant;                  // tells if the node has been defined (if it is an invariant it is not defined)
                                    
  set < Node * >                    children;                   // children of this node
  set < Node * >                    descendants;                // descendants of this node
  set < Node * >                    parents;                    // used to find the nodes to be deleted when refining
                                    
                                    
  vector < unsigned >               cases;                      // tells which case has been applied when generating this node


  /******************************** LAZY ABSTRACTION *********************************/
  bool                              abstracted;                  // says if the node as been abstracted at least once
  bool                              covered;
  bool                              covers;
  bool                              locked;
  set < Node * >                    covering_parents;           // set of nodes that cover this node
  set < Node * >                    covered_children;           // set of nodes this node covers
  set < Node * >                    locked_children;            // set of nodes are locked because this node is covered

};

#endif // NODE_H
