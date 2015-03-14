/*****************************************************
MCMT 2.0 -- Copyright (C) by the Authors (see AUTHORS)
For the license see LICENSE
*****************************************************/

#ifndef STRUCTURES_H
#define STRUCTURES_H

#include "Enode.h"
#include "Snode.h"

struct ArrayVar
{
  ArrayVar( char * n , Snode * t , Enode * e , bool b , bool a )                   
    : global   ( b )
    , abstract ( a )
    , enode    ( e )
    , name     ( n )
    , type     ( t )
  { }

  inline const char * getName( ) { return name.c_str( ); }
  inline Snode *      getType( ) { return type; }

  bool           global;
  bool           abstract;
  Enode *        enode;

private:

  const string   name;
  Snode *        type;       // This is actually only the return type

};

#endif
