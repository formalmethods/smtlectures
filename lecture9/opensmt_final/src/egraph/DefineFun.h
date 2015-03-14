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

#ifndef DEFINE_FUN_H
#define DEFINE_FUN_H

struct DefineFun
{
  DefineFun ( const char * name_
            , Enode *      var_list_
	    , Enode *      define_ )
    : name   ( name_ )
    , define ( define_ )
  {
    assert( name );
    assert( var_list_ );
    assert( define );
    assert( var_list_->isList( ) );

    for ( Enode * v_list = var_list_ 
	; !v_list->isEnil( ) 
	; v_list = v_list->getCdr( ) )
    {
      Enode * v = v_list->getCar( );
      arg_to_var.push_back( v );
    }
  }

  inline Enode * getArg    ( unsigned n ) { assert( n < arg_to_var.size( ) ); return arg_to_var[ n ]; }
  inline Enode * getDefine ( )            { return define; }

private:

  const char *         name;
  vector< Enode * >    arg_to_var;
  Enode *              define;
};

#endif
