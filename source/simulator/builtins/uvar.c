//////////////////////////////////////////////////////////////////////////////
//Copyright 2008
//  Andrew Gacek, Nathan Guermond, Steven Holte, 
//  Gopalan Nadathur, Xiaochu Qi, Zach Snow
//////////////////////////////////////////////////////////////////////////////
// This file is part of Teyjus.                                             //
//                                                                          //
// Teyjus is free software: you can redistribute it and/or modify           //
// it under the terms of the GNU General Public License as published by     //
// the Free Software Foundation, either version 3 of the License, or        //
// (at your option) any later version.                                      //
//                                                                          //
// Teyjus is distributed in the hope that it will be useful,                //
// but WITHOUT ANY WARRANTY; without even the implied warranty of           //
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            //
// GNU General Public License for more details.                             //
//                                                                          //
// You should have received a copy of the GNU General Public License        //
// along with Teyjus.  If not, see <http://www.gnu.org/licenses/>.          //
//////////////////////////////////////////////////////////////////////////////

/* #include <stdio.h>            //temp */
/* #include "../printterm.h" */
#include "../dataformats.h"
#include "../abstmachine.h"
#include "../../tables/pervasives.h"


/* The idea of uvar is as follows:

     type `    A -> dyn
     type uvar A -> (list dyn) -> o

   when
   
     uvar (X a1 ... an) Args

   is called, Args is assigned to the polymorphic list

     [ ` a1, ..., ` an]

   Note that we are not *unifying* the output with this list,
   which means that the output may freely depend on local variables.
*/

MemPtr BIUVAR_args_list(DF_TermPtr tm)
{

  int arity = DF_appArity(tm);
  int index = 0;

  int SIZE = DF_TM_ATOMIC_SIZE;
  int SIZE2 = DF_TM_APP_SIZE;
  int BSIZE = SIZE2 + 2 * SIZE;

  MemPtr args = DF_appArgs(tm);
  MemPtr lst_start = AM_hreg;
  MemPtr lst_end = AM_hreg + arity * SIZE * DF_CONS_ARITY + SIZE;
  MemPtr tmp = lst_start;
  MemPtr loc = lst_end;

  // List layout is as follows:
  // Cons             lst_start
  // Ref              lst_start + SIZE
  // ...
  // Cons             lst_start + (arity - 1) * 2 * SIZE
  // Ref              lst_start + (arity - 1) * 2 * SIZE + SIZE
  // Nil              lst_end - SIZE

  DF_mkNil(lst_end - SIZE);

  while(index < arity){

    DF_mkCons(tmp,       tmp + SIZE);
    DF_mkRef(tmp + SIZE, loc);

    // Note that the type argument for dync is not needed
    // Argument values are layed out in blocks representing
    //   App(Const(dync), args(index))
    // as follows:    

    // ...
    // App              loc                       [SIZE2]
    // Const            loc + SIZE2               [SIZE]
    // Ref              loc + SIZE2 + SIZE        [SIZE]
    // ...
    
    DF_mkApp(loc, 1,
             loc + SIZE2,
             loc + SIZE2 + SIZE);
    DF_mkConst(loc + SIZE2, 0, PERV_DYNC_INDEX);
    DF_mkRef(loc + SIZE2 + SIZE, args + index * SIZE);

    // increment counters
    tmp += SIZE * DF_CONS_ARITY;
    loc += BSIZE;
    index ++;
  }
  
  AM_hreg = lst_end + (BSIZE * arity);
  return lst_start;
}
  

void BIUVAR_uvar()
{
  DF_TermPtr tm = DF_termDeref((DF_TermPtr)AM_reg(1));
  DF_TermPtr out = DF_termDeref((DF_TermPtr)AM_reg(2));

  if(!DF_isFV(out)){
    /* Output should be an unbound variable */
    EM_THROW(EM_FAIL);
    
  }else if(DF_isFV(tm)){
    /* If input is a variable, return nil */
    DF_mkNil((MemPtr)out);
    AM_preg = AM_cpreg;
    
  }else if(DF_isApp(tm)){
    /* If input is an application,
       create a polymorphic list of its arguments
       provided the applicand is a variable */
    if(!DF_isFV(DF_termDeref(DF_appFunc(tm)))){
      EM_THROW(EM_FAIL);
    }
    // TODO: Need to unify output
    DF_mkRef(out, BIUVAR_args_list(tm));
    AM_preg = AM_cpreg;
    
  }/* TODO: Handle eta-expanded variables
      Need to recognize arguments of the form
        (x \ X A1 ... An x) as (X A1 ... An)
      Note the following should fail:
        (x \ X (A1 x) ... (An x) x)
   */
  else{
    EM_THROW(EM_FAIL);
  }
  return;
}
