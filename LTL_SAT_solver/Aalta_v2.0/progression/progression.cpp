/* 
 * formula progression algorithm 
 * 
 * File:   progression.cpp
 * Author: Jianwen Li
 * 
 *
 * Created on November 15, 2014
 */
 
 #include "progression.h"
 
 nondeter_prog_state* 
 nondeter_progf (aalta_formula *f, aalta_formula::af_prt_set P)
 {
   nondeter_prog_state *result, *l, *r;
   switch (f->oper ())
   {
     case aalta_formula::Not:
       if (f->r_af ()->oper () <= aalta_formula::Undefined)
       {
         printf ("progression::nondeter_progf: the Not formula is not a literal!\n");
         exit (0);
       }
       if (P.find (f) != P.end ())
         result = new nondeter_prog_state (aalta_formula::TRUE ());
       else 
         result = new nondeter_prog_state (aalta_formula::FALSE ());
       break;
     case aalta_formula::Next:
       result = new nondeter_prog_state (f->r_af ());
       break;
     case aalta_formula::Until:
       r = nondeter_progf (f->r_af (), P);
       l = nondeter_progf (f->l_af (), P);
       
     case aalta_formula::Release:
     case aalta_formula::And:
     case aalta_formula::Or
     default:
   }
 }
