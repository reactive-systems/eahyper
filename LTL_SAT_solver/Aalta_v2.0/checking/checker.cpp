/* 
 * The checker structure
 * 
 * File:   checker.cpp
 * Author: Jianwen Li
 * 
 *
 * Created on November 15, 2014
 */
 
 #include "checker.h"
 #include "aalta_formula.h"
 #include <iostream>
 #include <stdio.h>
 #include <stdlib.h>
 
 using namespace std;
 
 checker::checker (aalta_formula *f)
 {
   _input = f;
 }
 
 checker::~checker () 
 {
 }
 
 aalta_formula* 
 checker::negation (aalta_formula::af_prt_set P)
 {
   aalta_formula *result, *f;
   aalta_formula::af_prt_set::iterator it = P.begin ();
   if ((*it)->r_af () != NULL)
     result = (*it)->r_af ();
   else if ((*it)->oper () == aalta_formula::True)
     result = aalta_formula::FALSE ();
   else
     result = aalta_formula (aalta_formula::Not, NULL,*it).unique ();
   it ++;
   for(; it != P.end (); it ++)
   {
     if ((*it)->r_af () != NULL)
       result = aalta_formula (aalta_formula::Or, result, (*it)->r_af ()).unique ();
     else
     {
       f = aalta_formula (aalta_formula::Not, NULL, *it).unique ();
       result = aalta_formula (aalta_formula::Or, result, f).unique ();
     }
   }
   return result;
 }
 
 void 
 checker::print (aalta_formula::af_prt_set P)
 {
   aalta_formula::af_prt_set::iterator it;
   printf ("{");
   for(it = P.begin (); it != P.end (); it ++)
   {
     printf ("%s,", (*it)->to_string().c_str());
   }
   printf ("}\n");
 }
