 /* 
 * aiger translator to aalta_formula
 * File:   AIGER.cpp
 * Author: Jianwen Li
 * 
 * Created on November 19, 2014
 */
 
 #include "AIGER.h"
 #include "formula/aalta_formua.h"
 #include <string>
 #include <stdio.h>
 #include <stdlib.h>
 
 using namespace std;
 
 aalta_formula* aiger_to_ltl (const string& fn, bool safety)
 {
   //get aiger object
   aiger* aig = aiger_init ();
   aiger_open_and_read_from_file(aig, fn.c_str());
   const char * err = aiger_error(aig);
   if (err) 
   {
     cout << err << endl;
     throw InputError(err);
   }
   if (!aiger_is_reencoded(aig))
     aiger_reencode(aig);
     
   if (safety)  //safety property
     return aiger_safety (aig);
   else
     return aiger_fair (aig);    
 }
 
 aalta_formula* aiger_safety (aiger *aig)
 {
   aalta_formula *result, *constraint, *output, *bad;
   result = NULL;
   constraint = NULL;
   output = NULL;
   bad = NULL;
   
   for (size_t i = 0; i < aig->num_constraints; ++i) 
   {
     if (i == 0)
       constraint = generate_constraint (aig, 0);
     else
       constraint = aalta_formula (aalta_formula::And, constraint, generate_constraint (aiger, i)).unique ();
   }
   
   /* not sure for the outputs!!
   for (size_t i = 0; i < aig->num_outputs; ++i) 
   {
     if (i == 0)
      output = generate_output (aig, 0);
    else
      output = aalta_formula (aalta_formula::Or, output, generate_output (aiger, i)).unique ();
   }
   */
    
   for (size_t i = 0; i < aig->num_bad; ++i) 
   {
     if (i == 0)
      bad = generate_bad (aig, 0);
    else
      bad = aalta_formula (aalta_formula::Or, bad, generate_bad (aiger, i)).unique ();
   }
   if (constraint == NULL)
   {
     if (bad != NULL)
       result = bad;
   }
   else
   {
     assert (bad != NULL);
     bad = aalta_formula (aalta_formula::And, constraint, bad).unique ();
     result = aalta_formula (aalta_formula::Until, constraint, bad).unique ();
   }
   return result;
 }
 
 aalta_formula* generate_constraint (aiger *aig, unsigned pos)
 {
   unsigned id = aig->constraints[pos].lit;
   aalta_formula *result = generate_formula (aig, id);
   return result;
 }
 
 aalta_formula* generate_bad (aiger *aig, unsigned pos)
 {
   unsigned id = aig->bad[pos].lit;
   aalta_formula *result = generate_formula (aig, id);
   return result;
 }
 
 aalta_formula* aiger_fair (aiger* aig)
 {
   aalta_formula *result, *fair, *justice, *f, *g;
   result = NULL;
   for (size_t i = 0; i < aig->num_constraints; ++i) 
   {
     if (i == 0)
       result = generate_constraint (aig, 0);
     else
       result = aalta_formula (aalta_formula::And, result, generate_constraint (aiger, i)).unique ();
   }
   if (result != NULL)
     result = aalta_formula (aalta_formula::Release, aalta_formula::FALSE (), result).unique ();
   
   for (size_t i = 0; i < aig->num_fairness; ++i) 
   {
     fair = generate_fair (aig, i);
     f = aalta_formula (aalta_formula::Until, aalta_formula::TRUE (), fair).unique ();
     g = aalta_formula (aalta_formula::Release, aalta_formula::FALSE (), f).unique ();
     if (result == NULL)
       result = g;
     else
       result = aalta_formula (aalta_formula::And, result, g).unique ();
   }
   for (size_t i = 0; i < aig->num_justice; ++i) 
   {
     justice = generate_justice (aig, i);
     if (result == NULL)
       result = justice;
     else
       result = aalta_formula (aalta_formula::Or, result, justice).unique ();
   }
   return result;
 }
 
 aalta_formula* generate_fair (aiger *aig, unsigned pos)
 {
   unsigned id = aig->fairness[pos].lit;
   aalta_formula *result = generate_formula (aig, id);
   return result;
 }
 
 aalta_formula* generate_justice (aiger *aig, unsigned pos)
 {
   const aiger_symbol & sym = aig->justice[pos];
   aalta_formula *result, *just, *f, *g;
   result = NULL;
   for (size_t j = 0; j < sym.size; ++j)
   {
     just = generate_formula (aig, sym.lits[j]);
     f = aalta_formula (aalta_formula::Until, aalta_formula::TRUE (), fair).unique ();
     g = aalta_formula (aalta_formula::Release, aalta_formula::FALSE (), f).unique ();
     if (result == NULL)
       result = g;
     else
       result = aalta_formula (aalta_formula::And, result, g).unique ();
   }
   return result;
 }
 
 aalta_formula* generate_formula (aiger *aig, unsigned id)
 {
   unsigned pos = id / 2;
   aalta_formula *result;
   if (FORMULAS[pos] != NULL)
     result = FORMULAS[pos];
   else
   {
     unsigned index;
     aalta_formula *f, *l, *r;
     for (size_t i = 0; i < aig->num_inputs; ++i) 
     {
       index = aig->inputs[i].lit / 2;
       if (FORMULAS[index] == NULL)
         FORMULAS[index] = aalta_formula (index).unique ();
       if (pos == index)
       {
         result = FORMULAS[index];
         break;
       }
     }
     for (size_t i = 0; i < aig->num_ands; ++i) 
     {
       const aiger_and * aa = aig->ands + i;
       index = aa->lhs / 2;
       if (FORMULAS[index] == NULL)
       {
         l = generate_formula (aig, aa->rhs0);
         r = generate_formula (aig, aa->rhs1);
         f = aalta_formula (aalta_formula::And, l, r).unique ();
         FORMULAS[index] = f;
       }
       if (pos == index)
       {
         result = FORMULAS[index];
         break;
       }
     }
     
     for (size_t i = 0; i < aig->num_latches, ++i)
     {
       index = aig->latches[i].lit / 2;
       if (FORMULAS[index] == NULL)
         FORMULAS[index] = aalta_formula (index).unique ();
       if (id == index)
       {
         result = FORMULAS[index];
         break;
       }
         
       unsigned next = aig->latches[i].next / 2;
       if (FORMULAS[next] == NULL)
         FORMULAS[next] = aalta_formula (aalta_formula::Next, NULL, FORMULAS[index]).unique ();
       if (pos == next)
       {
         result = FORMULAS[next];
         break;
       }
     }
     
     if (id % 2 != 0)
     {
       result = aalta_formula (aalta_formula::Not, NULL, result).unique ();
       result = result->nnf ();
     }   
   }
  return result;
 }
 
 
 
 
 
 
