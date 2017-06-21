  /* 
 * formula progression structure and algorithm
 * 
 * File:   progression.cpp
 * Author: Jianwen Li
 * 
 *
 * Created on October 18, 2014
 */
 
 #include "progression.h"
 #include <iostream>
 #include <assert.h>
 #include <stdio.h>
 #include <stdlib.h>
 
 using namespace std;
 
 progression::progf_set progression::_all_progfs;
 
 progression::~progression () { }
 
 progression::progression (aalta_formula *af)
 {
   _type = OTHER;
   _formula = af;
   _left = NULL;
   _right = NULL;
   _tt = false;
   _ff = false;
   switch(af->oper ())
   {
     case aalta_formula::And:  
       _type = AND;
       _formula = NULL;
       _left = progression (af->l_af ()).unique ();
       _right = progression (af->r_af ()).unique ();
       if (_left->_tt && _right->_tt)
         _tt = true;
       else if (_left->_ff || _right->_ff)
         _ff = true;
       break; 
     case aalta_formula::Or:
       _type = OR;
       _formula = NULL;
       _left = progression (af->l_af ()).unique ();
       _right = progression (af->r_af ()).unique ();
       if (_left->_tt || _right->_tt)
         _tt = true;
       else if (_left->_ff && _right->_ff)
         _ff = true;
       break; 
     default:
       if (af == aalta_formula::TRUE ())
         _tt = true;
       else if (af == aalta_formula::FALSE ())
         _ff = true;
       break;
   }
   
   hash ();
 }
 
 progression::progression (const progression &orig)
 {
   *this = orig;
 }
 
 progression::progression (int type, progression* left, progression* right) //for type = AND or type = OR;
 {
   _type = type;
   _formula = NULL; 
   _left = left;
   _right = right;
   _tt = false;
   _ff = false;
   if (type == AND)
   {
     if (left->_tt && right->_tt)
       _tt = true;
     else if (left->_ff || right->_ff)
       _ff = true;
   }
   else
   {
     if (left->_tt || right->_tt)
       _tt = true;
     else if (left->_ff && right->_ff)
       _ff = true;
   }

   hash ();
 }
 
 progression::progression (aalta_formula *af, std::vector<progression*> formula_list)
 {
   _formula = af;
   _formula_list = formula_list;
   _left = NULL;
   _right = NULL;
   _type = OTHER;
   _tt = false;
   _ff = false;
   if (! formula_list.empty ())
   {
   if (af->oper () == aalta_formula::Until)
   {
     assert (formula_list[0] != NULL);
     assert (formula_list[1] != NULL);
     if (formula_list[0]->_tt && formula_list[1]->_tt)
       _tt = true;
     
     if (_formula_list[0]->_ff && _formula_list[1]->_ff)
       _ff = true;
   }
   else if (af->oper () == aalta_formula::Release)
   {
     assert (formula_list[0] != NULL);
     assert (formula_list[1] != NULL);
     if (formula_list[0]->_ff && formula_list[1]->_ff)
       _ff = true;
     
     if (_formula_list[0]->_tt && _formula_list[1]->_tt)
       _tt = true;
   }
   }
   
   hash ();
 }
 
 aalta_formula* 
 progression::to_formula_from_list (std::vector<progression*> list, int type, aalta_formula *start)
 {
   aalta_formula *result, *af;
   int count, size;
   size = list.size ();
   result = start;
   for(count = size - 1; count >= 0; count --)
   {
     if(list[count] == NULL)
       continue;
             
     af = list[count]->to_formula ();
     if(count % 2 == 1)
     {
       if (type == aalta_formula::Until)
       {
         if(af->oper () == aalta_formula::True)
           continue;
         if(af->oper () == aalta_formula::False)
           result = af;
         else if (result == aalta_formula::TRUE ())
           result = af;
         else if (result != aalta_formula::FALSE ())
           result = aalta_formula (aalta_formula::And, af, result).unique ();
       }
       else //for Release formula
       {
         if(af->oper () == aalta_formula::False)
           continue;
         if(af->oper () == aalta_formula::True)
           result = af;
         else if (result == aalta_formula::FALSE ())
           result = af;
         else if (result != aalta_formula::TRUE ())
           result = aalta_formula (aalta_formula::Or, af, result).unique ();
       }
     }
     else
     {
       if (type == aalta_formula::Until)
       {
         if(af->oper () == aalta_formula::False)
           continue;
         if(af->oper () == aalta_formula::True)
           result = af;
         else if (result == aalta_formula::FALSE ())
           result = af;
         else if (result != aalta_formula::TRUE ())
           result = aalta_formula (aalta_formula::Or, af, result).unique ();
       }
       else //for Release formula
       {
         if(af->oper () == aalta_formula::True)
           continue;
         if(af->oper () == aalta_formula::False)
           result = af;
         else if (result == aalta_formula::TRUE ())
           result = af;
         else if (result != aalta_formula::FALSE ())
           result = aalta_formula (aalta_formula::And, af, result).unique ();
       }
     }
   }       
   return result;
 }
 
 aalta_formula*  
 progression::to_formula ()
 {
   aalta_formula *result, *af, *af1, *af2;
   int count, size;
   size = _formula_list.size ();
   switch(_type)
   {
     case OTHER:
       if(_formula_list.empty ())
         result = _formula;
       else
         result = to_formula_from_list (_formula_list, _formula->oper (), _formula);
       break;
     case OR:
       af1 = _left->to_formula ();
       af2 = _right->to_formula ();
       if(af1->oper () == aalta_formula::True)
         result = af1;
       else if(af1->oper () == aalta_formula::False)
         result = af2;
       else
       {
         if(af2->oper () == aalta_formula::True)
           result = af2;
         else if (af2->oper () == aalta_formula::False)
           result = af1;
         else
           result = aalta_formula (aalta_formula::Or, af1, af2).unique ();
       }
       break;
     case AND:
       af1 = _left->to_formula ();
       af2 = _right->to_formula ();
       if(af1->oper () == aalta_formula::False)
         result = af1;
       else if(af1->oper () == aalta_formula::True)
         result = af2;
       else
       {
         if(af2->oper () == aalta_formula::False)
           result = af2;
         else if (af2->oper () == aalta_formula::True)
           result = af1;
         else
           result = aalta_formula (aalta_formula::And, af1, af2).unique ();
       }
       break;
   }
   return result;
 }
 

 
 aalta_formula* 
 progression::to_inv_formula ()
 {
   aalta_formula *result, *f1, *f2;
   switch(_type)
   {
     case OTHER:
       if (_formula->oper () == aalta_formula::Until || _formula->oper () == aalta_formula::Release)
         result = _formula;
       else
         result = aalta_formula::TRUE ();
       break;
     case OR:
       f1 = _left->to_inv_formula ();
       f2 = _right->to_inv_formula ();
       if (f1->oper () == aalta_formula::True)
         result = f1;
       else if (f2->oper () == aalta_formula::True)
         result = f2;
       else
         result = aalta_formula (aalta_formula::Or, f1, f2).unique ();
       break;
     case AND:
       f1 = _left->to_inv_formula ();
       f2 = _right->to_inv_formula ();
       if (f1->oper () == aalta_formula::True)
         result = f2;
       else if (f2->oper () == aalta_formula::True)
         result = f1;
       else
         result = aalta_formula (aalta_formula::Or, f1, f2).unique ();
       break;
   }
   return result;
 }
 
 progression* 
 progression::progf (af_prt_set P)
 {
   if (is_true () || is_false ())
     return this;
   progression *result, *p, *p1, *p2;
   int count, size;
   aalta_formula *f;
   std::vector<progression*> formula_list;
   switch(_type)
   {
     case OTHER:
       
       if(_formula->oper () == aalta_formula::Next)
       {
         result = progression (_formula->r_af ()).unique ();
       }
       else if (_formula->oper () == aalta_formula::Until || _formula->oper () == aalta_formula::Release)
       {
         for(count = 0; count < _formula_list.size (); count ++)
         {
           if (_formula_list[count] == NULL)
             formula_list.push_back ((progression*) NULL);
           else
           {
             p = _formula_list[count]->progf (P);
             if (p->is_true ())
               formula_list.push_back (progression (aalta_formula::TRUE ()).unique ());
             else if (p->is_false ())
               formula_list.push_back (progression (aalta_formula::FALSE ()).unique ());
             else 
               formula_list.push_back (p);
           }
         }
         p1 = progression (_formula->r_af ()).unique ();
         p2 = progression (_formula->l_af ()).unique ();
         p1 = p1->progf (P);
         p2 = p2->progf (P);
         formula_list.push_back(p1);
         formula_list.push_back(p2);
         
         //printf ("%s\n", _formula->to_string ().c_str ());
         simplify_formula_list (formula_list, _formula->oper ());
         result = progression (_formula, formula_list).unique ();
         if (result->is_true ())
           result = progression (aalta_formula::TRUE ()).unique ();
         else if (result->is_false ())
           result = progression (aalta_formula::FALSE ()).unique ();
       }
       else
       {
         if (P.find (_formula) != P.end ())
           result = progression (aalta_formula::TRUE ()).unique ();
         else
         {
           if (_formula->r_af () != NULL)
           {
             if (P.find (_formula->r_af ()) != P.end ())
               result = progression (aalta_formula::FALSE ()).unique ();
             else
               result = progression (aalta_formula::TRUE ()).unique ();
           }
           else
           {   
             if (_formula == aalta_formula::FALSE ())
               result = progression (aalta_formula::FALSE ()).unique ();
             else if (P.find (aalta_formula (aalta_formula::Not, NULL, _formula).unique ()) != P.end ())
               result = progression (aalta_formula::FALSE ()).unique ();
             else
               result = progression (aalta_formula::TRUE ()).unique ();
           }
         }
       }
       break;
     case OR:
       p1 = _left->progf (P);
       p2 = _right->progf (P);
       if (p1->is_true () || p2->is_true ())
         result = progression (aalta_formula::TRUE ()).unique ();
       else if (p1->is_false () && p2->is_false ())
         result = progression (aalta_formula::FALSE ()).unique ();
       else
         result = progression (OR, p1, p2).unique ();
       break;
     case AND:
       p1 = _left->progf (P);
       p2 = _right->progf (P);
       if (p1->is_false () || p2->is_false ())
         result = progression (aalta_formula::FALSE ()).unique ();
       else if (p1->is_true () && p2->is_true ())
         result = progression (aalta_formula::TRUE ()).unique ();
       else
         result = progression (AND, p1, p2).unique ();
       break;
   }
   
   //result->print ();
   return result;
 }
 
 void 
 progression::simplify_formula_list (std::vector<progression*>& formula_list, int type)
 {
   aalta_formula::af_prt_set odds, evens;
   int i, j;
   aalta_formula *f;
   progression *p;
   
   for (i = 0; i < formula_list.size (); i ++)
   {
     if (formula_list[i] == NULL)
       continue;
     if (i % 2 == 0 && type == aalta_formula::Until && formula_list[i]->is_true ())
     {
       p = formula_list[i];
       for (j = i-1; j > 0; j = j-2)
       {
         if (formula_list[j] == NULL)
           break;
         if (! formula_list[j]->is_true ())
           break;
       }
       if (j <= 0)
       {
         formula_list.clear ();
         formula_list.push_back (p);
         formula_list.push_back (p);
       }
       else
       {
         formula_list[i+1] = p;
         formula_list.resize (i+2);
       }
     }
     else if (i % 2 == 1 && type == aalta_formula::Until && formula_list[i]->is_false ())
     {
       p = formula_list[i];
       for (j = i-1; j >= 0; j = j-2)
       {
         if (formula_list[j] == NULL)
           break;
         if (! formula_list[j]->is_false ())
           break;
       }
       if (j < 0)
       {
         formula_list.clear ();
         formula_list.push_back (p);
         formula_list.push_back (p);
       }
       else
       {
         formula_list.resize (i+1);
       }
     }
     else if (i % 2 == 1 && type == aalta_formula::Release && formula_list[i]->is_true ())
     {
       p = formula_list[i];
       for (j = i-1; j >= 0; j = j-2)
       {
         if (formula_list[j] == NULL)
           break;
         if (! formula_list[j]->is_true ())
           break;
       }
       if (j < 0)
       {
         formula_list.clear ();
         formula_list.push_back (p);
         formula_list.push_back (p);
       }
       else
       {
         formula_list.resize (i+1);
       }
     }
     else if (i % 2 == 0 && type == aalta_formula::Release && formula_list[i]->is_false ())
     {
       p = formula_list[i];
       for (j = i-1; j > 0; j = j-2)
       {
         if (formula_list[j] == NULL)
           break;
         if (! formula_list[j]->is_false ())
           break;
       }
       if (j <= 0)
       {
         formula_list.clear ();
         formula_list.push_back (p);
         formula_list.push_back (p);
       }
       else
       {
         formula_list[i+1] = p;
         formula_list.resize (i+2);
       }
     }
     else
     {
       if (! formula_list[i]->is_true () && ! formula_list[i]->is_false ())
       {
         f = formula_list[i]->to_formula ();
         //printf ("%s\n", f->to_string().c_str ());
         if (i % 2 == 0)
         {
           if (evens.find (f) != evens.end ())
             formula_list[i] = NULL;
           else
             evens.insert (f);
         }
         else
         {
           if (odds.find (f) != odds.end ())
             formula_list[i] = NULL;
           else
             odds.insert (f);
         }
       }
     }
   } 
   
   /*
   i = formula_list.size () - 1;
   for (; i > 2; i = i-2)
   {
     if (formula_list[i] == NULL)
     {
       if (formula_list[i-1] == NULL)
         continue;
       else if (type == aalta_formula::Until && formula_list[i-1]->is_false ())
         continue;
       //else if (type == aalta_formula::Release && formula_list[i-1]->is_true ())
         //continue;
       else
         break;
     }
     else if (formula_list[i-1] == NULL)
     {
       if (type == aalta_formula::Until && formula_list[i]->is_true ())
         continue;
       //else if (type == aalta_formula::Release && formula_list[i]->is_false ())
         //continue;
       else
         break;
     }
     else
     {
       if (type == aalta_formula::Until && formula_list[i]->is_true () && formula_list[i-1]->is_false ())
         continue;
       //else if (type == aalta_formula::Release && formula_list[i]->is_false () && formula_list[i-1]->is_true ())
         //continue;
       else
         break;
     }
   }
   formula_list.resize (i+1);
   */ 
   
   
   /*
   progf_set odds, evens;
   int i;
   progression *p0, *p1;
  
   bool until_odd = true;          //record all odd positions are true
   bool until_even = true;         //all even positions are false
   bool release_odd = true;        //all odd positions are false
   bool release_even = true;       //all even positions are true
   for(i = 0; i < formula_list.size (); i ++)
   {
     if (formula_list[i] == NULL)
       continue;
     if(i % 2 == 0)
     {
       //if Until is satisfied in an even position
       if (type == aalta_formula::Until && formula_list[i]->is_true ())
       {
         if (until_odd)       //if all odd positions before are also satisfied
         {
           p0 = formula_list[i];
           p1 = progression (aalta_formula::TRUE ()).unique ();
           formula_list.clear ();
           formula_list.push_back (p0);
           formula_list.push_back (p1);
           #ifdef _DEBUG
             printf ("Doing until_odd, the formula is \n   %s\n", formula_list[i]->to_string().c_str());
           #endif
           break;
         }
         else               //else only remove the elements after the satisfied pair.
           formula_list.resize (i+2);
       }
       
        //if Release is unsatisfied in an even position
       if (type == aalta_formula::Release && formula_list[i]->is_false ())
       {
         if (release_odd)             //if all odd positions before are also unsatisfied
         {
           p0 = formula_list[i];
           p1 = progression (aalta_formula::FALSE ()).unique ();

           formula_list.clear ();
           formula_list.push_back (p0);
           formula_list.push_back (p1);
           #ifdef _DEBUG
             printf ("Doing release_odd, the formula is \n   %s\n", formula_list[i]->to_string().c_str());
           #endif
           break;
         }
         else                         //else only remove the elements after the unsatisfied pair.
           formula_list.resize (i+2);
       }
       
       if (type == aalta_formula::Until && ! formula_list[i]->is_false ())
         until_even = false;
         
       if (type == aalta_formula::Release && ! formula_list[i]->is_true ())
         release_even = false;
         
       //if the element appears in previous even positions
       if (evens.find (formula_list[i]) != evens.end ())
         formula_list[i] = NULL;
       else  
         evens.insert (formula_list[i]);
     }
     else
     {
       //if Until is unsatisfied in an odd position
       if (type == aalta_formula::Until && formula_list[i]->is_false ())
       {
         if (until_even)                    //if all even positions before are also unsatisfied
         {
           p1 = formula_list[i];
           p0 = progression (aalta_formula::FALSE ()).unique ();
           //p0 = formula_list[i-1];
           formula_list.clear ();
           formula_list.push_back (p0);
           formula_list.push_back (p1);
           #ifdef _DEBUG
             printf ("Doing until_even, the formula is \n   %s\n", formula_list[i]->to_string().c_str());
           #endif
           break;
         }
         else                             //else only remove the elements after the pair.
           formula_list.resize (i+1);
       }
       
       //if Release is satisfied in an odd position
       if (type == aalta_formula::Release && formula_list[i]->is_true ())
       {
         if (release_even)                 //if all even positions before are also satisfied
         {
           p1 = formula_list[i];
           p0 = progression (aalta_formula::TRUE ()).unique ();
           //p0 = formula_list[i-1];
           formula_list.clear ();
           formula_list.push_back (p0);
           formula_list.push_back (p1);
           #ifdef _DEBUG
             printf ("Doing release_even, the formula is \n   %s\n", formula_list[i]->to_string().c_str());
           #endif
           break;
         }
         else                              //else only remove the elements after the pair.
           formula_list.resize (i+1);
       }
       
       if (type == aalta_formula::Until && ! formula_list[i]->is_true ())
         until_odd = false;
         
       if (type == aalta_formula::Release && ! formula_list[i]->is_false ())
         release_odd = false;
       
       //if the element appears in previous odd positions
       if (odds.find (formula_list[i]) != odds.end ())
         formula_list[i] = NULL;
       else
         odds.insert (formula_list[i]);
     }
   }
   
   
   std::vector<progression*> list;
   for (i = 0; i < formula_list.size (); i = i + 2)
   {
     //if there is a [null, null] in the list, then remove it.
     if (formula_list[i] == NULL && formula_list[i+1] == NULL)
       continue;
     else if (formula_list[i] == NULL)
     {
       //if there is a [null, true] in the list when type is until, then remove it.
       if (type == aalta_formula::Until && formula_list[i+1]->is_true ())
         continue;
       //if there is a [null, false] in the list when type is release, then remove it.
       if (type == aalta_formula::Release && formula_list[i+1]->is_false ())
         continue;
     }
     else if (formula_list[i+1] == NULL)
     {
       //if there is a [false, null] in the list when type is until, then remove it.
       if (type == aalta_formula::Until && formula_list[i]->is_false ())
         continue;
       //if there is a [true, null] in the list when type is release, then remove it.
       if (type == aalta_formula::Release && formula_list[i]->is_true ())
         continue;
     }
     
     list.push_back (formula_list[i]);
     list.push_back (formula_list[i+1]);
   }
   */
   
   /*
   //  if there is a [false, true] in Until or [true, false] in Release, then remove it. 

   if (list.size () > 2)
   {
     if (type == aalta_formula::Until)
     {
       if (list[0]->is_false () && list[1]->is_true ())
       {
         if (list[2] == NULL)
           list[2] = list[0];
         if (list[3] == NULL)
           list[3] = list[1];
         list.erase (list.begin ());
         list.erase (list.begin ());
       }
     }
     else
     {
       if (list[0]->is_true () && list[1]->is_false ())
       {
         if (list[2] == NULL)
           list[2] = list[0];
         if (list[3] == NULL)
           list[3] = list[1]; 
         list.erase (list.begin ());
         list.erase (list.begin ());        
       }
     }
   } 
   
   
   formula_list.clear ();
   formula_list.insert (formula_list.begin (), list.begin (), list.end ());
   */
   
   
 }
 
 bool 
 progression::compare (progression *p)
 {
   int i;
   bool until = true;
   bool release = true;
   switch (_type)
   {
     case OTHER:
       if (_formula->oper () == aalta_formula::Until)
       {
         for (i = 0; i < _formula_list.size (); i ++)
         {
           if (_formula_list[i] == NULL || p->_formula_list[i] == NULL)
             continue;
           if (i % 2 == 0)
           {
             if (_formula_list[i]->is_true ())
               return true;
             if (_formula_list[i]->is_false ())
               continue;
             if (p->_formula_list[i]->is_true ())
               return true;
             if (p->_formula_list[i]->is_false ())
               return false;
             if (_formula_list[i]->compare (p->_formula_list[i]))
               return true;
             else
               continue;
           }
           else
           {
             if (_formula_list[i]->is_false ())
               return false;
             if (_formula_list[i]->is_true ())
               continue;
             if (p->_formula_list[i]->is_true ())
               continue;
             if (p->_formula_list[i]->is_false ())
               return false;
             if (_formula_list[i]->compare (p->_formula_list[i]))
               continue;
             else 
               return false;
           }
         }
         return false;
       }
       else if (_formula->oper () == aalta_formula::Release)
       {
         for (i = 0; i < _formula_list.size (); i ++)
         {
           if (_formula_list[i] == NULL)
             continue;
           if (p->_formula_list[i] == NULL)
           {
             if (i % 2 == 0)
               return true;
             else 
               continue;
           }
           if (i % 2 == 0)
           {
             if (_formula_list[i]->is_true ())
               continue;
             if (_formula_list[i]->is_false ())
               return false;
             if (p->_formula_list[i]->is_false ())
               return false;
             if (p->_formula_list[i]->is_true ())
               return true;
             if (_formula_list[i]->compare (p->_formula_list[i]))
               continue;
             else
               return false;
           }
           else
           {
             if (_formula_list[i]->is_false ())
               continue;
             if (_formula_list[i]->is_true ())
               return true;
             if (p->_formula_list[i]->is_false ())
               continue;
             if (p->_formula_list[i]->is_true ())
               return true;
             if (_formula_list[i]->compare (p->_formula_list[i]))
               return true;
             else
               continue;
           }
         }
         return true;
       }
       else
       {
         if (p->_formula == aalta_formula::TRUE ())
           return true;
         else 
           return false;
       }
     case OR:
       if (p->is_true ())
         return true;
       if (p->is_false ())
         return false;
       if (_left->compare (p->_left) || _right->compare (p->_right))
         return true;
       else 
         return false;
     case AND:
       if (p->is_true ())
         return true;
       if (p->is_false ())
         return false;
       if (_left->compare (p->_left) && _right->compare (p->_right))
         return true;
       else 
         return false;
   }
   return false;
 }
 
 
 std::pair<bool, progression*> 
 progression::intersect (progression *p)
 {
   std::pair<bool, progression*> pa, pa1, pa2;
   int size, i;
   std::vector<progression*> formula_list;
   //assert (_type == p->_type);
   /*
   if(_type != p->_type)
   {
     pa = std::make_pair<bool, progression*> (false, p);
     return pa;
   }
   */
   if (p->is_true ())
     pa = std::make_pair<bool, progression*> (true, p);
   else if (p->is_false ())
     pa = std::make_pair<bool, progression*> (false, p);
   else
   {
   switch (_type)
   {
     case OTHER:
       ///////////for until formula
       if (_formula->oper () == aalta_formula::Until)
       {
         //to be done
         //assert (_formula == p->_formula);
         size = _formula_list.size () > p->_formula_list.size () ? p->_formula_list.size () : _formula_list.size ();
         for (i = 0; i < size; i ++)
         {
           if (i % 2 == 0)
           {
             if (_formula_list[i] == NULL || p->_formula_list[i] == NULL)
             {
               formula_list.push_back (progression (aalta_formula::FALSE ()).unique ());
               continue;
             }
             pa1 = _formula_list[i]->intersect (p->_formula_list[i]);
             formula_list.push_back (pa1.second);
             if (pa1.first)
             {
               formula_list.push_back (progression (aalta_formula::TRUE ()).unique ());  //make the size even
               pa = std::make_pair<bool, progression*> (true, progression (_formula, formula_list).unique ());
               break;
             }
           }
           else
           {
             if (_formula_list[i] == NULL || p->_formula_list[i] == NULL)
             {
               formula_list.push_back (progression (aalta_formula::TRUE ()).unique ());
               continue;
             }
             pa1 = _formula_list[i]->intersect (p->_formula_list[i]);
             formula_list.push_back (pa1.second);
             if (! pa1.first)
             {
               pa = std::make_pair<bool, progression*> (false, progression (_formula, formula_list).unique ());
               break;
             }
           }
         }
         if(i >= size)
           pa = std::make_pair<bool, progression*> (false, progression (_formula, formula_list).unique ());       
       }
       //////////////////for release formula
       else if (_formula->oper () == aalta_formula::Release)
       {
         //to be done
         //assert (_formula == p->_formula);

         size = _formula_list.size () > (p->_formula_list).size () ? (p->_formula_list).size () : _formula_list.size ();
         for (i = 0; i < size; i ++)
         {
           if (i % 2 == 0)
           {
             if (_formula_list[i] == NULL || p->_formula_list[i] == NULL)
             {
               formula_list.push_back (progression (aalta_formula::TRUE ()).unique ());
               continue;
             }
             pa1 = _formula_list[i]->intersect (p->_formula_list[i]);
             formula_list.push_back (pa1.second);
             if (! pa1.first)
             {
               formula_list.push_back (progression (aalta_formula::FALSE ()).unique ());  //make the size even
               pa = std::make_pair<bool, progression*> (false, progression (_formula, formula_list).unique ());
               break;
             }
           }
           else
           {
             if (_formula_list[i] == NULL || p->_formula_list[i] == NULL)
             {
               formula_list.push_back (progression (aalta_formula::FALSE ()).unique ());
               continue;
             }
             pa1 = _formula_list[i]->intersect (p->_formula_list[i]);
             formula_list.push_back (pa1.second);
             if (pa1.first)
             {
               pa = std::make_pair<bool, progression*> (true, progression (_formula, formula_list).unique ());
               break;
             }
           }
         }
         if(i >= size)
           pa = std::make_pair<bool, progression*> (true, progression (_formula, formula_list).unique ());
       }
       ///////////////for other formulas
       else
       {
         if (_formula->oper () == aalta_formula::True || p->_formula->oper () == aalta_formula::True)
           pa = std::make_pair<bool, progression*> (true, progression (aalta_formula::TRUE ()).unique ());
         else
           pa = std::make_pair<bool, progression*> (false, progression (aalta_formula::FALSE ()).unique ());
       }
       break;
     case OR:
       pa1 = _left->intersect (p->_left);
       pa2 = _right->intersect (p->_right);
       pa = std::make_pair<bool, progression*> (pa1.first || pa2.first, progression (OR, pa1.second, pa2.second).unique ());
       break;    
     case AND:
       /*
       i = 0;
       printf ("orig type: %d\n%s\n", _type, to_string(i).c_str ());
       i = 0;
       printf ("cur type: %d\n%s\n", p->_type, p->to_string(i).c_str ());
       assert (_left != NULL);
       assert (p != NULL);
       */
       pa1 = _left->intersect (p->_left);
       pa2 = _right->intersect (p->_right);
       pa = std::make_pair<bool, progression*> (pa1.first && pa2.first, progression (AND, pa1.second, pa2.second).unique ());
       break;
   }
   }
   return pa;
 }
 
 progression* 
 progression::unique ()
 {
   progf_set::iterator it = _all_progfs.find (this);
   if(it != _all_progfs.end ())
     return *it;
   else
   {
     progression *p = clone ();
     _all_progfs.insert (p);
     return p;
   }
 }
 
 progression* 
 progression::clone ()
 {
   progression *p = new progression (*this);
   if (p == NULL)
   {
     destroy ();
     printf ("Memory error!\n");
     exit (EXIT_FAILURE);
   }
   return p;
 }
 
 bool 
 progression::operator == (const progression &p) const 
 {
   if(_type == p._type && _formula == p._formula && _left == p._left && _right == p._right 
   && _formula_list.size () == p._formula_list.size ())
   {
     for(int i = 0; i < _formula_list.size (); i ++)
     {
       if (_formula_list[i] != p._formula_list[i])
         return false;
     }
     return true;
   }
   else
     return false;
 }
 
 std::string 
 progression::to_string (int &n)
 {
   std::string result = "";
   //for (int i = 0; i < n; i ++)
     //result += " ";
   //result += "\n";
   if (_type == OTHER)
   {
     if (_formula != NULL)
     {
       for (int i = 0; i < n; i ++)
         result += " ";
       result += _formula->to_string ();
     }
     if (! _formula_list.empty ())
     {
       result += "\n";
       for (int i = 0; i < n; i ++)
         result += " ";
       result += "  [\n";
       for (int i = 0; i < _formula_list.size (); i ++)
       {
         n = n + 1;
         if (_formula_list[i] != NULL)
           result += "  " + _formula_list[i]->to_string (n) + ",\n";
         else
         {
           for (int i = 0; i < n; i ++)
           result += " ";
           result += "  null, \n";
         }
         n = n - 1;
       }
       //result += "\n";
       for (int i = 0; i < n; i ++)
         result += " ";
       result += "  ]";
     }
     else
      result += "[]";
   }
   else
   {
     if (_type == OR)
     {
       result += _left->to_string (n) + "\n";
       for (int i = 0; i < n; i ++)
         result += " ";
       result += "   | \n  " + _right->to_string (n);
     }
     else
       {
       result += _left->to_string (n) + "\n";
       for (int i = 0; i < n; i ++)
         result += " ";
       result += "   & \n  " + _right->to_string (n);
     }
   }
   return result;
 }
 
 void 
 progression::print ()
 {
   int n = 0;
   printf ("%s\n", to_string (n).c_str ());
 }
 
 
 void 
 progression::hash ()
 {
   _hash = HASH_INIT;
   _hash = (_hash << 5) ^ (_hash >> 27) ^ (size_t)_type;
   _hash = (_hash << 5) ^ (_hash >> 27) ^ (size_t)_formula;
   _hash = (_hash << 5) ^ (_hash >> 27) ^ (size_t)_left;
   _hash = (_hash << 5) ^ (_hash >> 27) ^ (size_t)_right;
   _hash = (_hash << 5) ^ (_hash >> 27) ^ (size_t)_tt;
   _hash = (_hash << 5) ^ (_hash >> 27) ^ (size_t)_ff;
   
   std::vector<progression*>::iterator it;
   for(it = _formula_list.begin(); it != _formula_list.end (); it ++)
   {
     if((*it) != NULL)
     {
       _hash = (_hash << 5) ^ (_hash >> 27) ^ (size_t)(*it);
     }
   } 
 }
 
 void 
 progression::destroy ()
 {
   progf_set::iterator it;
   for(it = _all_progfs.begin (); it != _all_progfs.end (); it ++)
   {
     delete *it;
   }
 }
 
 

