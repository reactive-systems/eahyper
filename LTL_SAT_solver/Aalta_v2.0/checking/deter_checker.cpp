 /* 
 * The checker structure
 * 
 * File:   checker.cpp
 * Author: Jianwen Li
 * 
 *
 * Created on October 21, 2014
 */
 
 #include "checker.h"
 #include "formula/aalta_formula.h"
 #include "util/utility.h"
 #include <iostream>
 #include <stdio.h>
 #include <stdlib.h>
 
 using namespace std;
 
 
 std::vector<check_deter_state*> checker::_visited;
 aalta_formula::af_prt_set checker::_explored;
 std::vector<check_deter_state*> checker::_all_sts;
 
 checker::checker (aalta_formula *af)
 {
   _input = af;
 }
 checker::~checker ()
 {
   for(int i = 0; i < _all_sts.size (); i ++)
   {
     delete _all_sts[i];
   }
   progression::destroy ();
 }
 
 bool 
 checker::check ()
 {
   if (_input == aalta_formula::TRUE ())
     return true;
   if (_input == aalta_formula::FALSE ())
     return false;
   bool result = false;
   progression *cur = progression (_input).unique ();
   check_deter_state *s = new check_deter_state (cur, _input);
   _visited.push_back (s);
   _all_sts.push_back (s);
   return dfs ();
 }
 
 bool 
 checker::dfs ()
 {
   check_deter_state *s = _visited.back ();
   aalta_formula *f = s->get_formula ();
   progression *p = s->get_progf ();
   
   //printf ("%s\n", f ->to_string ().c_str ());
   
   
   aalta_formula *c = f->cf ();        
   aalta_formula::af_prt_set P;
   progression *nxt, *orig;
   aalta_formula *next, *neg;
   
   while (true)
   {
     P = c->SAT ();  
     //print (P);              
     if(P.empty ())
     {
       _visited.pop_back ();
       _explored.insert (f);
       return false;
     }
     
     f->complete (P);
     //print (P);
     
     nxt = p->progf (P);
     //nxt->print ();
     next = nxt->to_formula ();
     

     //printf ("%s\n\n\n", next->to_string ().c_str ());

     orig = find (_visited, next);
     if(orig != NULL)
     {
       if (model (orig, nxt))          
         return true;
     }
     else
     {
       if (_explored.find (next) == _explored.end ())
       {
         check_deter_state *st = new check_deter_state (nxt, next);
         _visited.push_back (st);
         _all_sts.push_back (st);
         if(dfs ())
           return true;
       }
     }
     neg = negation (P);           
     if (neg->oper () == aalta_formula::False)
       c = neg;
     else
       c = aalta_formula (aalta_formula::And, c, neg).unique ();
   }
   return false;
 }
 
 progression* 
 checker::find (std::vector<check_deter_state*> visited, aalta_formula *f)
 {
   int size = visited.size () - 1;
   for (int i = size; i >=0; i --)
   {
     if (f == visited[i]->get_formula ())
       return visited[i]->get_progf ();
   }
   return NULL;
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
       f = aalta_formula (aalta_formula::Not, NULL,*it).unique ();
       result = aalta_formula (aalta_formula::Or, result, f).unique ();
     }
   }
   return result;
 }
 
 bool 
 checker::model (progression *p1, progression *p2)
 { 
   return p1->compare (p2);
   /*
   std::pair<bool, progression*> pa = p1->intersect (p2);
   if (pa.first)
     return true;
   return false;
   */
   
    /*TO BE DONE: scc checking, or can prove only cycle checking is enough?
    std::pair<bool, progression*> pa;
    pa = p1->intersect (p2);                      //to be done
    if (pa.first)
      return true; 
    aalta_formula *inv = pa->to_inv_formula ();
    progf_set pset;
    af_progf_map::iterator it = _visited_map.find (inv);
    if (it == _visited.end ())
    {
      pset.insert (pa.second);
      _visited_map.insert (std::pair<aalta_formula*, progf_set>(inv, pset));
      return false;
    }
    else
    {
      pset = it->second;
      progression *p = pa.second;
      progf_set::iterator iter;
      progf_set temp_set;
      for (iter = pset.begin ();  iter != pset.end (); iter ++)
      {
        pa = p->intersect (*iter);
        if(pa.first)
        {
          if (find_evindence (pa.second))             //to be done
            return true;
          continue;                                   //the evidence is fake
        }
        temp_set.insert (pa.second);
      }
      pset.insert (temp_set.begin (), temp_set.end ());
      _visited_map.erase (it);
      _visited_map.insert (std::pair<aalta_formula*, progf_set>(inv, pset))
    }
    return false;
   */
 }
 
 void 
 checker::print (aalta_formula::af_prt_set P)
 {
   aalta_formula::af_prt_set::iterator it;
   for(it = P.begin (); it != P.end (); it ++)
   {
     printf ("%s,", (*it)->to_string().c_str());
   }
   printf ("\n");
 }
 
 
 
 
