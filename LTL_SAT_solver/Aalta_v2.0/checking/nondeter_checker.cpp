/* 
 * The nondeterministic checker structure
 * 
 * File:   nondeter_checker.cpp
 * Author: Jianwen Li
 * 
 *
 * Created on November 15, 2014
 */
 
 #include "nondeter_checker.h"
 #include "formula/olg_formula.h"
 #include <stdio.h>
 #include <iostream>
 #include <stdlib.h>
 #include <assert.h>
 
 using namespace std;
 
 std::vector<aalta_formula::af_prt_set> nondeter_checker::_visited_edges;
 std::vector<aalta_formula*> nondeter_checker::_visited;
 aalta_formula::af_prt_set nondeter_checker::_explored;
 nondeter_checker::formula_int_map nondeter_checker::_formula_ints;
 int nondeter_checker::_satisfied_pos = 0;
 int nondeter_checker::_next_satisfied_pos = 0;
 
 bool nondeter_checker::_start = true;
 
 
 nondeter_checker::nondeter_checker (aalta_formula *f) : checker (f)
 {
   _unsat_pos = -1;
   _input = seperate_next (_input);
 }
 
 aalta_formula* 
 nondeter_checker::seperate_next (aalta_formula *f)
 {
   aalta_formula *res, *res1, *res2, *f1, *f2;
   if (f->oper() == aalta_formula::Next)
   {
     if (f->r_af ()->oper () == aalta_formula::And || f->r_af ()->oper () == aalta_formula::Or)
     {
       f1 = aalta_formula (aalta_formula::Next, NULL, f->r_af()->l_af()).unique ();
       f2 = aalta_formula (aalta_formula::Next, NULL, f->r_af()->r_af()).unique ();
       res1 = seperate_next (f1);
       res2 = seperate_next (f2);
       res = aalta_formula (f->r_af()->oper(), res1, res2).unique ();
     }
     else if (f->r_af ()->oper () == aalta_formula::Next)
     {
       res = seperate_next (f->r_af ());
       res = nondeter_prog_state::apply_next (res);
     }
     else
     {
       res = seperate_next (f->r_af ());
       res = aalta_formula (aalta_formula::Next, NULL, res).unique ();
     }
   }
   else
   {
     if (f->l_af () != NULL)
     { 
       assert (f->r_af () != NULL);
       f1 = seperate_next (f->l_af ());
       f2 = seperate_next (f->r_af ());
       res = aalta_formula (f->oper (), f1, f2).unique ();
     }
     else
     {
       if (f->r_af () != NULL)
       {
         f2 = seperate_next (f->r_af ());
         res = aalta_formula (f->oper (), NULL, f2).unique ();
       }
       else
         res = f;
     }
   }
   return res;
 }
 
 nondeter_checker::~nondeter_checker ()
 {
   for (int i = 0; i < _sccs.size (); i ++)
     _sccs[i]->destroy ();
   scc_transition::destroy ();
   _visited.clear ();
   _visited_edges.clear ();
   _explored.clear ();
 }
 
 int nondeter_checker::count = 0;
 
 bool 
 nondeter_checker::check ()
 {
   if (_input == aalta_formula::TRUE ())
     return true;
   else if (_input == aalta_formula::FALSE ())
     return false;
   else 
   {
   
     {
       olg_formula olg (_input);
       if (olg.sat ())
         return true;
       if (olg.unsat ())
         return false;
     }
     
     _visited.push_back (_input);
     _formula_ints.insert (pair<aalta_formula*, int> (_input, 0));
     //printf ("%s\n\n", _input->to_string().c_str ());
     return dfs ();
   }
 }
 
 bool 
 nondeter_checker::dfs ()
 {
   aalta_formula *f, *pf, *cf, *nx, *neg;
   aalta_formula::af_prt_set P;
   //printf ("count = %d, begin dfs\n", count++);
   
   {
     f = _visited.back ();
     if (f == aalta_formula::TRUE ())
       return true;
     if (f == aalta_formula::FALSE ())
     {
       _visited.pop_back ();
       return false;
     }
     
     nondeter_prog_state *pgst = new nondeter_prog_state (f);
       
     set_next_wanted (f);
     
     
     std::pair<aalta_formula::af_prt_set, aalta_formula*> pa = pgst->get_next_pair (_visited.size ());

     while ((!pa.first.empty ()) || (pa.second != aalta_formula::FALSE ()))
     {  
       //printf ("pa.first is:\n");
       //print (pa.first);
       
       aalta_formula *temp = nondeter_prog_state::erase_global (pa.second);
       /*
       if (temp != NULL)
         printf ("pa.second is:\n%s\n", temp->to_string ().c_str ());
       else
         printf ("pa.second is:\n%s\n", (pa.second)->to_string ().c_str ());
       */
       
       _visited_edges.push_back (pa.first);
       nx = pa.second;
       if (_explored.find (nx) == _explored.end ())
       {
         int pos = visited (nx);
         if (pos >= 0)
         {
           if (model (pos))
           {
             delete pgst;
             return true;
           } 
         }
         //else
         {
           _visited.push_back (nx);
           if (dfs ())
           {
             delete pgst;
             return true;
           }      
               
         }
       }
       
       _visited.pop_back ();
       if (_visited.size ()-1 < _next_satisfied_pos)
         _next_satisfied_pos --;
       _visited_edges.pop_back ();
       formula_int_map::iterator it = _formula_ints.find (nx);
       if (it != _formula_ints.end ())
         _formula_ints.erase (it);
       
       if (_explored.find (f) != _explored.end ())
       {
         delete pgst;
         //printf ("count = %d, false, return back\n", count --);
         return false;
       }
       
       
       pa = pgst->get_next_pair (_visited.size ());
       //printf ("_visisted size: %d\n", _visited.size ());
       //printf ("_visited_edges size: %d\n", _visited_edges.size ());
     }

     delete pgst;
     
   }
   //printf ("count = %d, false, return back\n\n\n", -- count);
   return false;
 }
 
 int nondeter_checker::compute_next_wanted_count_ = 0;
 void 
 nondeter_checker::set_next_wanted (aalta_formula *f)
 {
   if (_start)
   {
     nondeter_prog_state::initial_unsatisfied (_input);
     _start = false;
   }
   if (nondeter_prog_state::unsatisfied ().empty () && !nondeter_prog_state::no_until_fulfilled ())
   {
     compute_next_wanted_count_ ++;
     
     //if set_next_wanted has been computed for 10 times but still not get the satisfying model,  
     //then decline this heuristics.
     if (compute_next_wanted_count_ <= 10)
     {
       //if (_satisfied_pos != _next_satisfied_pos)
       //printf ("_satisfied_pos is %d\n_next_satisfied_pos is %d\n", _satisfied_pos, _next_satisfied_pos);
       aalta_formula *flat = f->flatted ();
       _satisfied_pos = _next_satisfied_pos;
       _next_satisfied_pos = _visited.size () - 1;
       aalta_formula *f = get_next_wanted (flat);
       //assert (f == NULL)
       //f = nondeter_prog_state::convert_to_formula (nondeter_prog_state::global ());
       set_solver_next_computed (f);
     }
   }
 }
 
 aalta_formula* 
 nondeter_checker::get_next_wanted (aalta_formula *flat)
 {
   aalta_formula::af_prt_set P = get_nexts (flat);
   aalta_formula *res = NULL;
   aalta_formula *nx;
   //printf ("_satisfied_pos is %d\n", _satisfied_pos);
   for (int i = _satisfied_pos; i >= 0; i--)
   {
     nx = get_next_formula (_visited[i], P);
     if (nx != NULL)
     {
       if (res == NULL)
         res = nx;
       else
         res = aalta_formula (aalta_formula::Or, res, nx).unique ();
     }
   }
   return res;
 }
 
 aalta_formula::af_prt_set 
 nondeter_checker::get_nexts (aalta_formula *flat)
 {
   aalta_formula::af_prt_set P, P1, P2;
   if (flat->oper () == aalta_formula::Next)
   {
     aalta_formula *r = flat->r_af();
     if (r->oper () == aalta_formula::Release && r->l_af () == aalta_formula::FALSE ())
     {
     }
     else
       P.insert (flat);
   }
   else if (flat->oper () == aalta_formula::And || flat->oper () == aalta_formula::Or)
   {
     P1 = get_nexts (flat->l_af ());
     P2 = get_nexts (flat->r_af ());
     P.insert (P1.begin (), P1.end ());
     P.insert (P2.begin (), P2.end ());
   }
   return P;
 }
 
 aalta_formula* 
 nondeter_checker::get_next_formula (aalta_formula *f, aalta_formula::af_prt_set& P)
 {
   aalta_formula::af_prt_set P2, P3, P4;
   P2 = f->to_set ();
   aalta_formula *nx;
   for (aalta_formula::af_prt_set::iterator it = P2.begin (); it != P2.end (); it ++)
   {
     nx = aalta_formula (aalta_formula::Next, NULL, *it).unique ();
     if (P.find (nx) == P.end ())
     {
       if ((*it)->oper () == aalta_formula::Release && (*it)->l_af () == aalta_formula::FALSE ())
         continue;
       else
       {
         if ((*it)->oper () > aalta_formula::Undefined || (*it)->oper () == aalta_formula::Not)
           P3.insert (nx);
         else
         {
           //printf ("does not find: %s\n", nx->to_string ().c_str ());
           return NULL;
         }
       }
     }
     else
       P3.insert (nx);
   }
   
   aalta_formula *not_want = NULL;
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
   {
     if (P3.find (*it) == P3.end ())
     {
       if (not_want == NULL)
         not_want = aalta_formula (aalta_formula::Not, NULL, *it).unique ();
       else 
         not_want = aalta_formula (aalta_formula::And, not_want, aalta_formula (aalta_formula::Not, NULL, *it).unique ()).unique ();
       //P4.insert (aalta_formula (aalta_formula::Not, NULL, *it).unique ());
     }
   }
   
   aalta_formula *want;
   want = nondeter_prog_state::convert_to_formula (P3);
   //not_want = nondeter_prog_state::convert_to_formula (P4);
   aalta_formula *res;
   if (want == NULL)
     res = not_want;
   else if (not_want == NULL)
     res = want;
   else
     res = aalta_formula (aalta_formula::And, want, not_want).unique ();

   return res;   
 }
 
 void 
 nondeter_checker::set_solver_next_computed (aalta_formula *f)
 {
   //printf ("set _next_wanted\n");
   //assert (f != NULL);
   nondeter_prog_state::set_next_wanted (f);
 }
 
 void 
 nondeter_checker::confirm_explored ()
 {
 /*
   aalta_formula::af_prt_set P = nondeter_prog_state::get_potential ();
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
     update_explored (*it);
     */
 }
 
 void 
 nondeter_checker::update_explored (aalta_formula *f)
 {
  /*
   if (_explored.find (f) == _explored.end ())
   {
     nondeter_prog_state::update_unsat (f);
     _explored.insert (f);
   }
   */
 }
 
 void 
 nondeter_checker::update_scc (scc* sc)
 { 
   std::vector<scc*> merges, unmerges, news;
   
   //printf ("will add scc: \n");
   //sc->print ();
   //printf ("existed sccs:\n");
   for (int i = 0; i < _sccs.size (); i ++)
   {
     //_sccs[i]->print ();
     if (_sccs[i]->contain (sc->root ()->get_id ()) || sc->contain (_sccs[i]->root ()->get_id ()))
       merges.push_back (_sccs[i]);
     else
       unmerges.push_back (_sccs[i]);
   }
   scc *sc2 = sc;
   scc *sc3 = sc;
   for (int i = 0; i < merges.size (); i ++)
   {
     sc2 = sc2->merge (merges[i]);
     news.push_back (sc2);
   }
   if (!news.empty ())
   {
     news.pop_back ();
     sc3->destroy ();
   }
   _sccs.clear ();
   _sccs.push_back (sc2);
   //printf ("updated scc:\n");
   //sc2->print ();
   for (int i = 0; i < unmerges.size (); i ++)
     _sccs.push_back (unmerges[i]);
   
   for (int i = 0; i < merges.size (); i ++)
     merges[i]->destroy ();
   for (int i = 0; i < news.size (); i ++)
     news[i]->destroy ();
   
   merges.clear();
   unmerges.clear();
   news.clear ();
 }
 
 int 
 nondeter_checker::visited (aalta_formula *f)
 {
   formula_int_map::iterator it = _formula_ints.find (f);
   if (it != _formula_ints.end ())
     return it->second;
   else
     _formula_ints.insert (pair<aalta_formula*, int> (f, _visited.size ()));
   /*
   for (int i = _visited.size ()-1; i >= 0; i --)
   {
     if (_visited[i] == f)
     {
       //update_scc (i);
       return i;
     }
   }
   */
   return -1;
 }
 
 bool 
 nondeter_checker::model (int pos)
 {
   aalta_formula::af_prt_set P, P2;
   for (int i = pos; i < _visited_edges.size (); i ++)
   {
     P2 = collect_until (_visited_edges[i]);
     P.insert (P2.begin (), P2.end ());
   }
   //printf ("nondeter_checker::model: satisfied are:\n");
   //checker::print (P);
   if (_visited[pos]->model_until (P))
     return true;
   return false;
 }
 
 aalta_formula::af_prt_set 
 nondeter_checker::collect_until (aalta_formula::af_prt_set P)
 {
   aalta_formula::af_prt_set res;
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
   {
     if ((*it)->is_until_marked ())
       res.insert (*it);
   }
   return res;
 }
 
 bool 
 nondeter_checker::unsat_of_core (aalta_formula* f, aalta_formula::af_prt_set P)
 {
   aalta_formula::af_prt_set::iterator it;
   aalta_formula::af_prt_set P2;
   aalta_formula *pf;
   for (it = P.begin (); it != P.end (); it ++)
   {
     pf = aalta_formula (aalta_formula::And, f, *it).unique ();
     pf = pf->flatted ();
     P2 = pf->SAT ();
     if (!P2.empty ())
       return false;
   }
   return true;
 }
 
 void 
 nondeter_checker::show_evidence ()
 {
 /*
   aalta_formula *root = _scc->root ();
   aalta_formula *f;
   for (int i = 0; i < _visited.size()-1; i ++)
   {
     f = _visited[i]->normal ();
     if (f == root)
       break;
     print (_visited_edges[i]);
     printf (", ");
   }
   _scc->print ();
   */
 }
 
 
 
