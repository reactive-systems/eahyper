/* 
 * scc structure
 * 
 * File:   scc.h
 * Author: Jianwen Li
 * 
 *
 * Created on November 16, 2014
 */
 
 #include "scc.h"
 #include "progression/nondeter_prog_state.h"
 #include "checking/checker.h"
 #include <iostream>
 #include <stdio.h>
 #include <stdlib.h>
 #include <assert.h>
 #include <stdio.h>
 #include <string>
 
 using namespace std;
 
 
 
 scc_transition::scc_tran_set scc_transition::_trans;
 
 scc_transition::scc_transition (aalta_formula::af_prt_set P, scc_state* st)
 {
   _edge = P;
   _dest = st->get_id ();
   hash ();
 }
 
 scc_transition::scc_transition (const scc_transition &orig)
 {
   *this = orig;
 }
 
 scc_transition* 
 scc_transition::unique ()
 {
   scc_tran_set::iterator it = _trans.find (this);
   if (it != _trans.end ())
     return *it;
   else
   {
     scc_transition *t = clone ();
     _trans.insert (t);
     return t;
   }
 }
 
 
 bool 
 scc_transition::operator == (const scc_transition& scct)const
 {
 
   if (_edge.size () != scct._edge.size ())
     return false;

   aalta_formula::af_prt_set::const_iterator it, it2;
   it2 = scct._edge.begin ();
   for (it = _edge.begin (); it != _edge.end (); it ++)
   {
     if ((*it) != (*it2))
       return false;
     it2 ++;
   }
   
   if (_dest != scct._dest)
     return false;
   return true;
 }
 
 scc_transition* 
 scc_transition::clone ()
 {
   scc_transition *t = new scc_transition (*this);
   if (t == NULL)
    {
      printf ("scc_transition::clone: Memory error!");
      exit (1);
    }
  return t;
 }
 
 void 
 scc_transition::hash ()
 {
   _hash = HASH_INIT;
   aalta_formula::af_prt_set::iterator it;
   for (it = _edge.begin (); it != _edge.end (); it ++)
     _hash = (_hash << 5) ^ (_hash >> 27) ^ (*it)->hash ();
   
   _hash = (_hash << 5) ^ (_hash >> 27) ^ (size_t) _dest;
 }
 
 void 
 scc_transition::print ()
 {
   std::string str = "{";
   aalta_formula::af_prt_set::iterator it;
   for (it = _edge.begin (); it != _edge.end (); it ++)
     str += (*it)->to_string () + ", ";
   str += "}";
   printf ("%s -> %d\n", str.c_str (), _dest);
 }
 
 void 
 scc_transition::destroy ()
 {
   scc_tran_set::iterator it;
   for (it = _trans.begin (); it != _trans.end (); it ++)
     delete *it;
 }
 
 int scc_state::_max_id = 0;
 //std::vector<scc_state*> scc_state::_sts;
 scc_state::formula_id_map scc_state::_formula_ids;
 
 scc_state::scc_state (aalta_formula* f)
 {
   _formula = f;
   formula_id_map::iterator it = _formula_ids.find (f);
   if (it != _formula_ids.end ())
     _id = it->second;
   else 
   {
     _id = _max_id ++;
     _formula_ids.insert (std::pair<aalta_formula*, int> (f, _id));
   }
   //_sts.push_back (this);
 }
 
 scc_state::scc_state (scc_transition::scc_tran_set trans, aalta_formula *f)
 {
   _formula = f;
   formula_id_map::iterator it = _formula_ids.find (f);
   if (it != _formula_ids.end ())
     _id = it->second;
   else 
   {
     _id = _max_id ++;
     _formula_ids.insert (std::pair<aalta_formula*, int> (f, _id));
   }
   _trans = trans;
 }
 
 scc_state::scc_state (const scc_state &orig)
 {
   *this = orig;
 }
 
 scc_state* 
 scc_state::clone ()
 {
   scc_state *st = new scc_state (*this);
   return st;
 }
 
 void 
 scc_state::add_transition (scc_transition *t)
 {
   _trans.insert (t);
 }
 
 scc_state* 
 scc_state::merge (scc_state *st)
 {
   scc_state *result;
   scc_transition::scc_tran_set trans;
   scc_transition::scc_tran_set::iterator it;
   for (it = _trans.begin(); it != _trans.end (); it ++)
     trans.insert (*it);
   for (it = st->_trans.begin (); it != st->_trans.end (); it ++)
     trans.insert (*it);
     
   result = new scc_state (trans, _formula);
   return result;
 }
 
 void 
 scc_state::print ()
 {
   printf ("id: %d\n", _id);
   printf ("formula: %s\n", _formula->to_string().c_str ());
   scc_transition::scc_tran_set::iterator it;
   for (it = _trans.begin(); it != _trans.end (); it ++)
     (*it)->print ();
   
 }
 
 void 
 scc_state::destroy ()
 {
   delete this;
 }
 
 aalta_formula::af_prt_set 
 scc::get_mark_untils (aalta_formula::af_prt_set P)
 {
   aalta_formula::af_prt_set result;
   aalta_formula::af_prt_set::iterator it;
   for (it = P.begin (); it != P.end (); it ++)
   {
     if ((*it)->is_until_marked ())
       result.insert (*it);
   }
   return result;
 }
 
 scc::scc (std::vector<aalta_formula*> states, std::vector<aalta_formula::af_prt_set> edges)
 {
   //assert (states.size () == edges.size ());
   if (states.size () != edges.size ())
   {
     printf ("states and edges sizes are not equal: \n");
     //printf ("states: %d\n", states.size ());
     //printf ("edges: %d\n", edges.size ());
     exit (0);
   }
   scc_state *st;
   std::vector<scc_state*> sts;
   for (int i = 0; i < states.size (); i ++)
   {
     st = new scc_state (states[i]);
     sts.push_back (st);
   }
   scc_transition *t;
   for (int i = 0; i < sts.size (); i ++)
   {
     if (i == sts.size ()-1)
       t = scc_transition (edges[i], sts[0]).unique ();
     else
       t = scc_transition (edges[i], sts[i+1]).unique ();
     sts[i]->add_transition (t);
     _state_map.insert (pair <int, scc_state*> (sts[i]->get_id (), sts[i]));
   }
   
   aalta_formula::af_prt_set P;
   for (int i = 0; i < edges.size (); i ++)
   {
     P = get_mark_untils (edges[i]);
     _satisfied_untils.insert (P.begin (), P.end ());
   }
   _root = sts[0];
   _cores = set_cores ();
   _unsatisfied = set_unsatisfied ();
 }
 
 scc::scc (scc_state* root, hash_map<int, scc_state*> state_map, aalta_formula::af_prt_set satisfied_untils)
 {
   _root = root;
   _state_map = state_map;
   _satisfied_untils = satisfied_untils;
   _cores = set_cores ();
   _unsatisfied = set_unsatisfied ();
 }
 
 aalta_formula::af_prt_set  
 scc::set_cores ()
 {
   hash_map<int, scc_state*>::iterator it;
   aalta_formula::af_prt_set P, P1, P2;
   P = _root->get_formula ()->to_set ();
   for (it = _state_map.begin (); it != _state_map.end (); it ++)
   {
     //P1.insert (P.begin (), P.end ());
     P1 = it->second->get_formula ()->to_set ();
     P2.clear ();
     for (aalta_formula::af_prt_set::iterator it = P1.begin (); it != P1.end (); it ++)
     {
       if (P.find (*it) != P.end ())
         P2.insert (*it);
     }
     //P1.erase (P2.begin (), P2.end ());
     //P.erase (P1.begin(), P1.end ());
     P.clear ();
     P.insert (P2.begin (), P2.end ());
   }
   
   return P;
 }
 

 aalta_formula* 
 scc::get_core_false ()
 {
   aalta_formula::af_prt_set P;
   aalta_formula *f;
   for (aalta_formula::af_prt_set::iterator it = _cores.begin (); it != _cores.end (); it ++)
   {
     f = aalta_formula (aalta_formula::Next, NULL, *it).unique ();
     P.insert (f);
   }
   aalta_formula *f2 = nondeter_prog_state::convert_to_formula (P);
   f2 = aalta_formula (aalta_formula::Not, NULL, f2).unique ();
   return f2;
 }
 
 aalta_formula::af_prt_set 
 scc::set_unsatisfied ()
 {
   aalta_formula::af_prt_set P, P2; 
   for (aalta_formula::af_prt_set::iterator it = _cores.begin (); it != _cores.end (); it ++)
   {
     if ((*it)->oper () == aalta_formula::Until)
       P.insert (*it);
   }
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
   {
     if (_satisfied_untils.find (*it) == _satisfied_untils.end ())
       P2.insert (*it);
   }
   //P.erase (_satisfied_untils.begin (), _satisfied_untils.end ());
   return P2;
 }
 
 bool 
 scc::unsat_core ()
 {
   return false;
  /*
   aalta_formula *f = nondeter_prog_state::convert_to_formula (_cores);
   printf ("scc core: \n");
   printf ("%s\n", f->to_string ().c_str ());
   aalta_formula *pf = f->flatted ();
   aalta_formula::af_prt_set P2 = nondeter_prog_state::get_false_next (pf, _cores);
   aalta_formula *f2 = nondeter_prog_state::convert_to_formula (P2);
   f2 = aalta_formula (aalta_formula::Not, NULL, f2).unique ();
   
   aalta_formula *f3 = aalta_formula (aalta_formula::And, pf, f2).unique ();
   if ((f3->SAT ()).empty ())
     return true;
   return false;
   */

 }
 
 scc* 
 scc::merge (scc *sc)
 {
   int root_id = _root->get_id () <= sc->_root->get_id () ? _root->get_id() : sc->_root->get_id ();
   hash_map<int, scc_state*> state_map;
   hash_map<int, scc_state*>::iterator it, it2;
   for (it = sc->_state_map.begin (); it != sc->_state_map.end (); it ++)
   {
     it2 = _state_map.find (it->first);
     if (it2 != _state_map.end ())
     {
       scc_state *st = (it2->second)->merge (it->second);
       state_map.insert (pair<int, scc_state*> (it->first, st));
     }
     else
       state_map.insert (pair<int, scc_state*> (it->first, it->second->clone ()));
   }
   for (it = _state_map.begin (); it != _state_map.end (); it ++)
   {
     it2 = state_map.find (it->first);
     if (it2 == state_map.end ())
       state_map.insert (pair<int, scc_state*> (it->first, it->second->clone ()));
   }
   it = state_map.find (root_id);
   if (it == state_map.end ())
   {
     //printf ("root id: %d\nAnother root id: %d\n", _root->get_id (), sc->_root->get_id ());
     //for (it2 = state_map.begin(); it2 != state_map.end(); it2 ++)
       //printf ("%d\n", it2->first);
     printf ("Error at scc::merge: Cannot find root!\n");
     exit (0);
   }
   scc_state* root = it->second;
   aalta_formula::af_prt_set satisfied_untils;
   satisfied_untils.insert (_satisfied_untils.begin(), _satisfied_untils.end ());
   satisfied_untils.insert (sc->_satisfied_untils.begin(),sc-> _satisfied_untils.end ());
   scc* result = new scc (root, state_map, satisfied_untils);
   
   return result;
 }
 
 bool 
 scc::contain (int id)
 {
   hash_map<int, scc_state*>::iterator it;
   it = _state_map.find (id);
   if (it != _state_map.end ())
     return true;
   return false;
 }
 
 /*
 aalta_formula* 
 scc::normal (aalta_formula *f)
 {
  aalta_formula *result, *f1, *f2;
  if (f->oper () == aalta_formula::And)
  {
    f1 = normal (f->l_af ());
    f2 = normal (f->r_af ());
    if (f1 == aalta_formula::TRUE ())
      result = f2;
    else if (f2 == aalta_formula::TRUE ())
      result = f1;
    else
      result = aalta_formula (aalta_formula::And, f1, f2).unique ();
  }
  else
  {
    if (f->oper () > aalta_formula::Undefined)
    {
      string str = aalta_formula::get_name(f->oper ());
      if (str.find ("FOR_UNTIL_") != string::npos)
        result = aalta_formula::TRUE ();
      else
        result = f;
    }
    else
      result = f;
  }
  return result;
 }
 
 void 
 scc::add_cycle (std::vector<aalta_formula*> states, std::vector<aalta_formula::af_prt_set> edges)
 {
   hash_map<aalta_formula*, scc_state*, aalta_formula::af_prt_hash>::iterator it, it2;
   scc_state *s, *st;
   aalta_formula *f, *f2;
   aalta_formula::af_prt_set P, P2;
   int i;
     
   //_root = states[0]->normal ();
   
   for (i = 0; i < states.size (); i ++)
   {
     f = normal (states[i]);
     //if (_root == NULL)
       //_root = f->unique ();
     P2 = states[i]->get_until_flags ();
     P.insert (P2.begin (), P2.end ());
     it = _formula_state_map.find (f);
     if (it != _formula_state_map.end ())
       break;
     
   }

   if (i >= states.size ())
   {
     _formula_state_map.clear ();
     _satisfied_untils.clear ();
     _root = normal (states[0]);
   }
   
   
   for (i=0; i < states.size (); i ++)
   {
     f = normal (states[i]);
     it = _formula_state_map.find (f);
     if (it != _formula_state_map.end ())
     {
       s = it->second;
     }
     else
     {
       s = new scc_state (f);
       _formula_state_map.insert (pair<aalta_formula*, scc_state*> (f, s));
     }
     
     if (i == states.size ()-1)
     {
       f2 = normal (states[0]);
       it2 = _formula_state_map.find (f2);
       if (it2 == _formula_state_map.end ())
       {
         st = new scc_state (f2);
         _formula_state_map.insert (pair<aalta_formula*, scc_state*> (f2, st));
       }
       else
         st = it2->second;
     }
     else
     {
       f2 = normal (states[i+1]);
       st = new scc_state (f2);
       _formula_state_map.insert (pair<aalta_formula*, scc_state*> (f2, st));
     }       
     s->add_transition (edges[i], st);
   }
   
   _satisfied_untils.insert (P.begin (), P.end ());
   
   
 }
 */
 
 void 
 scc::print ()
 {
   printf ("root id is: %d\n", _root->get_id ());
   hash_map<int, scc_state*>::iterator it;
   for (it = _state_map.begin (); it != _state_map.end (); it ++)
   {
     (it->second)->print ();
     printf ("\n");
   }
   printf ("Satisfied:\n");
   checker::print (_satisfied_untils);
 }
 
 void 
 scc::destroy ()
 {
   hash_map<int, scc_state*>::iterator it;
   for (it = _state_map.begin (); it != _state_map.end (); it ++)
     it->second->destroy ();
   delete this;
 }
 
 
 
 
 
