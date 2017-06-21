 /* 
 * nondeterministic formula progression structure 
 * 
 * File:   nondeter_prog_state.cpp
 * Author: Jianwen Li
 * 
 *
 * Created on November 14, 2014
 */
 
 #include "nondeter_prog_state.h"
 #include "checking/checker.h"
 #include <iostream>
 #include <assert.h>
 #include <stdio.h>
 #include <stdlib.h>
 
 using namespace std;
 
 aalta_formula::af_prt_set nondeter_prog_state::_unsatisfied;
 aalta_formula::af_prt_set nondeter_prog_state::_unsatisfied_untils;

 aalta_formula* nondeter_prog_state::_avoid = NULL;

 
 bool nondeter_prog_state::_global_not_set = true;
 aalta_formula::af_prt_set nondeter_prog_state::_globals;
  //for implementation reason, _invariant_found is used to flag the current constraint is an invariant so as to be 
  //considered to be unsat
 bool nondeter_prog_state::_invariant_found = false;
 aalta_formula* nondeter_prog_state::_next_wanted = NULL;
 //for implementation reason, _fulfilled is used to flag _unsatisfied is indeed eliminated
 //rather than is originally empty
 bool nondeter_prog_state::_fulfilled = false;
 
 void 
 nondeter_prog_state::set_unsatisfied_untils ()
 {
   _unsatisfied_untils.clear ();
   for (aalta_formula::af_prt_set::iterator it = _unsatisfied.begin (); it != _unsatisfied.end (); it ++)
   {
     _unsatisfied_untils.insert ((*it)->get_until ());
   }
 }
 
 void 
 nondeter_prog_state::initial_unsatisfied (aalta_formula *f)
 {
    _unsatisfied = get_until_element_of (f);
    set_unsatisfied_untils ();
 }
 
 nondeter_prog_state::nondeter_prog_state (aalta_formula *f)
 {
   _formula = f;
   _flatted_formula = f->flatted ();
   //_avoid = NULL;
   _constraints = NULL;
   //add_constraint ();
   _assignments = NULL;
   //_all_progfs.push_back (this);
   if (_global_not_set)
   {
     set_global ();
     _global_not_set = false;
   }
   
   //must after set_global ()
   set_avoid ();
   set_input_flatted ();
 }
 
 void 
 nondeter_prog_state::set_avoid ()
 {
   if (_avoid == NULL)
   {
     aalta_formula::af_prt_set P = _formula->get_alphabet ();
     //checker::print (P);
     _avoid = avoid_next_false (P);
         
     aalta_formula *global = global_next_true ();
     if (global != NULL)
       _avoid = aalta_formula (aalta_formula::And, _avoid, global).unique ();
       
     global = global_next_n_true ();
     if (global != NULL)
       _avoid = aalta_formula (aalta_formula::And, _avoid, global).unique ();
     
     //printf ("%s\n", _avoid->to_string ().c_str ());
   }
 }
 
 aalta_formula* 
 nondeter_prog_state::global_next_n_true ()
 {
   hash_map<aalta_formula*, std::set<int>, aalta_formula::af_prt_hash > next_deeps;
   get_next_deep_map (next_deeps);
   hash_map<aalta_formula*, std::set<int>, aalta_formula::af_prt_hash >::iterator it, it2;
   aalta_formula *f1, *f2, *res = NULL, *f3;
   for (it = next_deeps.begin (); it != next_deeps.end (); it ++)
   {
     f1 = it->first;
     //handle only atoms now!
     if (f1->oper () > aalta_formula::Undefined)
     {
       f2 = aalta_formula (aalta_formula::Not, NULL, f1).unique ();
       it2 = next_deeps.find (f2);
       if (it2 != next_deeps.end ())
       {
         f3 = get_next_n_formula (f1, it->second, it2->second);
         if (f3 == NULL)
           continue;
         if (res == NULL)
           res = f3;
         else
           res = aalta_formula (aalta_formula::And, res, f3).unique ();
       }
     }
   }
   
   //for phltl formulas only
   aalta_formula *prop = prop_in_globals ();
   aalta_formula *temp = NULL, *temp2 = NULL;
   if (prop != NULL)
   {
     int deep = common_deep (next_deeps);
     if (deep > 1)
     {
       for (it = next_deeps.begin (); it != next_deeps.end (); it ++)
       {
         f1 = it->first;
         if (f1->oper () == aalta_formula::Not) 
         {
           temp2 = NULL;
           break;
         }
         if (temp2 == NULL)
           temp2 = create_next_avoid_false (f1, deep);
         else
           temp2 = aalta_formula (aalta_formula::And, temp2, create_next_avoid_false (f1, deep)).unique ();
       }
       if (temp2 != NULL)
       {
         temp = apply_next_n (prop, deep);
         temp = aalta_formula (aalta_formula::And, temp, temp2).unique ();
       }
     }
   }
   if (temp != NULL)
   {
     if (res == NULL)
       res = temp;
     else
       res = aalta_formula (aalta_formula::And, res, temp).unique ();
   }
   
   return res;
 }
 
 aalta_formula* 
 nondeter_prog_state::prop_in_globals ()
 {
   if (_globals.empty ())
     return NULL;
   aalta_formula *res = NULL;
   for (aalta_formula::af_prt_set::iterator it = _globals.begin (); it != _globals.end (); it ++)
   {
     if (is_prop ((*it)->r_af ()))
     {
       if (res == NULL)
         res = (*it)->r_af ();
       else
         res = aalta_formula (aalta_formula::And, res, (*it)->r_af ()).unique ();
     }
   }
   return res;
 }
 
 int 
 nondeter_prog_state::common_deep (hash_map<aalta_formula*, std::set<int>, aalta_formula::af_prt_hash >& next_deeps)
 {
   hash_map<aalta_formula*, std::set<int>, aalta_formula::af_prt_hash >::iterator it;
   int deep = -1;
   for (it = next_deeps.begin (); it != next_deeps.end (); it ++)
   {
     if (it->first->oper () == aalta_formula::Not)
       return 0;
     if ((it->second).size () > 1)
       return 0;
     if (deep = -1)
       deep = *((it->second).begin ());
     else if (deep != *((it->second).begin ()))
       return 0;
   }
   return deep;
 }
 
 aalta_formula* 
 nondeter_prog_state::get_next_n_formula (aalta_formula* f, std::set<int>& deeps_pos, std::set<int>& deeps_neg)
 {
   std::set<int>::iterator it, it2;
   aalta_formula *res = NULL;
   it = deeps_pos.begin ();
   it2 = deeps_neg.begin ();
   while (it != deeps_pos.end () && it2 != deeps_neg.end ())
   {
     if ((*it) >= (*it2))
     {
       if (res == NULL)
         res = create_next_avoid_false (f, *it2);
       else
         res = aalta_formula (aalta_formula::And, res, create_next_avoid_false (f, *it2)).unique ();
       it2 ++;
     }
     else
     {
       if (res == NULL)
         res = create_next_avoid_false (f, *it);
       else
         res = aalta_formula (aalta_formula::And, res, create_next_avoid_false (f, *it)).unique ();
       it ++;
     }
   }
   return res;
 }
 
 aalta_formula* 
 nondeter_prog_state::create_next_avoid_false (aalta_formula *f, int deep)
 {
   aalta_formula *not_f = aalta_formula (aalta_formula::Not, NULL, f).unique ();
   aalta_formula *nx_f, *nx_not_f;
   nx_f = apply_next_n (f, deep);
   nx_not_f = apply_next_n (not_f, deep);
   aalta_formula *temp, *res;
   temp = aalta_formula (aalta_formula::And, nx_f, nx_not_f).unique ();
   temp = aalta_formula (aalta_formula::Not, NULL, temp).unique ();
   res = temp;
   temp = aalta_formula (aalta_formula::Or, nx_f, nx_not_f).unique ();
   res = aalta_formula (aalta_formula::And, res, temp).unique ();
   return res;
 }
 
 aalta_formula* 
 nondeter_prog_state::apply_next_n (aalta_formula *f, int deep)
 {
   aalta_formula *res = NULL;
   for (int i = 1; i <= deep; i ++)
   {
     if (res == NULL)
       res = apply_next (f);
     else
       res = apply_next (res);
   }
   return res;
 }
 
 void 
 nondeter_prog_state::get_next_deep_map (hash_map<aalta_formula*, std::set<int>, aalta_formula::af_prt_hash >& next_deeps)
 {
   get_next_deep_map_from (_formula, next_deeps);
 }
 
 void 
 nondeter_prog_state::get_next_deep_map_from (aalta_formula *f, 
                                              hash_map<aalta_formula*, std::set<int>, aalta_formula::af_prt_hash >& next_deeps)
 {
   if (f->oper () == aalta_formula::Next)
     get_next_deep_from (f, next_deeps);
   else
   {
     if (f->l_af () != NULL)
       get_next_deep_map_from (f->l_af (), next_deeps);
     if (f->r_af () != NULL)
       get_next_deep_map_from (f->r_af (), next_deeps);
   }
 }
 
 void 
 nondeter_prog_state::get_next_deep_from (aalta_formula *f, 
                                          hash_map<aalta_formula*, std::set<int>, aalta_formula::af_prt_hash >& next_deeps)
 {
   assert (f->oper () == aalta_formula::Next);
   std::set <int> deeps;
   int deep = 1;
   aalta_formula *nx = f->r_af ();
   while (nx->oper () == aalta_formula::Next)
   {
     deep ++;
     nx = nx->r_af ();
   }
   if (deep > 1)
   {
     //store literals only now
     if (nx->oper () > aalta_formula::Undefined || nx->oper () == aalta_formula::Not)
     {
       hash_map<aalta_formula*, std::set<int>, aalta_formula::af_prt_hash >::iterator it = next_deeps.find (nx);
       if (it != next_deeps.end ())
       {
         deeps = it->second;
         next_deeps.erase (it);
       }
       deeps.insert (deep);
       next_deeps.insert (std::pair<aalta_formula*, std::set<int> >(nx, deeps));
     }
   }
 }
 
 
 
 
 
 aalta_formula* 
 nondeter_prog_state::global_next_true ()
 {
   if (_globals.empty ())
     return NULL;
   aalta_formula::af_prt_set::iterator it = _globals.begin ();
   aalta_formula *res, *f;
   while (!is_prop ((*it)->r_af()))
   {
     it ++;
     if (it == _globals.end ())
       return NULL;
   }
   f = next_must_true (*it);
   assert (f != NULL);
   res = f;
   it ++;
   for (; it != _globals.end (); it ++)
   {
     if (!is_prop ((*it)->r_af ()))
       continue;
     f = next_must_true (*it);
     assert (f != NULL);
     res = aalta_formula (aalta_formula::And, res, f).unique ();
   }
   return res;
 }
 
 bool 
 nondeter_prog_state::is_prop (aalta_formula *f)
 {
   if (f->oper () > aalta_formula::Undefined || f->oper () == aalta_formula::Not)
     return true;
   else
   {
     if (f->oper () == aalta_formula::And || f->oper () == aalta_formula::Or)
       return is_prop (f->l_af ()) && is_prop (f->r_af ());
     else
       return false;
   }
 }
 
 aalta_formula* 
 nondeter_prog_state::next_must_true (aalta_formula *f)
 {
   assert (f->is_globally ());
   aalta_formula *f2 = f->r_af ()->flatted ();
   aalta_formula *res = apply_next (f2);
   return res;
 }
 
 

 
 aalta_formula* 
 nondeter_prog_state::avoid_next_false (aalta_formula::af_prt_set P)
 {
   aalta_formula *nx, *not_nx, *res1, *res2, *res;
   res = NULL;
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
   {
     nx = aalta_formula (aalta_formula::Next, NULL, *it).unique ();
     not_nx = 
       aalta_formula (aalta_formula::Next, NULL, aalta_formula (aalta_formula::Not, NULL, *it).unique()).unique ();
     res1 = aalta_formula (aalta_formula::And, nx, not_nx).unique ();
     res1 = aalta_formula (aalta_formula::Not, NULL, res1).unique ();
     res2 = aalta_formula (aalta_formula::Or, nx, not_nx).unique ();
     res2 = aalta_formula (aalta_formula::And, res1, res2).unique ();
     if (res == NULL)
       res = res2; 
     else
     {
       res = aalta_formula (aalta_formula::And, res, res2).unique (); 
     }
   }
   return res;
 }
 
 
 aalta_formula::af_prt_set 
 nondeter_prog_state::get_until_element_of (aalta_formula *f)
 {
   aalta_formula::af_prt_set P, P1, P2;
   if (f->oper () != aalta_formula::And)
   {
     if (f->oper () == aalta_formula::Until)
       P.insert (f->get_var ());
   }
   else
   {
     P1 = get_until_element_of (f->l_af ());
     P2 = get_until_element_of (f->r_af ());
     P.insert (P1.begin (), P1.end ());
     P.insert (P2.begin (), P2.end ());
   }
   return P;
 }
 
 
 
 void 
 nondeter_prog_state::update_unsatisfied ()
 {
   aalta_formula::af_prt_set P = get_until_element_of (_formula);
   aalta_formula *temp;
   aalta_formula::af_prt_set P2;
   P2.insert (_unsatisfied.begin (), _unsatisfied.end ());
   for (aalta_formula::af_prt_set::iterator it = P2.begin (); it != P2.end (); it ++)
   {
     //printf ("nondeter_prog_state::update_unsatisfied: %s\n", (*it)->to_string ().c_str ());
     if (P.find (*it) == P.end ())
     {
       _unsatisfied.erase (*it);
     }
   }
   set_unsatisfied_untils ();
 }
 
 
 
 
 
 aalta_formula::af_prt_set nondeter_prog_state::_potential_unsat;
 aalta_formula* nondeter_prog_state::_unsat_root = NULL;
 std::vector<std::pair<aalta_formula::af_prt_set, aalta_formula*> > nondeter_prog_state::_witness;
 hash_map<aalta_formula*, node*, aalta_formula::af_prt_hash> nondeter_prog_state::_f_node_map;
 bool nondeter_prog_state::_fill_witness_already_done = false;
 
 void 
 nondeter_prog_state::update_node (aalta_formula *f, aalta_formula *ucore, aalta_formula::af_prt_set P, aalta_formula *nx)
 {
   //printf ("update_node:: create transition:\n%s\n->\n%s\n", nx->to_string().c_str (), f->to_string().c_str ());
   hash_map<aalta_formula*, node*, aalta_formula::af_prt_hash>::iterator it = _f_node_map.find (f);
   aalta_formula::af_prt_set S;
   S.clear ();
   std::pair<aalta_formula::af_prt_set, aalta_formula*> pa;
   if (it != _f_node_map.end ())
   {
     node *n = it->second;
     pa = n->_tran;
     node *n2;
     if (ucore == NULL)
       n2 = new node (f, n->_ucore, pa);
     else
       n2 = new node (f, ucore, pa);
     _f_node_map.erase (it);
     _f_node_map.insert (pair<aalta_formula*, node*> (f, n2));
     delete n;
   }
   else
   {
     pa = make_pair (S, (aalta_formula*)NULL);
     node *n = new node (f, ucore, pa);
     _f_node_map.insert (pair<aalta_formula*, node*> (f, n));
   }
   
   if (nx == NULL)
     return;
   it = _f_node_map.find (nx);
   if (it != _f_node_map.end ())
   {
     printf ("nondeter_prog::update_node:\n The formula already creates the node!\n%s\n", nx->to_string().c_str());
     //print_f_node_map ();
     exit (0);
   }
   else
   {
     std::vector<std::pair<aalta_formula::af_prt_set, aalta_formula*> > trans;
     std::pair<aalta_formula::af_prt_set, aalta_formula*> tran = make_pair (P, f);
     node *n = new node (nx, NULL, tran);
     _f_node_map.insert (pair<aalta_formula*, node*> (nx, n));
   }
   
 }
 
 void 
 nondeter_prog_state::add_transition_to_node (aalta_formula* f, aalta_formula::af_prt_set P, aalta_formula* nx)
 {
   hash_map<aalta_formula*, node*, aalta_formula::af_prt_hash>::iterator it = _f_node_map.find (nx);
   if (it == _f_node_map.end ())
   {
     printf ("nondeter_prog_state::add_transition_to_node:\n The formula already creates the node: \n%s\n", nx->to_string().c_str());
     exit (0);
   }
   std::pair<aalta_formula::af_prt_set, aalta_formula*> tran = make_pair (P, f);
   node *n = new node (nx, NULL, tran);
   _f_node_map.insert (pair<aalta_formula*, node*> (nx, n));
 }
 
 void 
 nondeter_prog_state::clear_f_node_map ()
 {
   hash_map<aalta_formula*, node*, aalta_formula::af_prt_hash>::iterator it;
   for (it = _f_node_map.begin (); it != _f_node_map.end (); it ++)
   {
     delete it->second;
   }
   _f_node_map.clear ();
 }
 
 //print elements in _f_node_map
 void 
 nondeter_prog_state::print_f_node_map ()
 {
   hash_map<aalta_formula*, node*, aalta_formula::af_prt_hash>::iterator it;
   aalta_formula *f;
   for (it = _f_node_map.begin (); it != _f_node_map.end (); it ++)
   {
     f = (it->second->_tran).second;
     /*
     if (f != NULL)
       printf ("[\n %s\n -> %s\n]\n\n", (it->first)->to_string().c_str (), f->to_string().c_str ());
     else 
       printf ("[\n %s\n -> NULL\n]\n\n", (it->first)->to_string().c_str ());
     */
   }
 }
 
 //find a satisfied path from intial postponed state (_unsat_root) to dest
 void 
 nondeter_prog_state::fill_witness_from_to (aalta_formula *dest)
 {
   //assert (_unsat_root != dest);
   hash_map<aalta_formula*, node*, aalta_formula::af_prt_hash>::iterator it = _f_node_map.find (dest);
   if (it == _f_node_map.end ())
   {
     printf ("nondeter_prog_state::fill_witness_from_to:\n Cannot find the node:\n%s\n", dest->to_string().c_str ());
     exit (0);
   }
   node *n = it->second;
   if ((n->_tran).second == NULL)
   {
     printf ("nondeter_prog_state::fill_witness_from_to:\nCannot find the path to:\n%s\n", _unsat_root->to_string().c_str());
     print_f_node_map ();
     aalta_formula::af_prt_set P = _unsat_root->to_set ();
     //checker::print (P);
     exit (0);
   }
   else
   {
     _witness.push_back (pair<aalta_formula::af_prt_set, aalta_formula*> ((n->_tran).first, dest));
     if ((n->_tran).second == _unsat_root)
       return;
     else
       fill_witness_from_to ((n->_tran).second);
   }
   
 }
 
 aalta_formula* 
 nondeter_prog_state::AND (aalta_formula::af_prt_set P)
 {
   return convert_to_formula (P);
 }
 
 aalta_formula* 
 nondeter_prog_state::OR (aalta_formula::af_prt_set P)
 {
   aalta_formula *res = NULL;
   if (P.empty ())
     return res;
   aalta_formula::af_prt_set::iterator it = P.begin ();
   res = *it;
   it ++;
   for (; it != P.end (); it ++)
   {
     res = aalta_formula (aalta_formula::Or, res, *it).unique ();
   }
   return res;
 } 
 
 nondeter_prog_state::history_map nondeter_prog_state::_hist_map;
 
 std::pair<aalta_formula::af_prt_set, bool>  
 nondeter_prog_state::match_from_history (aalta_formula *f, aalta_formula::af_prt_set P)
 {
   aalta_formula::af_prt_set res;
   history_map::iterator it = _hist_map.find (f);
   if (it == _hist_map.end ())
     return std::make_pair (res, false);
   std::vector<aalta_formula::af_prt_set > vec = it->second;
   aalta_formula::af_prt_set P1;
   for (int i = vec.size ()-1; i >= 0; i --)
   {
     if (aalta_formula::contain (P, vec[i]))
       return std::make_pair (vec[i], true);
   }
   return std::make_pair (res, false);
 }
 
 void 
 nondeter_prog_state::update_history (aalta_formula* ucore, aalta_formula::af_prt_set P)
 {
   aalta_formula::af_prt_set res;
   history_map::iterator it = _hist_map.find (ucore);
   std::vector<aalta_formula::af_prt_set > vec;
   if (it == _hist_map.end ())
   {
     vec.push_back (P);
     _hist_map.insert (pair<aalta_formula*, std::vector<aalta_formula::af_prt_set > > (ucore, vec));
   }
   else
   {
     vec = it->second;
     vec.push_back (P);
     _hist_map.erase (ucore);
     _hist_map.insert (pair<aalta_formula*, std::vector<aalta_formula::af_prt_set > > (ucore, vec));
   }
   return;
 }
 
 //split binary the formula set P into two sets P2 and P3
 void 
 nondeter_prog_state::split_binary (aalta_formula::af_prt_set P, aalta_formula::af_prt_set& P2,         
                                    aalta_formula::af_prt_set& P3)
 {
   int binary = P.size () / 2;
   int i = 0;
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
   {
     if (i < binary)
       P2.insert (*it);
     else
       P3.insert (*it);
     i ++;
   }
 }
 
 aalta_formula* 
 nondeter_prog_state::create_list_formula (std::list <aalta_formula::af_prt_set > lt)
 {
   aalta_formula *res = NULL;
   for (std::list <aalta_formula::af_prt_set > ::iterator it = lt.begin (); it != lt.end (); it ++)
   {
     if (res == NULL)
       res = AND (*it);
     else
       res = aalta_formula (aalta_formula::And, res, AND (*it)).unique ();
   }
   return res;
 }
 
 //compute the minimal unsat core from f corresponding to ! X (avoid)
 aalta_formula* 
 nondeter_prog_state::MUC (aalta_formula::af_prt_set f_set, aalta_formula *avoid)
 {
   //printf ("in MUC, the set is\n");
   //checker::print (f_set);
   aalta_formula* guarantee_check = create_check_formula (AND (f_set), avoid);
   aalta_formula::af_prt_set P = guarantee_check->SAT();
   if (!P.empty ())
   {
     printf ("MUC: the formula is satisfiable\n%s\n%s\n%s\n", (AND (f_set)->to_string()).c_str (), avoid->to_string().c_str (), guarantee_check->to_string ().c_str ());
     //checker::print (P);
     //printf ("MUC::_unsatisfied is\n");
     //checker::print (_unsatisfied);
     exit (0);
   }
   
   aalta_formula* basic_to_check = create_check_formula (NULL, avoid);
   P = basic_to_check->SAT ();
   if (P.empty ())
   {
     return NULL;
   }
   
   P = f_set;
   std::list <aalta_formula::af_prt_set > lt;
   lt.push_back (P);
   aalta_formula::af_prt_set P2, P3, P4, affirmed;
   aalta_formula *f2, *f3, *f_affirmed, *lt_formula;
   while (!lt.empty ())
   {
     P = lt.front ();
     lt.pop_front ();
     f_affirmed = AND (affirmed);
     lt_formula = create_list_formula (lt);
     
     P2.clear ();
     P3.clear ();
     split_binary (P, P2, P3);
     if (P2.size () == 1 && P3.empty ())
     {
       affirmed.insert (P2.begin (), P2.end ());
       continue;
     }
     else if (!P2.empty ())
     {
       f2 = AND (P2);
       if (f_affirmed != NULL)
         f2 = aalta_formula (aalta_formula::And, f2, f_affirmed).unique ();
       if (lt_formula != NULL)
         f2 = aalta_formula (aalta_formula::And, f2, lt_formula).unique ();
       f2 = f2->flatted ();
       if (basic_to_check != NULL)
         f2 = aalta_formula (aalta_formula::And, f2, basic_to_check).unique ();
       P4 = f2->SAT ();
       if (P4.empty ())
       {
         lt.push_back (P2);
         continue;
       }
     }
     
     if (P3.size () == 1 && P2.empty ())
     {
       affirmed.insert (P3.begin (), P3.end ());
       continue;
     }
     else if (!P3.empty ())
     {
       f3 = AND (P3);
       if (f_affirmed != NULL)
         f3 = aalta_formula (aalta_formula::And, f3, f_affirmed).unique ();
       if (lt_formula != NULL)
         f3 = aalta_formula (aalta_formula::And, f3, lt_formula).unique ();
       f3 = f3->flatted ();
       if (basic_to_check != NULL)
         f3 = aalta_formula (aalta_formula::And, f3, basic_to_check).unique ();
       P4 = f3->SAT ();
       if (P4.empty ())
       {
         lt.push_back (P3);
         continue;
       }
     }
     
     if (!P2.empty ())
       lt.push_back (P2);
     if (!P3.empty ())
       lt.push_back (P3);
   }
   
   if (avoid != NULL)
   {
     for (aalta_formula::af_prt_set::iterator it = _unsatisfied_untils.begin (); 
         it != _unsatisfied_untils.end (); it ++)
         affirmed.erase (*it);
   }
     
   return AND (affirmed);
 }
 
 aalta_formula* 
 nondeter_prog_state::MUC (aalta_formula *f, aalta_formula *ucore)
 {
   
   //assert (ucore != NULL);
   aalta_formula::af_prt_set P, P2, P3, P4, P5;
   int count  = 0;
   P = f->to_set ();
   if (ucore == NULL)
   {
     P3.insert (P.begin (), P.end ());
   }
   else
   {
     P2 = ucore->to_set ();
     for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
     {
       if (P2.find (*it) == P2.end () && _globals.find (*it) == _globals.end ())
         P3.insert (*it);
     }
   }
   
   //std::pair<aalta_formula::af_prt_set, bool> pa = match_from_history (ucore, P3);
   //if (pa.second)
     //P = pa.first;
   //else
   {   
   P2.clear ();
   P2.insert (P.begin (), P.end ());
   P5.insert (P.begin (), P.end ());
   P4.clear ();
   P.clear ();
   aalta_formula *f2, *f3, *f4, *nx;
   nx = NULL;
   if (_avoid != NULL)
     nx = _avoid;
   f3 = OR (_potential_unsat);
   if (f3 != NULL)
     nx = aalta_formula (aalta_formula::And, nx, negation_next(f3)).unique ();
   if (ucore != NULL)
     nx = aalta_formula (aalta_formula::And, nx, negation_next(ucore)).unique ();
   
   for (aalta_formula::af_prt_set::iterator it = P3.begin (); it != P3.end (); it ++)
   {
     if (_globals.find (*it) != _globals.end ())
       continue;
     P2.erase (*it);
     f2 = convert_to_formula (P2);
     if (f2 == NULL)
       return NULL;
     f2 = f2->flatted ();
     if (nx != NULL)
       f2 = aalta_formula (aalta_formula::And, f2, nx).unique ();
     P4 = f2->SAT ();
     count ++;
     if (!P4.empty ())
     {
       P.insert (*it);
       P2.insert (*it);
     }
   }
   //if (!P.empty ())
     //update_history (ucore, P);
   }
   //printf ("nondeter_prog_state::MUC: do SAT %d times\n", count);
   
   aalta_formula *res = convert_to_formula (P);
   return res;
 }
 

 
 aalta_formula::af_prt_set   
 nondeter_prog_state::UC (aalta_formula *f, aalta_formula *ucore)
 {
   //ERASE_NODE (f);
   //printf ("before UC: the final ucore is\n%s\n", ucore->to_string ().c_str());
   assert (ucore != NULL);
   aalta_formula *temp = ucore;
   _potential_unsat.erase (ucore);
   aalta_formula *f2, *f3, *flat;
   flat = f->flatted ();
   
   aalta_formula::af_prt_set prop_atoms = propAtoms (flat);
   
   if (_avoid != NULL)
     flat = aalta_formula (aalta_formula::And, flat, _avoid).unique ();
   f3 = OR (_potential_unsat);
   if (f3 != NULL)
     flat = aalta_formula (aalta_formula::And, flat, negation_next (f3)).unique ();
     
   f2 = flat;
   f2 = aalta_formula (aalta_formula::And, f2, negation_next (ucore)).unique ();
   aalta_formula::af_prt_set P = f2->SAT ();
   int count = 0;
   while (P.empty ())
   {
     f3 = MUC (f, ucore);
     count ++;
     if (f3 != NULL)
     {
       ucore = aalta_formula (aalta_formula::And, ucore, f3).unique ();
       f2 = flat;
       f2 = aalta_formula (aalta_formula::And, f2, negation_next (ucore)).unique ();
       P = f2->SAT ();
     }
     else
       break; 
   }
   //printf ("nondeter_prog_state::UC: do MUC %d times\n", count);
   if (P.empty ())
   {
     update_node (f, ucore, P, NULL);
   }
   else
     update_node (f, ucore, current_in (P), next_in (P, prop_atoms));
   _potential_unsat.insert (ucore);
   //printf ("after UC: the final ucore is\n%s\n", ucore->to_string ().c_str());
   return P;
   
 }
 
 void 
 nondeter_prog_state::UNSAT_INVARIANT (aalta_formula *f)
 {
   aalta_formula *f2, *f3;
   //printf ("UNSAT_INVARIANT: the formula is\n%s\n", erase_global(f)->to_string().c_str ());
   f2 = f->flatted ();
   
   aalta_formula::af_prt_set prop_atoms = propAtoms (f2);
   
   if (_avoid != NULL)
     f2 = aalta_formula (aalta_formula::And, f2, _avoid).unique ();
   f3 = OR (_unsatisfied);
   if (f3 != NULL)
     f2 = aalta_formula (aalta_formula::And, f2, f3).unique ();
   aalta_formula::af_prt_set P, P2, P3;
   P = f2->SAT ();
   if (P.empty ())
   {
     P2 = UC (f, AND (_unsatisfied_untils));
     if (P2.empty ())
     {
       UNSAT_INVARIANT_BACK ();
     }
     else
     {
       P3 = current_in (P2);
       f3 = next_in (P2, prop_atoms);
       add_transition_to_node (f, P3, f3);
       UNSAT_INVARIANT (f3);
     }
   }
   else
   {
     f3 = next_in (P, prop_atoms);
     update_node (f, NULL, current_in (P), f3);
     fill_witness_from_to (f3);
   }
   return;
 }
 
 bool 
 nondeter_prog_state::is_potential_unsat_invariant ()
 {
   aalta_formula *f2 = OR (_potential_unsat);
   if (f2 == NULL)
     return false;
   aalta_formula *f3 = negation_next (f2);
   aalta_formula *global = convert_to_formula (_globals);
   if (global != NULL)
     f2 = aalta_formula (aalta_formula::And, f2, global).unique ();
   aalta_formula *f = f2->flatted ();
   f = aalta_formula (aalta_formula::And, f, f3).unique ();
   if (_avoid != NULL)
     f = aalta_formula (aalta_formula::And, f, _avoid).unique ();
   aalta_formula::af_prt_set P = f->SAT ();
   if (P.empty ())
     return true;
   return false;
 }
 
 void 
 nondeter_prog_state::UNSAT_INVARIANT_BACK ()
 {
   //printf ("step in UNSAT_INVARIANT_BACK ..\n");
   aalta_formula::af_prt_set P, P2;
   aalta_formula *f2, *f3;
   hash_map<aalta_formula*, node*, aalta_formula::af_prt_hash>::iterator it, it2;
   std::vector<node*> nodes;
   if (is_potential_unsat_invariant ())
     return;
   for (it = _f_node_map.begin (); it != _f_node_map.end (); it ++)
   {
     nodes.push_back (it->second);
   }
   aalta_formula *formula, *ucore;
   int i, size;
   size = nodes.size ();
   for (i = 0; i < size; i ++)
   {
     formula = nodes[i]->_formula;
     ucore = nodes[i]->_ucore;
     if (ucore == NULL)
       continue;
     P = UC (formula, ucore);
     if (!P.empty ())
     {
       P2 = current_in (P);
       aalta_formula *flat = formula->flatted ();
       aalta_formula::af_prt_set prop_atoms = propAtoms (flat);
       f3 = next_in (P, prop_atoms);
       add_transition_to_node (formula, P2, f3);
       UNSAT_INVARIANT (f3);
       break;
     }
   }
   if (i >= size)
     UNSAT_INVARIANT_BACK ();
   //printf ("step out UNSAT_INVARIANT_BACK\n");
 }
 
 aalta_formula* nondeter_prog_state::_current_avoid = NULL;
 bool 
 nondeter_prog_state::imply_avoid ()
 {
 /* 
   aalta_formula *f;
   aalta_formula::af_prt_set P = _flatted_formula->SAT ();
   if (P.empty ())
     return false;
   if (_current_avoid != NULL)
   {
     f = _current_avoid->flatted ();
     f = aalta_formula (aalta_formula::Not, NULL, f).unique ();
     //Note here _flatted_formula is used, but be sure global parts may change!
     f = aalta_formula (aalta_formula::And, f, _flatted_formula).unique ();
     P = f->SAT ();
     if (P.empty ())
       return true;
   }
   */
   return false;
 }
 
 
 std::pair<aalta_formula::af_prt_set, aalta_formula*> 
 nondeter_prog_state::get_next_pair (size_t pos)
 {
   //printf ("original formula is:\n%s\n\n", _formula->to_string().c_str ());                 
   //printf ("after flatten, the formula is:\n%s\n", _flatted_formula->to_string ().c_str ());
   
   if (! _witness.empty ())
   {
     std::pair<aalta_formula::af_prt_set, aalta_formula*> pa = _witness.back ();
     _witness.pop_back ();
     return pa;
   }
   
   //_pos = pos;
   
   std::pair<aalta_formula::af_prt_set, aalta_formula*> pa;
   aalta_formula::af_prt_set P, P2;
   aalta_formula *nx, *f2;
   aalta_formula *f = _flatted_formula;
   
   /*
    * SAT_PUSURING mode
    *_next_wanted store all formulas we expect to see in next state
   */
   
   if (_next_wanted != NULL)
   {
     //printf ("_next_wanted is not NULL\n");
     //checker::print (_unsatisfied);
     //printf ("_next_wanted is\n%s\n", _next_wanted->to_string ().c_str ());
     f = aalta_formula (aalta_formula::And, f, _next_wanted).unique ();
     //printf ("_formula is\n%s\n", _formula->to_string ().c_str ());
     P = f->SAT ();
     if (!P.empty ())
     {
       _fulfilled = false;   
       //printf ("return here\n");
       //printf ("_next_wanted is\n%s\n", _next_wanted->to_string ().c_str ());
       _next_wanted = NULL;
       return assignment_pair (P);
     }
     else
     {
       _next_wanted = NULL;
       f = _flatted_formula;
     }
     //printf ("cannot get an assignment from _next_wanted!\n");
     _fulfilled = false;
   }
   
   ///end of sat seeking part
   
   update_unsatisfied ();
   //printf ("before nondeter_prog_state::get_next_pair::_unsatisfied:\n");
   //checker::print (_unsatisfied);
   //printf ("Number: %d\n", (int)_unsatisfied.size ());
   
   
   
   
   
   
   if (_avoid != NULL)
   {
     if (_avoid == aalta_formula::FALSE ())
     {
       return empty_pair ();
     }
     //printf ("_avoid is: %s\n", _avoid->to_string().c_str ());
     f = aalta_formula (aalta_formula::And, f, _avoid).unique ();
   }
   
   P = f->SAT ();
   if (P.empty ())
   {
     //_formula is unsatisfiable itself
     if (_last_invariant != NULL)
       if (contain (_formula, _last_invariant))
         return empty_pair ();
     if (imply_avoid ())
       return empty_pair ();
     aalta_formula *temp = erase_global (_formula);
     if (temp != NULL)
     {
       //printf ("get_next_pair:: do MUC\n");
       temp = MUC (temp->to_set(), NULL);  //all globals are removed in the core (they are not necessary)
       update_avoid_with (temp);
       //checker::print (temp->to_set ());
     }
     else 
       _avoid = aalta_formula::FALSE ();
       
     return empty_pair ();
   }
   if (_unsatisfied.empty ())
     return assignment_pair (P);
   
   
   f2 = OR (_unsatisfied);
   //f = aalta_formula (aalta_formula::And, f, f2).unique ();
   f = aalta_formula (aalta_formula::And, f2, f).unique ();
   
   P = f->SAT ();
   if (!P.empty ())
     return assignment_pair (P);
   else
   {
   /*
    * UNSAT_PUSURING mode
   */
   

   
   //check whether _global_flatted_formula is the reason causing _unsatisfied_untils not fulfilled
   //if so, we can know elements in _unsatisfied_untils are unsat.
   if (_global_flatted_formula != NULL)
   {
     aalta_formula* temp_f = create_check_formula (AND (_unsatisfied_untils), NULL);
     temp_f = aalta_formula (aalta_formula::And, temp_f, OR (_unsatisfied)).unique ();
     aalta_formula::af_prt_set temp_P = temp_f->SAT();
     if (temp_P.empty ())
     {
       update_avoid_with (AND (_unsatisfied_untils));
       return empty_pair ();
     }
   }
   
   
   assert (_f_node_map.empty ());
   _unsat_root = _formula;
   
   bool succeed = compute_next_pair_from_history (pa);
   if (succeed)
     return pa;
   
   //printf ("The formula is unsatisfiable, go to UNSAT_PUSURING mode..\n%s\n", f->to_string().c_str ());
   //printf ("\n\nCurrent state is \n %s\n\n", erase_global (_formula)->to_string ().c_str ());
   aalta_formula::af_prt_set visited;
   
   aalta_formula::af_prt_set common = distinguish_states (visited);
   if (common.empty ())           //at least one element of _unsatisfied_untils is satisfied 
   {
     pa = _witness.back ();
     _witness.pop_back ();
     clear_f_node_map ();
     return pa;
   } 
   else if (is_invariant (AND (common)))       //common itself is an invariant
   {
     //printf ("the invariant is\n %s\n", (AND(common))->to_string().c_str ());
     update_avoid_with (AND (common));
     pa = empty_pair ();
     clear_f_node_map ();
     return pa;
   }
   
   //printf ("nondeter_prog_state::get_next_pair:: common is \n%s\n", AND (common)->to_string ().c_str ());  
   
   std::vector<aalta_formula::af_prt_set > seq;
   initial_seq (seq, common);
   if (seq.empty ())
   {
     clear_f_node_map ();
     return empty_pair ();
   }
   //printf ("nondeter_prog_state::get_next_pair:: after initilization, seq formula is\n");
   //print_seq (seq);
   
   int pos = seq.size ()-1;
   
   aalta_formula *f_to_check, *next_state, *pre_state, *global_erased;
   aalta_formula::af_prt_set qi, prop_atoms;
   aalta_formula* avoid = update_avoid (seq, pos);
   //printf ("current avoid formula is\n %s\n", avoid->to_string ().c_str ());
   aalta_formula::af_prt_set P;   
   
   while (true)
   {
     do
     {
       qi = compute_muc (visited, seq, pos);
       if (!qi.empty ())
       {
         pos ++;
         update_seq (seq, qi, pos);
       }
       //printf ("nondeter_prog_state::get_next_pair:: after updated, seq formula is\n");
       //print_seq (seq);
       avoid = update_avoid (seq, pos);
       if (is_invariant (avoid))
       {
         aalta_formula *temp_f = OR (seq[pos]);
         if (is_invariant (temp_f) && is_initially (temp_f))
         {
           update_global_flatted_formula (seq);
           update_avoid_with (AND(_unsatisfied_untils));
         }
         else
         {
           //printf ("the invariant is\n %s\n", avoid->to_string().c_str ());
           update_avoid_with (avoid);
         }
         pa = empty_pair ();
         clear_f_node_map ();
         return pa;
       }
       assert (!qi.empty ());
       //printf ("current avoid formula is\n %s\n", avoid->to_string ().c_str ());
       assert (pos < seq.size ());
       f_to_check = create_check_formula (visited, OR (seq[pos]));
       P = f_to_check->SAT();

     } while (P.empty ());
     
     pre_state = previous_state (visited, P);
     next_state = next_in (P, pre_state->flatted ());
     update_node (pre_state, NULL, current_in (P), next_state);
     
     visited.insert (next_state);
     pos = pos - 1;
     avoid = update_avoid (seq, pos);
     //printf ("current avoid formula is\n %s\n", avoid->to_string ().c_str ());
     assert (pos < seq.size ());
     if (pos == 0)
     {
       f_to_check = create_check_formula (visited, NULL);
       f_to_check = aalta_formula (aalta_formula::And, f_to_check, OR (_unsatisfied)).unique ();
     }
     else
       f_to_check = create_check_formula (visited, OR (seq[pos]));
     P = f_to_check->SAT();
     
     while (!P.empty ())
     {
       pre_state = previous_state (visited, P);
       next_state = next_in (P, pre_state->flatted ());
       pos = pos - 1;
       if (pos < 0)
       {
         fill_witness_from_to (pre_state);
         assert (!_witness.empty ());
         pa = _witness.back ();
         _witness.pop_back ();
         clear_f_node_map ();
         update_until_avoid_seqs (P, seq);
         update_pre_seq_hist (P, seq);
         return pa;
       }
       update_node (pre_state, NULL, current_in (P), next_state);  
       visited.insert (next_state);
       avoid = update_avoid (seq, pos);
       //printf ("current avoid formula is\n %s\n", avoid->to_string ().c_str ());
       assert (pos < seq.size ());
       if (pos == 0)
       {
         f_to_check = create_check_formula (visited, NULL);
         //f_to_check = aalta_formula (aalta_formula::And, f_to_check, OR (_unsatisfied)).unique ();
         f_to_check = aalta_formula (aalta_formula::And, OR (_unsatisfied), f_to_check).unique ();
       }
       else
         f_to_check = create_check_formula (visited, OR (seq[pos]));
       P = f_to_check->SAT();
     }
   }
   
   }
 }
 
 //use the history information to compute the sequence of states that lead to the satisfaction of at 
 //least one element of _unsatisfied_untils
 bool 
 nondeter_prog_state::compute_next_pair_from_history (std::pair<aalta_formula::af_prt_set, aalta_formula*>& pa)
 {
   std::vector<aalta_formula::af_prt_set > seq;
   hash_map<aalta_formula*, std::vector<aalta_formula::af_prt_set > >::iterator iter;
   if (_pre_seq_hist.empty ())
   {
     for (aalta_formula::af_prt_set::iterator it = _unsatisfied_untils.begin (); it != _unsatisfied_untils.end (); it ++)
     {
       iter = _until_avoid_seqs.find (*it);
       if (iter != _until_avoid_seqs.end ())
       {
         seq = iter->second;
         //printf ("compute_next_pair_from_history:: use history from _until_avoid_seqs\n");
         break;
       }
     }
     if (seq.empty ())
       return false;
   }
   else
   {
     seq = adjust_to_unsatisfied (_pre_seq_hist);
     if (seq.empty ())
       return false;
     //printf ("compute_next_pair_from_history:: use history from _pre_seq_hist\n");
   }
   aalta_formula::af_prt_set visited;
   visited.insert (_formula);
   pa = compute_next_pair_via_seq (seq, visited);
   return true;
 }
 
 std::vector<aalta_formula::af_prt_set > 
 nondeter_prog_state::adjust_to_unsatisfied (std::vector<aalta_formula::af_prt_set > seq)
 {
   aalta_formula::af_prt_set Q1, Q2;
   Q1 = Q2 = seq[0];
   for (aalta_formula::af_prt_set::iterator it = Q1.begin (); it != Q1.end (); it ++)
   {
     if (_unsatisfied_untils.find (*it) == _unsatisfied_untils.end ())
       Q2.erase (*it);
   }
   if (Q2.empty ())
     seq.clear ();
   else
     seq[0] = Q2;
   return seq;
 }
 
 std::pair<aalta_formula::af_prt_set, aalta_formula*> 
 nondeter_prog_state::compute_next_pair_via_seq (std::vector<aalta_formula::af_prt_set > seq, aalta_formula::af_prt_set visited)
 {
   std::pair<aalta_formula::af_prt_set, aalta_formula*> pa; 
   aalta_formula::af_prt_set P, qi;
   aalta_formula *pre_state, *next_state, *avoid, *f_to_check;
   int pos = seq.size () - 1;   
   
   while (true)
   {
     if (pos == 0)
     {
       f_to_check = create_check_formula (visited, NULL);
       f_to_check = aalta_formula (aalta_formula::And, f_to_check, OR (_unsatisfied)).unique ();
     }
     else
       f_to_check = create_check_formula (visited, OR (seq[pos]));
     P = f_to_check->SAT();
     
     while (!P.empty ())
     {
       pre_state = previous_state (visited, P);
       next_state = next_in (P, pre_state->flatted ());
       pos = pos - 1;
       if (pos < 0)
       {
         fill_witness_from_to (pre_state);
         assert (!_witness.empty ());
         pa = _witness.back ();
         _witness.pop_back ();
         clear_f_node_map ();
         update_until_avoid_seqs (P, seq);
         update_pre_seq_hist (P, seq);
         return pa;
       }
       if (visited.find (next_state) == visited.end ())
       {
         update_node (pre_state, NULL, current_in (P), next_state);  
         visited.insert (next_state);
       }
       avoid = update_avoid (seq, pos);
       //printf ("current avoid formula is\n %s\n", avoid->to_string ().c_str ());
       assert (pos < seq.size ());
       if (pos == 0)
       {
         f_to_check = create_check_formula (visited, NULL);
         //f_to_check = aalta_formula (aalta_formula::And, f_to_check, OR (_unsatisfied)).unique ();
         f_to_check = aalta_formula (aalta_formula::And, OR (_unsatisfied), f_to_check).unique ();
       }
       else
         f_to_check = create_check_formula (visited, OR (seq[pos]));
       P = f_to_check->SAT();
     }
     
     do
     {
       //printf ("nondeter_prog_state::compute_next_pair_via_seq:: before updated, seq formula is\n");
       //print_seq (seq);
       //printf ("pos is %d\n", pos);
       //printf ("visited size is %d\n", (int)visited.size ());
       qi = compute_muc (visited, seq, pos);
       if (!qi.empty ())
       {
         pos ++;
         update_seq (seq, qi, pos);
       }
       //printf ("nondeter_prog_state::compute_next_pair_via_seq:: after updated, seq formula is\n");
       //print_seq (seq);
       avoid = update_avoid (seq, pos);
       //printf ("nondeter_prog_state::compute_next_pair_via_seq:: avoid is\n%s\n", avoid->to_string ().c_str ());
       if (is_invariant (avoid))
       {
         aalta_formula *temp_f = OR (seq[pos]);
         if (is_invariant (temp_f) && is_initially (temp_f))
         {
           update_global_flatted_formula (seq);
           update_avoid_with (AND(_unsatisfied_untils));
         }
         else
         {
           //printf ("the invariant is\n %s\n", avoid->to_string().c_str ());
           update_avoid_with (avoid);
         }
         pa = empty_pair ();
         clear_f_node_map ();
         return pa;
       }
       assert (!qi.empty ());
       //printf ("current avoid formula is\n %s\n", avoid->to_string ().c_str ());
       assert (pos < seq.size ());
       f_to_check = create_check_formula (visited, OR (seq[pos]));
       P = f_to_check->SAT();
     } while (P.empty ());
     
     pre_state = previous_state (visited, P);
     next_state = next_in (P, pre_state->flatted ());
     update_node (pre_state, NULL, current_in (P), next_state);
     
     visited.insert (next_state);
     pos = pos - 1;
     //avoid = update_avoid (seq, pos);
     //printf ("current avoid formula is\n %s\n", avoid->to_string ().c_str ());
     assert (pos < seq.size ());
     
   }
   
 }
 
 hash_map<aalta_formula*, std::vector<aalta_formula::af_prt_set> > nondeter_prog_state::_until_avoid_seqs;
 void 
 nondeter_prog_state::update_until_avoid_seqs (aalta_formula::af_prt_set& P, std::vector<aalta_formula::af_prt_set > seq)
 {
   aalta_formula::af_prt_set Q;
   for (aalta_formula::af_prt_set::iterator it = _unsatisfied_untils.begin (); it != _unsatisfied_untils.end (); it ++)
   {
     if (P.find ((*it)->get_var ()) != P.end ())
       _until_avoid_seqs.erase (*it);
     Q.clear ();
     Q.insert (*it);
     seq[0] = Q;
     _until_avoid_seqs.insert (std::pair<aalta_formula*, std::vector<aalta_formula::af_prt_set > > (*it, seq));
   }
 }
 
 std::vector<aalta_formula::af_prt_set> nondeter_prog_state::_pre_seq_hist;
 void 
 nondeter_prog_state::update_pre_seq_hist (aalta_formula::af_prt_set& P, std::vector<aalta_formula::af_prt_set > seq)
 {
   aalta_formula::af_prt_set Q = _unsatisfied_untils;
   for (aalta_formula::af_prt_set::iterator it = _unsatisfied_untils.begin (); it != _unsatisfied_untils.end (); it ++)
   {
     if (P.find ((*it)->get_var ()) != P.end ())
       Q.erase (*it);
   }
   aalta_formula::af_prt_set Q2;
   if (AND (Q) != NULL)
   {
     Q2.insert (AND (Q));
     seq[0] = Q2;
     _pre_seq_hist = seq;
   }
   else
     _pre_seq_hist.clear ();
   //printf ("_pre_seq_hist is set!\n");
   //print_seq (_pre_seq_hist);
 }
 
 //store the original input formula
 aalta_formula* nondeter_prog_state::_input_flatted = NULL;
 
 void 
 nondeter_prog_state::set_input_flatted ()
 {
   if (_input_flatted == NULL)
     _input_flatted = _flatted_formula;
 }
 //check whether f is true initially
 bool 
 nondeter_prog_state::is_initially (aalta_formula* f)
 {
   assert (_input_flatted != NULL);
   aalta_formula *flat = f->flatted ();
   flat = aalta_formula (aalta_formula::Not, NULL, flat).unique ();
   flat = aalta_formula (aalta_formula::And, _input_flatted, flat).unique ();
   aalta_formula::af_prt_set P = flat->SAT ();
   if (P.empty ())
     return true;
   else 
     return false;
 }
 
 
 
 //update _global_flatted_formula
 void 
 nondeter_prog_state::update_global_flatted_formula (std::vector<aalta_formula::af_prt_set > seq)
 {
   for (int i = 1; i < seq.size (); i ++)
   {
     if (_global_flatted_formula == NULL)
     {
       _global_flatted_formula = OR (seq[i])->flatted ();
     }
     else
       _global_flatted_formula = aalta_formula (aalta_formula::And, _global_flatted_formula, OR (seq[i])->flatted ()).unique ();
   }
   //printf ("after update _always_true is \n%s\n", _always_true->to_string ().c_str ());
 }
 
 //print the information of seq
 void 
 nondeter_prog_state::print_seq (std::vector<aalta_formula::af_prt_set > seq)
 {
   for (int i = 0; i < seq.size (); i ++)
     checker::print (seq[i]);
   printf ("\n\n");
 }
 
 //compute minimal unsat cores from collected states. 
 //During the computation, existed information in the avoidabe sequence can be used. 
 aalta_formula::af_prt_set 
 nondeter_prog_state::compute_muc (aalta_formula::af_prt_set S, 
                                   std::vector<aalta_formula::af_prt_set > seq, int pos)
 {
   aalta_formula::af_prt_set Q, res, temp, P;
   aalta_formula* ucore, *f, *guarantee_check, *f2;
   if (pos+1 < seq.size ())
     Q = seq[pos+1];
     
   //check whether there is one X(seq[pos]), if so, it is obvious an MUC
   for (aalta_formula::af_prt_set::iterator it = seq[pos].begin (); it != seq[pos].end (); it ++)
     P.insert (apply_next (*it));

   for (aalta_formula::af_prt_set::iterator it = S.begin (); it != S.end (); it ++)
   {
     //printf ("in compute_muc, the formula is\n%s\n", (*it)->to_string().c_str ());
     f = erase_global (*it);
     if (f == NULL)
       return res;

     /*
     guarantee_check = create_check_formula (f, NULL);
     P = guarantee_check->SAT ();
     if (P.empty ())
     {
       ucore = MUC (guarantee_check, NULL);
       update_avoid_with (ucore);
       continue;
     }
     */
     //f2 = OR (seq[pos]);
     for (aalta_formula::af_prt_set::iterator it2 = P.begin (); it2 != P.end (); it2 ++)
     { 
       if (contain (f, *it2))
       {
         res.insert (*it2);
         Q.insert (*it2);
       }
     }
     temp = MUC_set (f, Q, OR (seq[pos]));
     res.insert (temp.begin (), temp.end ());
     Q.insert (temp.begin (), temp.end ());
     
   }
   
   return res;
 }
 
 //compute the set of unsat core for the formula f under the condition negation Next (avoid)
 //Note to avoid the unsat core already exists in Q
 aalta_formula::af_prt_set 
 nondeter_prog_state::MUC_set (aalta_formula *f, aalta_formula::af_prt_set Q, aalta_formula *avoid)
 {
   //printf ("before muc_set, the formula f is \n%s\n", f->to_string().c_str ());
   aalta_formula::af_prt_set res, res1, P;
   aalta_formula *temp, *to_check_formula, *ucore;
   for (aalta_formula::af_prt_set::iterator it = Q.begin (); it != Q.end (); it ++)
   {
     temp = erase_from (f, *it);
     if (temp != NULL)
     {
       to_check_formula = create_check_formula (temp, avoid);
       P = to_check_formula->SAT ();
       if (P.empty ())
       {
         Q.erase (*it);
         return MUC_set (temp, Q, avoid);
       }
     }
   }
   
   ucore = MUC (f->to_set (), avoid);
   if (ucore == NULL)
   {
     //printf ("MUC_set:: ucore is NULL\n");
     //printf ("MUC_set:: avoid is \n%s\n", avoid->to_string ().c_str ());
     return res;
   }
   res.insert (ucore);
   
   temp = erase_from (f, ucore);
   if (temp != NULL)
   {
     to_check_formula = create_check_formula (temp, avoid);
     P = to_check_formula->SAT ();
     if (P.empty ())
     {
       res1 = MUC_set (temp, Q, avoid);
       res.insert (res1.begin (), res1.end ());
     }
   }
   return res;
 }
 
 //erase f2 from f1
 aalta_formula* 
 nondeter_prog_state::erase_from (aalta_formula* f1, aalta_formula* f2)
 {
   aalta_formula::af_prt_set P1, P2;
   P1 = f1->to_set ();
   P2 = f2->to_set ();
   for (aalta_formula::af_prt_set::iterator it = P2.begin (); it != P2.end (); it ++)
   {
     if (P1.find (*it) != P1.end ())
       P1.erase (*it);
     else
       return NULL;
   }
   return AND (P1);
 }
 
 //check whether there is one formula f' in Q such that elements of f' are included in f  
 bool 
 nondeter_prog_state::contain_one_of (aalta_formula *f, aalta_formula::af_prt_set Q)
 {
   for (aalta_formula::af_prt_set::iterator it = Q.begin (); it != Q.end (); it ++)
   {
     if (contain (f, *it))
       return true;
   }
   return false;
 }
 
 //check whether elements of f2 are included in f1
 bool 
 nondeter_prog_state::contain (aalta_formula *f1, aalta_formula *f2)
 {
   aalta_formula::af_prt_set P1, P2;
   P1 = f1->to_set ();
   P2 = f2->to_set ();
   for (aalta_formula::af_prt_set::iterator it = P2.begin (); it != P2.end (); it ++)
   {
     if (P1.find (*it) == P1.end ())
       return false;
   }
   return true;
 }
 
 //initial the avoidable sequence
 void 
 nondeter_prog_state::initial_seq (std::vector<aalta_formula::af_prt_set >& seq, aalta_formula::af_prt_set common)
 {
   /*
   aalta_formula *guarantee_check = create_check_formula (AND (common), NULL);
   aalta_formula::af_prt_set P2 = guarantee_check->SAT();
   if (P2.empty ())
   {
     aalta_formula* ucore = MUC (AND (common), NULL);
     update_avoid_with (ucore);
     seq.clear ();
     return;
   }
   */
   aalta_formula::af_prt_set q0;
   q0.insert (AND (_unsatisfied_untils));
   seq.push_back (q0);
   int pos = 0;
   aalta_formula *current_avoid = OR (seq[pos]);
   aalta_formula* f_to_check = create_check_formula (AND (common), current_avoid);
   aalta_formula::af_prt_set P = f_to_check->SAT();
   aalta_formula* ucore;
   aalta_formula::af_prt_set qi;
   aalta_formula* total_avoid;
   while (P.empty ())
   {
     ucore = MUC (common, current_avoid);
     
     if (ucore == NULL)
     {
       update_avoid_with (current_avoid);
       seq.clear ();
       return;
     }
     assert (ucore != NULL);
     qi.clear ();
     qi.insert (ucore);
     seq.push_back (qi);
     //print_seq (seq);
     pos ++;
     total_avoid = update_avoid (seq, pos);
     if (is_invariant (total_avoid))
     {
       update_avoid_with (total_avoid);
       seq.clear ();
       return;
     }
     
     current_avoid = OR (seq[pos]);
     f_to_check = create_check_formula (AND (common), current_avoid);
     P = f_to_check->SAT();
   }
 }
 
 //update avoid due to whether pos or seq changes
 aalta_formula* 
 nondeter_prog_state::update_avoid (std::vector<aalta_formula::af_prt_set > seq, int pos)
 {
   aalta_formula *res = NULL;
   aalta_formula::af_prt_set Q;
   for (int i = 0; i <= pos; i ++)
   {
     Q = seq[i];
     if (res == NULL)
       res = OR (Q);
     else
       res = aalta_formula (aalta_formula::And, res, OR (Q)).unique ();
   }
   return res;
 }
 
 //update the information of avoidable sequence
 void 
 nondeter_prog_state::update_seq (std::vector<aalta_formula::af_prt_set >& seq, aalta_formula::af_prt_set S, int pos)
 {
   aalta_formula::af_prt_set Q;
   if (seq.size () > pos)
   {
     Q = seq [pos];
     Q.insert (S.begin (), S.end ());
     seq [pos] = Q;
   }
   else
   {
     assert (pos == seq.size ());
     seq.push_back (S);
   }
 }
 
 //check whether current avoid is invariant
 bool 
 nondeter_prog_state::is_invariant (aalta_formula *f)
 {
 /*
   aalta_formula* flat = f->flatted ();
   if (_global_flatted_formula != NULL)
     flat = aalta_formula (aalta_formula::And, flat, _global_flatted_formula).unique ();
   if (_avoid != NULL)
     flat = aalta_formula (aalta_formula::And, flat, _avoid).unique ();
   flat = aalta_formula (aalta_formula::And, flat, negation_next (f)).unique ();
   */
   aalta_formula *flat = create_check_formula (f, f);
   aalta_formula::af_prt_set P = flat->SAT();
   
   if (P.empty ())
     return true;
   else
     return false;
 }
 
 //get a set of reachable states from the original postponed state
 aalta_formula::af_prt_set 
 nondeter_prog_state::distinguish_states (aalta_formula::af_prt_set& S)
 {
   S.insert (_formula);
   aalta_formula *f = erase_global (_formula);
   assert (f != NULL);
   aalta_formula::af_prt_set common = f->to_set ();
   
   aalta_formula *next_state, *f2, *pre_state;
   aalta_formula::af_prt_set prop_atoms, P2;
   f2 = aalta_formula (aalta_formula::Or, OR (_unsatisfied), negation_next (AND (common))).unique ();
   aalta_formula *f_to_check = create_check_formula (S, NULL);
   f_to_check = aalta_formula (aalta_formula::And, f2, f_to_check).unique ();
   aalta_formula::af_prt_set P = f_to_check->SAT ();
   aalta_formula::af_prt_set::iterator it;
   aalta_formula* temp;
   //printf ("in distinguish_states\n");
   while (!P.empty ())
   {
     pre_state = previous_state (S, P);

     assert (pre_state != NULL);
     next_state = next_in (P, pre_state->flatted ());
     for (it = _unsatisfied.begin (); it != _unsatisfied.end (); it ++)
     {
       if (P.find (*it) != P.end ())
       {
         common.clear ();
         //printf ("distinguish_states::pre_state is \n%s\n", pre_state->to_string ().c_str ());
         fill_witness_from_to (pre_state);
         assert (!_witness.empty ());
         //printf ("after distinguish_state, the number of states is %d\n", (int)S.size ());
         //printf ("after distinguish_state, the number of _witness is %d\n", (int)_witness.size ());
         return common;
       }
     }
     update_node (pre_state, NULL, current_in (P), next_state);
     S.insert (next_state);
     
     
     f_to_check = create_check_formula (erase_global (next_state), NULL);
     f_to_check = aalta_formula (aalta_formula::And, OR (_unsatisfied), f_to_check).unique ();
     P = f_to_check->SAT ();
     if (!P.empty ())
     {
       common.clear ();
       fill_witness_from_to (next_state);
         assert (!_witness.empty ());
         //printf ("after distinguish_state, the number of states is %d\n", (int)S.size ());
         //printf ("after distinguish_state, the number of _witness is %d\n", (int)_witness.size ());
         return common;
     }
     

     common = intersect (common, next_state->to_set ());
     f2 = aalta_formula (aalta_formula::Or, OR (_unsatisfied), negation_next (AND (common))).unique ();

     f_to_check = create_check_formula (S, NULL);
     f_to_check = aalta_formula (aalta_formula::And, f2, f_to_check).unique ();
     P = f_to_check->SAT ();
   }
   //printf ("after distinguish_state, the number of states is %d\n", (int)S.size ());
   return common;
 }
 
 //get the previous state in S that points to the next state in P
 aalta_formula* 
 nondeter_prog_state::previous_state (const aalta_formula::af_prt_set& S, const aalta_formula::af_prt_set& P)
 {
   aalta_formula *res = NULL;
   for (aalta_formula::af_prt_set::const_iterator it = S.begin (); it != S.end (); it ++)
   { 
     if (model (P, (*it)->flatted ()))
     {
       res = *it;
       break;
     }
   }
   return res;
 }
 
 //check whether assignment P propositionally satisfies f
 bool 
 nondeter_prog_state::model (const aalta_formula::af_prt_set& P, aalta_formula* f)
 {
   assert (f->oper () != aalta_formula::Until && f->oper () != aalta_formula::Release);
   if (f->oper () == aalta_formula::And)
     return model (P, f->l_af ()) && model (P, f->r_af ());
   else if (f->oper () == aalta_formula::Or)
     return model (P, f->l_af ()) || model (P, f->r_af ());
   else if (P.find (f) != P.end ())
     return true;
   else 
     return false;
 }
 
 //intersection between set P1 and P2
 aalta_formula::af_prt_set 
 nondeter_prog_state::intersect (aalta_formula::af_prt_set P1, aalta_formula::af_prt_set P2)
 {
   aalta_formula::af_prt_set res;
   for (aalta_formula::af_prt_set::iterator it = P1.begin (); it != P1.end (); it ++)
   {
     if (P2.find (*it) != P2.end ())
       res.insert (*it);
   }
   return res;
 }
 
 //create the formula need to be checked by SAT solvers
 aalta_formula* 
 nondeter_prog_state::create_check_formula (aalta_formula *cur, aalta_formula *not_next)
 {
   aalta_formula *flat = NULL;
   if (cur != NULL) 
   {
     flat = cur->flatted ();
     if (not_next != NULL)
       flat = aalta_formula (aalta_formula::And, flat, negation_next (not_next)).unique ();
     if (_global_flatted_formula != NULL)
       flat = aalta_formula (aalta_formula::And, flat, _global_flatted_formula).unique ();
     if (_avoid != NULL)
       flat = aalta_formula (aalta_formula::And, flat, _avoid).unique (); 
   }
   else
   {
     if (not_next != NULL)
       flat = negation_next (not_next);
     if (_global_flatted_formula != NULL)
     {
       if (flat != NULL)
         flat = aalta_formula (aalta_formula::And, flat, _global_flatted_formula).unique ();
       else 
         flat = _global_flatted_formula;
     }
     if (_avoid != NULL)
     {
       if (flat != NULL)
         flat = aalta_formula (aalta_formula::And, flat, _avoid).unique ();
       else
         flat = _avoid; 
     }
   }
    
   return flat;
 }
 
 aalta_formula* 
 nondeter_prog_state::create_check_formula (aalta_formula::af_prt_set S, aalta_formula *not_next)
 {
   aalta_formula::af_prt_set::const_iterator it;
   aalta_formula::af_prt_set P;
   aalta_formula *f;
   for (it = S.begin (); it != S.end (); it ++)
   {
     f = erase_global (*it);
     if (f != NULL)
       P.insert (f);
   }
   return create_check_formula (OR (P), not_next);
 }

 aalta_formula::af_prt_set nondeter_prog_state::_avoids;
 aalta_formula* nondeter_prog_state::_last_invariant = NULL;
 void 
 nondeter_prog_state::update_avoid_with (aalta_formula *f)
 {
   if (f == NULL)
   {
     _avoid = aalta_formula::FALSE ();
     _current_avoid = _avoid;
   }
   else if (_avoid == NULL)
   {
     _avoid = negation_next (f);
     _current_avoid = f;
   }
   else
   {
     if (_avoids.find (f) == _avoids.end ())
     {
       _avoid = aalta_formula (aalta_formula::And, _avoid, negation_next (f)).unique ();
       if (_current_avoid == NULL)
         _current_avoid = f;
       else
         _current_avoid = aalta_formula (aalta_formula::And, _current_avoid, f).unique ();
       _avoids.insert (f);
     }
   }
   _last_invariant = f;
   
 }
 
 std::pair<aalta_formula::af_prt_set, aalta_formula*> 
 nondeter_prog_state::empty_pair ()
 {
   aalta_formula::af_prt_set P;
   P.clear ();
   return std::make_pair (P, aalta_formula::FALSE ());
 }
 
 bool nondeter_prog_state::_no_until_fulfilled = true;
 
 std::pair<aalta_formula::af_prt_set, aalta_formula*> 
 nondeter_prog_state::assignment_pair (aalta_formula::af_prt_set P)
 {
   aalta_formula *f2 = convert_to_formula (P);
   //f2 = erase_next_global (f2);
   //printf ("f2 is :\n%s\n", f2->to_string().c_str ());
   aalta_formula::af_prt_set P2 = current_in (P);
   
   //aalta_formula::af_prt_set prop_atoms = propAtoms (_flatted_formula);
   //checker::print (prop_atoms);
   //aalta_formula *nx = next_in (P, prop_atoms);
   aalta_formula *nx = next_in (P, _flatted_formula);

   if (f2->oper () == aalta_formula::Not)
     f2 = f2->r_af ();
   else
     f2 = aalta_formula (aalta_formula::Not, NULL, f2).unique ();
   if (_unsatisfied.empty ())
   {
     _unsatisfied = get_until_element_of (nx);
     _no_until_fulfilled = true;
   }
   else
   {
     for (aalta_formula::af_prt_set::iterator it = P2.begin (); it != P2.end (); it ++)
     {
       //printf ("%s\n", (*it)->to_string ().c_str ());
       if (_unsatisfied.find (*it) != _unsatisfied.end ())
         _unsatisfied.erase (*it);
     }
     if (_unsatisfied.empty ())
     {
       _no_until_fulfilled = false;
       _pre_seq_hist.clear ();
     }
   }
   //printf ("after nondeter_prog_state::get_next_pair::_unsatisfied:\n");
   //checker::print (_unsatisfied);
   std::pair<aalta_formula::af_prt_set, aalta_formula*> pa = std::make_pair (P2, nx);
   
   return pa;
 }
 
 
 bool 
 nondeter_prog_state::no_need_fulfilled (aalta_formula *f)
 {
   aalta_formula::af_prt_set P = f->to_set ();
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
   {
     if ((*it)->oper() == aalta_formula::Until)
       return false;
   }
   return true;
 }
 
 aalta_formula* nondeter_prog_state::_global_flatted_formula = NULL;
 
 void 
 nondeter_prog_state::set_global ()
 {
   aalta_formula::af_prt_set P = _formula->to_set ();
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
   {
     if ((*it)->oper () == aalta_formula::Release && (*it)->l_af() == aalta_formula::FALSE ())
       _globals.insert (*it);
   }
   _global_flatted_formula = convert_to_formula (_globals);
   if (_global_flatted_formula != NULL)
     _global_flatted_formula = _global_flatted_formula->flatted ();
 }
 
 aalta_formula* 
 nondeter_prog_state::erase_global (aalta_formula *f)
 {
  /*
   aalta_formula::af_prt_set P = f->to_set ();
   aalta_formula::af_prt_set P2;
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
   {
     if (_globals.find (*it) == _globals.end ())
       P2.insert (*it);
   }
   aalta_formula *res = convert_to_formula (P2);
   return res;
   */
   aalta_formula *res = NULL, *res1, *res2;
   if (f->oper () == aalta_formula::And)
   {
     res1 = erase_global (f->l_af());
     res2 = erase_global (f->r_af());
     if (res1 == NULL)
       res = res2;
     else if (res2 == NULL)
       res = res1;
     else
       res = aalta_formula (f->oper(), res1, res2).unique ();
   }
   else
   {
     if (f->is_globally () && _globals.find (f) != _globals.end ())
       res = NULL;
     else
       res = f;
   }
   return res;
 }
 

 
 aalta_formula* 
 nondeter_prog_state::convert_to_formula (aalta_formula::af_prt_set P)
 {
   aalta_formula *result = NULL;
   aalta_formula::af_prt_set temp;
   aalta_formula::af_prt_set::iterator it;
   //remove the negative Next formulas, i.e. !(X a)
   for (it = P.begin (); it != P.end (); it ++)
   {
     if ((*it)->oper () == aalta_formula::Not)
     {
       //assert ((*it)->r_af ()->oper () != aalta_formula::Until);
       //assert ((*it)->r_af ()->oper () != aalta_formula::Release);
       //assert ((*it)->r_af ()->oper () != aalta_formula::And);
       //assert ((*it)->r_af ()->oper () != aalta_formula::Or);
       if ((*it)->r_af ()->oper () == aalta_formula::Next)
         continue;
     }
     else
     {
       //assert ((*it)->oper () != aalta_formula::Until);
       //assert ((*it)->oper () != aalta_formula::Release);
       //assert ((*it)->oper () != aalta_formula::And);
       //assert ((*it)->oper () != aalta_formula::Or);
     }
     if (result == NULL)
       result = *it;
     else
       result = aalta_formula (aalta_formula::And, result, *it).unique ();
   } 

   return result;
 }
 
 aalta_formula* 
 nondeter_prog_state::generate_constraint (aalta_formula::af_prt_set P)
 {
   aalta_formula *result = NULL;
   if (P.empty ())
     return NULL;
   aalta_formula::af_prt_set::iterator it = P.begin ();
   result = *it;
   it ++;
   for (; it != P.end (); it ++)
   {
     result = aalta_formula (aalta_formula::Or, result, *it).unique ();
   } 

   return result;
 }
 
 aalta_formula::af_prt_set 
 nondeter_prog_state::current_in (aalta_formula::af_prt_set P)
 {
   aalta_formula::af_prt_set result;
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
   {
     if ((*it)->oper () > aalta_formula::Undefined)
       result.insert (*it);
     else if (((*it)->oper () == aalta_formula::Not) && ((*it)->r_af()->oper () > aalta_formula::Undefined))
       result.insert (*it);
   }
   return result;
 }
 
 //get the propositional atoms in the LTL formula f. 
 //Note f does not contain global formulas, so we must add them back at first.
 aalta_formula::af_prt_set 
 nondeter_prog_state::propAtoms (aalta_formula *f)
 {
   //if (_global_flatted_formula != NULL)
     //f = aalta_formula (aalta_formula::And, f, _global_flatted_formula).unique ();
   return propAtoms_child (f);
 }
 
 //child process of propAtoms
 aalta_formula::af_prt_set 
 nondeter_prog_state::propAtoms_child (aalta_formula *f)
 {
   aalta_formula::af_prt_set res, res1, res2;
   assert (f->oper () != aalta_formula::Until && f->oper () != aalta_formula::Release);
   if (f->oper () > aalta_formula::Undefined || f->oper () == aalta_formula::Next)
     res.insert (f);
   else
   {
     if (f->l_af () != NULL)
       res1 = propAtoms_child (f->l_af ());
     if (f->r_af () != NULL)
       res2 = propAtoms_child (f->r_af ());
     res.insert (res1.begin (), res1.end ());
     res.insert (res2.begin (), res2.end ());
   }
   return res;
 }
 
 
 aalta_formula* 
 nondeter_prog_state::next_in (aalta_formula::af_prt_set P, aalta_formula::af_prt_set prop_atoms)
 {
   aalta_formula *result = NULL, *l, *r;
   aalta_formula::af_prt_set P2;
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
   {
     //printf ("%s\n", (*it)->to_string ().c_str ());
     if ((*it)->oper () == aalta_formula::Next && prop_atoms.find (*it) != prop_atoms.end ())
       P2.insert ((*it)->r_af ());
   }
   if (P2.empty ())
     result = aalta_formula::TRUE ();
   else 
     result = convert_to_formula (P2);
   return result;
   
 }
 
 aalta_formula* 
 nondeter_prog_state::next_in (const aalta_formula::af_prt_set &P, aalta_formula *flat)
 {
   aalta_formula *result = NULL;
   aalta_formula::af_prt_set P2;
   for (aalta_formula::af_prt_set::const_iterator it = P.begin (); it != P.end (); it ++)
   {
     //printf ("%s\n", (*it)->to_string ().c_str ());
     if ((*it)->oper () == aalta_formula::Next && flat->find_prop_atom (*it))
       P2.insert ((*it)->r_af ());
   }
   if (P2.empty ())
     result = aalta_formula::TRUE ();
   else 
     result = convert_to_formula (P2);
   return result;
 }

 
 aalta_formula* 
 nondeter_prog_state::apply_next (aalta_formula *f)
 {
   assert (f != NULL);
   aalta_formula *res;
   if (f->oper () == aalta_formula::And || f->oper () == aalta_formula::Or)
   {
     aalta_formula *f1 = apply_next (f->l_af ());
     aalta_formula *f2 = apply_next (f->r_af ());
     res = aalta_formula (f->oper (), f1, f2).unique ();
   }
   else
     res = aalta_formula (aalta_formula::Next, NULL, f).unique ();
   return res;
 }
 
 aalta_formula* 
 nondeter_prog_state::negation_next (aalta_formula *f)
 {
   assert (f != NULL);
   aalta_formula *res = apply_next (f);
   res = aalta_formula (aalta_formula::Not, NULL, res).unique ();
   //res = aalta_formula (aalta_formula::And, res, aalta_formula (aalta_formula::Not, NULL, f).unique ()).unique ();
   return res;
   
 }
 
 
 

 
 void 
 nondeter_prog_state::destroy ()
 {
 /*
   std::vector<nondeter_prog_state*>::iterator it;
   for(it = _all_progfs.begin (); it != _all_progfs.end (); it ++)
   {
     delete *it;
   }
   */
 }
 
