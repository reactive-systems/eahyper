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
   set_avoid ();
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
 }
 
 void 
 nondeter_prog_state::set_avoid ()
 {
   if (_avoid == NULL)
   {
     aalta_formula::af_prt_set P = _formula->get_alphabet ();
     //checker::print (P);
     _avoid = avoid_next_false (P);
     //printf ("%s\n", _avoid->to_string ().c_str ());
   }
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
 std::vector<aalta_formula*> nondeter_prog_state::_constraint_stack;
 
 void 
 nondeter_prog_state::print_nodes ()
 {
   hash_map<aalta_formula*, node*, aalta_formula::af_prt_hash>::iterator it;
   node* n;
   for (it = _f_node_map.begin (); it != _f_node_map.end (); it ++)
   {
     n = it->second;
     printf ("%s   %p->\n", it->first->to_string ().c_str (), (void*)it->first);
     printf ("<%s,  %s>\n", n->_formula->to_string ().c_str (), n->_ucore->to_string().c_str ());
   }
 }
 
 void 
 nondeter_prog_state::update_node (aalta_formula *f, aalta_formula *ucore, aalta_formula::af_prt_set P, aalta_formula *nx)
 {
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
     printf ("nondeter_prog::update_node:\n The formula already creates the node!\n%s  %p\n", nx->to_string().c_str(), (void*)nx);
     printf ("_potential_unsat is\n%s\n", OR(_potential_unsat)->to_string ().c_str ());
     printf ("the created nodes are:\n");
     print_nodes ();
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
 
 aalta_formula* 
 nondeter_prog_state::MUC (aalta_formula *f, aalta_formula *ucore)
 {
   //assert (ucore != NULL);
   aalta_formula::af_prt_set P, P2, P3, P4;
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
       if (P2.find (*it) == P2.end ())
         P3.insert (*it);
     }
   }
   P2.clear ();
   P2.insert (P.begin (), P.end ());
   P4.clear ();
   P.clear ();
   aalta_formula *f2, *f3;
   for (aalta_formula::af_prt_set::iterator it = P3.begin (); it != P3.end (); it ++)
   {
     if (_globals.find (*it) != _globals.end ())
       continue;
     P2.erase (*it);
     if (P2.empty ())
       return NULL;
     f2 = convert_to_formula (P2);
     f2 = f2->flatted ();
     if (_avoid != NULL)
       f2 = aalta_formula (aalta_formula::And, f2, _avoid).unique ();
     f3 = OR (_potential_unsat);
     if (f3 != NULL)
       f2 = aalta_formula (aalta_formula::And, f2, negation_next(f3)).unique ();
     if (ucore != NULL)
       f2 = aalta_formula (aalta_formula::And, f2, negation_next(ucore)).unique ();
     P4 = f2->SAT ();
     if (!P4.empty ())
     {
       P.insert (*it);
       P2.insert (*it);
     }
   }
   aalta_formula *res = convert_to_formula (P);
   return res;
   
 }

 
 aalta_formula::af_prt_set   
 nondeter_prog_state::UC (aalta_formula *f, aalta_formula *ucore)
 {
   printf ("before UC: the final ucore is\n%s\n", ucore->to_string ().c_str());
   assert (ucore != NULL);
   aalta_formula *temp = ucore;
   _potential_unsat.erase (ucore);
   aalta_formula *f2, *f3, *flat;
   flat = f->flatted ();
   if (_avoid != NULL)
     flat = aalta_formula (aalta_formula::And, flat, _avoid).unique ();
   f3 = OR (_potential_unsat);
   if (f3 != NULL)
     flat = aalta_formula (aalta_formula::And, flat, negation_next (f3)).unique ();
     
   f2 = flat;
   f2 = aalta_formula (aalta_formula::And, f2, negation_next (ucore)).unique ();
   aalta_formula::af_prt_set P = f2->SAT ();
   std::vector<aalta_formula*> constraint_stack;

   while (P.empty ())
   {
     f3 = MUC (f, ucore);
     if (f3 != NULL)
     {
       constraint_stack.push_back (ucore);
       ucore = aalta_formula (aalta_formula::And, ucore, f3).unique ();
       
       f2 = flat;
       f2 = aalta_formula (aalta_formula::And, f2, negation_next (ucore)).unique ();
       P = f2->SAT ();
     }
     else
       break;
   }
   if (P.empty ())
   {
     //ucore = temp;
     update_node (f, ucore, P, NULL);
   }
   else
   {
     //if (constraint_stack.size () > 0)
       //constraint_stack.pop_back ();
     for (int i = 0; i < constraint_stack.size (); i ++)
       _constraint_stack.push_back (constraint_stack[i]);
     update_node (f, ucore, current_in (P), next_in (P));
   }
   _potential_unsat.insert (ucore);
   printf ("after UC: the final ucore is\n%s\n", ucore->to_string ().c_str());
   return P;
   
 }
 
 void 
 nondeter_prog_state::UNSAT_INVARIANT (aalta_formula *f)
 {
   aalta_formula *f2, *f3, *ucore;
   printf ("UNSAT_INVARIANT: the formula is\n%s\n", erase_global(f)->to_string().c_str ());
   f2 = f->flatted ();
   if (_avoid != NULL)
     f2 = aalta_formula (aalta_formula::And, f2, _avoid).unique ();
   
   printf ("_constraint_stack size is %d\n", _constraint_stack.size ());  
   
   assert (_constraint_stack.size () >= 1);
   
   if (_constraint_stack.size () == 1)
     f3 = OR (_unsatisfied);
   else
   {
     f3 = _constraint_stack.back ();
     f3 = negation_next (f3);
   }
     
   if (f3 != NULL)
     f2 = aalta_formula (aalta_formula::And, f2, f3).unique ();
   aalta_formula::af_prt_set P, P2, P3;
   P = f2->SAT ();
   if (P.empty ())
   {
     ucore = _constraint_stack.back ();
     _constraint_stack.pop_back ();
     P2 = UC (f, ucore);
     if (P2.empty ())
     {
       _constraint_stack.push_back (ucore);
       UNSAT_INVARIANT_BACK ();
     }
     else
     {
       P3 = current_in (P2);
       f3 = next_in (P2);
       add_transition_to_node (f, P3, f3);
       UNSAT_INVARIANT (f3);
     }
   }
   else
   {
     
     f3 = next_in (P);
     update_node (f, NULL, current_in (P), f3);
     //add_transition_to_node (f, current_in (P), f3);
     if (_constraint_stack.size () == 1)
       fill_witness_from_to (f3);
     else
     { 
       _potential_unsat.insert (_constraint_stack.back ());
       _constraint_stack.pop_back ();
       UNSAT_INVARIANT (f3);
     }
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
       f3 = next_in (P);
       add_transition_to_node (formula, P2, f3);
       UNSAT_INVARIANT (f3);
       break;
     }
   }
   if (i >= size)
     UNSAT_INVARIANT_BACK ();
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
     printf ("_next_wanted is\n%s\n", _next_wanted->to_string ().c_str ());
     f = aalta_formula (aalta_formula::And, f, _next_wanted).unique ();
     //printf ("_formula is\n%s\n", _formula->to_string ().c_str ());
     P = f->SAT ();
     if (!P.empty ())
     {
       _fulfilled = false;   
       printf ("return here\n");
       //printf ("_next_wanted is\n%s\n", _next_wanted->to_string ().c_str ());
       return assignment_pair (P);
     }
     else
     {
       _next_wanted = NULL;
       f = _flatted_formula;
     }
     _fulfilled = false;
   }
   ///end of sat seeking part
   
   update_unsatisfied ();
   printf ("before nondeter_prog_state::get_next_pair::_unsatisfied:\n");
   checker::print (_unsatisfied);
   
   
   
   
   
   
   if (_avoid != NULL)
   {
     if (_avoid == aalta_formula::FALSE ())
     {
       return empty_pair ();
     }
     printf ("_avoid is: %s\n", _avoid->to_string().c_str ());
     f = aalta_formula (aalta_formula::And, f, _avoid).unique ();
   }
   
   P = f->SAT ();
   if (P.empty ())
   {
     //f is unsatisfiable itself
     aalta_formula *temp = MUC (_formula, NULL);  //all globals are removed in the core (they are not necessary)
     update_avoid_with (temp);
     return empty_pair ();
   }
   if (_unsatisfied.empty ())
     return assignment_pair (P);
   
   assert (!_unsatisfied_untils.empty ());
   assert (!_unsatisfied.empty ());
     
     
   f2 = OR (_unsatisfied);
   f = aalta_formula (aalta_formula::And, f, f2).unique ();
   
   P = f->SAT ();
   if (!P.empty ())
     return assignment_pair (P);
   else
   {
   /*
    * UNSAT_PUSURING mode
   */
     printf ("_formula is:\n%s\n", erase_global(_formula)->to_string().c_str ());
     _unsat_root = _formula;
     
     P = UC (_formula, AND (_unsatisfied_untils));
     if (!P.empty ())
       UNSAT_INVARIANT (next_in (P));
   
     if (_witness.empty ())
     {
       update_avoid_with (OR (_potential_unsat));
       pa = empty_pair ();
     }
     else
     {
       pa = _witness.back ();
       _witness.pop_back ();
     }   
     clear_f_node_map ();
     _potential_unsat.clear ();
     _constraint_stack.clear ();
     return pa;
   }
 }

 
 void 
 nondeter_prog_state::update_avoid_with (aalta_formula *f)
 {
   if (f == NULL)
     _avoid = aalta_formula::FALSE ();
   else if (_avoid == NULL)
     _avoid = negation_next (f);
   else
     _avoid = aalta_formula (aalta_formula::And, _avoid, negation_next (f)).unique ();
 }
 
 std::pair<aalta_formula::af_prt_set, aalta_formula*> 
 nondeter_prog_state::empty_pair ()
 {
   aalta_formula::af_prt_set P;
   P.clear ();
   return std::make_pair (P, aalta_formula::FALSE ());
 }
 
 
 std::pair<aalta_formula::af_prt_set, aalta_formula*> 
 nondeter_prog_state::assignment_pair (aalta_formula::af_prt_set P)
 {
   aalta_formula *f2 = convert_to_formula (P);
   //f2 = erase_next_global (f2);
   //printf ("f2 is :\n%s\n", f2->to_string().c_str ());
   aalta_formula::af_prt_set P2 = current_in (P);
   aalta_formula *nx = next_in (P);

   if (f2->oper () == aalta_formula::Not)
     f2 = f2->r_af ();
   else
     f2 = aalta_formula (aalta_formula::Not, NULL, f2).unique ();
   if (_unsatisfied.empty ())
     _unsatisfied = get_until_element_of (nx);
   else
   {
     for (aalta_formula::af_prt_set::iterator it = P2.begin (); it != P2.end (); it ++)
     {
       //printf ("%s\n", (*it)->to_string ().c_str ());
       if (_unsatisfied.find (*it) != _unsatisfied.end ())
         _unsatisfied.erase (*it);
     }
   }
   printf ("after nondeter_prog_state::get_next_pair::_unsatisfied:\n");
   checker::print (_unsatisfied);
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
 

 
 void 
 nondeter_prog_state::set_global ()
 {
   aalta_formula::af_prt_set P = _formula->to_set ();
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
   {
     if ((*it)->oper () == aalta_formula::Release && (*it)->l_af() == aalta_formula::FALSE ())
       _globals.insert (*it);
   }
 }
 
 aalta_formula* 
 nondeter_prog_state::erase_global (aalta_formula *f)
 {
   aalta_formula::af_prt_set P = f->to_set ();
   aalta_formula::af_prt_set P2;
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
   {
     if (_globals.find (*it) == _globals.end ())
       P2.insert (*it);
   }
   aalta_formula *res = convert_to_formula (P2);
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
 
 aalta_formula* 
 nondeter_prog_state::next_in (aalta_formula::af_prt_set P)
 {
   aalta_formula *result = NULL, *l, *r;
   aalta_formula::af_prt_set P2;
   for (aalta_formula::af_prt_set::iterator it = P.begin (); it != P.end (); it ++)
   {
     if ((*it)->oper () == aalta_formula::Next)
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
 
