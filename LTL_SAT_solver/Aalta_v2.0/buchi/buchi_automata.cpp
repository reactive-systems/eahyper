/* 
 * File:   buchi_automata.cpp
 * Author: yaoyinbo
 * 
 * Created on October 30, 2013, 4:58 PM
 */

#include "buchi_automata.h"
#include "../util/utility.h"
#include "../sat_solver.h"

buchi_automata::buchi_automata (const char* input)
{
  buchi_node node (aalta_formula (input).unique ());
  explore (node);
  _initial = _nodes[node];
}

buchi_automata::buchi_automata (aalta_formula* formula)
{
  buchi_node node (formula->unique ());
  explore (node);
  _initial = _nodes[node];
}

buchi_automata::~buchi_automata ()
{
  for (node_map::const_iterator it = _nodes.begin (); it != _nodes.end (); it++)
    delete it->second;
}

/**
 * 构造Buchi Automata
 * @param v
 */
void
buchi_automata::explore (buchi_node& node)
{
  //print_msg(("node: " + node.to_string ()).c_str());
  if (_nodes.find (node) != _nodes.end ()) return;
  buchi_node *v = node.clone ();
  _nodes[node] = v;
  dnf_formula::dnf_clause_set* dc_set = dnf_formula (node.get_state ()).get_next ();
  sat_solver::edge_set set;
  for (dnf_formula::dnf_clause_set::iterator it = dc_set->begin (); it != dc_set->end (); it++)
    {
      aalta_formula *tmp = aalta_formula::merge_and (node.get_p (), (*it).current);
      set.clear ();
      sat_solver::split2set (aalta_formula::And, tmp, &set);
      if (sat_solver::scc_sat ((*it).next, &set))
        tmp = NULL;
      buchi_node next ((*it).next, tmp);
      //buchi_node next ((*it).next, aalta_formula::merge_and (node.get_p (), (*it).current));
      explore (next);
      v->add_edge ((*it).current, _nodes[next]);
    }
}

std::string
buchi_automata::to_neverclaim () const
{
  std::string ret = "never { /* ";
  ret += _initial->get_state ()->to_string ();
  ret += " */\n";
  hash_map<buchi_node *, int> ids;
  int id;
  for (node_map::const_iterator it = _nodes.begin (); it != _nodes.end (); it++)
    {
      if (ids.find (it->second) == ids.end ())
        {
          id = ids.size ();
          ids[it->second] = id;
        }
    }
  for (node_map::const_iterator it = _nodes.begin (); it != _nodes.end (); it++)
    {
      if (_initial == it->second) ret += "accept_init";
      else
        {
          ret += "T" + convert_to_string (ids[it->second]);
          if (it->second->get_p () == NULL)
            ret += "_accept";
        }
      ret += ":\n  if\n";
      const std::list<buchi_node::edge_t> *edges = it->second->get_edges ();
      for (std::list<buchi_node::edge_t>::const_iterator lit = edges->begin (); lit != edges->end (); lit++)
        {
          ret += "  :: (";
          ret += (*lit).first->to_string ();
          ret += ") -> goto ";
          if (_initial == (*lit).second) ret += "accept_init";
          else
            {
              ret += "T" + convert_to_string (ids[(*lit).second]);
              if ((*lit).second->get_p () == NULL)
                ret += "_accept";
            }
          ret += "\n";
        }
      ret += "  fi;\n";
    }
  ret += "}";
  return ret;
}

std::string
buchi_automata::to_lbtt () const
{
  std::string ret = convert_to_string (_nodes.size ());
  ret += " 1s\n";

  hash_map<buchi_node *, int> ids;
  ids[_initial] = 0;
  int id;
  for (node_map::const_iterator it = _nodes.begin (); it != _nodes.end (); it++)
    {
      if (ids.find (it->second) == ids.end ())
        {
          id = ids.size ();
          ids[it->second] = id;
        }
    }

  for (node_map::const_iterator it = _nodes.begin (); it != _nodes.end (); it++)
    {
      ret += convert_to_string (ids[it->second]);
      if (_initial == it->second) ret += " 1 0 -1\n";
      else
        {
          ret += " 0 ";
          if (it->second->get_p () == NULL)
            ret += "0 ";
          ret += "-1\n";
        }
      const std::list<buchi_node::edge_t> *edges = it->second->get_edges ();
      for (std::list<buchi_node::edge_t>::const_iterator lit = edges->begin (); lit != edges->end (); lit++)
        {
          ret += convert_to_string (ids[(*lit).second]);
          ret += " ";
          ret += (*lit).first->to_RPN ();
          ret += "\n";
        }
      ret += "-1\n";
    }

  return ret;
}

std::string
buchi_automata::to_string () const
{
  std::string ret;
  for (node_map::const_iterator it = _nodes.begin (); it != _nodes.end (); it++)
    ret += it->second->to_string ();
  return ret;
}
