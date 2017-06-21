/* 
 * File:   buchi_node.cpp
 * Author: yaoyinbo
 * 
 * Created on October 30, 2013, 4:12 PM
 */

#include "buchi_node.h"

buchi_node::buchi_node (aalta_formula* state, aalta_formula* p)
: _state (state), _p (p) { }

buchi_node::buchi_node (const buchi_node& orig)
{
  *this = orig;
}

buchi_node::~buchi_node () { }

buchi_node& buchi_node::operator = (const buchi_node& node)
{
  if (this != &node)
    {
      _state = node._state;
      _p = node._p;
      _edges = node._edges;
    }
  return *this;
}

bool buchi_node::operator == (const buchi_node& node) const
{
  return _state == node._state && _p == node._p;
}

bool buchi_node::operator< (const buchi_node& node) const
{
  if (_state != node._state)
    return _state < node._state;
  return _p < node._p;
}

/**
 * 克隆出该对象的副本（需要在外部显式delete）
 * @return 
 */
buchi_node *
buchi_node::clone () const
{
  buchi_node *new_node = new buchi_node (*this);

  return new_node;
}

/**
 * 添一条边
 * @param edge
 * @param node
 */
void
buchi_node::add_edge (aalta_formula* edge, buchi_node* node)
{
  _edges.push_back (edge_t (edge, node));
}

aalta_formula *
buchi_node::get_state () const
{
  return _state;
}

aalta_formula *
buchi_node::get_p () const
{
  return _p;
}

const std::list<buchi_node::edge_t> *
buchi_node::get_edges () const
{
  return &_edges;
}

std::string
buchi_node::to_string () const
{
  std::string ret;
  ret += _state->to_string ();
  ret += " <" + (_p == NULL ? " " : _p->to_string ()) + ">\n{\n";
  for (std::list<edge_t>::const_iterator it = _edges.begin (); it != _edges.end (); it++)
    {
      ret += "\t" + (*it).first->to_string () + " -> " + (*it).second->_state->to_string ();
      ret += " <" + ((*it).second->_p == NULL ? " " : (*it).second->_p->to_string ()) + ">\n";
    }
  ret += "}\n";
  return ret;
}
