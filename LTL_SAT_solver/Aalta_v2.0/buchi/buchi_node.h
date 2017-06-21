/* 
 * Buchi Automata节点声明
 * File:   buchi_node.h
 * Author: yaoyinbo
 *
 * Created on October 30, 2013, 4:12 PM
 */

#ifndef BUCHI_NODE_H
#define	BUCHI_NODE_H

#include "../formula/aalta_formula.h"

#include <utility>

class buchi_node
{
public:

  /* buchi_node的hash函数 */
  struct buchi_node_hash
  {

    size_t operator () (const buchi_node& node) const
    { //@ TODO: 是否存hash值
      size_t hash = HASH_INIT;
      hash = (hash << 5) ^ (hash >> 27) ^ (size_t) node._state;
      hash = (hash << 5) ^ (hash >> 27) ^ (size_t) node._p;
      return hash;
    }
  };
  typedef std::pair<aalta_formula *, buchi_node *> edge_t;

private:
  ///////////
  //成员变量//
  //////////////////////////////////////////////////
  aalta_formula *_state;
  aalta_formula *_p; //@ TODO: rename

  std::list<edge_t> _edges; // 边信息
  //////////////////////////////////////////////////

  //------------------------------------------------
  /* 成员方法 */
public:
  buchi_node (aalta_formula *state, aalta_formula *p = NULL);
  buchi_node (const buchi_node& orig);
  virtual ~buchi_node ();

  buchi_node& operator = (const buchi_node& node);
  bool operator == (const buchi_node& node)const;
  bool operator< (const buchi_node& node)const;

  buchi_node *clone()const;
  void add_edge (aalta_formula *edge, buchi_node *node);
  
  aalta_formula *get_state()const;
  aalta_formula *get_p()const;
  const std::list<edge_t> *get_edges()const;
  
  std::string to_string()const;
private:

};

#endif	/* BUCHI_NODE_H */

