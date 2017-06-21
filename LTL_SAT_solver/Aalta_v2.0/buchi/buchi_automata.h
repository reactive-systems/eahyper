/* 
 * Buchi Automata
 * File:   buchi_automata.h
 * Author: yaoyinbo
 *
 * Created on October 30, 2013, 4:58 PM
 */

#ifndef BUCHI_AUTOMATA_H
#define	BUCHI_AUTOMATA_H

#include "buchi_node.h"
#include "../formula/dnf_formula.h"

class buchi_automata
{
  ///////////
  //成员变量//
  //////////////////////////////////////////////////
private:
  typedef hash_map<buchi_node, buchi_node *, buchi_node::buchi_node_hash> node_map;
  buchi_node *_initial; // 初始状态
  
  node_map _nodes; // 记录生成的buchi_node
  
  static dnf_formula DNF; // 初始化dnf_formula，无实质用处
  //////////////////////////////////////////////////
  
  //------------------------------------------------
  /* 成员方法 */
public:
  buchi_automata (const char *input);
  buchi_automata (aalta_formula *formula);
  virtual ~buchi_automata ();
  
  std::string to_string()const;
  std::string to_neverclaim()const;
  std::string to_lbtt()const;
  
private:
  void explore(buchi_node& v);

};

#endif	/* BUCHI_AUTOMATA_H */

