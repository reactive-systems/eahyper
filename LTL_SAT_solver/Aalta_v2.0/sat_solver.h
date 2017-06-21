/* 
 * File:   sat_solver.h
 * Author: yaoyinbo and Jianwen Li
 * Note: Jianwen Li added the LTLf checking part
 *
 * On-the-fly Plus Obligation Acceleration 算法判可满足性 OFOA(λ):
 * 1) We first tag the formula and get λt. Then we construct Tλ,
 *    where we explore the states in an on-the-fly manner,
 *    by performing nest depth-first,
 * 2) Whenever a formula is found, we compute the obliga- tion set.
 *    In case that it contains a consistent obligation set, we return true,
 * 3) If a SCC B is reached, φ ∈ B,
 *    and L(B) is a superset of some obligation set O ∈ Olg(φ), we return true,
 * 4) If all SCCs are explored,
 *    and all do not have the property in step 3, we return false.
 * 
 * Created on October 27, 2013, 1:46 PM
 */

#ifndef SAT_SOLVER_H
#define	SAT_SOLVER_H

#include "formula/aalta_formula.h"
#include "formula/dnf_formula.h"
#include "formula/olg_item.h"

#include <stack>

class sat_solver
{
public:
  typedef hash_set<aalta_formula *> edge_set;
private:
  typedef hash_set<aalta_formula *> dnf_set;
  typedef hash_set<aalta_formula *> afp_set;
  typedef hash_map<aalta_formula *, int> timestamp;
  typedef hash_map<dnf_formula *, edge_set *> scc_edge;

  ///////////
  //成员变量//
  //////////////////////////////////////////////////
private:
  static timestamp low; //节点搜索的次序编号(时间戳)
  static timestamp dfn; //节点或节点的子树能够追溯到的最早的栈中节点的次序号

  int _index; //节点访问次序
  std::stack<aalta_formula *> _stk; //栈
  dnf_set _instk; // 记是否在栈中

  std::string _result; //记录sat证据
  scc_edge _scc; //记录scc边的信息
  //////////////////////////////////////////////////

  //------------------------------------------------
  /* 成员方法 */
public:
  sat_solver ();
  virtual ~sat_solver ();

  bool sat (const std::string& input);
  bool sat (const char *input);
  bool sat (aalta_formula& af);
  bool sat (aalta_formula *afp);
  std::string get_result()const;
  
  /*
   * LTLf satisfiability checking
   */
  bool satLTLf(aalta_formula *af);
private: 
  static hash_set<aalta_formula*> ltlf_visited;
private:
  void init ();
  bool tarjan (aalta_formula *u);
  
  static std::vector<edge_set> _path;
  static std::vector<aalta_formula*> _states;
  
  void generate_evidence(hash_map<int, bool>);
  void generate_evidence(std::vector<edge_set>, std::vector<edge_set>);
  std::string set_to_string(edge_set);
  
public:
  static bool scc_sat (aalta_formula *af, edge_set *s);
  static void split2set (int op, aalta_formula *af, edge_set *s);
  
  std::string _evidence;
  
  static int _count; 
};

#endif	/* SAT_SOLVER_H */

