 /* 
 * formula progression structure
 * 
 * File:   checker.h
 * Author: Jianwen Li
 * 
 *
 * Created on October 21, 2014
 */

#ifndef CHECK_H
#define	CHECK_H

#include "formula/aalta_formula.h"
#include "progression/progression.h"
#include "state/check_deter_state.h"
#include <vector>


class checker
{
  public:
    checker (aalta_formula*);
    ~checker ();
    bool check ();
    void show_evidence ();
    
  typedef hash_map<aalta_formula*, progression::progf_set, aalta_formula::af_prt_hash> af_progf_map;
    
  private:
    aalta_formula *_input;
    //evidence *_evi;
    static std::vector<check_deter_state*> _visited;        //states visited in current branch, the progf needs also to be recorded 
    //static std::vector<cycle*> _cycles;
    static af_progf_map _visited_map;
    static aalta_formula::af_prt_set _explored;                               //formulas explored in all branches
    
    bool dfs ();
    progression* find (std::vector<check_deter_state*>, aalta_formula*);
    aalta_formula* negation (aalta_formula::af_prt_set);
    bool model (progression*, progression*);
    void print (aalta_formula::af_prt_set);
    
    static std::vector<check_deter_state*> _all_sts;
    //static void destroy (); 
};

#endif
