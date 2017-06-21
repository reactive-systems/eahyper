/* 
 * Satisfiability checking by nondeterminism
 * 
 * File:   nondeter_checker.h
 * Author: Jianwen Li
 * 
 *
 * Created on November 15, 2014
 */

#ifndef NONDETER_CHECKER_H
#define NONDETER_CHECKER_H

#include "checker.h"
#include "progression/progression.h"
#include "formula/aalta_formula.h"
#include "scc.h"
#include <vector>

class nondeter_checker :public checker 
{
  public:
    nondeter_checker (aalta_formula*);
    ~nondeter_checker ();
    bool check ();
    void show_evidence ();
    
    bool unsat_of_core (aalta_formula*, aalta_formula::af_prt_set);
    //static void destroy ();
    typedef hash_map<aalta_formula*, int, aalta_formula::af_prt_hash, aalta_formula::af_prt_eq> formula_int_map;
  private:
    int _unsat_pos;
    bool dfs ();
    bool model (int);
    int visited (aalta_formula*);
    void update_scc (scc*);
    void update_explored (aalta_formula*);
    aalta_formula* seperate_next (aalta_formula*);
    void confirm_explored ();
    aalta_formula::af_prt_set collect_until (aalta_formula::af_prt_set);
    
    
    
    void set_next_wanted (aalta_formula*);
    aalta_formula* get_next_wanted (aalta_formula *);
    aalta_formula::af_prt_set get_nexts (aalta_formula *);
    aalta_formula* get_next_formula (aalta_formula *, aalta_formula::af_prt_set&);
    void set_solver_next_computed (aalta_formula *);

    
    
    std::vector<scc*> _sccs;
    static std::vector<aalta_formula::af_prt_set> _visited_edges;
    static std::vector<aalta_formula*> _visited;  
    static aalta_formula::af_prt_set _explored;
    static formula_int_map _formula_ints;
    static int count;
    static int _satisfied_pos;
    static int _next_satisfied_pos;
    static bool _start;
    static int compute_next_wanted_count_;
};



#endif
