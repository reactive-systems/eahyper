 /* 
 * nonderterministic formula progression structure
 * 
 * File:   nondeter_prog_state.h
 * Author: Jianwen Li
 * 
 *
 * Created on October 18, 2014
 */

#ifndef NODETER_PROG_STATE_H
#define	NODETER_PROG_STATE_H

#include "formula/aalta_formula.h"
#include "util/utility.h"
#include <vector>

class node
{
  public:
    node (aalta_formula* f, aalta_formula *uc) {_formula = f; _ucore = uc;}
    node (aalta_formula* f, aalta_formula *uc, std::pair<aalta_formula::af_prt_set, aalta_formula*> tran) 
      {_formula = f; _ucore = uc; _tran = tran;}
    aalta_formula* _formula;
    aalta_formula* _ucore;
    std::pair<aalta_formula::af_prt_set, aalta_formula*> _tran;
};


class nondeter_prog_state 
{
  public: 
    
    nondeter_prog_state (aalta_formula* af); 
    ~nondeter_prog_state (){}
    //nondeter_prog_state* clone ();
    static aalta_formula* convert_to_formula (aalta_formula::af_prt_set);
    //aalta_formula* add_constraint ();
    //void set_constraint (aalta_formula *f) {_constraints = f;}
    std::pair<aalta_formula::af_prt_set, aalta_formula*> get_next_pair (size_t);
    std::pair<aalta_formula::af_prt_set, aalta_formula*> assignment_pair (aalta_formula::af_prt_set);
    std::pair<aalta_formula::af_prt_set, aalta_formula*> empty_pair ();
    void update_avoid_with (aalta_formula*);
    
    aalta_formula::af_prt_set current_in (aalta_formula::af_prt_set);
    aalta_formula* next_in (aalta_formula::af_prt_set, aalta_formula::af_prt_set);
    
    
    static aalta_formula::af_prt_set get_until_element_of (aalta_formula*);
    
    //static void update_unsat (aalta_formula*);
    static aalta_formula* negation_next (aalta_formula*);
    static aalta_formula* apply_next (aalta_formula*);
    aalta_formula* global_next_true ();
    aalta_formula* next_must_true (aalta_formula *);
    bool is_prop (aalta_formula*);
    
    //void avoid_false_next (aalta_formula::af_prt_set);
    //static aalta_formula::af_prt_set get_false_next (aalta_formula*, aalta_formula::af_prt_set);
    
    //typedef hash_set<nondeter_prog_state*, progf_prt_hash, progf_prt_eq> progf_set;
    //nondeter_prog_state* unique ();
    //bool find (aalta_formula*);
    static void destroy ();
    //static bool confirm_unsat_scc ();
    //static void reset_potential ();
    //static aalta_formula::af_prt_set get_potential () {return _potentials;}
    //static bool _potential;
    //static bool is_potential () {return _potential;}
    static aalta_formula::af_prt_set unsatisfied () {return _unsatisfied;}
    static void initial_unsatisfied (aalta_formula*);
    static void set_next_wanted (aalta_formula *f) {_next_wanted = f;}  //set _next_wanted
    
    static aalta_formula::af_prt_set global () {return _globals;}
    static bool fulfilled () {return _fulfilled;}
    static aalta_formula *erase_global (aalta_formula*);
    
  private:
    aalta_formula *_formula;              //formula before progression
    aalta_formula *_flatted_formula;      //formula after progression
    aalta_formula::af_prt_set _prop_atoms;
    aalta_formula::af_prt_set propAtoms (aalta_formula*);
   
    static aalta_formula* _avoid;              //explored formula avoid to be visited in next state
    static aalta_formula::af_prt_set _avoids;  //the set of elements in _avoid
    //static aalta_formula* _potential_explored; //potential explored formula avoid to be visited in next state
    aalta_formula *_constraints;          //formula stored the constraint of _formula
    aalta_formula *_assignments;          //formula recording assignments visisted so far
    
    //static aalta_formula::af_prt_set _potentials;
    //static aalta_formula::af_prt_set _potential_candidates;
    static aalta_formula::af_prt_set _unsatisfied;
    
    //static std::vector<nondeter_prog_state*> _all_progfs;   //store all newed pointers
    static aalta_formula::af_prt_set _globals;
    static bool _global_not_set;
    static bool _invariant_found;
    static bool _fulfilled;
    
    static aalta_formula* _next_wanted;
    
    //aalta_formula *invariant_core (aalta_formula*);
    //aalta_formula* unsat_core (aalta_formula*);    
    
    void set_global ();
    //aalta_formula *erase_next_global (aalta_formula*);
    
    
    bool no_need_fulfilled (aalta_formula *);
    
    
    
    void set_avoid ();
    aalta_formula* avoid_next_false (aalta_formula::af_prt_set);
    //aalta_formula::af_prt_set get_next_literal (aalta_formula*);
    
    aalta_formula* generate_constraint (aalta_formula::af_prt_set);
    
   // aalta_formula* get_new_potential (aalta_formula*, aalta_formula*);
    
    void update_unsatisfied ();
    
    typedef std::vector<aalta_formula::af_prt_set > history_vec;
    typedef hash_map<aalta_formula*, history_vec > history_map;
    static history_map _hist_map;
    std::pair<aalta_formula::af_prt_set, bool> match_from_history (aalta_formula*, aalta_formula::af_prt_set);
    void update_history (aalta_formula*, aalta_formula::af_prt_set);
    aalta_formula* MUC (aalta_formula*, aalta_formula*);
    aalta_formula::af_prt_set  UC (aalta_formula*, aalta_formula*);
    void UNSAT_INVARIANT (aalta_formula*);
    void UNSAT_INVARIANT_BACK ();
    aalta_formula* OR (aalta_formula::af_prt_set);
    aalta_formula* AND (aalta_formula::af_prt_set);
    bool is_potential_unsat_invariant ();
    
    void update_node (aalta_formula*, aalta_formula*, aalta_formula::af_prt_set, aalta_formula*);
    void add_transition_to_node (aalta_formula*, aalta_formula::af_prt_set, aalta_formula*);
    void fill_witness_from_to (aalta_formula*);
    void clear_f_node_map ();
    
    static bool _fill_witness_already_done;
    static aalta_formula::af_prt_set _unsatisfied_untils;
    static void set_unsatisfied_untils ();
    static aalta_formula::af_prt_set _potential_unsat;
    static aalta_formula* _unsat_root;
    static std::vector<std::pair<aalta_formula::af_prt_set, aalta_formula*> > _witness; 
    static hash_map<aalta_formula*, node*, aalta_formula::af_prt_hash> _f_node_map;
    
    
    
    
    
    bool is_invariant (aalta_formula*);
    aalta_formula::af_prt_set distinguish_states (aalta_formula::af_prt_set&);
    aalta_formula::af_prt_set intersect (aalta_formula::af_prt_set, aalta_formula::af_prt_set);
    static aalta_formula* _global_flatted_formula;
    aalta_formula* create_check_formula (aalta_formula*, aalta_formula*);
    aalta_formula* create_check_formula (aalta_formula::af_prt_set, aalta_formula*);
    aalta_formula* update_avoid (std::vector<aalta_formula::af_prt_set >, int);
    void update_seq (std::vector<aalta_formula::af_prt_set >&, aalta_formula::af_prt_set, int);
    aalta_formula* previous_state (const aalta_formula::af_prt_set&, const aalta_formula::af_prt_set&);
    void initial_seq (std::vector<aalta_formula::af_prt_set >&, aalta_formula::af_prt_set);
    aalta_formula::af_prt_set compute_muc (aalta_formula::af_prt_set, std::vector<aalta_formula::af_prt_set >, int);
    bool contain_one_of (aalta_formula*, aalta_formula::af_prt_set);
    bool contain (aalta_formula*, aalta_formula*);
    aalta_formula* MUC (aalta_formula::af_prt_set, aalta_formula*);
    void split_binary (aalta_formula::af_prt_set, aalta_formula::af_prt_set&, aalta_formula::af_prt_set&);
    bool model (const aalta_formula::af_prt_set&, aalta_formula*);
    aalta_formula::af_prt_set propAtoms_child (aalta_formula*);
    void print_seq (std::vector<aalta_formula::af_prt_set >);
    aalta_formula* create_list_formula (std::list <aalta_formula::af_prt_set >);
    void print_f_node_map ();
    static aalta_formula* _last_invariant;
    aalta_formula* next_in (const aalta_formula::af_prt_set&, aalta_formula*);
    aalta_formula::af_prt_set MUC_set (aalta_formula*, aalta_formula::af_prt_set, aalta_formula*);
    aalta_formula* erase_from (aalta_formula*, aalta_formula*);
    bool is_initially (aalta_formula*);
    void update_global_flatted_formula (std::vector<aalta_formula::af_prt_set >);
    void set_input_flatted ();
    static aalta_formula* _input_flatted;
    static bool _no_until_fulfilled;
  public:
    static bool no_until_fulfilled () {return _no_until_fulfilled;}
  private:
    aalta_formula* global_next_n_true ();
    aalta_formula* get_next_n_formula (aalta_formula*, std::set<int>&, std::set<int>&);
    aalta_formula* create_next_avoid_false (aalta_formula *, int);
    aalta_formula* apply_next_n (aalta_formula *, int);
    void get_next_deep_map (hash_map<aalta_formula*, std::set<int>, aalta_formula::af_prt_hash >&);
    void get_next_deep_map_from (aalta_formula *, hash_map<aalta_formula*, std::set<int>, aalta_formula::af_prt_hash >&);
    void get_next_deep_from (aalta_formula *, hash_map<aalta_formula*, std::set<int>, aalta_formula::af_prt_hash >&);
    aalta_formula* prop_in_globals ();
    int common_deep (hash_map<aalta_formula*, std::set<int>, aalta_formula::af_prt_hash >&);
    
    bool compute_next_pair_from_history (std::pair<aalta_formula::af_prt_set, aalta_formula*>&);
    std::pair<aalta_formula::af_prt_set, aalta_formula*> compute_next_pair_via_seq (std::vector<aalta_formula::af_prt_set >, aalta_formula::af_prt_set);
    void update_until_avoid_seqs (aalta_formula::af_prt_set&, std::vector<aalta_formula::af_prt_set >);
    void update_pre_seq_hist (aalta_formula::af_prt_set&, std::vector<aalta_formula::af_prt_set >);
    static hash_map<aalta_formula*, std::vector<aalta_formula::af_prt_set> > _until_avoid_seqs;
    static std::vector<aalta_formula::af_prt_set> _pre_seq_hist;
    std::vector<aalta_formula::af_prt_set > adjust_to_unsatisfied (std::vector<aalta_formula::af_prt_set >);
    bool imply_avoid ();
    static aalta_formula* _current_avoid;
    /*
    size_t _pos;   //position of current state in the list visited
    static std::vector<Constraint> _constraint_stack;
    void update_constraint_stack ();
    Constraint back_of_constraint_stack ();
    bool constraint_stack_empty ();
    void pop_back_constraint_stack ();
    void update_back_of_constraint_stack (aalta_formula*, size_t, aalta_formula*);
    void erase_constraint_with_position (size_t);
    void push_to_constraint_stack (aalta_formula*, size_t, aalta_formula*);
    
    void print_constraint_stack ();
    */
    
    
    
    
    
};

#endif
