/* 
 * scc structure
 * 
 * File:   scc.h
 * Author: Jianwen Li
 * 
 *
 * Created on November 16, 2014
 */

#ifndef SCC_H
#define SCC_H

#include "formula/aalta_formula.h"
#include "scc_state.h"
#include <vector>

class scc_state;
class scc_transition 
{
  public:

    struct scc_tran_prt_hash
    {

      size_t operator () (const scc_transition *scct_prt) const
      {
        return scct_prt->_hash;
      }
    };

    struct scc_tran_prt_eq
    {

      bool operator () (const scc_transition *scct_prt1, const scc_transition *scct_prt2) const
      {
        return *scct_prt1 == *scct_prt2;
      }
    };
  
    scc_transition (aalta_formula::af_prt_set, scc_state*);
    scc_transition (const scc_transition &);
    ~scc_transition () {}
    bool operator == (const scc_transition& )const;
    scc_transition* unique ();
    void print ();
    static void destroy ();
    typedef hash_set<scc_transition*, scc_tran_prt_hash, scc_tran_prt_eq> scc_tran_set;
  private:
    size_t _hash;
    aalta_formula::af_prt_set _edge;
    int _dest;
    static scc_tran_set _trans;
    
    scc_transition* clone ();
    void hash ();
};

class scc_state 
{
   public:
     scc_state (aalta_formula*);
     scc_state (scc_transition::scc_tran_set, aalta_formula *);
     scc_state (const scc_state &orig);
     int get_id () {return _id;}
     void add_transition (scc_transition *);
     aalta_formula *get_formula () {return _formula;}
     scc_state* merge (scc_state*);
     scc_state* clone ();
     void print ();
     void destroy ();
   private:
     int _id;
     aalta_formula *_formula;
     scc_transition::scc_tran_set _trans;
     
     //static std::vector<scc_state*> _sts;
     static int _max_id;
     typedef hash_map<aalta_formula*, int, aalta_formula::af_prt_hash, aalta_formula::af_prt_eq> formula_id_map;
     static formula_id_map _formula_ids;
};
 
 
class scc 
{
  public:
    scc (std::vector<aalta_formula*>, std::vector<aalta_formula::af_prt_set>);
    scc (scc_state*, hash_map<int, scc_state*>, aalta_formula::af_prt_set);
    ~scc () {}
    //void add_cycle (std::vector<aalta_formula*>, std::vector<aalta_formula::af_prt_set>);
    scc_state* root () {return _root;}
    aalta_formula::af_prt_set satisfied ()  {return _satisfied_untils;}
    //aalta_formula* normal (aalta_formula*);
    bool contain (int);
    aalta_formula::af_prt_set unsatisfied () {return _unsatisfied;}
    bool unsat_core ();
    aalta_formula* get_core_false ();
    aalta_formula::af_prt_set get_cores () {return _cores;}
    scc* merge (scc*);
    void print ();
    void destroy ();
  private:
    scc_state *_root;
    aalta_formula::af_prt_set _cores;
    //std::vector<scc_state*> _sts;
    aalta_formula::af_prt_set _satisfied_untils;
    aalta_formula::af_prt_set _unsatisfied;
    hash_map<int, scc_state*> _state_map;
    
    aalta_formula::af_prt_set get_mark_untils (aalta_formula::af_prt_set);
    aalta_formula::af_prt_set set_cores ();
    aalta_formula::af_prt_set set_unsatisfied ();
    
};

#endif
