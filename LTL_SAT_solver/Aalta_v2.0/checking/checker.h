 /* 
 * Satisfiability checking 
 * 
 * File:   checker.h
 * Author: Jianwen Li
 * 
 *
 * Created on November 15, 2014
 */

#ifndef CHECK_H
#define	CHECK_H

#include "formula/aalta_formula.h"
#include "progression/progression.h"
#include <vector>


class checker
{
  public:
    checker (aalta_formula*);
    ~checker ();
    virtual bool check () = 0;
    virtual void show_evidence () = 0;
    static void print (aalta_formula::af_prt_set);
    
    aalta_formula *_input;
    
    aalta_formula* negation (aalta_formula::af_prt_set);
    
    virtual bool dfs () = 0;
    
};

#endif
