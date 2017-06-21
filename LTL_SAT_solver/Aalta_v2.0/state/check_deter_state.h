 /* 
 * Deterministic state for checking
 * 
 * File:   check_deter_state.h
 * Author: Jianwen Li
 * 
 *
 * Created on October 21, 2014
 */

#ifndef CHECK_DETER_STATE_H
#define	CHECK_DETER_STATE_H

#include "formula/aalta_formula.h"
#include "progression/progression.h"

class check_deter_state 
{
  public:
    check_deter_state (progression *progf, aalta_formula* af=NULL)
    {
      _progf = progf;
      if (af != NULL)
        _formula = af;
      else
        _formula = progf->to_formula ();
    }
    ~check_deter_state () { }
    aalta_formula *get_formula () {return _formula;}
    progression *get_progf () {return _progf;}
    
  private:
    aalta_formula *_formula;
    progression *_progf;
    
};


#endif
