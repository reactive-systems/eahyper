 /* 
 * deterministic formula progression structure
 * 
 * File:   deter_progression.h
 * Author: Jianwen Li
 * 
 *
 * Created on October 18, 2014
 */

#ifndef DETER_PROGRESSION_H
#define	DETER_PROGRESSION_H

#include "formula/aalta_formula.h"
#include <vector>

class deter_progression 
{
  public:
  
    typedef aalta_formula::af_prt_set af_prt_set;
    /* hashing funtion for progression pointers */
    struct progf_prt_hash
    {
      size_t operator () (const progression *p) const
      {
        return p->_hash;
      }
    };
    /* equal funtion for progression pointers */
    struct progf_prt_eq
    {

      bool operator () (const progression *p1, const progression *p2) const
      {
        return *p1 == *p2;
      }
    };
  
    progression (aalta_formula*);
    progression (const progression&);
    progression (int, progression*, progression*);
    progression (aalta_formula*, std::vector<progression*>);  //for until and release only
    virtual ~progression ();
    progression* progf(af_prt_set);
    progression* clone ();
    
    int type () {return _type;}
    bool operator == (const progression& p)const;
    std::pair<bool, progression*> intersect (progression*);
    progression* unique ();   
    aalta_formula* to_formula_from_list (std::vector<progression*>, int, aalta_formula*); //get the formula from the list
    aalta_formula* to_formula ();                        //get the real formula
    aalta_formula* to_inv_formula ();                    //get the invarant formula (Only Until and Release or their combinations)
    static void destroy ();
    std::string to_string (int &);
    void print ();
    bool is_true () {return _tt;}
    bool is_false () {return _ff;}
    bool compare (progression*);
    
    typedef hash_set<progression*, progf_prt_hash, progf_prt_eq> progf_set; 
    
  private:
    enum opkind
    {
    OR,
    AND,
    OTHER
    };
  
    size_t _hash;
    int _type;                                   // 1 for And, 0 for Or, -1 for others
    aalta_formula *_formula;                 
    
    progression *_left;
    progression *_right;
    std::vector<progression*> _formula_list;      //for Until or Release only
    bool _tt;                                      //is true? 
    bool _ff;                                      //is false?
    
    
    void hash ();                                //hash funtion computing _hash
    void simplify_formula_list (std::vector<progression*>&, int);
    
    static progf_set _all_progfs;             //store all created progressin objects
};


#endif
