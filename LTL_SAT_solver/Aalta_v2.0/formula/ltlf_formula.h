/*
 * LTLf formula
 * created by Jianwen Li at May 29th, 2014
 */
 
#ifndef LTLF_H
#define	LTLF_H

#include "util/define.h"
#include "util/hash_map.h"
#include "util/hash_set.h"
#include "ltlparser/ltl_formula.h"

class ltlf_formula
{
private:
  int _op;
  ltlf_formula* _left;
  ltlf_formula* _right;
  size_t _hash;
  aalta_formula *_unique; // 指向唯一指针标识
  aalta_formula *_simp; // 指向化简后的公式指针
  
public:
  struct ff_hash
  {

    size_t operator () (const ltlf_formula& ff) const
    {
      return ff._hash;
    }
  };

  /* af指针的hash函数 */
  struct ff_prt_hash
  {

    size_t operator () (const ltlf_formula *ff_prt) const
    {
      return size_t (ff_prt);
    }
  };

  /* af指针的hash函数 */
  struct ff_prt_hash2
  {

    size_t operator () (const ltlf_formula *ff_prt) const
    {
      return ff_prt->_hash;
    }
  };
  /* af指针的相等函数 */
  struct ff_prt_eq
  {

    bool operator () (const ltlf_formula *ff_prt1, const ltlf_formula *ff_prt2) const
    {
      return *ff_prt1 == *ff_prt2;
    }
  };
  
  
};
