/* 
 * File:   sat_solver.cpp
 * Author: yaoyinbo
 * 
 * Created on October 27, 2013, 1:46 PM
 */

#include "sat_solver.h"
#include "util/utility.h"
#include "formula/olg_formula.h"
#include <iostream>
using namespace std;


#include <algorithm>

///////////////////////////////////////////
// 开始静态部分
/* 初始化静态变量 */
sat_solver::timestamp sat_solver::dfn;
sat_solver::timestamp sat_solver::low;

/**
 * 将公式按照op分离存于集合中
 * @param op
 * @param af
 * @param s
 */
void
sat_solver::split2set (int op, aalta_formula *af, edge_set *s)
{
  if (af == NULL) return;

  if (af->oper () != op)
    {
      s->insert (af);
    }
  else
    {
      split2set (op, af->l_af (), s);
      split2set (op, af->r_af (), s);
    }
}

/**
 * 判断一个强联通分支是否可满足
 * @param af
 * @param s
 * @return 
 */
bool
sat_solver::scc_sat (aalta_formula *af, edge_set *s)
{
  switch (af->oper ())
    {
    case aalta_formula::And:
      return scc_sat (af->l_af (), s) && scc_sat (af->r_af (), s);
    case aalta_formula::Or:
      return scc_sat (af->l_af (), s) || scc_sat (af->r_af (), s);
    case aalta_formula::Until:
    case aalta_formula::Release:
    case aalta_formula::Next:
      return scc_sat (af->r_af (), s);
    case aalta_formula::True:
      return true;
    case aalta_formula::False:
      return false;
    default:
      return s->find (af) != s->end ();
    }
}

std::string
scc_str (aalta_formula *af)
{
  switch (af->oper ())
    {
    case aalta_formula::And:
      return "(" + scc_str (af->l_af ()) + " && " + scc_str (af->r_af ()) + ")";
    case aalta_formula::Or:
      return "(" + scc_str (af->l_af ()) + " || " + scc_str (af->r_af ()) + ")";
    case aalta_formula::Until:
    case aalta_formula::Release:
    case aalta_formula::Next:
      return scc_str (af->r_af ());
    case aalta_formula::True:
      return "true";
    case aalta_formula::False:
      return "false";
    default:
      return af->to_string ();
    }
}

// 结束静态部分
///////////////////////////////////////////

sat_solver::sat_solver () { }

sat_solver::~sat_solver ()
{
  for (scc_edge::iterator sit = _scc.begin (); sit != _scc.end (); sit++)
    delete sit->second;
  _scc.clear ();
  dnf_formula::destroy ();
}

/**
 * 初始化
 */
void
sat_solver::init ()
{
  this->_index = 1;
  this->low.clear ();
  this->dfn.clear ();
  while (!this->_stk.empty ())this->_stk.pop ();
  this->_instk.clear ();
  this->_result = "";
  _path.clear();
  _states.clear();
  _evidence = "";
}

/**
 * 获取sat证据
 * @return 
 */
std::string
sat_solver::get_result ()const
{
  return "(" + this->_result + ")";
}

/**
 * 判断字符串公式是否可满足
 * @param input
 * @return 
 */
bool
sat_solver::sat (const std::string& input)
{
  return sat (input.c_str ());
}

/**
 * 判断字符串公式是否可满足
 * @param input
 * @return 
 */
bool
sat_solver::sat (const char *input)
{
  if (input == NULL || input[0] == '\0')
    return false;
  aalta_formula af (input);
  //print_msg(("af :" + af.to_string ()).c_str());
  return sat (af.unique ());
}

/**
 * 判断aalta_formula公式是否可满足
 * @param af
 * @return 
 */
bool
sat_solver::sat (aalta_formula& af)
{
  return sat (af.unique ());
}

/**
 * 判断aalta_formula公式是否可满足
 * @param afp
 * @return 
 */
bool
sat_solver::sat (aalta_formula *afp)
{
  init ();
  return tarjan (afp->unique ());
}

std::vector<sat_solver::edge_set> sat_solver::_path;
std::vector<aalta_formula*> sat_solver::_states;

//generate the evidence for satisfiable formulas
string 
sat_solver::set_to_string(edge_set atoms)
{
  string res = "";
  edge_set::iterator it;
  for(it = atoms.begin(); it != atoms.end(); it ++)
  {
    res += (*it)->to_string();
  }
  return res;
}
void 
sat_solver::generate_evidence(hash_map<int, bool> vMap)
{
  int size = _path.size();
  for(int i = 0; i < size; i++)
  {
    string s = set_to_string(_path[i]);
    _evidence += s + ", ";
  }
  string literals = "";
  hash_map<int, bool>::iterator it;
  for(it = vMap.begin(); it != vMap.end(); it ++)
  {
    if(it->second)
      literals += aalta_formula::get_name(it->first);
    else
      literals += "!" + aalta_formula::get_name(it->second);
  }
  _evidence += "(" + literals + ")";
}
void 
sat_solver::generate_evidence(std::vector<edge_set> prefix, std::vector<edge_set> scc)
{
  int size = prefix.size();
  for(int i = 0; i < size; i++)
  {
    string s = set_to_string(prefix[i]);
    _evidence += s + ", ";
  }
  string loop = "";
  size = scc.size();
  for(int i = size - 1; i >= 0; i --)
  {
     loop += set_to_string(scc[i]);
     if(i != 0)
       loop += ", ";
  }
  _evidence += "(" + loop + ")";
}

int sat_solver::_count = 0;

/**
 * tarjan算法寻找强连通分量 O(n+m)
 * @param u
 * @return
 */
bool
sat_solver::tarjan (aalta_formula *u)
{
  //print_msg(("u: " + u->to_string ()).c_str());
  dfn[u] = low[u] = _index++;
  //cout << u->to_string() << endl;
  /* 判断该节点是否可满足 */
  
  switch (u->oper ())
    {
    case aalta_formula::True:
    {
      _evidence = "true";
      return true;
    }
    case aalta_formula::False:
      return false;
    default:
      {
        olg_formula olg (u);
        
        if (olg.sat ())
        {
          generate_evidence(olg._evidence);
          return true;
        }
        //printf ("%s\n", u->to_string().c_str());
        //printf ("_count = %d\n", _count++);
        if (olg.unsat ())
          return false;
          
          
      }
    }

  /* 遍历dnf */
  //cout << u->to_string() << endl;
  dnf_formula *dnf = dnf_formula (u).unique ();
  edge_set *es = new edge_set ();
  _scc[dnf] = es;
  edge_set::iterator eit;

  _stk.push (u);
  _instk.insert (u);
  aalta_formula *v;
  dnf_formula::dnf_clause_set *dc_set = dnf->get_next ();
  int size = dc_set->size ();
  //printf("size: %d\n",size);
  if (size > 0)
    {
      /* 将dnf_clause按照next的公式长度排序 */
      int i = 0;
      dnf_clause *dnf_arr = new dnf_clause[size + 1];
      for (dnf_formula::dnf_clause_set::iterator it = dc_set->begin (); it != dc_set->end (); it++)
      {
        dnf_arr[i++] = *it;
        //printf("%s\n", (*it).to_string().c_str());
      }
      std::sort (dnf_arr, dnf_arr + size);

      /* 遍历 */
      for (i = 0; i < size; ++i)
        {
          _path.push_back(dnf_arr[i].current->and_to_set());
          _states.push_back(u);
          
          v = dnf_arr[i].next->unique ();
          if (dfn.find (v) == dfn.end ())
            {
              if (tarjan (v)) return true;
              timestamp::iterator u_it = low.find (u);
              timestamp::iterator v_it = low.find (v);
              if (u_it->second > v_it->second)
                u_it->second = v_it->second;
            }
          else if (_instk.find (v) != _instk.end ())
            {
              timestamp::iterator u_it = low.find (u);
              timestamp::iterator v_it = low.find (v);
              if (u_it->second > v_it->second)
                u_it->second = v_it->second;
            }
          
          
          
          if (low[u] == low[v])
            { // 合并强连通上的边
              split2set (aalta_formula::And, dnf_arr[i].current, es);
              if (u != v)
                {
                  edge_set *next_edge = _scc[dnf_formula::get_dnf (v)];
                  for (eit = next_edge->begin (); eit != next_edge->end (); eit++)
                    es->insert (*eit);
                }
              if (scc_sat (u->unique (), es))
                {
                  /*
                  printf("es: ");
                  for(eit = es->begin(); eit != es->end (); eit ++)
                  {
                    printf("%s: %p\n", (*eit)->to_string().c_str(), (*eit));
                  }
                  */
                  
                  aalta_formula *aff = _states.back();
                  _states.pop_back();
                  std::vector<edge_set> path;
                  while(aff != v)
                  {
                    path.push_back(_path.back());
                    _path.pop_back();
                  }
                  generate_evidence(_path, path);
                  delete[] dnf_arr;
                  return true;
                }
            }
        }
      delete[] dnf_arr;
    }

  if (dfn[u] == low[u])
    {
      do
        {
          v = _stk.top ();
          _instk.erase (v);
          _stk.pop ();
        }
      while (v != u);
    }
  return false;
}

hash_set<aalta_formula*> sat_solver::ltlf_visited;
bool 
sat_solver::satLTLf(aalta_formula *af)
{
  if(af->oper() == aalta_formula::True)
  {
    _evidence = "true";
    return true;
  }
  if(af->oper() == aalta_formula::False)
    return false;
  
  if(af->is_global()) //for global formulas
  {
    aalta_formula *afg = af->ofg();
    olg_formula olg (afg);
    return olg.sat();
  }
  
  if(!af->is_wnext_free()) //weak Next free
  {
    aalta_formula *aaf = af->off();
    olg_formula olg (aaf);
    if(olg.sat())
    {
      generate_evidence(olg._evidence);
      return true;
    }
  }
  else
  {  
    aalta_formula *aaf = af->simplify();
    olg_formula olg (aaf);
    if(olg.unsat())
      return false;
  }
  
  //for general case
  dnf_formula *dnf = dnf_formula (af).unique ();
  dnf_formula::dnf_clause_set *dc_set = dnf->get_next ();
  int size = dc_set->size ();
  aalta_formula *v;
  //printf("size: %d\n",size);
  if (size > 0)
    {
      /* 将dnf_clause按照next的公式长度排序 */
      int i = 0;
      dnf_clause *dnf_arr = new dnf_clause[size + 1];
      for (dnf_formula::dnf_clause_set::iterator it = dc_set->begin (); it != dc_set->end (); it++)
      {
        dnf_arr[i++] = *it;
        //printf("%s\n", (*it).to_string().c_str());
      }
      std::sort (dnf_arr, dnf_arr + size);

      /* 遍历 */
      ltlf_visited.insert(af);
      for (i = 0; i < size; ++i)
        {
          _path.push_back(dnf_arr[i].current->and_to_set());
          _states.push_back(af);
          
          v = dnf_arr[i].current->unique ();
          //af_prt_set P = v->to_set();
          if(af->model(v))
          {
            std::vector<edge_set> path;
            generate_evidence(_path, path);
            delete[] dnf_arr;
            return true;
          }
          v = dnf_arr[i].next->unique();
          if(ltlf_visited.find(v) == ltlf_visited.end())
          {
            if(satLTLf(v))
            {
              delete[] dnf_arr;
              return true;
            }
            
          }
        }
      delete[] dnf_arr;
    }
  
  return false;

}



