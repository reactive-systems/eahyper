#include "sat_solver.h"
#include "buchi/buchi_automata.h"
#include "checking/nondeter_checker.h"
#include "util/utility.h"
#include <stdio.h>
#include <string.h>
#include <sys/time.h>
#define MAXN 100000000
char in[MAXN];


void 
nondeter_sat (int argc, char** argv)
{
  if (argc == 1)
    {
      puts ("please input the formula:");
      if (fgets (in, MAXN, stdin) == NULL)
      {
        printf ("Error: read input!\n");
        exit (0);
      }
    }
  else
    {
      strcpy (in, argv[1]);
    }
  aalta_formula* af;
  
  af = aalta_formula(in).unique();
  af = af->simplify ();
  
  nondeter_checker ch (af);
  
  printf ("%s\n", ch.check () ? "sat" : "unsat");
  //aalta_formula::print_sat_count ();
  aalta_formula::destroy();
}

/*
void 
deter_sat (int argc, char** argv)
{
  if (argc == 1)
    {
      puts ("please input the formula:");
      if (fgets (in, MAXN, stdin) == NULL)
      {
        printf ("Error: read input!\n");
        exit (0);
      }
    }
  else
    {
      strcpy (in, argv[1]);
    }
  aalta_formula* af;
  
  af = aalta_formula(in).unique();
  af = af->simplify ();
  checker ch (af);
  //af = af -> classify();
  printf ("%s\n", ch.check () ? "sat" : "unsat");
  aalta_formula::destroy();
}
*/


void
sat (int argc, char** argv)
{
  //freopen ("tests/in", "r", stdin);
  bool dfa = false;
  bool f2l = false;
  if (argc == 1)
    {
      puts ("please input the formula:");
      if (fgets (in, MAXN, stdin) == NULL)
      {
        printf ("Error: read input!\n");
        exit (0);
      }
    }
  else
    {
      strcpy (in, argv[1]);
    }
  aalta_formula* af;
  sat_solver solver;
  
  af = aalta_formula(in).unique();
  af = af -> classify();
  printf ("%s\n", solver.sat (af) ? "sat" : "unsat");
  aalta_formula::destroy();
}

void
ltlf_sat (int argc, char** argv)
{
  //freopen ("tests/in", "r", stdin);
  bool dfa = false;
  bool f2l = false;
  if (argc == 1)
    {
      puts ("please input the formula:");
      if (fgets (in, MAXN, stdin) == NULL)
      {
        printf ("Error: read input!\n");
        exit (0);
      }
    }
  else
    {
      strcpy (in, argv[1]);
    }
  aalta_formula* af;
  sat_solver solver;
  
  af = aalta_formula(in, true).unique();
  af = af->simplify ();
  
  printf ("%s\n", solver.satLTLf (af) ? "sat" : "unsat");
  aalta_formula::destroy();
}

void
dnf (int argc, char** argv)
{
  if (freopen ("tests/in", "r", stdin) == NULL)
  {
    printf ("Error: read the file tests/in!\n");
    exit (0);
  }
  if (argc == 1)
    {
      puts ("please input the formula:");
      if (fgets (in, MAXN, stdin) == NULL)
      {
        printf ("Error: read input!\n");
        exit (0);
      }
    }
  else
    {
      strcpy (in, argv[1]);
    }
  dnf_formula dnf (in);
  printf ("%s\n", dnf.to_string ().c_str ());
}


void
buchi (int argc, char** argv)
{
  //freopen ("tests/in", "r", stdin);
  if (argc == 1)
    {
      puts ("please input the formula:");
      if (fgets (in, MAXN, stdin) == NULL)
      {
        printf ("Error: read input!\n");
        exit (0);
      }
    }
  else
    {
      strcpy (in, argv[1]);
    }
  buchi_automata ba (in);
  printf ("%s\n", ba.to_neverclaim ().c_str ());
  //printf ("%s\n", ba.to_lbtt ().c_str ());
  //  printf ("%s\n", ba.to_string ().c_str ());
}


double
current_time ()
{
  struct timeval tv;
  gettimeofday (&tv, NULL);
  return tv.tv_sec + tv.tv_usec / 1000000.0;
}

void print_help()
{
  printf("\n\tThe parameters of Aalta are listed as follows:\n");
  
  printf("\n\t\t-l -c (-e)\t\tLTL satisfiability checking (default). An evidence is shown if '-e' is given and the formula is satisfiable.;\n");
  printf("\n\t\t-f -c (-e)\t\tLTLf satisfiability checking. An evidence is given if '-e' is given and the formula is satisfiable.;\n");
  printf("\n\t\t-l -b\t\tLTL-to-Buchi translation.\n");
  printf("\n\t\t-h\t\t Help information\n");
  printf("\n\t\twhere every parameter has the meaning of:\n");
  printf("\t\t-l\t\tThe input is an LTL formula;\n");
  printf("\t\t-f\t\tThe input is an LTLf formula;\n");
  printf("\t\t-c\t\tDo the satisfiability checking;\n");
  printf("\t\t-e\t\tShow an evidence for the satisfiable formula;\n");
  printf("\t\t-b\t\tGenerate the Buchi automaton;\n");
}

int
main (int argc, char** argv)
{
/*
  bool ltl = false;
  bool ltlf = false;
  bool evidence = false;
  bool buchi = false;
  bool check = false;
  bool help = false;
  if(argc == 1)
  {
    ltl = true;
    check = true;
  }
  else
  {
    for (int i = 1; i < argc; i++)
    {
      if(strcmp(argv[i], "-l") == 0)
      {
        ltl = true;
        continue;
      }
      if(strcmp(argv[i], "-f") == 0)
      {
        ltlf = true;
        continue;
      }
      if(strcmp(argv[i], "-c") == 0)
      {
        check = true;
        continue;
      }
      if(strcmp(argv[i], "-e") == 0)
      {
        evidence = true;
        continue;
      }
      if(strcmp(argv[i], "-b") == 0)
      {
        buchi = true;
        continue;
      }
      if(strcmp(argv[i], "-h") == 0)
      {
        help = true;
        continue;
      }
    }
  }
  if(help)
  {
    print_help();
    return 0;
  }
  
  //to do: show the evidence!!
  if(ltl && check && !ltlf && !buchi)
  {
    puts ("please input the formula:");
    fgets (in, MAXN, stdin);
    aalta_formula* af;
    sat_solver solver;
  
    af = aalta_formula(in).unique();
    af = af -> classify();
    printf ("%s\n", solver.sat (af) ? "sat" : "unsat");
    if(evidence)
      printf ("%s\n", solver._evidence.c_str());
    aalta_formula::destroy();
    return 0;
  }
  if(ltlf && check && !ltl && !buchi)
  {
    puts ("please input the formula:");
    fgets (in, MAXN, stdin);
    aalta_formula* af;
    sat_solver solver;
    af = aalta_formula(in, true).unique();
    printf ("%s\n", solver.satLTLf (af) ? "sat" : "unsat");
    if(evidence)
      printf ("%s\n", solver._evidence.c_str());
    aalta_formula::destroy();
    return 0;
  }
  if(ltl && buchi && !ltlf && !check)
  {
    puts ("please input the formula:");
    fgets (in, MAXN, stdin);
    buchi_automata ba (in);
    printf ("%s\n", ba.to_neverclaim ().c_str ());
    return 0;
  }
  print_help();
  return 0;
  */
  
  //dnf (argc, argv);
  //sat (argc, argv);
  //ltlf_sat(argc, argv);
  //buchi (argc, argv);
  nondeter_sat (argc, argv);
  return 0;
  

}
