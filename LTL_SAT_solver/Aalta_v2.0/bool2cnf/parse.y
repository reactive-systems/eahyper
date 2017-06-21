%{

/*
 * Copyright 2011 Tatsuhiro Tsuchiya. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification, are
 * permitted provided that the following conditions are met:
 * 
 *    1. Redistributions of source code must retain the above copyright notice, this list of
 *       conditions and the following disclaimer.
 * 
 *    2. Redistributions in binary form must reproduce the above copyright notice, this list
 *       of conditions and the following disclaimer in the documentation and/or other materials
 *       provided with the distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY Tatsuhiro Tsuchiya ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
 * FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL Tatsuhiro Tsuchiya OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * The views and conclusions contained in the software and documentation are those of the
 * authors and should not be interpreted as representing official policies, either expressed
 * or implied, of Tatsuhiro Tsuchiya.
 * 
 */ 

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include "node.h"

int no_variables;
int no_terms;

int no_clauses;
int result_output;
extern int plus(Node *);
extern int yyparse();

  %}

%union {
  int var; /* variable index */
  Node *node;
}

%token <var> VAR
%token IMP

%type <node> program exp

%left  '=' 
%left IMP
%left  '|'
%left '&'
%right '!'

%start program
%%
program
: exp { result_output = 0; 
     plus( $1);
     printf("p cnf %d %d\n", no_terms, ++no_clauses);

     printf("%d 0\n", $1->index);
     result_output = 1; 
     plus( $1);
}
;

exp
: VAR           { $$ = make_node( VAR_Node, NULL, NULL, $1); printf("%d\n", $1);}
| '(' exp ')'   { $$ = $2; }
| exp '&' exp   { no_terms++; $$ = make_node( '&', $1, $3, no_terms); }
| exp '|' exp   { no_terms++; $$ = make_node( '|', $1, $3, no_terms); }
| exp '=' exp   { no_terms++; $$ = make_node( '=', $1, $3, no_terms); }
| exp IMP exp   { no_terms++; $$ = make_node( IMP_Node, $1, $3, no_terms); }
| '!' exp         { $$ = make_node( '!', $2, NULL, -$2->index); }
;
%%

int main(void)
{
  no_variables = no_terms = no_clauses = 0;
  (void) yyparse();
  return(0);
}

#include "lex.yy.c"
