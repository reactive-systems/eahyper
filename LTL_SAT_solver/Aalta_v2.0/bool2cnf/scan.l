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

#include <stdlib.h>
#include <string.h>

#define MAX_No_Variables 10000
#define MAX_Length_String 64

int line_no = 1;
int variable_index(void);

%}

%%
[ \t]    { ; }
\n       { line_no ++;}
"->"     { return( IMP);}
[A-Za-z][A-Za-z0-9_]*   {
           yylval.var = variable_index();
           return( VAR);
         }
.        { return( yytext[ 0]); }
%%

int variable_index(void)
{
  static char variable_table[MAX_No_Variables][MAX_Length_String];
  static int variable_index[MAX_No_Variables];

  int i;

  for( i=0; i < MAX_No_Variables; i++)
    if( strncmp( variable_table[ i], yytext, MAX_Length_String)==0)
      return( variable_index[i]);

  no_variables++; no_terms++;
  if ( no_variables >= MAX_No_Variables)
    {
      fprintf(stderr, "too many variables\n");
      exit( 1);
    }
 
  variable_index[ no_variables -1] = no_terms;

  strncpy( variable_table[ no_variables -1], yytext, MAX_Length_String);
  return(  variable_index[ no_variables -1]);
}
