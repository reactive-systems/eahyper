
FORMULAFILES =	formula/aalta_formula.cpp formula/dnf_clause.cpp \
		formula/dnf_formula.cpp formula/olg_formula.cpp formula/olg_item.cpp 
	
PARSERFILES  =	ltlparser/ltl_formula.c ltlparser/ltllexer.c ltlparser/ltlparser.c ltlparser/trans.c 

UTILFILES    =	util/utility.cpp

BUCHI	     =	buchi/buchi_node.cpp buchi/buchi_automata.cpp

MINISAT		= minisat/core/Solver.cc

CHECKING	=  checking/checker.cpp checking/nondeter_checker.cpp checking/scc.cpp

PROGRESSION	=  progression/nondeter_prog_state.cpp

ALLFILES     =	$(CHECKING) $(PROGRESSION) $(MINISAT) $(FORMULAFILES) $(PARSERFILES) $(UTILFILES) $(BUCHI) sat_solver.cpp main.cpp

COSAFETYFILES  =  $(PARSERFILES) $(UTILFILES) formula/aalta_formula.cpp cosafety2smv.cpp

CC	    =   g++
FLAG    = -I./ -I./minisat/ -I./formula/ -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS 
DEBUGFLAG   =	-g -pg
RELEASEFLAG =	-O2 

aalta :	release

ltlparser/ltllexer.c :
	ltlparser/grammar/ltllexer.l
	flex ltlparser/grammar/ltllexer.l

ltlparser/ltlparser.c :
	ltlparser/grammar/ltlparser.y
	bison ltlparser/grammar/ltlparser.y
	
	
cosafety2smv : $(COSAFETYFILES)
	       $(CC) $(FLAG) $(DEBUGFLAG) $(COSAFETYFILES) -lz -o cosafety2smv

.PHONY :    release debug clean

release :   $(ALLFILES)
	    $(CC) $(FLAG) $(RELEASEFLAG) $(ALLFILES) -lz -o aalta

debug :	$(ALLFILES)
	$(CC) $(FLAG) $(DEBUGFLAG) $(ALLFILES) -lz -o aalta

clean :
	rm -f *.o *~ aalta
