.PHONY: all clean clean_csv demo

all:

clean:
	rm -f cnf.dimacs runsolver_out_* solver_out_* stats_*

clean_csv:
	rm -f *.csv

demo: all
	./symm_script.sh 60 aalta pltl
	../eval.sh "symm_aalta.csv"
	../eval.sh "symm_pltl.csv"
