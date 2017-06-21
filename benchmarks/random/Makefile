.PHONY: all clean clean_csv demo

all:

clean:
	rm cnf.dimacs runsolver_out_* solver_out_* stats_*

clean_csv:
	rm *.csv

demo: all
	./random_script.sh 120 "random_60/formularand_60_5_4_3" aalta pltl
	../eval.sh "formularand_60_5_4_3_aalta.csv"
