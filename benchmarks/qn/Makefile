.PHONY: all clean clean_csv demo

all:
	go build qn_gen.go

clean:
	rm qn_gen cnf.dimacs runsolver_out_* solver_out_* stats_*

clean_csv:
	rm *.csv

demo: all
	./qn_script.sh 60 pltl
	../eval.sh "qn_pltl.csv"
