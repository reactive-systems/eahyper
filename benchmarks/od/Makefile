.PHONY: all clean clean_csv demo

all:
	go build od_gen.go

clean:
	rm -f od_gen cnf.dimacs runsolver_out_* solver_out_* stats_*

clean_csv:
	rm -f *.csv

demo: all
	./od_script.sh 60 aalta pltl
	../eval.sh "od_aalta.csv"
	../eval.sh "od_pltl.csv"
