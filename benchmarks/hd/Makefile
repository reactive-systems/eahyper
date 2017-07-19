.PHONY: all clean clean_csv demo

all:
	go build hd_gen.go

clean:
	rm -f hd_gen cnf.dimacs runsolver_out_* solver_out_* stats_*

clean_csv:
	rm -f *.csv

demo: all
	./hd_script.sh 120 aalta
	../eval.sh "hd_aalta.csv"
