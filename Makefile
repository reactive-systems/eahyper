.PHONY: all clean eahyper runsolver aalta pltl benchmarks clean_eahyper clean_runsolver clean_aalta clean_pltl clean_benchmarks

all: eahyper runsolver aalta pltl benchmarks

clean: clean_eahyper clean_runsolver clean_aalta clean_pltl clean_benchmarks

eahyper:
	$(MAKE) -C eahyper_src all

clean_eahyper:
	$(MAKE) -C eahyper_src clean

demo: all
	$(MAKE) -C eahyper_src demo

runsolver:
	$(MAKE) -C runsolver_src all

clean_runsolver:
	$(MAKE) -C runsolver_src clean

aalta:
	$(MAKE) -C LTL_SAT_solver aalta

clean_aalta:
	$(MAKE) -C LTL_SAT_solver clean_aalta

pltl:
	$(MAKE) -C LTL_SAT_solver pltl

clean_pltl:
	$(MAKE) -C LTL_SAT_solver clean_pltl

benchmarks: runsolver
	$(MAKE) -C benchmarks all

clean_benchmarks:
	$(MAKE) -C benchmarks clean
