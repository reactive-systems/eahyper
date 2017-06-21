.PHONY: all clean aalta pltl clean_aalta clean_pltl

all: aalta pltl

clean: clean_aalta clean_pltl

aalta_:
	$(MAKE) -C "Aalta_v2.0" release

aalta: aalta_
	ln -s $(shell realpath "Aalta_v2.0/aalta") aalta

clean_aalta:
	$(MAKE) -C "Aalta_v2.0" clean
	rm aalta

pltl_:
	$(MAKE) -C pltl_src all

pltl:
	ln -s $(shell realpath "pltl_src/pltl") pltl

clean_pltl:
	$(MAKE) -C pltl_src clean
	rm pltl
