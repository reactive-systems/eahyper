.PHONY: all clean clean_aalta clean_pltl

all: aalta pltl

clean: clean_aalta clean_pltl

aalta:
	$(MAKE) -C "Aalta_v2.0" release
	ln -s $(shell realpath "Aalta_v2.0/aalta") aalta

clean_aalta:
	$(MAKE) -C "Aalta_v2.0" clean
	rm -f aalta

pltl:
	$(MAKE) -C pltl_src all
	ln -sf $(shell realpath "pltl_src/pltl") pltl

clean_pltl:
	$(MAKE) -C pltl_src clean
	rm -f pltl
