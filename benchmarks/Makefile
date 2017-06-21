.PHONY: all clean clean_csv od qn hd symm random clean_od clean_qn clean_hd clean_symm clean_random

all: od qn hd symm random

clean: clean_od clean_qn clean_hd clean_symm clean_random

od:
	$(MAKE) -C od all

clean_od:
	$(MAKE) -C od clean

qn:
	$(MAKE) -C qn all

clean_qn:
	$(MAKE) -C qn clean

hd:
	$(MAKE) -C hd all

clean_hd:
	$(MAKE) -C hd clean

symm:
	$(MAKE) -C symm all

clean_symm:
	$(MAKE) -C symm clean

random:
	$(MAKE) -C random all

clean_random:
	$(MAKE) -C random clean

clean_csv:
	$(MAKE) -i -C od clean_csv
	$(MAKE) -i -C qn clean_csv
	$(MAKE) -i -C hd clean_csv
	$(MAKE) -i -C symm clean_csv
	$(MAKE) -i -C random clean_csv
