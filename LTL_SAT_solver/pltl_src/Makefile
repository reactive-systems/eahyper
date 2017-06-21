######################################################################
# Makefile (use GNU-Make)
# $* part of the file name that matched the % in the target pattern.
# $@ file name of the target of the rule
# $^ names of the prerequisites
# $< name of the first prerequisite
# $? names of all the prerequisites that are newer than the target
######################################################################


.DEFAULT:
	@echo "This target needs remaking: default = [$<]"
	@echo "No rule provided"

# If defined, the code will be compiled into native code,
# else it will be compiled into byte code.
NATIVE := 

# If defined, the dependencies will be updated automatically.
CHECKDEP := true

# If defined, it indicates the number of cores
# that make should use (e.g. -j2 for two cores).
PARALLEL :=

# The projects which will be compiled if "make all" is used.
PROGS := pltl

LIBS := unix
SOURCESMLI := $(wildcard *.mli)
SOURCESML := $(wildcard *.ml)

OCAMLC := ocamlc
OCAMLCFLAGS := -g
OCAMLOPT := ocamlopt 
OCAMLOPTFLAGS := -g -unsafe -inline 100


# No more user input beyond this point.

ifdef NATIVE
OC := $(OCAMLOPT)
OCAMLDEP := ocamldep -native
SUFFIX := .cmx
SUFFIXLIB := .cmxa
FLAGS := $(OCAMLOPTFLAGS)
else
OC := $(OCAMLC)
OCAMLDEP := ocamldep
SUFFIX := .cmo
SUFFIXLIB := .cma
FLAGS := $(OCAMLCFLAGS)
endif

LIBS := $(patsubst %,%$(SUFFIXLIB),$(LIBS))
LIBSMLI := $(patsubst %.mli,%.cmi,$(SOURCESMLI))
LIBSML := $(patsubst %.ml,%$(SUFFIX),$(SOURCESML))


.PHONY: all
all:
	$(MAKE) $(PARALLEL) $(PROGS)

PLTL_OBJS := miscSolver$(SUFFIX) altGenlex$(SUFFIX) hashConsing$(SUFFIX) \
             PLTLFormula$(SUFFIX) PLTLMisc$(SUFFIX) \
             PLTLTree$(SUFFIX) PLTLGraph$(SUFFIX)

pltl: $(PLTL_OBJS) pltl$(SUFFIX)
	$(OC) -o pltl $(FLAGS) $(LIBS) $^


%.cmi: %.mli
	$(OCAMLC) -c $(OCAMLCFLAGS) $<

%.cmo: %.ml
	$(OCAMLC) -c $(OCAMLCFLAGS) $<

%.cmx: %.ml
	$(OCAMLOPT) -c $(OCAMLOPTFLAGS) $<


.PHONY: clean
clean:
	find -regextype posix-egrep -regex ".*((\.(cmi|cmo|cma|cmx|o|cmxa))|~)$$" -delete


.PHONY: depend
depend:
	$(OCAMLDEP) $(SOURCESMLI) $(SOURCESML) > .depend

ifdef CHECKDEP
.depend: $(SOURCESMLI) $(SOURCESML)
	$(OCAMLDEP) $(SOURCESMLI) $(SOURCESML) > .depend
endif

include .depend

