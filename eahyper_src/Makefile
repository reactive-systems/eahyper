OCAMLBUILD=ocamlbuild
OCAMLBUILD_OPTS=-use-menhir -use-ocamlfind -menhir "menhir --explain" -pkg unix -pkg str

TARGET=eahyper
SOLVER_DIR="../LTL_SAT_solver/"

.PHONY: all clean demo

all: 
	$(OCAMLBUILD) $(OCAMLBUILD_OPTS) $(TARGET).native

clean:
	rm -f $(TARGET).native *~ \#*
	$(OCAMLBUILD) -clean

demo: all
	./eahyper.native -fs "exists x1. exists x2. forall y1. forall y2. G a_y1 & G b_y2 & G c_x1 & G d_x2" -v -d $(SOLVER_DIR)
