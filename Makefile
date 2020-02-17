CMO= lexeur.cmo parser.cmo typer.cmo x86_64.cmo alloc_ast.cmo compile.cmo main.cmo
GENERATED = lexeur.ml parser.ml parser.mli
FLAGS=-annot -g

all: pkotlinc

pkotlinc: $(CMO)
	ocamlc $(FLAGS) -o $@ unix.cma $(CMO)

.SUFFIXES: .mli .ml .cmi .cmo .mll .mly


.mli.cmi:
	ocamlc $(FLAGS) -c  $<

.ml.cmo:
	ocamlc $(FLAGS) -c $<

.mll.ml:
	ocamllex $<

.mly.ml:
	menhir -v $<

.mly.mli:
	menhir -v $<

clean:
	rm _build/ -rf
	rm -f *.cm[io] *.o *.annot  $(GENERATED)
	rm -f parser.output parser.automaton parser.conflicts

.depend depend:$(GENERATED)
	rm -f .depend
	ocamldep *.ml *.mli > .depend

include .depend
