
ML =  types.ml parser_functions.ml grammar.ml lexer.ml \
	util.ml dag.ml term.ml  \
	parsemaude.ml lexmaude.ml maude.ml \
	 rewriting.ml inputs.ml \
	  process.ml base.ml  horn.ml \
	 bijection.ml process_execution.ml tests.ml\
	 parser_queries.ml main.ml
MLI = $(wildcard $(ML:.ml=.mli)) grammar.mli parsemaude.mli
OCAMLC = ocamlfind ocamlopt -g -annot -package str,unix
OCAMLDEP = ocamldep -native
CMA = cmxa
CMO = cmx
OBJS = $(ML:.ml=.$(CMO))

akiss: $(OBJS)
	$(OCAMLC) -linkpkg -o akiss  $(OBJS)



%.$(CMO): %.ml
	$(OCAMLC)  -c $<

%.cmi: %.mli
	$(OCAMLC) -c $<

%.ml: %.mly
	ocamlyacc $<

%.ml: %.mll
	ocamllex $<

.depend: $(ML) $(MLI)
	$(OCAMLDEP) $(ML) $(MLI) > .depend

-include .depend

clean::
	rm -f parser.ml lexer.ml parser.mli lexer.mli
	rm -f lexmaude.ml lexmaude.mli parsemaude.ml parsemaude.mli
	rm -f lwt_compat.ml
	rm -f *.o *.cmi *.cmx *.cmo *.annot
	rm -f akiss
	rm -f .depend

doc: $(ML)
	mkdir -p doc
	ocamldoc -stars $(ML) -html -d doc

# TESTS

# Basic tests, with and without xor
TESTS = \
  ../examples/dag/test.api \
  ../examples/dag/ds-39.api \
  ../examples/dag/NSL-1chan-8sessions-4dishonest.api

VALIDATION = $(TESTS) \
		 ../examples/dag/BAC-2sessions.api  \
		 ../examples/dag/BAC-3sessions.api 

RUN = OCAMLRUNPARAM=b ./akiss -progress -bij

.PHONY: test validate

test:
	./runtests.sh test$(NAME) "$(TESTS)"

validate:
	./runtests.sh val$(NAME)  $(VALIDATION)
