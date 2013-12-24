ML = ast.ml parser.ml lexer.ml util.ml term.ml \
	 config.ml maude.ml lextam.ml parsetam.ml tamarin.ml \
	 rewriting.ml theory.ml \
	 base.ml horn.ml process.ml main.ml 
MLI = $(wildcard $(ML:.ml=.mli)) parser.mli parsetam.mli
OCAMLC = ocamlopt -g
OCAMLDEP = ocamldep -native
CMA = cmxa
CMO = cmx
OBJS = $(ML:.ml=.$(CMO))

akiss: $(OBJS)
	$(OCAMLC) -o akiss str.$(CMA) unix.$(CMA) $(OBJS)

%.$(CMO): %.ml
	$(OCAMLC) -c $<

%.cmi: %.mli
	$(OCAMLC) -c $<

%.ml: %.mly
	ocamlyacc $<

%.ml: %.mll
	ocamllex $<

.depend: $(ML) $(MLI)
	$(OCAMLDEP) $(ML) $(MLI) > .depend

-include .depend

clean:
	rm -f parser.ml lexer.ml parser.mli lexer.mli
	rm -f lextam.ml lextam.mli parsetam.ml parsetam.mli
	rm -f *.o *.cmi *.cmx *.cmo
	rm -f akiss
	rm -f .depend

doc: $(ML)
	mkdir -p doc
	ocamldoc -stars $(ML) -html -d doc

# TESTS

# Xor and non-AC tests, should work
TESTS = \
  examples/tests/xor.api examples/tests/rfid.api \
  examples/tests/statxor.api \
  examples/tests/xorsym.api \
  examples/tests/rigid.api \
  examples/running-example/running-example-both-traces.api
NOTESTS = \
  examples/tests/nstatxor.api \
  examples/tests/rfid0h.api
LONGTESTS = examples/tests/rfid0.api examples/tests/rfid1.api

# Pure AC: most of them do not terminate
AC_TESTS = \
  examples/tests/stat.api \
  examples/tests/ac.apiexamples/tests/ac3.api \
  examples/tests/ac2.api
AC_NOTESTS = \
  examples/tests/nstat.api \
  examples/tests/nac.api \
  examples/tests/nac2.api \
  examples/tests/nac3.api

# Diffie-Hellman: surprisingly, they pass
DH_TESTS = examples/tests/dh.api
DH_NOTESTS = examples/tests/dhneg.api

RUN = OCAMLRUNPARAM=b ./akiss -verbose

.PHONY: test actest dhtest
test:
	./runtests.sh test "$(TESTS) $(NOTESTS)"
actest:
	./runtests.sh actest "$(AC_TESTS) $(AC_NOTESTS)"
dhtest:
	./runtests.sh actest "$(DH_TESTS) $(DH_NOTESTS)"

test_tamarin: $(wildcard *.ml)
	ocamlopt unix.cmxa str.cmxa util.ml term.ml config.ml \
	  maude.ml lextam.ml parsetam.ml tamarin.ml test_tamarin.ml -o test_tamarin
