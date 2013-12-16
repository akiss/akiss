ML = base.ml parser.ml lexer.ml util.ml term.ml maude.ml \
	 horn.ml process.ml main.ml 
MLI = $(wildcard $(ML:.ml=.mli))
OCAMLC = ocamlopt -g
CMA = cmxa
CMO = cmx
OBJS = $(ML:.ml=.$(CMO))

akiss: $(OBJS)
	$(OCAMLC) -o akiss unix.$(CMA) $(OBJS)

%.$(CMO): %.ml
	$(OCAMLC) -c $<

%.cmi: %.mli
	$(OCAMLC) -c $<

%.ml: %.mly
	ocamlyacc $< && $(OCAMLC) -c -i $@ > $(@:.ml=.mli)

%.ml: %.mll
	ocamllex $<

.depend: $(ML) $(MLI)
	ocamldep $(ML) $(MLI) > .depend

-include .depend

clean:
	rm -f *.o
	rm -f parser.ml
	rm -f lexer.ml
	rm -f parser.mli
	rm -f lexer.mli
	rm -f akiss
	rm -f *.cmi
	rm -f *.cmx
	rm -f *.cmo
	rm -f *.o

doc: $(ML)
	mkdir -p doc
	ocamldoc -stars $(ML) -html -d doc

# TESTS
# Run make (PREFIX=DH_) test/yestest/notest

# Xor and non-AC tests, should work
TESTS = \
  examples/tests/xor.api examples/tests/rfid.api \
  examples/tests/statxor.api \
  examples/tests/xorsym.api \
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
