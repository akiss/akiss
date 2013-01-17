ML = lexer.ml parser.ml util.ml term.ml cime.ml maude.ml horn.ml process.ml main.ml 
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
	rm -rf *.o
	rm -rf parser.ml
	rm -rf lexer.ml
	rm -rf parser.mli
	rm -rf lexer.mli
	rm -rf akiss
	rm -rf *.cmi
	rm -rf *.cmx
	rm -rf *.cmo
	rm -rf *.o

doc: $(ML)
	mkdir -p doc
	ocamldoc -stars $(ML) -html -d doc

TESTS = examples/tests/stat.api \
		examples/tests/ac.api examples/tests/ac2.api examples/tests/ac3.api
NOTESTS = examples/tests/nstat.api \
		  examples/tests/nac.api examples/tests/nac2.api examples/tests/nac3.api
RUN = OCAMLRUNPARAM=b ./akiss -verbose

test: akiss $(TESTS)
	@for i in $(TESTS) ; do \
	  echo ; \
	  echo '>>' Checking $$i... ; \
	  $(RUN) < $$i || exit 1 ; \
	done
	@for i in $(NOTESTS) ; do \
	  echo ; \
	  echo '>>' Checking NOT $$i... ; \
	  $(RUN) < $$i || exit 1 ; \
	done

BFILES = log akiss.dot akiss.lbl NOTES
backup:
	date=`date +%y%m%d%H%M` ; mkdir test-$$date ; cp $(BFILES) test-$$date
