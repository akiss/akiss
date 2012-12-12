ML = lexer.ml parser.ml util.ml term.ml variants.ml horn.ml process.ml main.ml 
MLI = $(wildcard $(ML:.ml=.mli))
OCAMLC = ocamlopt
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

TESTS = tests/testac.api
RUN = ./akiss -verbose

test: akiss $(TESTS)
	@for i in $(TESTS) ; do \
	  echo '>>' Running $$i... ; \
	  $(RUN) < $$i || exit 1 ; \
	done
