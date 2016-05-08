HAS_NPROC := $(shell if ocamlfind query nproc >/dev/null 2>&1; then echo yes; fi)

ML = ast.ml parser.ml lexer.ml util.ml term.ml \
	 config.ml fullmaude.ml \
	 lexmaude.ml parsemaude.ml maude.ml \
	 lextam.ml parsetam.ml tamarin.ml \
	 rewriting.ml theory.ml \
	 base.ml horn.ml process.ml seed.ml lwt_compat.ml main.ml
MLI = $(wildcard $(ML:.ml=.mli)) parser.mli parsemaude.mli parsetam.mli 
OCAMLC = ocamlfind ocamlopt -g -annot -package str,unix $(if $(HAS_NPROC),-package nproc)
OCAMLDEP = ocamldep -native
CMA = cmxa
CMO = cmx
OBJS = $(ML:.ml=.$(CMO))

akiss: $(OBJS)
	$(OCAMLC) -linkpkg -o akiss $(OBJS)

ifeq ($(HAS_NPROC),)
lwt_compat.ml: lwt_compat_pure.ml
	cp $< $@
main.$(CMO): lwt_compat.$(CMO)
else
lwt_compat.ml:
	echo > $@
endif

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

clean::
	rm -f parser.ml lexer.ml parser.mli lexer.mli
	rm -f lextam.ml lextam.mli parsetam.ml parsetam.mli
	rm -f lexmaude.ml lexmaude.mli parsemaude.ml parsemaude.mli
	rm -f lwt_compat.ml
	rm -f *.o *.cmi *.cmx *.cmo *.annot
	rm -f akiss
	rm -f .depend

doc: $(ML)
	mkdir -p doc
	ocamldoc -stars $(ML) -html -d doc
