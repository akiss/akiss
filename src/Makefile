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

# TESTS

# Basic tests, with and without xor
TESTS = \
  ../examples/running-example/running-example-both-traces.api \
  ../examples/tests/xor3.api \
  ../examples/tests/statxor.api ../examples/tests/nstatxor.api \
  ../examples/tests/xorsym.api \
  ../examples/tests/rigid.api 

# Basic tests + RFID tests without Toy-v1 + NSLxor tests,
# without duplicates
VALIDATION = $(TESTS) \
			 ../examples/rfid/KCL-v1.api \
			 ../examples/rfid/KCL-v2.api \
			 ../examples/rfid/KCL-v3.api \
			 ../examples/rfid/KCL-v4.api \
			 ../examples/rfid/KCL-h1.api \
			 ../examples/rfid/KCL-h1bis.api \
			 ../examples/rfid/LAK-v1.api \
			 ../examples/rfid/LAK-v2.api \
			 ../examples/rfid/LD-v1.api \
			 ../examples/rfid/OTYT-v1.api \
			 ../examples/rfid/YPL-v1.api \
			 ../examples/rfid/YPL-v2.api \
			 ../examples/rfid/YPL-v3.api \
			 ../examples/NSLxor/nslhelp.api \
			 ../examples/NSLxor/nsl.api \
			 ../examples/NSLxor/NSL-xor-1a.api

# Case studies
CCS = ../examples/ccs/YPL-tag.api \
  ../examples/ccs/OTYT-tag.api \
  ../examples/ccs/NSL-xor-auth.api \
  ../examples/ccs/LD-tag.api \
  ../examples/ccs/LAK-tag.api \
  ../examples/ccs/LAK-auth.api \
  ../examples/ccs/KCL-tag.api \
  ../examples/ccs/KCL-running.api \
  ../examples/ccs/KCL-tag-correction.api \
  ../examples/ccs/KCL-running-correction.api

RUN = OCAMLRUNPARAM=b ./akiss -verbose

.PHONY: test actest dhtest validate

test:
	./runtests.sh test$(NAME) "$(TESTS)"

ccs:
	./runtests.sh ccs$(NAME) "$(CCS)"

validate:
	./runtests.sh val$(NAME)  $(VALIDATION)

test_tamarin: $(wildcard *.ml)
	ocamlopt unix.cmxa str.cmxa util.ml term.ml config.ml \
	  maude.ml lextam.ml parsetam.ml tamarin.ml test_tamarin.ml -o test_tamarin
