HAS_NPROC := $(shell if ocamlfind query nproc >/dev/null 2>&1; then echo yes; fi)

ML = ast.ml parser.ml lexer.ml util.ml term.ml \
	 config.ml  \
	 lexmaude.ml parsemaude.ml maude.ml \
	 rewriting.ml theory.ml \
	 base.ml horn.ml process.ml seed.ml lwt_compat.ml main.ml
MLI = $(wildcard $(ML:.ml=.mli)) parser.mli parsemaude.mli 
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
  ../examples/xor/misc/xor3.api \
  ../examples/xor/misc/statxor.api ../examples/xor/misc/nstatxor.api \
  ../examples/xor/misc/xorsym.api \
  ../examples/xor/misc/rigid.api 

# Basic tests + RFID tests without Toy-v1 + NSLxor tests,
# without duplicates
VALIDATION = $(TESTS) \
		 ../examples/xor/rfid/KCL.api \
		 ../examples/xor/rfid/KCL-running.api \
		 ../examples/xor/rfid/KCL-fixed.api \
		 ../examples/xor/rfid/LAK.api \
		 ../examples/xor/rfid/LD.api \
		 ../examples/xor/rfid/OTYT.api \
		 ../examples/xor/rfid/YPL.api \
		 ../examples/xor/NSLxor/nslhelp.api \
		 ../examples/xor/NSLxor/nsl.api \
		 ../examples/xor/NSLxor/NSL-xor-1a.api \
		 ../examples/xor/guessing/toy-protocol.api \
		 ../examples/xor/guessing/toy-protocol-passive.api \
		 ../examples/xor/guessing/secret-public-key-protocol.api \
		 ../examples/xor/guessing/secret-public-key-protocol-passive.api \
		 ../examples/xor/guessing/nonce-protocol.api \
		 ../examples/xor/guessing/nonce-protocol-passive.api \
		 ../examples/xor/guessing/gong-pwA-passive.api \
		 ../examples/xor/guessing/gong-pwB-passive.api \
		 ../examples/xor/guessing/direct-auth-protocol.api \
		 ../examples/xor/guessing/direct-auth-protocol-passive.api 

RUN = OCAMLRUNPARAM=b ./akiss -verbose

.PHONY: test actest dhtest validate

test:
	./runtests.sh test$(NAME) "$(TESTS)"

validate:
	./runtests.sh val$(NAME)  $(VALIDATION)
