HAS_NPROC := $(shell if ocamlfind query nproc >/dev/null 2>&1; then echo yes; fi)

ML = ast.ml parser.ml lexer.ml util.ml term.ml \
	 config.ml maude.ml lextam.ml parsetam.ml tamarin.ml \
	 rewriting.ml theory.ml \
	 base.ml horn.ml process.ml seed.ml lwt_compat.ml main.ml
MLI = $(wildcard $(ML:.ml=.mli)) parser.mli parsetam.mli
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
	rm -f lwt_compat.ml
	rm -f *.o *.cmi *.cmx *.cmo
	rm -f akiss
	rm -f .depend

doc: $(ML)
	mkdir -p doc
	ocamldoc -stars $(ML) -html -d doc

# TESTS

# Xor and non-AC tests, should work
TESTS = \
  examples/running-example/running-example-both-traces.api \
  examples/tests/xor.api \
  examples/tests/statxor.api examples/tests/nstatxor.api \
  examples/tests/xorsym.api \
  examples/tests/rigid.api \
  examples/rfid/KCL-h1bis.api \
  examples/NSLxor/nslhelp.api \
  examples/NSLxor/nsl.api

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

# Basic tests + RFID tests without Toy-v1 + NSLxor tests,
# without duplicates
VALIDATION = $(TESTS) \
			 examples/rfid/KCL-v1.api \
			 examples/rfid/KCL-v2.api \
			 examples/rfid/KCL-v3.api \
			 examples/rfid/KCL-v4.api \
			 examples/rfid/LAK-v1.api \
			 examples/rfid/LAK-v2.api \
			 examples/rfid/LD-v1.api \
			 examples/rfid/OTYT-v1.api \
			 examples/rfid/YPL-v1.api \
			 examples/rfid/YPL-v2.api \
			 examples/rfid/YPL-v3.api \
			 examples/NSLxor/NSL-xor-1a.api

RUN = OCAMLRUNPARAM=b ./akiss -verbose

.PHONY: test actest dhtest validate

test:
	./runtests.sh test$(NAME) "$(TESTS)"

actest:
	./runtests.sh actest$(NAME) "$(AC_TESTS) $(AC_NOTESTS)"

dhtest:
	./runtests.sh actest$(NAME) "$(DH_TESTS) $(DH_NOTESTS)"

validate:
	./runtests.sh val$(NAME)  $(VALIDATION)

test_tamarin: $(wildcard *.ml)
	ocamlopt unix.cmxa str.cmxa util.ml term.ml config.ml \
	  maude.ml lextam.ml parsetam.ml tamarin.ml test_tamarin.ml -o test_tamarin

# STATS

STATS_TESTS = \
  $(wildcard examples/everlasting-ind/*.api) \
  $(wildcard examples/foo/*.api) \
  $(wildcard examples/guessing/*.api) \
  $(wildcard examples/needham-schroeder/*.api) \
  $(wildcard examples/okamoto/*.api) \
  $(wildcard examples/running-example/*.api) \
  $(wildcard examples/strong-secrecy/*.api) \

STATS_STATS = $(STATS_TESTS:.api=.stats)
STATS_JOBS := 1

stats: $(STATS_STATS)

clean::
	rm -f $(STATS_STATS)

%.stats: %.api
	/usr/bin/time -o $@ ./akiss -j $(STATS_JOBS) < $< > /dev/null 2>&1
