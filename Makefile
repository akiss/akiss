akiss: lexer.o parser.o util.o term.o variants.o horn.o process.o main.o 
	ocamlopt -o akiss lexer.cmx parser.cmx util.cmx term.cmx variants.cmx horn.cmx process.cmx main.cmx 

process.o: process.ml
	ocamlopt -c process.ml

horn.o: horn.ml
	ocamlopt -c horn.ml

variants.o: variants.ml
	ocamlopt -c variants.ml

term.o: term.ml
	ocamlopt -c term.ml

util.o: util.ml
	ocamlopt -c util.ml

main.o: main.ml
	ocamlopt -c main.ml

lexer.o: lexer.ml parser.ml
	ocamlopt -c lexer.ml

parser.o: parser.ml
	ocamlopt -c parser.ml

parser.ml: parser.mly
	ocamlyacc parser.mly && ocamlopt -i parser.ml > parser.mli && ocamlopt -c parser.mli

lexer.ml: lexer.mll
	ocamllex lexer.mll

clean:
	rm -rf *.o
	rm -rf parser.ml
	rm -rf lexer.ml
	rm -rf parser.mli
	rm -rf lexer.mli
	rm -rf akiss
	rm -rf *.cmi
	rm -rf *.cmx
	rm -rf *.o
