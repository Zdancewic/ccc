LIBS = unix,str,nums

all: Main.native

Parser.ml:
	ocamlbuild -libs $(LIBS) Parser.ml -use-menhir -yaccflag --explain

.PHONY: Main.native
Main.native: 
	ocamlbuild -libs $(LIBS) Main.native -use-menhir -yaccflag --explain

.PHONY: clean
clean:
	ocamlbuild -clean
