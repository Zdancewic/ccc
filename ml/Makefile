LIBS = unix,str,nums
BUILDFLAGS = -use-menhir -yaccflag --explain -tag debug
OCAMLFLAGS = -g

FILES = $(wildcard *.ml) Parser.mly Lexer.mll

all: Main.native

Parser.ml:
	ocamlbuild -libs $(LIBS) Parser.ml $(BUILDFLAGS) -cflags $(OCAMLFLAGS)

%.native: $(FILES)
	ocamlbuild -libs $(LIBS) $@ $(BUILDFLAGS) -cflags $(OCAMLFLAGS)

%.byte: $(FILES)
	ocamlbuild -libs $(LIBS) $@ $(BUILDFLAGS) -cflags $(OCAMLFLAGS)


utop: Top.byte
	utop

.PHONY: clean
clean:
	ocamlbuild -clean
