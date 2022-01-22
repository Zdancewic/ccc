.PHONY: clean ccc

all: ccc

ccc: 
	dune build
	@cp bin/main.exe ccc

test: ccc
	./ccc --test

utop:
	utop

clean:
	dune clean
	rm -rf ccc
