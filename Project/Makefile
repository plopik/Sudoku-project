SRCPATH = src
BINPATH = bin
SOURCES = Sudoku.ml
RESULT = Sudoku
PACKS = glpk

all:
	ocamlc glpk.cma unix.cma $(SRCPATH)/$(SOURCES) -o $(RESULT)
	mv $(SRCPATH)/*.cm* $(BINPATH)
	./Sudoku

clean:
	rm $(BINPATH)/*.cmi $(BINPATH)/*.cmo $(RESULT)

opt:
	ocamlopt -noassert glpk.cmxa unix.cmxa $(SRCPATH)/$(SOURCES) -o $(RESULT)opt