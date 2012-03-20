SRCPATH = src
BINPATH = bin
SOURCES = Sudoku.ml
RESULT = Sudoku
PACKS = glpk

all:
	ocamlc glpk.cma $(SRCPATH)/$(SOURCES) -o $(RESULT)
	mv $(SRCPATH)/*.cm* $(BINPATH)
	./Sudoku

clean:
	rm $(BINPATH)/*.cmi $(BINPATH)/*.cmo $(RESULT)