SOURCES = Sudoku.ml
RESULT = Sudoku
PACKS = glpk

all:
	ocamlc glpk.cma $(SOURCES) -o $(RESULT)
	./Sudoku

clean:
	rm *.cmi *.cmo $(RESULT)