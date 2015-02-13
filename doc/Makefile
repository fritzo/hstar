all: main.pdf

SRC:=../src

body.tex: FORCE
	coqdoc --short --light --body-only --latex -o body.tex \
	$(SRC)/Notations.v \
	$(SRC)/Codes.v \
	$(SRC)/Substitution.v \
	$(SRC)/Convergence.v \
	$(SRC)/InformationOrdering.v \
	$(SRC)/Combinators.v \
	$(SRC)/Nontermination.v \
	$(SRC)/LeastFixedPoint.v \
	$(SRC)/DeBruijn.v \
	$(SRC)/Compile.v \
	$(SRC)/BohmTrees.v \
	$(SRC)/TypeConstructor.v \
	$(SRC)/Types.v \
	#

main.pdf: main.tex body.tex references.bib
	pdflatex -interaction=batchmode main
	bibtex -terse main
	pdflatex -interaction=batchmode main

FORCE:
