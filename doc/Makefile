all: main.pdf

SRC:=../src

body.tex: FORCE
	coqdoc --short --light --body-only --latex -o body.tex \
	$(SRC)/Notations.v \
	$(SRC)/Combinators.v \
	$(SRC)/InformationOrdering.v \
	$(SRC)/Nontermination.v \
	$(SRC)/LeastFixedPoint.v \
	$(SRC)/BohmTrees.v \
	$(SRC)/TypeConstructor.v \
	$(SRC)/Types.v \
	$(SRC)/DirectedSets.v \
	$(SRC)/Points.v \
	#

main.pdf: main.tex body.tex references.bib
	pdflatex main
	bibtex main
	pdflatex main

FORCE:
