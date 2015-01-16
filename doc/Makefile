all: main.pdf

SRC:=../src

body.tex: FORCE
	coqdoc --short --light --body-only --latex -o body.tex \
	$(SRC)/Notations.v \
	$(SRC)/Codes.v \
	$(SRC)/InformationOrdering.v \
	$(SRC)/Nontermination.v \
	$(SRC)/LeastFixedPoint.v \
	$(SRC)/TypeConstructor.v \
	$(SRC)/Types.v \
	$(SRC)/IndexedCodes.v \
	$(SRC)/Points.v \
	#

main.pdf: main.tex body.tex
	pdflatex main.tex

FORCE:
