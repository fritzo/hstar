all: main.pdf

SRC:=../src

body.tex: FORCE
	coqdoc --short --light --body-only --latex -o body.tex \
	$(SRC)/Notations.v \
	$(SRC)/Codes.v \
	$(SRC)/Constructor.v \
	$(SRC)/Types.v \
	$(SRC)/IndexedCodes.v \
	$(SRC)/Points.v \
	#

main.pdf: main.tex body.tex
	pdflatex main.tex

FORCE:
