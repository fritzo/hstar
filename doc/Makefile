all: main.pdf

SRC:=../src

body.tex: FORCE
	coqdoc --short --light --body-only --latex -o body.tex \
	$(SRC)/Notations.v \
	$(SRC)/Terms.v \
	$(SRC)/NormalForms.v \
	#

main.pdf: main.tex body.tex references.bib
	pdflatex -interaction=batchmode main
	bibtex -terse main
	pdflatex -interaction=batchmode main

FORCE:
