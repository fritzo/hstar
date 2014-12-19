all: bohm-trees.pdf

bohm-trees.tex: bohm-trees.v
	coqdoc --latex -o $@ $^

bohm-trees.pdf: bohm-trees.tex FORCE
	pdflatex bohm-trees.tex
	pdflatex bohm-trees.tex

FORCE:
