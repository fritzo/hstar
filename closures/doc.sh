#!/bin/sh

coqdoc --short --body-only --latex -o body.tex \
  Comprehension.v \
  ObAxioms.v \
  Lambda.v \
  Constructor.v \
  Types.v \
  #

pdflatex main.tex
