#!/bin/sh

coqdoc --short --body-only --latex -o body.tex \
  ObAxioms.v \
  Lambda.v \
  Constructor.v \
  Types.v \
  #

pdflatex main.tex
