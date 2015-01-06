#!/bin/sh

coqdoc --short --body-only --latex -o body.tex \
  Codes.v \
  IndexedCodes.v \
  Points.v \
  ObAxioms.v \
  Lambda.v \
  Bohm.v \
  Constructor.v \
  Types.v \
  #

pdflatex main.tex
