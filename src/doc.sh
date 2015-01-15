#!/bin/sh

coqdoc --short --light --body-only --latex -o body.tex \
  Notations.v \
  Codes.v \
  Constructor.v \
  Types.v \
  IndexedCodes.v \
  Points.v \
  #

pdflatex main.tex
