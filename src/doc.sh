#!/bin/sh

# We cat files rather than passing them as args
# to work around an apparent coqdoc notation printing bug whereby [1] fails.
# [1] http://comments.gmane.org/gmane.science.mathematics.logic.coq.club/5894
cat \
  Notations.v \
  Codes.v \
  IndexedCodes.v \
  Points.v \
  ObAxioms.v \
  Lambda.v \
  Bohm.v \
  Constructor.v \
  Types.v \
| coqdoc --short --light --body-only --latex -o body.tex

pdflatex main.tex
