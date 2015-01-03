#!/bin/sh

# Coq 8.4+ 
#coq_makefile -install none *.v > Makefile
# Coq <8.4
coq_makefile -no-install *.v > Makefile

make
