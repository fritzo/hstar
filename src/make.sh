#!/bin/sh

coq_makefile -install none *.v > Makefile
make
