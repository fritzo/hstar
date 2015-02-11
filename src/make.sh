#!/bin/sh

coq_makefile *.v -install none -o Makefile
make
