#!/bin/sh

dirs=$(find -type d | grep '/')
for i in $dirs
do
	(cd $i ; coq_makefile *.v -install none -o Makefile ; make)
done

coq_makefile *.v -install none -o Makefile ; make
