#!/bin/sh

HOLES=`cat src/*.v | grep -c '\<admit\>\|\<Admitted\>'`

if [ "$HOLES" -eq "0" ]
then
	BADGE="badge\/proofs-complete-green.svg"
else
	BADGE="badge\/proofs-$HOLES\_holes-red.svg"
fi

sed -i "s/badge\/proofs-.*\.svg/$BADGE/g" README.md
