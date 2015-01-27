#!/bin/sh

cd src

echo '--------------------------------'
echo 'HOLES\tFILE'
echo '--------------------------------'
grep -c '\<admit\>\|\<Admitted\>' *.v \
  | sed 's/^\(.*\):\([0-9]*\)$/\2\t\1/g' \
  | sort -nr \
  | grep -v '^0'
echo '--------------------------------'
