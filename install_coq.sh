#!/bin/sh

# latest version
COQ=coq-8.4pl5.tar.gz
test -e $COQ \
  || wget http://coq.inria.fr/distrib/V8.4pl5/files/$COQ \
  && tar -xzf $COQ

# version supported on travis
# COQ=coq-8.3pl5.tar.gz
# test -e $COQ \
#   || wget http://coq.inria.fr/distrib/V8.3pl5/files/$COQ \
#   && tar -xzf $COQ
