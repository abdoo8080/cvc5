#!/bin/bash

tfile="$(mktemp /tmp/foo.XXXXXXXXX)" || exit 1
outfile="$(mktemp /tmp/foo.XXXXXXXXX)" || exit 1

./prod/bin/cvc5 --dump-proofs --proof-format=lean --proof-granularity=theory-rewrite --dag-thresh=0 $@ | tail -n +2 > $tfile

cd ~/lean-smt
lean --load-dynlib=/home/hbarbosa/lean-smt/build/lib/libSmt.so $tfile > $outfile
cd - > /dev/null
if ! grep -q "error" $outfile; then
  echo "SUCCESS"
else
  echo "ERROR-LEAN"
fi
