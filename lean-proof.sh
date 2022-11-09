#!/bin/bash

tfile="$(mktemp /tmp/foo.XXXXXXXXX)" || exit 1
outfile="$(mktemp /tmp/foo.XXXXXXXXX)" || exit 1

# produce proof, remove first like (which is "unsat"), then remove
# last line (which is closing the s-expression string), then remove
# the s-expression/string prefix

./prod/bin/cvc5 --dump-proofs --proof-format=lean --proof-granularity=theory-rewrite --dag-thresh=0 $@ | tail -n +2 | head -n -1 | sed 's/(proof \"//' > $tfile

cd ~/lean-smt
lean --load-dynlib=/home/hbarbosa/lean-smt/build/lib/libSmt.so $tfile > $outfile
cd - > /dev/null
if ! grep -q "error" $outfile; then
  echo "SUCCESS"
else
  echo "ERROR-LEAN"
fi
