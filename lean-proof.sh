#!/bin/bash

#### To use this it's necessary to:
# cd ~/lean-smt
# elan self update
# lake build Smt:shared
# LEAN_PATH=./build/lib:/home/hbarbosa/.elan/toolchains/leanprover--lean4---nightly-2022-09-05/lib/lean; export LEAN_PATH in shell (or ~/.bashrc)


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
