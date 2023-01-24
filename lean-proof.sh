#!/bin/bash

#### To use this it's necessary to:
# cd ~/lean-smt
# elan self update
# lake build Smt:shared
# LEAN_PATH=./build/lib:/home/hbarbosa/.elan/toolchains/leanprover--lean4---nightly-2022-09-05/lib/lean; export LEAN_PATH in shell (or ~/.bashrc)


tfile="$(mktemp /tmp/fooXXXXXXXXX.lean)" || exit 1
fileName="$(echo $tfile | rev | cut -d'/' -f1 | rev | cut -d'.' -f1)"
echo $fileName
# tfile="/home/hbarbosa/cvc/wt-leanPrinter/pf.lean" || exit 1

# produce proof, remove first like (which is "unsat"), then remove
# last line (which is closing the s-expression string), then remove
# the s-expression/string prefix

./prod/bin/cvc5 --dump-proofs --proof-format=lean --proof-granularity=theory-rewrite --dag-thresh=0 $@ | tail -n +2 | head -n -1 | sed 's/(proof \"//' > $tfile
if ! grep -q -v "unsat" $tfile; then
    echo "ERROR-CVC5"
    exit
fi

cp $tfile ~/lean-smt/Smt/
cp $tfile .

cd ~/lean-smt
lake build +Smt.$fileName &> /tmp/$fileName
cd - > /dev/null
if ! grep -q "error" /tmp/$fileName; then
  echo "SUCCESS"
else
  echo "ERROR-LEAN"
fi
