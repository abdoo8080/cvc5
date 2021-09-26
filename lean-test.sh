#!/bin/bash

./prod/bin/cvc5 --dump-proof --proof-format=lean $@ &> tmpResult
tail -n +2 tmpResult > tmpResult.lean
rm tmpResult
# ~/cvc/signatures/lean4/build/bin/Cdclt tmpResult.lean
cp tmpResult.lean ~/cvc/signatures/lean4/Cdclt/examples/
cd ~/cvc/signatures/lean4/
ulimit -s 8388608 -t 30; leanpkg print-paths Cdclt.examples.tmpResult
# ulimit -s 16777216; leanpkg print-paths Cdclt.examples.tmpResult
rm build/Cdclt/examples/tmpResult.olean
cd -
