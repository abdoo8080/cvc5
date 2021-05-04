#!/bin/bash

./prod/bin/cvc5 $@ &> tmpResult
tail -n +2 tmpResult > tmpResult.lean
rm tmpResult
cp tmpResult.lean ~/cvc/signatures/lean4/Cdclt/examples/
cd ~/cvc/signatures/lean4/
leanpkg print-paths Cdclt.examples.tmpResult
cd -
