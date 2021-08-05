#!/bin/bash

datenow=$(date +"%Y%m%d%H%M")
solver=../prod/bin/cvc5
# options="--arrays-exp"
# options="--arrays-exp --bv-solver=simple"
options="--arrays-exp --check-proofs"
# options="--produce-proofs --finite-model-find --fmf-type-completion-thresh=1000000 --lang=smt2 -q"
traces=""
time=""
ulimit="ulimit -S -t 5"
# file="all.txt"
file="add.txt"
# file="test.txt"
path="./"

COUNT=0

function do_mkrulechecks()
{
  echo "Do grep for rule checks..."
  cat $1 | grep ruleCount > temp-rc.txt
  echo "Clean..."
  sed -i $'s/[^[:print:]\t]//g' temp-rc.txt
  sed -i 's/finalProof::ruleCount = { //g; s/, /\n/g; s/: /,/g; s/ }/\n/g' temp-rc.txt
  sed -i '/^$/d' temp-rc.txt
  # sed -i '/^.\/run.sh:/d' temp-rc.txt
  # sed -i '/^cvc5 interrupted/d' temp-rc.txt
  echo "Aggregate..."
  awk -F, '{a[$1]+=$2;}END{for(i in a)print i", "a[i];}' temp-rc.txt
  # rm temp-rc.txt
}

(
echo "Options: $options"
echo "Traces: $traces"
echo

while read name; do
    if [ "$COUNT" == "1" ]; then
      $ulimit; $time $solver $options $traces  "$path$name" >> temp.txt 2>&1;
    else
      echo "$solver on $path$name";
      $ulimit; $time $solver $options $traces "$path$name";
      echo "=====================================";
    fi
done < $file

if [ "$COUNT" == "1" ]; then
  # echo "Make regress with stats..."
  # make regress $@ CVC4_REGRESSION_ARGS="--check-proofs-new --stats" >& temp.txt
  do_mkrulechecks temp.txt
  # rm temp.txt
fi
) #> "results_$datenow.txt" 2> /dev/null
