#!/bin/bash

function do_mkrulechecks()
{
  # echo "Do grep for rule checks..."
  cat $1 | grep ruleCount > temp-rc.txt
  # echo "Clean..."
  sed -i $'s/[^[:print:]\t]//g' temp-rc.txt
  sed -i 's/finalProof::ruleCount = { //g; s/, /\n/g; s/: /,/g; s/ }/\n/g' temp-rc.txt
  sed -i '/^$/d' temp-rc.txt
  # sed -i '/^.\/run.sh:/d' temp-rc.txt
  # sed -i '/^cvc5 interrupted/d' temp-rc.txt
  # echo "Aggregate..."
  awk -F, '{a[$1]+=$2;}END{for(i in a)print i", "a[i];}' temp-rc.txt
  # rm temp-rc.txt
}

do_mkrulechecks $1 | sort -k2 -n -t, -r
