#!/bin/sh
# run2.sh N: inward copies containing 1 and N/2+2 (any max), sizes
N=$1; v=$((N/2+2))
for hi in $(seq $v $N); do
  r=$(timeout 100 ./endcopy $N 1 $hi 3 0 $v | tr '\n' ' ')
  echo "hi=$hi $r"
done
