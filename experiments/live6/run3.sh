#!/bin/sh
# run3.sh N u v: inward copies containing u and v that are not end copies (lo < u or hi > v)
N=$1; u=$2; v=$3
for lo in $(seq 1 $u); do
  for hi in $(seq $v $N); do
    [ $lo -eq $u ] && [ $hi -eq $v ] && continue
    r=$(timeout 100 ./endcopy $N $lo $hi 3 0 $u $v | tr '\n' ' ')
    echo "lo=$lo hi=$hi $r"
  done
done
