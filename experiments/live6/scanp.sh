#!/bin/sh
# scanp.sh u up N1 N2: for each N, the sizes p of inward end copies of (u, N+1-up)
u=$1; up=$2
for N in $(seq $3 $4); do
  v=$((N+1-up))
  line="$N:"
  for p in $(seq 3 $((N/2))); do
    r=$(./copyp $N $p $u $v 0 | sed 's/.*inward //')
    [ "$r" != "0" ] && line="$line p$p=$r"
  done
  echo "$line"
done
