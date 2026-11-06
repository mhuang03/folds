#!/bin/sh
# endscan.sh N1 N2: for every wide pair (u, v) (gap > max(u, N+1-v)), u <= N+1-v, report
# whether an inward end copy with good size exists (endcopy stopgood).
for N in $(seq $1 $2); do
  for u in $(seq 1 $N); do
    for v in $(seq $((u+1)) $N); do
      up=$((N+1-v)); g=$((v-u-1))
      [ $u -le $up ] || continue
      m=$u; [ $up -gt $m ] && m=$up
      [ $g -gt $m ] || continue
      [ $(( (v-u) % 2 )) -eq 1 ] || continue; r=$(timeout 20 ./endcopy $N $u $v 0 1)
      echo "$N $u $v :: $r"
    done
  done
done
