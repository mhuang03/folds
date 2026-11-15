#!/bin/sh
# Permuton matrices (N = 12..14, 20, 24) and min/max of set-computable statistics (N <= 30).
cd "$(dirname "$0")"
gcc -O2 -o permuton permuton.c
gcc -O2 -o minstat minstat.c
for n in 12 13 14 20 24; do ./permuton $n > data/permuton_$n.txt; done
: > data/minstat.txt
for mode in t_des t_pk a_exc; do
  for n in $(seq 1 ${1:-30}); do ./minstat $n $mode >> data/minstat.txt; done
done
echo done
