#!/bin/sh
# Statistic polynomials by subset DP.  One core, < 2.5 GB.  Output: data/dp_polys.txt
cd "$(dirname "$0")"
gcc -O2 -o statdp statdp.c
out=data/dp_polys.txt
: > $out
for mode in a_exc a_fix a_lrmax t_des t_exc t_lrmax t_pk; do
  for n in $(seq 1 23); do ./statdp $n $mode >> $out; done
done
for mode in inv t_maj; do
  for n in $(seq 1 20); do ./statdp $n $mode >> $out; done
done
for n in $(seq 1 19); do ./statdp $n a_des >> $out; done
for n in $(seq 1 16); do ./statdp $n a_maj >> $out; done
for n in $(seq 1 18); do ./statdp $n a_pk >> $out; done
: > data/dp_deslast.txt
for n in $(seq 1 19); do ./statdp $n a_deslast >> data/dp_deslast.txt; done
echo done
