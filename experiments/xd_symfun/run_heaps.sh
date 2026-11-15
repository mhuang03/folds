#!/bin/sh
# Commutation classes of V_N for N = 1..13 (needs data/V<N>.bin from run_enum.sh).
cd "$(dirname "$0")"
gcc -O2 -o heaps heaps.c
for n in $(seq 1 ${1:-13}); do ./heaps $n check; done > data/heaps_out.txt
cat data/heaps_out.txt
