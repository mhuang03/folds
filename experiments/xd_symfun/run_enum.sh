#!/bin/sh
# Build the enumerator and dump V_N for N = 1..MAX (default 13) into data/V<N>.bin (git-ignored).
cd "$(dirname "$0")"
mkdir -p data
gcc -O2 -o enum enum.c
MAX=${1:-13}
for n in $(seq 1 $MAX); do ./enum $n > data/V$n.bin; done
