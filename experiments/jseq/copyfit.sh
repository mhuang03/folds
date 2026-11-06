#!/bin/bash
# copyfit.sh: counts of copies of size K for N = 1..NMAX (lines "N K count"), out/fitK.txt
cd "$(dirname "$0")"
mkdir -p out
for spec in 2:240 3:200 4:150 5:120 6:100; do
  k=${spec%%:*}; nmax=${spec##*:}
  for n in $(seq 1 "$nmax"); do ./copies "$n" c "$k"; done > "out/fit$k.txt"
done
