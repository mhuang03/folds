#!/bin/sh
# diagnostics sweep: one run per N, P = 1000
cd "$(dirname "$0")"
for N in 64 128 256 512 1024 2048 4096 8192 16384; do
  ./smc2 $N 1000 7 runs/st_$N.txt >> runs/sweep1.txt
done
