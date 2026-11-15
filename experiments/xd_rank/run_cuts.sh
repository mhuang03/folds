#!/bin/bash
# Driver: all cuts for N = $1 .. $2, appended to out/cuts.txt
# usage: ./run_cuts.sh NMIN NMAX
cd "$(dirname "$0")"
for N in $(seq $1 $2); do
  ./cutmat.bin $N parity
  for j in $(seq 1 $((N-1))); do ./cutmat.bin $N spatial $j; done
  for r in 0 1 2; do ./cutmat.bin $N res 3 $r; done
  for r in 0 1 2 3; do ./cutmat.bin $N res 4 $r; done
  for d in 3 5 7; do if [ $((N % d)) -eq 0 ] && [ $N -gt $d ]; then ./cutmat.bin $N ed $d; fi; done
done
