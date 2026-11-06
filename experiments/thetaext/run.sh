#!/bin/sh
# Exact theta(n), n <= NMAX: NPROC processes, each with KPER primes below 2^61 (disjoint),
# then CRT.  Usage: sh run.sh NMAX NPROC KPER [OUTDIR]     (run from this directory)
#   e.g. sh run.sh 2000 3 15    (45 primes, 2745 bits)
set -e
NMAX=$1; NPROC=$2; KPER=$3; OUT=${4:-work}
mkdir -p $OUT
gcc -O3 -march=native -o theta.bin theta.c
i=0
while [ $i -lt $NPROC ]; do
  PRIMES=$(python3 crt.py primes $KPER $((i * KPER)))
  ( ./theta.bin $NMAX $PRIMES > $OUT/res_$i.txt 2> $OUT/log_$i.txt ) &
  i=$((i + 1))
done
wait
python3 checkres.py $OUT/res_*.txt
python3 crt.py combine $OUT/b003407.txt $OUT/res_*.txt
