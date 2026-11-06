#!/bin/sh
# Residues of theta(n), 19 <= n <= NMAX, modulo six primes below 2^62 (one core, sequential),
# then the exact values by CRT.  Usage: sh run_exact.sh NMAX OUTDIR
NMAX=$1; OUT=$2
for P in 4611686018427387847 4611686018427387817 4611686018427387787 4611686018427387761 \
         4611686018427387751 4611686018427387737; do
  echo "# $P" > $OUT/res_$P.txt
  PRIME=$P ./window_mod.bin all $NMAX >> $OUT/res_$P.txt
done
python3 crt.py combine $NMAX $OUT/res_*.txt > data/theta_exact.txt
