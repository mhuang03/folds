#!/bin/sh
# large-P runs at large N (the bias of log Z-hat is about -b(N)/P with b(N) growing like N^2,
# see NOTES.txt).  usage: big.sh "N:P:seed N:P:seed ..."
# Estimates are appended to runs/big.txt, diagnostics go to runs/d_*, snapshots to runs/dump_*.
cd "$(dirname "$0")"
for spec in $1; do
  N=$(echo $spec | cut -d: -f1); P=$(echo $spec | cut -d: -f2); s=$(echo $spec | cut -d: -f3)
  ./smc3 $N $P $s $((16 * P)) runs/d_${N}_${P}_$s.txt runs/dump_${N}_${P}_$s.txt >> runs/big.txt
done
