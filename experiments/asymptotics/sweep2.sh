#!/bin/sh
# production SMC runs (one core per invocation).  usage: sweep2.sh "N:P_hi N:P_hi ..."
# For each N: 4 replicates at P_hi/4 and 2 at P_hi (bias extrapolation in 1/P).
# Estimates go to runs/prod.txt, diagnostics to runs/d_N_P_seed.txt.
cd "$(dirname "$0")"
for spec in $1; do
  N=${spec%%:*}; PH=${spec##*:}; PL=$((PH / 4))
  for s in 1 2 3 4; do ./smc3 $N $PL $((100 + s)) $((64 * PL)) runs/d_${N}_${PL}_$((100 + s)).txt >> runs/prod.txt; done
  for s in 1 2; do ./smc3 $N $PH $((200 + s)) $((64 * PH)) runs/d_${N}_${PH}_$((200 + s)).txt >> runs/prod.txt; done
done
