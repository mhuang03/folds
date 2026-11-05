#!/bin/sh
# Dependence of the SMC log-estimate on the population size P (bias of log Z-hat).
# usage: pscan.sh N "P:reps P:reps ..."     output: runs/pscan.txt
cd "$(dirname "$0")"
N=$1
for spec in $2; do
  P=${spec%%:*}; R=${spec##*:}
  s=1
  while [ $s -le $R ]; do
    ./smc3 $N $P $((1000 + s)) $((64 * P)) runs/p_${N}_${P}_$s.txt >> runs/pscan.txt
    s=$((s + 1))
  done
done
