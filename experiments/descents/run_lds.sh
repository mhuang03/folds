#!/bin/bash
# usage: run_lds.sh N1 N2 [timeout]   checks min LDS = floor(log2(N+1)) for N1..N2
cd "$(dirname "$0")"
T=${3:-600}
for n in $(seq $1 $2); do
  M=$((n+1)); L=0; while [ $((2<<L)) -le $M ]; do L=$((L+1)); done
  timeout $T ./ldsdfs $n $((L-1)) || echo "N=$n L=$((L-1)) timeout"
  timeout $T ./ldsdfs $n $L || echo "N=$n L=$L timeout"
done
