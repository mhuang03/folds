#!/bin/bash
# refined statistics (u128, 2 threads).  usage: runstats.sh RULE N...
# semi N <= 24 are already in rust/results/stats.  N = 30 peaks at about 2.5 GB.
D=$(cd "$(dirname "$0")" && pwd)
B=$D/../../rust/target/release/folds
mkdir -p $D/data
rule=$1; shift
for n in "$@"; do
  if [ "$rule" = semi ]; then out=$D/data/stats_$n.txt; else out=$D/data/${rule}stats_$n.txt; fi
  $B stats $rule $n --threads 2 > $out
done
