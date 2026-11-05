#!/bin/bash
# timing comparison of encodings/solvers at N = 63, t = 5 (1 core, nice)
cd "$(dirname "$0")"
for opt in "" "--norm" "--solver kissat404" "--norm --solver kissat404"; do
  nice -n 10 python3 sat2.py 63 5 $opt
done
