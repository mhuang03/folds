#!/bin/bash
# exact left-half-only threshold for t = 5 (previously: SAT at 155, UNSAT at 160), then t = 6 at N = 127.
cd "$(dirname "$0")"
for N in 160 159 158 157 156; do
  nice -n 10 python3 sat2.py $N 5 --left >> left_t5.txt 2>&1
done
nice -n 10 python3 sat2.py 127 6 --norm >> t6.txt 2>&1
