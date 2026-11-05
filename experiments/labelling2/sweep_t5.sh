#!/bin/bash
# t = 5 sweep: full problem for N = 67..159 (N = 126 first), one panel at a time, 1 core, nice.
# Together with the left-half-only UNSAT at N = 160 (monotone relaxation) and N = 63..66 this
# would prove the conjecture for t = 5 (every N >= 63).  Output appended to sweep_t5.txt.
cd "$(dirname "$0")"
LIST="126 $(seq 67 125) $(seq 127 159)"
for N in $LIST; do
  if grep -q "^N=$N t=5:" sweep_t5.txt 2>/dev/null; then continue; fi
  nice -n 10 python3 sat2.py $N 5 --norm >> sweep_t5.txt 2>&1
done
