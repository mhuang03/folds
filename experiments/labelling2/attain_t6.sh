#!/bin/bash
# attainment: admissible labellings with 6 labels for N = 63..126 (so that min LDS of
# right-heavy permutations is exactly lg(N+1) = 6 there).  Appends to attain_t6.txt.
cd "$(dirname "$0")"
for N in $(seq 63 126); do
  if grep -q "^N=$N t=6:" attain_t6.txt 2>/dev/null; then continue; fi
  nice -n 10 timeout 1200 python3 sat2.py $N 6 >> attain_t6.txt 2>&1 || echo "N=$N t=6: TIMEOUT" >> attain_t6.txt
done
