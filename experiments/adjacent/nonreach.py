"""List the sets S of [N] that are NOT reachable from scratch (small N), by size."""
import sys
import numpy as np
from lib import R

N = int(sys.argv[1])
maxk = int(sys.argv[2]) if len(sys.argv) > 2 else N
Rb = R(N)
cnt = {}
for m in range(1 << N):
    if not (Rb[m >> 3] >> (m & 7)) & 1:
        S = [i + 1 for i in range(N) if m >> i & 1]
        k = len(S)
        cnt[k] = cnt.get(k, 0) + 1
        if k <= maxk:
            print(k, S, 'complement', [i for i in range(1, N + 1) if i not in S])
print(cnt)
