"""Which intervals [a, b] are co-reachable in [N]?  (LIVE2_DATA = directory of R_N.bin)"""
import sys
from lib import reachable
for N in range(2, int(sys.argv[1]) + 1):
    bad = []
    for a in range(1, N + 1):
        for b in range(a, N + 1):
            if not reachable(N, set(range(1, N + 1)) - set(range(a, b + 1))):
                bad.append((a, b))
    print(N, bad)
