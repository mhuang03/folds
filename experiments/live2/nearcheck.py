"""nearcheck.py N1 N2: near residue classes.  For k >= 3 not a power of 2:
  N = 1 mod k:  E = C_1 = {1, 1+k, ..., N},       X = E - {1} + {2}
  N = -1 mod k: E = C_k = {k, 2k, ..., N+1-k},    X = E - {k} + {k-1}
Check that X is a window copy and that [N] \\ X is reachable (bitsets from reach.c)."""
import sys
from lib import is_copy, reachable

for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    bad = []
    tot = 0
    for k in range(3, N):
        if k & (k - 1) == 0:
            continue
        cases = []
        if N % k == 1:
            E = set(range(1, N + 1, k))
            cases.append(E - {1} | {2})
        if N % k == k - 1:
            E = set(range(k, N + 1, k))
            cases.append(E - {k} | {k - 1})
        for X in cases:
            if len(X) < 2:
                continue
            tot += 1
            c = is_copy(N, X)
            r = reachable(N, set(range(1, N + 1)) - X)
            if not (c and r):
                bad.append((k, sorted(X), 'copy' if c else 'NOTCOPY', 'reach' if r else 'NOTREACH'))
    print(N, tot, bad)
