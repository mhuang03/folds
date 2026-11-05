"""nearres.py N k s: window copies X of [N] with |X| = |C| and |X ^ C| <= 4, where C is the
residue class s mod k (to replace an exceptional class), with complement reachability."""
import sys
from lib import load_copies

N, k, s = map(int, sys.argv[1:4])
C = set(range(s, N + 1, k))
for X, good in load_copies(N):
    S = set(X)
    if len(S) == len(C) and len(S ^ C) <= 4:
        print(sorted(C - S), '->', sorted(S - C), 'good' if good else 'BAD')
