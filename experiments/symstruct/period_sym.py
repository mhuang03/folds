"""period_sym.py FILE DEG L [NMIN]: smallest p | L with Delta_p^(DEG+1) T(N) = 0 for all
NMIN <= N <= max - p*(DEG+1), i.e. the exact period of the quasi-polynomial (series exact)."""
import sys
from math import comb
fn, deg, L = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
NMIN = int(sys.argv[4]) if len(sys.argv) > 4 else 1
d = {int(a): int(b) for a, b in (l.split() for l in open(fn))}
M = max(d)
def ok(p):
    top = M - p * (deg + 1)
    if top - NMIN < p:
        return None
    for n in range(NMIN, top + 1):
        s = 0
        for i in range(deg + 2):
            s += (-1) ** i * comb(deg + 1, i) * d[n + i * p]
        if s:
            return False
    return True
for p in sorted(q for q in range(1, L + 1) if L % q == 0):
    r = ok(p)
    if r is None:
        print(f"p={p}: not enough data"); break
    if r:
        print(f"exact period {p} (divides {L}), verified for N = {NMIN}..{M - p*(deg+1)}"); break
