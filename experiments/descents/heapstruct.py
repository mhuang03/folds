"""Which minimum-descent sequences have 'heap structure': every S_j (labels <= j) is closed
under left-heap children (m in S, 2m or 2m+1 <= N => child in S), and every U_j (labels > j)
is closed under right-heap children (g = M-m: 2g, 2g+1)."""
from common import *
import sys
def runs(a):
    R = [[a[0]]]
    for x in a[1:]:
        if x > R[-1][-1]: R[-1].append(x)
        else: R.append([x])
    return R
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    A = load(N); M = N + 1
    mind = min(des(list(a)) for a in A); tot = 0; good = []
    for a in A:
        a = list(a)
        if des(a) != mind: continue
        tot += 1; R = runs(a); S = set(); ok = True
        for r in R[:-1]:
            S |= set(r); U = set(range(1, N + 1)) - S
            if not all(c > N or c in S for m in S for c in (2*m, 2*m + 1)): ok = False
            if not all(M - c < 1 or (M - c) in U for m in U for c in (2*(M - m), 2*(M - m) + 1) if c < M): ok = False
        if ok: good.append(a)
    print(N, 'minimisers', tot, 'heap-structured', len(good), good[:3])
