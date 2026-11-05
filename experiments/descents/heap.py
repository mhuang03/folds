"""Heap structure test.  Left heap: node m has children 2m, 2m+1.  Right heap: node g = M - m
has children 2g, 2g+1.  For valid sequences with the MINIMUM number of runs, and for all valid
sequences, test after each complete run j whether the placed set S_j is
   (LC) closed under left-heap children   (m in S, child <= N  =>  child in S)
   (RP) closed under right-heap parents   (g in S(gap form), g >= 2 => g//2 in S)."""
from common import *
import sys
from collections import Counter
def runs(a):
    R = [[a[0]]]
    for x in a[1:]:
        if x > R[-1][-1]: R[-1].append(x)
        else: R.append([x])
    return R
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    A = load(N); M = N + 1; c = Counter()
    mind = min(des(list(a)) for a in A)
    for a in A:
        a = list(a); R = runs(a); ismin = len(R) - 1 == mind
        S = set()
        for j, r in enumerate(R[:-1]):
            S |= set(r)
            lc = all((2*m not in range(1, N+1) or 2*m in S) and (2*m+1 > N or 2*m+1 in S) for m in S)
            rp = all(g < 2 or (M - g//2) in S for g in (M - m for m in S))
            c[(ismin, 'LC', lc)] += 1; c[(ismin, 'RP', rp)] += 1
    print(N, sorted(c.items()))
