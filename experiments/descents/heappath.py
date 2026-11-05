"""Longest downward heap path along which every child is placed BEFORE its parent.
Left heap: children of m are 2m, 2m+1.  Right heap (gaps g = M-m): children 2g, 2g+1.
P_L(a) = longest such path in the left heap (any start), P_L1 = starting at the root 1;
same for the right heap.  Report min over valid a of several combinations vs lg(M)."""
from common import *
import sys
def longest(N, tau, kids, roots):
    memo = {}
    def f(v):
        if v in memo: return memo[v]
        b = 1
        for w in kids(v):
            if 1 <= w <= N and tau[w] < tau[v]: b = max(b, 1 + f(w))
        memo[v] = b; return b
    return max(f(v) for v in roots), f
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    A = load(N); M = N + 1
    res = {'L': 99, 'L1': 99, 'R': 99, 'R1': 99, 'max(L,R)': 99, 'max(L1,R1)': 99}
    for a in A:
        tau = {m: i for i, m in enumerate(a)}
        L, fL = longest(N, tau, lambda v: (2*v, 2*v+1), range(1, N+1))
        L1 = fL(1)
        R, fR = longest(N, tau, lambda v: (M - 2*(M-v), M - 2*(M-v) - 1), range(1, N+1))
        R1 = fR(N)
        for k, v in (('L', L), ('L1', L1), ('R', R), ('R1', R1), ('max(L,R)', max(L, R)), ('max(L1,R1)', max(L1, R1))):
            res[k] = min(res[k], v)
    print(N, 'lg M =', lg(M), res, flush=True)
