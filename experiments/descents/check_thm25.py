"""Sanity check of the intermediate inequalities in the proofs of Theorems 2.4 / 2.5
(PROOFS.txt) on all valid sequences, for the run index and the patience level:
  window lemma; R_{v+1}(n) <= R_v(n) + sum_i (1 + R_v(min(n, 2^(i+1) - 1)));
  A_{v+1} <= 2 A_v + 1 + R_v(floor(N/2));  P_v(i) <= C(i+3v, v) - 1."""
from common import *
from math import comb
import sys
def run_index(a):
    c = {}; k = 0
    for i, x in enumerate(a):
        if i and a[i] < a[i-1]: k += 1
        c[x] = k
    return c
def patience(a):
    c = {}; best = {}
    for i, x in enumerate(a):
        b = 1 + max([best[y] for y in a[:i] if y > x], default=0)
        best[x] = b; c[x] = b - 1
    return c
bad = 0
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    A = load(N); M = N + 1; h = M // 2; H = N // 2; L = lg(M)
    for a in A:
        a = [int(x) for x in a]; pos = {x: i for i, x in enumerate(a)}
        for c in (run_index(a), patience(a)):
            t = max(c.values()) + 1
            for m in range(1, N + 1):
                r = min(m - 1, N - m)
                if sum(c[m-d] <= c[m] for d in range(1, r+1)) > sum(c[m+d] < c[m] for d in range(1, r+1)):
                    bad += 1; print('window lemma fails', N, a)
            R = lambda v, n: sum(1 for x in range(1, N + 1) if c[x] < v and 1 <= M - x <= n)
            Aa = lambda v: sum(1 for x in range(1, h + 1) if c[x] < v)
            for v in range(t):
                for n in range(1, H + 1):
                    rhs = R(v, n) + sum(1 + R(v, min(n, 2**(i+1) - 1)) for i in range(lg(n) + 1))
                    if R(v + 1, n) > rhs: bad += 1; print('R rec fails', N, a, v, n)
                if Aa(v + 1) > 2 * Aa(v) + 1 + R(v, H): bad += 1; print('A rec fails', N, a, v)
                if R(v, H) > comb(L + 3 * v, v) - 1: bad += 1; print('P bound fails', N, a, v)
    print(N, 'violations so far', bad, flush=True)
