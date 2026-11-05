"""Records.  Decreasing chains: LR minima, RL maxima.  Increasing: LR maxima, RL minima.
min over valid a of several combinations, compared with lg(M)."""
from common import *
import sys
def lrmin(a):
    c, m = 0, 10**9
    for x in a:
        if x < m: c += 1; m = x
    return c
def lrmax(a): return lrmin([-x for x in a])
def rlmax(a): return lrmax(a[::-1])
def rlmin(a): return lrmin(a[::-1])
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    A = load(N); M = N + 1
    r = {}
    for a in A:
        a = list(a)
        v = {'max(LRmin,RLmax)': max(lrmin(a), rlmax(a)), 'LRmin+RLmax-1': lrmin(a) + rlmax(a) - 1,
             'LRmin': lrmin(a), 'LRmin+LRmax': lrmin(a) + lrmax(a)}
        for k, x in v.items(): r[k] = min(r.get(k, 99), x)
    print(N, lg(M), r, flush=True)
