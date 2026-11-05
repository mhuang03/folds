"""Conjecture C test: in a valid sequence, the v-th ascending run has at most
P_v(N) = #{g in [1, N] : popcount(g) = v} elements (and, by reverse-mirror symmetry, the
v-th run from the end too).  Also test cumulative: |run_1 + ... + run_v| <= #{g <= N : pc(g) <= v}."""
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
    A = load(N)
    P = Counter(bin(g).count('1') for g in range(1, N + 1))
    cum = lambda v: sum(P[u] for u in range(1, v + 1))
    bad = Counter(); worst = {}
    for a in A:
        R = runs(list(a))
        s = 0
        for v, r in enumerate(R, 1):
            s += len(r)
            if len(r) > P[v]: bad['single'] += 1; worst[v] = max(worst.get(v, 0), len(r) - P[v])
            if s > cum(v): bad['cum'] += 1
    print(N, 'P_v:', [P[v] for v in range(1, 6)], 'violations:', dict(bad), 'max excess by v:', worst, flush=True)
