#!/usr/bin/env python3
"""Sequences with exactly one valid swap: where is it?  (toward Z(N) = 0)"""
import sys
from collections import Counter
from brute import gen, indep
for N in range(4, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 12):
    V = gen(N); c = Counter(); cp = Counter(); ex = []
    for a in V:
        ps = [p for p in range(N - 1) if indep(N, a[p], a[p + 1])]
        if len(ps) == 1:
            p = ps[0]; c[tuple(sorted((a[p], a[p + 1])))] += 1; cp[p] += 1
            if len(ex) < 4: ex.append((a, p))
    print(N, 'pairs', sorted(c.items()), 'positions', sorted(cp.items()))
    for e in ex: print('   ', e)
