#!/usr/bin/env python3
"""Longest rigid prefixes (valid orderings in which every adjacent pair is dependent), and
the longest dependent run (factor) inside complete valid sequences."""
import sys
from brute import gen, indep, valid_step

def rigid_prefixes(N):
    best = []; bestlen = 0; cnt = {}
    def rec(a, S):
        nonlocal best, bestlen
        cnt[len(a)] = cnt.get(len(a), 0) + 1
        if len(a) > bestlen: bestlen = len(a); best = []
        if len(a) == bestlen and len(best) < 6: best.append(tuple(a))
        for m in range(1, N + 1):
            if m in S or not valid_step(N, S, m): continue
            if a and indep(N, a[-1], m): continue
            a.append(m); S.add(m); rec(a, S); a.pop(); S.remove(m)
    rec([], set())
    return bestlen, best, cnt

for N in range(2, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 13):
    bl, best, cnt = rigid_prefixes(N)
    line = f"N={N} longest rigid prefix={bl} (N-{N-bl}) examples={best[:3]}"
    if N <= 11:
        V = gen(N); mx = 0; ex = None
        for a in V:
            run = 1; b = 1
            for p in range(N - 1):
                if indep(N, a[p], a[p + 1]): run = 1
                else:
                    run += 1
                    if run > b: b = run
            if b > mx: mx = b; ex = a
        line += f" | longest dependent run in a complete valid sequence={mx} e.g. {ex}"
    print(line); sys.stdout.flush()
