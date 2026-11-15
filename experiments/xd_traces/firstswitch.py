#!/usr/bin/env python3
"""Test: in a valid sequence the FIRST adjacent pair (x,y) with x,y in opposite halves
(x < (N+1)/2 < y or the reverse) is independent.  Would imply Z(N) = 0 (no rigid sequences).
Tested (a) on complete valid sequences, (b) on all valid prefixes ending at the first switch
(no completability assumed)."""
import sys
from brute import gen, indep, valid_step

def side(N, x):
    return -1 if 2 * x < N + 1 else (1 if 2 * x > N + 1 else 0)

def first_switch(N, a):
    for p in range(len(a) - 1):
        if side(N, a[p]) * side(N, a[p + 1]) == -1: return p
    return None

def prefixes(N):
    """all valid prefixes that end exactly at the first switch"""
    out = []
    def rec(a, S):
        if len(a) >= 2 and side(N, a[-2]) * side(N, a[-1]) == -1:
            out.append(tuple(a)); return
        for m in range(1, N + 1):
            if m not in S and valid_step(N, S, m):
                a.append(m); S.add(m); rec(a, S); a.pop(); S.remove(m)
    rec([], set()); return out

for N in range(2, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 12):
    V = gen(N)
    bad = 0; none = 0; lastbad = 0
    for a in V:
        p = first_switch(N, a)
        if p is None: none += 1; continue
        if not indep(N, a[p], a[p + 1]): bad += 1
        # last switch (by reversal symmetry it must hold as well)
        q = max(p for p in range(N - 1) if side(N, a[p]) * side(N, a[p + 1]) == -1)
        if not indep(N, a[q], a[q + 1]): lastbad += 1
    P = prefixes(N)
    badp = [a for a in P if not indep(N, a[-2], a[-1])]
    print(f"N={N} valid={len(V)} no_switch={none} first_switch_dependent={bad} "
          f"last_switch_dependent={lastbad} | prefixes={len(P)} dependent={len(badp)} {badp[:3]}")
