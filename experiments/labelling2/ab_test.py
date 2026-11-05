"""Inversion form of (WI):  inv(m) = #{x in L(m): c(x) > c(m)} + #{x in R(m): c(x) < c(m)} >= r(m).
Split inv(m) = |A_m| + |B_m|, A_m = {x in L(m): c(x) > c(m)}, B_m = {x in R(m): c(x) < c(m)}.
Test: how large can |A_m| be in terms of a = #labels above c(m) actually present... we use
a = t-1-c(m) (labels available above) and b = c(m) (labels available below).
Prints max |A| per a and max |B| per b over all labellings and panels.
usage: ab_test.py t file1 [file2 ...]"""
import sys
from collections import defaultdict
t = int(sys.argv[1])
maxA = defaultdict(int); maxB = defaultdict(int); exA = {}; exB = {}
maxAd = defaultdict(int); maxBd = defaultdict(int)
for fn in sys.argv[2:]:
    for line in open(fn):
        s = line.strip()
        if not s[:1].isdigit(): continue
        c = list(map(int, s)); N = len(c)
        for m in range(1, N + 1):
            r = min(m - 1, N - m); v = c[m - 1]
            A = [x for x in range(m - r, m) if c[x - 1] > v]
            B = [x for x in range(m + 1, m + r + 1) if c[x - 1] < v]
            a = t - 1 - v; b = v
            # number of distinct labels actually used in A / B
            da = len(set(c[x - 1] for x in A)); db = len(set(c[x - 1] for x in B))
            if len(A) > maxA[a]: maxA[a] = len(A); exA[a] = (s, m)
            if len(B) > maxB[b]: maxB[b] = len(B); exB[b] = (s, m)
            maxAd[da] = max(maxAd[da], len(A)); maxBd[db] = max(maxBd[db], len(B))
print('max |A| by labels available above:', dict(sorted(maxA.items())))
print('max |B| by labels available below:', dict(sorted(maxB.items())))
print('max |A| by labels used in A:', dict(sorted(maxAd.items())))
print('max |B| by labels used in B:', dict(sorted(maxBd.items())))
for a in sorted(exA): print(' A ex', a, exA[a])
for b in sorted(exB): print(' B ex', b, exB[b])
