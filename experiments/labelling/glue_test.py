"""Glue the heap tops with clipping: new strip P0 || Q0 (P0 = [1, h//2], Q0 = last h'//2 panels),
labels: P0: max(c-1, 0), Q0: min(c, t-2).  Always <= t-1 labels.  Admissible?"""
import glob, sys
from reduce_test import adm
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    h = (N + 1) // 2; hp = N - h
    res = {}
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [None] + [int(ch) for ch in s]
        T = max(c[1:]) + 1
        for (a, b) in ((h // 2, hp // 2), ((h + 1) // 2, hp // 2), (h // 2, (hp + 1) // 2), ((h - 1) // 2, (hp - 1) // 2)):
            lab = [max(c[x] - 1, 0) for x in range(1, a + 1)] + [min(c[x], T - 2) for x in range(N - b + 1, N + 1)]
            k = (a, b)
            r = res.setdefault(k, [0, 0]); r[1] += 1; r[0] += adm([0] + lab)
    print(N, t, res)
