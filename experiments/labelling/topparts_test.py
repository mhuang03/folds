"""Reduction R ("glue the tops of the two heaps").  P = [1,h], h = (N+1)//2; Q = gaps [1,h'],
h' = N - h.  P0 = [1, a], Q0 = gaps [1, b] with a = h//2, b = h'//2 (also other a, b).
New strip of length a + b: panels 1..a carry c(x) - sP, panels a+1..a+b carry c at gaps
b..1 (i.e. the last b panels of the old strip) minus sQ.  Test admissibility and span."""
import glob, sys
from reduce_test import adm
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    h = (N + 1) // 2; hp = N - h
    variants = {}
    for (a, b) in ((h // 2, hp // 2), ((h - 1) // 2, (hp + 1) // 2), ((h + 1) // 2, hp // 2), (h // 2, (hp + 1) // 2)):
        for sP in (0, 1):
            variants[(a, b, sP)] = [0, 0, 0]   # admissible, admissible & span <= t-1, total
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [None] + [int(ch) for ch in s]
        for (a, b, sP), st in variants.items():
            lab = [c[x] - sP for x in range(1, a + 1)] + [c[x] for x in range(N - b + 1, N + 1)]
            ok = adm([0] + lab)
            st[0] += ok; st[2] += 1
            if ok and max(lab) - min(lab) + 1 <= t - 1: st[1] += 1
    print(N, t, {k: v[:2] for k, v in variants.items()}, 'of', next(iter(variants.values()))[2])
