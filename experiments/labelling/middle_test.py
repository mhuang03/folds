"""Conjecture E at the middle panel(s) mu, v = c(mu):
   #{y > mu : c y < v} <= 2^(#labels used below v, +1) - 2   and
   #{x < mu : c x > v} <= 2^(#labels used above v, +1) - 2.
Also report the max over all panels mu with r(mu) >= some fraction."""
import glob, sys
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    mids = [(N + 1) // 2] if N % 2 else [N // 2, N // 2 + 1]
    bad = {}; n = 0
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        n += 1
        c = [None] + [int(ch) for ch in s]
        for mu in range(1, N + 1):
            v = c[mu]
            right = [c[y] for y in range(mu + 1, N + 1) if c[y] < v]
            left = [c[x] for x in range(1, mu) if c[x] > v]
            kr = len(set(right)); kl = len(set(left))
            okr = len(right) <= 2 ** (kr + 1) - 2
            okl = len(left) <= 2 ** (kl + 1) - 2
            tag = 'mid' if mu in mids else 'other'
            if not okr: bad[tag, 'R'] = bad.get((tag, 'R'), 0) + 1
            if not okl: bad[tag, 'L'] = bad.get((tag, 'L'), 0) + 1
    print(N, t, n, bad)
