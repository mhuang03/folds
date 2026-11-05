"""Time/space split at a panel m of the right-heavy order a (sorted by (c, position)).
Y  = R(m) placed before m,   Y' = L(m) placed after m.  Every decreasing chain of Y, then m,
then a decreasing chain of Y' is a decreasing chain, and |Y| + |Y'| >= r(m).
Test: |Y| <= 2^(LDS(Y)+1) - 2 and |Y'| <= 2^(LDS(Y')+1) - 2 (for all m; report failures)."""
import glob, sys, bisect
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
def lds(seq):
    tails = []
    for v in seq:
        v = -v
        i = bisect.bisect_left(tails, v)
        if i == len(tails): tails.append(v)
        else: tails[i] = v
    return len(tails)
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    bad = {'Y': 0, "Y'": 0, 'Ymid': 0, "Y'mid": 0}; ex = {}
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [None] + [int(ch) for ch in s]
        a = sorted(range(1, N + 1), key=lambda m: (c[m], m))
        pos = {x: i for i, x in enumerate(a)}
        for m in range(1, N + 1):
            r = min(m - 1, N - m)
            Y = [x for x in a if m < x <= m + r and pos[x] < pos[m]]
            Yp = [x for x in a if m - r <= x < m and pos[x] > pos[m]]
            mid = m in ((N + 1) // 2, N // 2 + 1)
            for name, Z in (('Y', Y), ("Y'", Yp)):
                if len(Z) > 2 ** (lds(Z) + 1) - 2:
                    bad[name] += 1; ex.setdefault(name, (s, m, Z))
                    if mid: bad[name + 'mid'] += 1; ex.setdefault(name + 'mid', (s, m, Z))
    print(N, t, bad, ex)
