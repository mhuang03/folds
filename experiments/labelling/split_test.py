"""Split test.  p = last panel of the top label class, q = first panel of the bottom class.
Is the suffix strip (p, N] admissible?  The prefix strip [1, q)?  Is p <= q + 1?"""
import glob, sys
from reduce_test import adm
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    st = dict(n=0, suf=0, pre=0, pq=0, all3=0)
    ex = {}
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [None] + [int(ch) for ch in s]
        top = max(c[1:]); bot = min(c[1:])
        p = max(x for x in range(1, N + 1) if c[x] == top)
        q = min(x for x in range(1, N + 1) if c[x] == bot)
        a = adm([0] + c[p + 1:]); b = adm([0] + c[1:q]); d = p <= q + 1
        st['n'] += 1; st['suf'] += a; st['pre'] += b; st['pq'] += d; st['all3'] += a and b and d
        for k, ok in (('suf', a), ('pre', b), ('pq', d)):
            if not ok and k not in ex: ex[k] = s
    print(N, t, st, ex)
