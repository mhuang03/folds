# fams.py N0 N1: classify the residual of Live3q's rules (bin/l<N>.txt, canonical orientation
# a + c <= N + 1) by the corner pair (a, N - c) and the rule of Live3r that settles it
# (bin/c<N>.txt: X chiX, R nearTrB, R ... P nearTrP); prints per N the families with counts.
import sys, os, collections
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'bin')
N0, N1 = int(sys.argv[1]), int(sys.argv[2])
tot = collections.Counter()
for N in range(N0, N1 + 1):
    fn = os.path.join(D, 'c%d.txt' % N)
    if not os.path.exists(fn): continue
    fam = collections.defaultdict(collections.Counter)
    for line in open(fn):
        f = line.split()
        if len(f) < 5: continue
        a, b, c = map(int, f[1:4])
        if f[4] == 'LEFT': rule = 'LEFT'
        elif f[5] == 'X': rule = 'X'
        else: rule = ('P' if 'P' in f else 'B') + f[4] + 'k' + f[6]
        key = (a, N - c) if b > 3 * a + 5 or a > 2 else (a, b, 'c=N-%d' % (N - c))
        fam[key][rule] += 1
        tot[rule] += 1
    out = []
    for k in sorted(fam, key=lambda k: -sum(fam[k].values())):
        out.append('%s:%s' % (k, dict(fam[k])))
    print('N=%d' % N, '; '.join(out))
print('total by rule', dict(tot))
