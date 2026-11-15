"""P-recursive / C-finite fits for the new sequences (engine: experiments/recsearch/common.py).
  REC(r,d): sum_{i<=r, j<=d} c_ij n^j s(n-i) = 0, all (r,d) with at least SPARE spare equations.
Sequences: E(n) = H(2n) (wall table), its bisections, s/n!, the offset columns a(N;0,be)
(be = 1..4), the wall diagonals W(n,2n-2c) and W(n,n+c)."""
import os, sys
from fractions import Fraction
from math import factorial
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'recsearch'))
from common import analyze

SPARE = 3
W = {}
for l in open(os.path.join(HERE, 'out', 'wall_rows.txt')):
    n, r = l.split(':'); n = int(n)
    for i, v in enumerate(r.split()):
        W[(n, n + i)] = int(v)
A = {}
for l in open(os.path.join(HERE, 'out', 'row0.txt')):
    n, r = l.split(':'); n = int(n)
    for b, v in enumerate(r.split()):
        A[(n, b)] = int(v)
E = [None] + [W[(n, 2 * n)] for n in range(1, 25)]
for l in open(os.path.join(HERE, 'out', 'E_extra.txt')) if os.path.exists(os.path.join(HERE, 'out', 'E_extra.txt')) else []:
    f = l.split()
    if len(f) == 2 and int(f[0]) == len(E): E.append(int(f[1]))

def rec_rows(s, r, d):
    L = len(s) - 1
    return [[Fraction(n) ** j * s[n - i] for i in range(r + 1) for j in range(d + 1)]
            for n in range(r + 1, L + 1)]

def run(name, s):
    L = len(s) - 1; best = None; tried = 0; hits = []
    for r in range(1, 13):
        for d in range(0, 7):
            K = (r + 1) * (d + 1); Eq = L - r
            if Eq < K + SPARE: continue
            res = analyze(rec_rows(s, r, d)); tried += 1
            if res['rank'] < K: hits.append((r, d, res['kernel'][0]))
            if best is None or res['excess'] > best[0]: best = (res['excess'], r, d)
    print("%-28s terms=%2d  shapes tried=%3d  fits=%d  max excess=%s" %
          (name, L, tried, len(hits), best))
    for h in hits[:3]: print("    FIT r=%d d=%d kernel=%s" % h)

seqs = [("E(n)=H(2n)", E),
        ("E(n)/n!", [None] + [Fraction(E[n], factorial(n)) for n in range(1, len(E))]),
        ("E(2k)", [None] + E[2::2]), ("E(2k-1)", [None] + E[1::2]),
        ("E(2k)/E(2k-1)", [None] + [Fraction(E[2 * k], E[2 * k - 1]) for k in range(1, (len(E) - 1) // 2 + 1)]),
        ("E(2k+1)/E(2k)", [None] + [Fraction(E[2 * k + 1], E[2 * k]) for k in range(1, (len(E) - 2) // 2 + 1)])]
NA = max(n for n, _ in A)
for be in range(1, 5):
    seqs.append(("a(N;0,%d), N>=%d" % (be, be + 1), [None] + [A[(N, be)] for N in range(be + 1, NA + 1)]))
NW = max(n for n, _ in W)
for c in range(1, 4):
    seqs.append(("W(n,2n-%d)" % (2 * c), [None] + [W[(n, 2 * n - 2 * c)] for n in range(2 * c, NW + 1)]))
for c in (2, 4):
    seqs.append(("W(2j,2j+%d)" % c, [None] + [W[(n, n + c)] for n in range(c, NW + 1, 2)]))
    seqs.append(("W(2j+1,2j+1+%d)" % (c + 1), [None] + [W[(n, n + c + 1)] for n in range(c + 1, NW + 1, 2)]))
for name, s in seqs:
    run(name, s)
