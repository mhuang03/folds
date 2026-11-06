#!/usr/bin/env python3
"""analyse.py: combine jdp outputs (CRT over moduli), compute C_N(k), J(N), I(N), and
per-copy completion counts g(X^c).  Writes out/data.txt (machine readable) and prints a summary.

J(N) = a(N) - sum_{k=2}^{N-1} J(k) C_N(k)      (identity (B))
I(N) = a(N) - 2a(floor(N/2))a(ceil(N/2)) - 2 sum_{d|N odd, 3<=d<N} a(jN/d) a((j+1)N/d)   (identity (A))
"""
import glob, os, re, sys
from fractions import Fraction
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
A = [0]
for l in open(os.path.join(HERE, '..', 'semi_counts.txt')):
    p = l.split()
    if len(p) >= 2 and p[0].isdigit():
        A.append(int(p[1]))
A = A[:]  # a(1..38)

def crt(res):  # res: list of (r, m)
    x, M = 0, 1
    for r, m in res:
        # solve x + M t = r mod m
        t = ((r - x) * pow(M, -1, m)) % m
        x += M * t; M *= m
    return x, M

def load(N):
    files = glob.glob(os.path.join(HERE, 'out', 'jdp_%d_*.txt' % N))
    runs = []
    for f in files:
        mod = int(re.search(r'jdp_%d_(\d+)\.txt' % N, f).group(1))
        mod = mod if mod else 1 << 64
        d = {'copy': {}, 'gcopy': {}, 'C': {}, 'a': None}
        ok = False
        for l in open(f):
            p = l.split()
            if p[0] == 'copy': d['copy'][int(p[2], 16)] = int(p[3])
            elif p[0] == 'gcopy': d['gcopy'][int(p[2], 16)] = int(p[3])
            elif p[0] == 'C': d['C'][int(p[1])] = int(p[2])
            elif p[0] == 'a': d['a'] = int(p[1]); ok = True
        if ok: runs.append((mod, d))
    if not runs: return None
    mods = [m for m, _ in runs]
    M = 1
    for m in mods: M *= m
    def comb(get):
        return crt([(get(d), m) for m, d in runs])[0]
    a = comb(lambda d: d['a'])
    # redundancy: every combined value is <= a(N); if the moduli without the largest one
    # already exceed a(N), all values must lie below that partial product ("stable").
    big = max(mods)
    stable = None
    if len(runs) > 1 and M // big > A[N]:
        stable = True
        for k in runs[0][1]['C']:
            if comb(lambda d, k=k: d['C'][k]) >= M // big: stable = False
    # use all but the last modulus to check stability if more than one modulus
    C = {k: comb(lambda d, k=k: d['C'][k]) for k in runs[0][1]['C']}
    copy = {X: comb(lambda d, X=X: d['copy'][X]) for X in runs[0][1]['copy']}
    return dict(a=a, C=C, copy=copy, M=M, mods=mods, stable=stable)

def oddd(N):
    return [d for d in range(3, N, 2) if N % d == 0]

def I_of(N):
    s = 2 * A[N // 2] * A[(N + 1) // 2]
    for d in oddd(N):
        j = (d - 1) // 2
        s += 2 * A[j * N // d] * A[(j + 1) * N // d]
    return A[N] - s

if __name__ == '__main__':
    J = {1: 1}
    rows = []
    out = open(os.path.join(HERE, 'out', 'data.txt'), 'w')
    for N in range(2, 40):
        D = load(N)
        if D is None: break
        assert D['a'] == A[N], (N, D['a'], A[N])
        assert A[N] < D['M']
        JN = A[N] - sum(J[k] * D['C'][k] for k in range(2, N))
        J[N] = JN
        out.write('N %d a %d J %d I %d mods %s stable %s\n' % (N, A[N], JN, I_of(N), ','.join(map(str, D['mods'])), D['stable']))
        assert D['stable'] is not False, N
        for k in range(1, N):
            out.write('C %d %d %d\n' % (N, k, D['C'][k]))
        for X, v in sorted(D['copy'].items(), key=lambda t: (bin(t[0]).count('1'), t[0])):
            out.write('X %d %d %x %d\n' % (N, bin(X).count('1'), X, v))
    out.close()
    for N in sorted(J):
        if N >= 2:
            print(N, J[N], '%.5f' % (J[N] / A[N]), '%.6f' % (I_of(N) / A[N]))
