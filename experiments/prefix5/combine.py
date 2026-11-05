"""combine.py K [NMAXCHECK]: sum the per-class generating functions of classes_K*.json into the
exact quasi-polynomial of T(N,K).

1. Every class GF is t^shift * num(t) / prod (1 - t^d).  Expanding it gives #P(N) exactly for
   every N (no fitting).  T(N,K) = sum of these.
2. The quasi-polynomial: P = lcm of all d.  When deg(num) + shift < sum(d) (checked), the
   coefficient of t^N is a quasi-polynomial of period P for ALL N >= 0, so the polynomial of
   residue class r is determined by the K+1 values N = r, r+P, ..., r+KP (exact Lagrange).
   We interpolate from 0..(K+1)P-1 and verify on the next P values.
3. For each coefficient c_j(N) (T = sum_j c_j(N) N^j) we report the minimal period and the
   decomposition c_j = sum_d c_{j,d}(N mod d), where c_{j,d} is the part of c_j whose discrete
   Fourier frequencies have exact order d (Moebius over averages; exact rationals).

Writes qpK.txt (residue r, coefficients c_0..c_K) and prints the analysis.
"""
import sys
import json
import glob
from fractions import Fraction as Fr
from math import lcm, gcd

K = int(sys.argv[1])
files = sorted(glob.glob(f'classes_{K}.json')) or sorted(glob.glob(f'classes_{K}_*of*.json'))
L = []
for fn in files:
    L += [json.loads(l) for l in open(fn)]
print(f'K={K}: {len(L)} classes from {files}')

P = 1
worst = -10**9
for c in L:
    P = lcm(P, *c['den'])
    worst = max(worst, len(c['num']) - 1 + c['shift'] - sum(c['den']))
print('period bound P = lcm of denominators =', P, '; max deg(num)+shift-sum(den) =', worst)
assert worst < 0

NM = (K + 2) * P + 1
if len(sys.argv) > 2:
    NM = max(NM, int(sys.argv[2]) + 1)


def expand(c, n):
    a = [0] * n
    for i, v in enumerate(c['num']):
        if c['shift'] + i < n:
            a[c['shift'] + i] += v
    for d in c['den']:     # divide by (1 - t^d): a[i] += a[i-d]
        for i in range(d, n):
            a[i] += a[i - d]
    return a


T = [0] * NM
per_class = {}
for c in L:
    e = expand(c, NM)
    per_class[''.join(map(str, c['pi']))] = e
    for i in range(NM):
        T[i] += e[i]
with open(f'T{K}_series.txt', 'w') as f:
    for n in range(1, NM):
        f.write(f'{n} {T[n]}\n')


def interp(xs, ys):
    """coefficients (ascending) of the polynomial through (xs, ys), exact."""
    n = len(xs)
    coef = [Fr(0)] * n
    for i in range(n):
        # basis polynomial
        b = [Fr(1)]
        den = Fr(1)
        for j in range(n):
            if j == i:
                continue
            b = [Fr(0)] + b
            for k in range(len(b) - 1):
                b[k] -= xs[j] * b[k + 1]
            den *= xs[i] - xs[j]
        for k in range(n):
            coef[k] += ys[i] * b[k] / den
    return coef


Q = []
for r in range(P):
    xs = [r + m * P for m in range(K + 1)]
    Q.append(interp(xs, [T[x] for x in xs]))


def qp(N):
    return sum(c * N**j for j, c in enumerate(Q[N % P]))


for N in range(0, NM):
    assert qp(N) == T[N], N
print(f'quasi-polynomial (period {P}) reproduces the series for all N = 0..{NM - 1}')
with open(f'qp{K}.txt', 'w') as f:
    f.write(f'# T(N,{K}) = sum_j c_j(N) N^j ; line: r = N mod {P}, c_0 .. c_{K}\n')
    for r in range(P):
        f.write(f'{r} ' + ' '.join(str(c) for c in Q[r]) + '\n')


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def mobius(n):
    m, p, r = n, 2, 1
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            r = -r
        p += 1
    return -r if m > 1 else r


def components(f):
    """f: list of length P. returns {d: g_d (list of length d)} for the nonzero exact-order parts."""
    avg = {}
    for d in divisors(P):
        avg[d] = [sum(f[r::d], Fr(0)) / (P // d) for r in range(d)]
    out = {}
    for d in divisors(P):
        g = [Fr(0)] * d
        for e in divisors(d):
            mu = mobius(d // e)
            if mu:
                for r in range(d):
                    g[r] += mu * avg[e][r % e]
        if any(g):
            out[d] = g
    return out


def minperiod(f):
    for d in divisors(P):
        if all(f[r] == f[r % d] for r in range(P)):
            return d


print()
for j in range(K, -1, -1):
    f = [Q[r][j] for r in range(P)]
    comp = components(f)
    print(f'c_{j}: minimal period {minperiod(f)}; exact-order components d = {sorted(comp)}')
    if len(set(f)) == 1:
        print('      constant', f[0])
    else:
        for d, g in sorted(comp.items()):
            if d <= 24:
                print(f'      d={d}:', [str(x) for x in g])
