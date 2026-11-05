"""k7.py: T(N,7) from classes_7.json (ehrhart.py 7; 4260 classes).

1. Leading coefficient exactly: a class GF t^s num(t)/prod_{i=1..8}(1-t^{d_i}) contributes
   num(1) / (prod d_i * 7!) to the coefficient of N^7.
2. Exact period.  The lcm of all class periods, P = 624960, is a period (proven: every class
   GF is proper, see qpoly.py).  To show that no proper divisor Q = P/p is a period, we compute
   T(N,7) mod a prime q for N < 9P (numpy, classes grouped by denominator) and evaluate the
   8-fold Q-step difference  D(N) = sum_i (-1)^i C(8,i) T(N + iQ).  D vanishes identically
   iff Q is a period; one nonzero value mod q is a rigorous certificate that it is not.
   The same series are checked against ../prefix/T7.txt.
"""
import json
from fractions import Fraction as Fr
from math import lcm, factorial, comb, prod
import numpy as np

K = 7
L = [json.loads(l) for l in open('classes_7.json')]
c7 = sum(Fr(sum(c['num']), prod(c['den']) * factorial(K)) for c in L)
print('c_7 =', c7, '=', float(c7))
print('matches ../prefix value 12908310624317597/3982715969863680000:',
      c7 == Fr(12908310624317597, 3982715969863680000), flush=True)

P = lcm(*[lcm(*c['den']) for c in L])
print('P =', P)
LEN = 9 * P

# group by (den multiset): sum shifted numerators
groups = {}
for c in L:
    key = tuple(sorted(c['den']))
    g = groups.setdefault(key, {})
    for i, v in enumerate(c['num']):
        e = c['shift'] + i
        g[e] = g.get(e, 0) + v
print(len(groups), 'distinct denominators', flush=True)


def series_mod(q):
    T = np.zeros(LEN, dtype=np.int64)
    for den, num in groups.items():
        a = np.zeros(LEN, dtype=np.int64)
        for e, v in num.items():
            a[e] = v % q
        for d in den:
            a = np.cumsum(a.reshape(-1, d), axis=0).ravel() % q
        T += a
        T %= q
    return T


data = {}
for l in open('../prefix/T7.txt'):
    t = l.split()
    if len(t) > 7 and t[0][0] in '0123456789':
        data[int(t[0])] = int(t[7])

for q in (2147483647, 2147483629):
    T = series_mod(q)
    bad = [n for n, v in data.items() if T[n] != v % q]
    print(f'q={q}: T7.txt N = {min(data)}..{max(data)} agree:', not bad, flush=True)
    for p in (2, 3, 5, 7, 31):
        Q = P // p
        n = LEN - 8 * Q
        D = np.zeros(n, dtype=np.int64)
        for i in range(9):
            D = (D + (-1) ** i * comb(8, i) % q * T[i * Q:i * Q + n]) % q
        nz = np.flatnonzero(D)
        print(f'   Q = P/{p} = {Q}: {"NOT a period" if len(nz) else "difference vanishes"}'
              + (f' (first N with D != 0: {nz[0]})' if len(nz) else ''), flush=True)

# 3. Staircase.  D = Delta_Q^8 T is a quasi-polynomial of period P whose degree is exactly
#    max{ j : c_j(N) does not have period dividing Q }  (E^Q - 1 is invertible on the part of a
#    periodic function with no Q-periodic component, so that part of the top such coefficient
#    survives).  The degree is read off from the P-step differences of D.  Prediction from the
#    staircase period(c_{7-m}) = B(m) (B = 1,1,2,12,168,1680,104160,624960 for m = 0..7).
B = {0: 1, 1: 1, 2: 2, 3: 12, 4: 168, 5: 1680, 6: 104160, 7: 624960}
print('staircase test (last q):')
for div in (2, 3, 4, 5, 7, 8, 9, 16, 31, 32, 64):
    Q = P // div
    n = LEN - 8 * Q
    D = np.zeros(n, dtype=np.int64)
    for i in range(9):
        D = (D + (-1) ** i * comb(8, i) % q * T[i * Q:i * Q + n]) % q
    deg, ok = -1, True
    while np.any(D):
        if D.size <= 2 * P:
            ok = False
            break
        deg += 1
        D = (D[P:] - D[:-P]) % q
    pred = max([K - m for m in B if Q % B[m] != 0], default=-1)
    print(f'   Q = P/{div} = {Q}: max j with c_j not Q-periodic = {deg if ok else "?"}'
          f'  (staircase predicts {pred})', flush=True)
