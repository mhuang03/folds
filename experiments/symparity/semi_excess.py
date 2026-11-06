"""Semi-symmetric parity excess X(N) = #even-first - #odd-first for odd N (N = 7..29,
from ../structure2/FINDINGS.txt 1.2).  Search for an exact formula as a rational linear
combination of at most 3 candidate features, fitted on some points and checked on all.
Features: a, s at N, N+-1, N+-2, at n = (N-1)/2 and n+1, their products, 2^N."""
import itertools
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'structure2'))
from common import counts  # noqa: E402

X = dict(zip(range(7, 30, 2), [20, 148, 2312, 56344, 1680608, 41779316, 1654712136,
                               53436724154, 2559348278480, 146989716562612,
                               7818662696900268, 522220844799116936]))
a, s = counts()
# s(N) for N <= 30 from the sym stats totals
_sd = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'structure2', 'data')
for _N in range(2, 31):
    _p = os.path.join(_sd, f'symstats_{_N}.txt')
    if os.path.exists(_p):
        for _l in open(_p):
            if _l.startswith('total'):
                s[_N] = int(_l.split()[1])


def feats(N):
    n = (N - 1) // 2
    f = {}
    for name, seq in (('a', a), ('s', s)):
        for d in (-2, -1, 0, 1):
            if N + d in seq:
                f[f'{name}(N{d:+d})'] = seq[N + d]
        if n in seq and n + 1 in seq:
            f[f'{name}(n)'] = seq[n]
            f[f'{name}(n+1)'] = seq[n + 1]
            f[f'{name}(n)^2'] = seq[n] ** 2
            f[f'{name}(n+1)^2'] = seq[n + 1] ** 2
            f[f'{name}(n){name}(n+1)'] = seq[n] * seq[n + 1]
    if n in a and n in s and n + 1 in a and n + 1 in s:
        f['a(n)s(n+1)'] = a[n] * s[n + 1]
        f['a(n+1)s(n)'] = a[n + 1] * s[n]
        f['a(n)s(n)'] = a[n] * s[n]
        f['a(n+1)s(n+1)'] = a[n + 1] * s[n + 1]
    f['2^N'] = 2 ** N
    f['1'] = 1
    return f


def solve(rows, rhs):
    """Exact Gaussian elimination; returns the unique solution or None."""
    m = len(rhs)
    k = len(rows[0])
    A = [[Fraction(x) for x in r] + [Fraction(y)] for r, y in zip(rows, rhs)]
    r = 0
    piv = []
    for c in range(k):
        p = next((i for i in range(r, m) if A[i][c] != 0), None)
        if p is None:
            return None
        A[r], A[p] = A[p], A[r]
        for i in range(m):
            if i != r and A[i][c] != 0:
                fac = A[i][c] / A[r][c]
                A[i] = [x - fac * y for x, y in zip(A[i], A[r])]
        piv.append(c); r += 1
    if any(A[i][k] != 0 for i in range(r, m)):
        return None
    return [A[i][k] / A[i][i] for i in range(k)]


Ns = sorted(X)
F = {N: feats(N) for N in Ns}
names = sorted(set.intersection(*(set(F[N]) for N in Ns)))
print('points:', Ns)
print('features on all points:', names)
found = 0
for size in (1, 2, 3):
    for combo in itertools.combinations(names, size):
        rows = [[F[N][c] for c in combo] for N in Ns]
        sol = solve(rows, [X[N] for N in Ns])
        if sol is not None:
            found += 1
            print('RELATION:', ' + '.join(f'({c}) {n}' for c, n in zip(sol, combo)))
print('relations found:', found)
# ratios for the record
for N in Ns:
    print(N, X[N], 'X/a(N) = %.5f' % (X[N] / a[N]), 'X/a(N-1) = %.5f' % (X[N] / a[N - 1]))
