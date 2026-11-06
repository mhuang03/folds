#!/usr/bin/env python3
"""relfit.py: test whether C_N(k) (k = 2, 3, 4) is a fixed linear combination of products of
smaller a- and J-values (constant coefficients, polynomial-in-N weights up to N^2).
Fit exactly on the first n rows (N = 12, 13, ...), test on the held-out rows."""
from analyse import *
from fractions import Fraction

J = {1: 1}; C = {}
NMAX = 2
while load(NMAX + 1) is not None: NMAX += 1
for N in range(2, NMAX + 1):
    D = load(N); C[N] = D['C']; J[N] = A[N] - sum(J[k] * D['C'][k] for k in range(2, N))

def basis(N, k):
    m = N - k
    v = [A[m], A[m - 1], J[m], J[m - 1]]
    v += [A[i] * A[m - i] for i in range(2, 5)]
    v += [J[m - 2], N * J[m - 1]]
    v += [N * A[m], N * N * A[m], N * A[m - 1], N * J[m]]
    return v

def solve(rows, rhs):
    n = len(rows[0]); M = [[Fraction(x) for x in r] + [Fraction(b)] for r, b in zip(rows, rhs)]
    for c in range(n):
        p = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[p] = M[p], M[c]
        M[c] = [x / M[c][c] for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                M[i] = [x - M[i][c] * y for x, y in zip(M[i], M[c])]
    return [M[i][n] for i in range(n)]

for k in (2, 3, 4):
    Ns = list(range(12, NMAX + 1))
    rows = [basis(N, k) for N in Ns]; rhs = [C[N][k] for N in Ns]
    n = len(rows[0])
    sol = solve(rows[:n], rhs[:n])
    res = [float((sum(s * x for s, x in zip(sol, rows[i])) - rhs[i]) / rhs[i]) for i in range(n, len(Ns))]
    print('k=%d: %d unknowns, fitted on N=%d..%d; relative residuals on N=%d..%d:' %
          (k, n, Ns[0], Ns[n - 1], Ns[n], Ns[-1]), ['%.2e' % r for r in res])
