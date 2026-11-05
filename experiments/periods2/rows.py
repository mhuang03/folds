"""rows.py: T(N,k) for all k <= N <= 22 (from ../prefix/levels.txt, full subset DP) and a search
for a transfer structure in k: linear recurrences
    sum_{0<=i<=I, 0<=j<=J} p_ij(N,k) T(N-i, k-j) = 0     (deg p_ij <= d in N, k jointly)
valid on the whole triangle (with T(N,k) = 0 for k > N or k < 0), by exact nullspace.
Also prints the row polynomials' simple facts (T(N,N) = T(N,N-1) = a(N))."""
import sys
from itertools import product
import sympy as sp


def load(path='../prefix/levels.txt'):
    T = {}
    for line in open(path):
        p = line.split()
        if len(p) >= 3:
            T[(int(p[0]), int(p[1]))] = int(p[2])
    return T


def search(T, NMAX, I, J, d, NMIN=4):
    mons = [(a, b) for a in range(d + 1) for b in range(d + 1 - a)]
    cols = [(i, j, a, b) for i in range(I + 1) for j in range(J + 1) for (a, b) in mons]
    rows = []
    for N in range(NMIN + I, NMAX + 1):
        for k in range(J, N + 1):
            r = []
            for (i, j, a, b) in cols:
                v = T.get((N - i, k - j), 0) if k - j <= N - i else 0
                r.append(sp.Integer(v) * N ** a * k ** b)
            rows.append(r)
    M = sp.Matrix(rows)
    ns = M.nullspace()
    return len(cols), len(rows), len(ns)


if __name__ == '__main__':
    T = load()
    NMAX = max(N for N, k in T)
    print(f'data: N <= {NMAX}')
    for N in range(1, 21):
        print(f'N={N:2d}:', ' '.join(str(T[(N, k)]) for k in range(0, N + 1)))
    print('T(N,N) == T(N,N-1) for all N:', all(T[(N, N)] == T[(N, N - 1)] for N in range(2, NMAX + 1)))
    for (I, J, d) in [(1, 1, 2), (2, 1, 2), (1, 2, 2), (2, 2, 1), (2, 2, 2), (3, 2, 1), (2, 3, 1)]:
        nu, ne, nn = search(T, NMAX, I, J, d)
        print(f'recurrence support {I+1}x{J+1}, degree {d}: {nu} unknowns, {ne} equations, '
              f'nullspace dimension {nn}', flush=True)
