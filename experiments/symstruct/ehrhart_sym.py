"""ehrhart_sym.py K NMAX: EXACT generating function of T_sym(N,K) via Normaliz (PyNormaliz).

T_sym(N,K) = number of K-step prefixes (x_1..x_K distinct in [1,N]) in which every step is
symmetric: for i < j, the partner 2x_j - x_i of x_i about x_j is outside [1,N] or is an
earlier x_l.  (Same method as ../prefix5/ehrhart.py.)  A class is (pi, tau): pi the order
type, and for every i < j
   tau_ij = 'L':  2x_j <= x_i            (partner below 1)
   tau_ij = 'R':  2x_j >= N + x_i + 1    (partner above N)
   tau_ij = l  :  2x_j = x_i + x_l, l < j, l != i
The classes partition the valid prefixes and each is the lattice-point set of one rational
polyhedron in (x, N); Normaliz gives its Hilbert series in N exactly.  The sum is expanded to
NMAX and written to data/Tsym{K}_series.txt; the period of the quasi-polynomial divides the
lcm of the denominators, and the exact period is found by fitting on the exact series.
"""
import sys
from itertools import product
from math import lcm
import PyNormaliz as PN


def build(K, pi, tau):
    ineq, eq = [], []

    def row(coef, cN, b, R):
        a = [0] * K
        for i, c in coef:
            a[i] += c
        R.append(a + [cN, b])
    for i in range(K):
        row([(i, 1)], 0, -1, ineq)
        row([(i, -1)], 1, 0, ineq)
    order = sorted(range(K), key=lambda i: pi[i])
    for u, v in zip(order, order[1:]):
        row([(v, 1), (u, -1)], 0, -1, ineq)
    for (i, j), t in tau.items():
        if t == 'L':
            row([(j, -2), (i, 1)], 0, 0, ineq)
        elif t == 'R':
            row([(j, 2), (i, -1)], -1, -1, ineq)
        else:
            row([(j, 2), (i, -1), (t, -1)], 0, 0, eq)
    return ineq, eq


def series(K, pi, tau):
    ineq, eq = build(K, pi, tau)
    kw = dict(inhom_inequalities=ineq, grading=[[0] * K + [1]])
    if eq:
        kw['inhom_equations'] = eq
    C = PN.Cone(**kw)
    num, den, shift = C.HilbertSeries()
    return [int(x) for x in num], [int(x) for x in den], int(shift)


def extensions(pi, tau, K):
    j = K - 1
    for r in range(1, K + 1):
        npi = tuple(p + (p >= r) for p in pi) + (r,)
        opts = []
        for i in range(j):
            o = []
            if npi[j] < npi[i]:
                o.append('L')      # 2x_j <= x_i possible only if x_j < x_i
            else:
                o.append('R')
            o += [l for l in range(j) if l != i]
            opts.append(o)
        for choice in product(*opts):
            t = dict(tau)
            ok = True
            for i, c in enumerate(choice):
                if c not in ('L', 'R'):
                    # equality 2x_j = x_i + x_l needs x_j strictly between, and symmetry
                    if not (min(npi[i], npi[c]) < npi[j] < max(npi[i], npi[c])) or choice[c] != i:
                        ok = False
                        break
                t[(i, j)] = c
            if ok:
                yield npi, t


def expand(num, den, shift, NMAX):
    c = [0] * (NMAX + 1)
    for e, a in enumerate(num):
        if e + shift <= NMAX:
            c[e + shift] += a
    for d in den:
        for n in range(d, NMAX + 1):
            c[n] += c[n - d]
    return c


def main():
    KMAX, NMAX = int(sys.argv[1]), int(sys.argv[2])
    classes = [((1,), {})]
    for K in range(2, KMAX + 1):
        new = []
        cand = [c for pi, tau in classes for c in extensions(pi, tau, K)]
        for npi, t in cand:
            num, den, shift = series(K, npi, t)
            if any(num):
                new.append((npi, t, (num, den, shift)))
        classes = [(p, t) for p, t, _ in new]
        print(f"k={K}: {len(cand)} candidates, {len(new)} nonempty classes", file=sys.stderr, flush=True)
    tot = [0] * (NMAX + 1)
    L = 1
    for _, _, (num, den, shift) in new:
        for n, v in enumerate(expand(num, den, shift, NMAX)):
            tot[n] += v
        for d in den:
            L = lcm(L, d)
    print(f"lcm of denominators: {L}", file=sys.stderr)
    with open(f"data/Tsym{KMAX}_series.txt", "w") as f:
        for n in range(1, NMAX + 1):
            f.write(f"{n} {tot[n]}\n")


if __name__ == '__main__':
    main()
