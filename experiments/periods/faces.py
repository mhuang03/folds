"""faces.py K: check the face lemma of PROOFS.txt on every admissible order-type polytope.

For every nonempty face F of the closed polytope Pbar_pi (N = 1) we compute
   codim m = K - dim F,
   D_F = least D > 0 such that aff(D F) contains an integer point (McMullen's index of F),
via determinantal divisors: if A y = beta (A r x K of rank r) cuts out aff F, then
   D_F = g(A) / gcd(g(A), g'(A, beta)),
where g(A) = gcd of the r x r minors of A and g' = gcd of the r x r minors of [A | beta] that use
the beta column (Smith normal form argument, see PROOFS.txt section 2).
Checks:  D_F | B(m), and the finer form  D_F | lcm over components ...  is not needed;
reports per m the lcm of D_F over all classes and compares with B(m).
Also records, per m, the set of D_F values that occur."""
import sys
from fractions import Fraction as F
from itertools import combinations
from math import gcd
import PyNormaliz as PN
from poly import rows


def lcm(a, b):
    return a * b // gcd(a, b)


def B(m):
    if m <= 1:
        return 1
    v = 2 ** (m - 1)
    for s in range(1, m):
        a = m - 1 - s
        v = lcm(v, 2 ** a * (2 ** s - 1))
    return v


def det(M):
    M = [[F(x) for x in r] for r in M]
    n = len(M)
    d = F(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return 0
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if f:
                M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return int(d)


def rank_rows(R):
    """indices of a maximal independent subset of rows."""
    basis = []   # reduced rows
    idx = []
    for n, r in enumerate(R):
        v = [F(x) for x in r]
        for b, piv in basis:
            if v[piv]:
                f = v[piv] / b[piv]
                v = [x - f * y for x, y in zip(v, b)]
        piv = next((i for i, x in enumerate(v) if x), None)
        if piv is not None:
            basis.append((v, piv))
            idx.append(n)
    return idx


def index_of(A, beta):
    r = len(A)
    if r == 0:
        return 1
    K = len(A[0])
    gA = 0
    for cols in combinations(range(K), r):
        gA = gcd(gA, det([[row[c] for c in cols] for row in A]))
    gb = 0
    for cols in combinations(range(K), r - 1):
        gb = gcd(gb, det([[row[c] for c in cols] + [b] for row, b in zip(A, beta)]))
    return gA // gcd(gA, gb)


def faces_of(pi):
    K = len(pi)
    R = rows(pi)
    ineq = [list(a) + [c] for a, c, s, t in R]
    C = PN.Cone(inequalities=ineq, grading=[[0] * K + [1]])
    V = [tuple(F(int(x), int(v[-1])) for x in v[:-1]) for v in C.ExtremeRays()]
    tight = []
    for a, c, s, t in R:
        tight.append(frozenset(n for n, v in enumerate(V)
                               if sum(ai * vi for ai, vi in zip(a, v)) + c == 0))
    allv = frozenset(range(len(V)))
    faces = {allv}
    frontier = {allv}
    while frontier:
        new = set()
        for f in frontier:
            for t in tight:
                g = f & t
                if g and g not in faces:
                    new.add(g)
        faces |= new
        frontier = new
    out = []
    for f in faces:
        eqs = [(R[n][0], -R[n][1]) for n, t in enumerate(tight) if f <= t]
        idx = rank_rows([list(a) for a, b in eqs])
        A = [list(eqs[i][0]) for i in idx]
        beta = [eqs[i][1] for i in idx]
        m = len(idx)
        out.append((m, index_of(A, beta), f, V))
    return out


if __name__ == '__main__':
    K = int(sys.argv[1])
    types = [tuple(map(int, l.split())) for l in open(f'types_{K}.txt')]
    per_m = {}
    carriers = {}
    nf = 0
    bad = 0
    for pi in types:
        for m, D, f, V in faces_of(pi):
            nf += 1
            per_m.setdefault(m, set()).add(D)
            if B(m) % D:
                bad += 1
                print('VIOLATION', pi, m, D, [V[i] for i in f])
            if m == K:
                carriers.setdefault(D, {}).setdefault(pi, V[min(f)])
    print(f'K={K}: {len(types)} polytopes, {nf} nonempty faces, {bad} violations of D_F | B(m)')
    for m in sorted(per_m):
        L = 1
        for d in per_m[m]:
            L = lcm(L, d)
        print(f'  m={m}: B(m)={B(m)}, lcm D_F = {L}, values {sorted(per_m[m])}')
    print('  vertices (m = K) by index D: number of classes having one, an example')
    for D in sorted(carriers):
        pi, v = sorted(carriers[D].items())[0]
        print(f'    D={D}: {len(carriers[D])} classes, e.g.', ''.join(map(str, pi)),
              '(' + ', '.join(str(x) for x in v) + ')')
