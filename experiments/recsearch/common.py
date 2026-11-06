"""Shared data and exact linear-algebra engine for the recurrence search.

Every ansatz used here is LINEAR in its unknown coefficients: an equation is a row
  sum_k c_k * phi_k(N) = 0
with phi_k computed exactly from the data.  For a row list we compute
  K      number of unknowns (columns),
  E      number of equations (rows),
  rank   rank over Q (certified by rank mod two 61-bit primes: full rank mod p implies
         full rank over Q; deficient rank is re-checked over Q with flint),
  nfit   the largest m such that the first m rows still have a nonzero common solution.
         Generically nfit = K-1.  excess = nfit-(K-1) > 0 is a "near miss": a formula
         matching more of the first rows than its number of free parameters allows.
A fit counts only if the full system (all E rows, normally E >= K+5) has a nonzero
solution; it is then printed and re-verified over Q.
"""
import os
from fractions import Fraction
from math import factorial, comb, gcd

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


def load_a():
    a = {}
    for line in open(os.path.join(ROOT, 'semi_counts.txt')):
        if line.startswith('#') or not line.strip():
            continue
        f = line.split()
        a[int(f[0])] = int(f[1])
    n = max(a)
    assert sorted(a) == list(range(1, n + 1))
    return [None] + [a[i] for i in range(1, n + 1)]   # 1-indexed, A[0] unused


def load_c():
    c = {}
    for line in open(os.path.join(ROOT, 'arith', 'selfdual_out.txt')):
        f = line.split()
        if len(f) == 2 and f[0].isdigit():
            c[int(f[0])] = int(f[1])
    n = max(c)
    return [None] + [c[i] for i in range(1, n + 1)]


A = load_a()          # A[1..37]
NMAX = len(A) - 1
C = load_c()          # C[1..41]


def _is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for b in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(b, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


P1 = (1 << 61) - 1
P2 = (1 << 61) - 3
while not _is_prime(P2):
    P2 -= 2
assert _is_prime(P1)


def modp(x, p):
    if isinstance(x, Fraction):
        return x.numerator % p * pow(x.denominator % p, -1, p) % p
    return int(x) % p


def prefix_ranks(rows, p=P1):
    """rank mod p of the first m rows, for m = 1..E (incremental elimination)."""
    piv = {}
    ranks = []
    r = 0
    for row in rows:
        v = [modp(x, p) for x in row]
        for col, pr in piv.items():
            f = v[col]
            if f:
                v = [(x - f * y) % p for x, y in zip(v, pr)]
        lead = next((i for i, x in enumerate(v) if x), None)
        if lead is not None:
            inv = pow(v[lead], -1, p)
            v = [x * inv % p for x in v]
            for col in list(piv):
                pr = piv[col]
                f = pr[lead]
                if f:
                    piv[col] = [(x - f * y) % p for x, y in zip(pr, v)]
            piv[lead] = v
            r += 1
        ranks.append(r)
    return ranks


def rational_kernel(rows):
    """Nullspace over Q; returns a list of integer kernel vectors."""
    import flint
    den = 1
    for row in rows:
        for x in row:
            if isinstance(x, Fraction):
                den = den * x.denominator // gcd(den, x.denominator)
    K = len(rows[0])
    M = flint.fmpz_mat(len(rows), K, [int(Fraction(x) * den) for row in rows for x in row])
    X, nul = M.nullspace()
    out = []
    for j in range(nul):
        v = [int(X[i, j]) for i in range(K)]
        g = 0
        for x in v:
            g = gcd(g, x)
        out.append([x // g for x in v] if g else v)
    return out


def analyze(rows, target_cols=None):
    """K, E, rank, nfit, excess and (if any) the rational kernel.
    target_cols: the columns carrying the unknown term; a kernel vector vanishing on
    all of them is a relation among the basis functions only ('spurious')."""
    K = len(rows[0])
    E = len(rows)
    r1 = prefix_ranks(rows, P1)
    r2 = prefix_ranks(rows, P2)
    rk = [max(x, y) for x, y in zip(r1, r2)]
    rank = rk[-1]
    nfit = 0
    for m in range(1, E + 1):
        if rk[m - 1] < K:
            nfit = m
    res = dict(K=K, E=E, rank=rank, nfit=nfit, excess=nfit - (K - 1), kernel=[])
    if rank < K:
        ker = rational_kernel(rows)
        res['kernel'] = ker
        if target_cols is not None:
            res['genuine'] = [v for v in ker if any(v[c] for c in target_cols)]
    return res


def fmt(res):
    s = (f"K={res['K']:3d} E={res['E']:3d} spare={res['E'] - res['K']:3d} "
         f"rank={res['rank']:3d} nfit={res['nfit']:3d} excess={res['excess']:+d}")
    if res['kernel']:
        s += f"  KERNEL dim {len(res['kernel'])}"
        if 'genuine' in res:
            s += f" (genuine {len(res['genuine'])})"
    return s
