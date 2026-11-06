"""Data + engine for recsearch2.  Reuses the exact rank / prefix-rank / kernel engine of
../recsearch/common.py (rank mod two 61-bit primes, kernels over Q with flint).

A fit counts only if the FULL system (E rows, E - K >= spare, normally 5) has a kernel
vector with a non-zero 'target' coefficient; it is then re-verified over Q.
nfit / excess measure near misses as in recsearch (excess > 0 = matches more leading
equations than its free parameters allow)."""
import os, sys
from fractions import Fraction
from math import factorial, comb, gcd
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, 'recsearch'))
from common import analyze, fmt, prefix_ranks, rational_kernel, load_a, load_c  # noqa

A = load_a()            # A[1..38]
NMAX = len(A) - 1
C = load_c()            # C[1..41]


def load_J():
    J = {1: 1}
    for line in open(os.path.join(ROOT, 'jseq', 'out', 'data.txt')):
        f = line.split()
        if f and f[0] == 'N':
            J[int(f[1])] = int(f[5])
    n = max(J)
    return [None] + [J[i] for i in range(1, n + 1)]


def product_part(N):
    s = 2 * A[N // 2] * A[(N + 1) // 2] if N >= 2 else 0
    for d in range(3, N, 2):
        if N % d == 0:
            j = (d - 1) // 2
            s += 2 * A[j * N // d] * A[(j + 1) * N // d]
    return s


J = load_J()                                                   # J[1..33]
I = [None, 1] + [A[N] - product_part(N) for N in range(2, NMAX + 1)]   # I[1..38], identity (A)


def load_T():
    T = {}
    d = os.path.join(ROOT, '..', 'rust', 'results', 'stats')
    for N in range(2, 40):
        p = os.path.join(d, f'semi_{N}.txt')
        if not os.path.exists(p):
            continue
        for line in open(p):
            if line.startswith('prefixes'):
                T[N] = [int(x) for x in line.split()[1:]]
    T[1] = [1, 1]
    return T


T = load_T()                                                   # T[N][k], N <= 24


def check_data():
    for line in open(os.path.join(ROOT, 'jseq', 'out', 'data.txt')):
        f = line.split()
        if f and f[0] == 'N':
            N = int(f[1])
            assert int(f[3]) == A[N] and int(f[7]) == I[N], N
    for N, row in T.items():
        assert row[N] == A[N] and row[-1] == A[N]


check_data()


def rec_rows(s, r, d, n0=1, shifts=None):
    """P-recursive rows for a sequence s (list, index -> Fraction, None = missing):
    sum_{i in shifts, j<=d} c_ij n^j s(n-i) = 0 for all n with all s(n-i) defined."""
    if shifts is None:
        shifts = list(range(r + 1))
    rows = []
    for n in range(n0 + max(shifts), len(s)):
        vals = [s[n - i] if n - i >= 0 else None for i in shifts]
        if any(v is None for v in vals):
            continue
        rows.append([Fraction(n) ** j * v for v in vals for j in range(d + 1)])
    return rows


def rec_search(s, maxK=30, spare=5, rmax=14, skip=0, cfinite=False):
    """All boxes REC(r,d) (or C-finite: d=0 only, any r) with K <= maxK and E-K >= spare.
    Returns (number of boxes, best-excess box, hits)."""
    best, hits, nb = None, [], 0
    for r in range(1, rmax + 1):
        for d in range(0, 1 if cfinite else 30):
            K = (r + 1) * (d + 1)
            rows = rec_rows(s, r, d)[skip:]
            if K > maxK or len(rows) - K < spare:
                break
            res = analyze(rows, target_cols=list(range(d + 1)))
            nb += 1
            if best is None or res['excess'] > best[2]['excess']:
                best = (r, d, res)
            if res.get('genuine'):
                hits.append((r, d, res))
    return nb, best, hits


def seqfrac(f, lo=1, hi=None):
    """list indexed 0..hi with Fraction values f(n) for lo <= n <= hi (None elsewhere)."""
    hi = NMAX if hi is None else hi
    out = [None] * (hi + 1)
    for n in range(lo, hi + 1):
        try:
            v = f(n)
        except (ZeroDivisionError, IndexError, TypeError):
            v = None
        out[n] = None if v is None else Fraction(v)
    return out
