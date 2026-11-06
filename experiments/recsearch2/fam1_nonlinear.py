"""Family 1: nonlinear shift recurrences (all linear in the unknown coefficients).

 1a Somos / Hirota bilinear:  al(n) s(n)s(n-k) + be(n) s(n-i)s(n-k+i) + ga(n) s(n-j)s(n-k+j)
    [+ de(n) s(n-l)s(n-k+l)] = 0,  al..de polynomials of degree d, 1 <= i < j (< l) <= k/2.
 1b Riccati-type: p0(n) s(n)s(n-g) + p1(n) s(n) + p2(n) s(n-g) + p3(n) = 0, gaps g = 1..4.
 1c General polynomial relations P(n, s(n), ..., s(n-r)) = 0: all monomials of a-degree in
    a set Dset (homogeneous 2, homogeneous 3, all <= 2, all <= 3), times n^0..n^d.
 Run on several sequences s: a, a/n!, r(n) = a(n)/a(n-1), r(n)/n, a/n^n,
c(2n), c(4n+1), a(2n), J(N).
Every box has E - K >= 5.  Any kernel vector is a relation (all terms involve the data,
so there is no 'target' column); every kernel is re-verified over Q and printed."""
import itertools, sys
from fractions import Fraction
from math import factorial
from common2 import A, C, J, NMAX, analyze, seqfrac

SPARE = 5
SEQS = {
    'a': seqfrac(lambda n: A[n]),
    'a/n!': seqfrac(lambda n: Fraction(A[n], factorial(n))),
    'r=a(n)/a(n-1)': seqfrac(lambda n: Fraction(A[n], A[n - 1]), lo=2),
    'r/n': seqfrac(lambda n: Fraction(A[n], n * A[n - 1]), lo=2),
    'a/n^n': seqfrac(lambda n: Fraction(A[n], n ** n)),
    # c(N) = 0 for N = 3 (mod 4): its zero pattern decouples monomials into blocks with too
    # few equations each (spurious kernels), so only zero-free subsequences are used.
    'c(2n)': seqfrac(lambda n: C[2 * n], hi=20),
    'c(4n+1)': seqfrac(lambda n: C[4 * n + 1], lo=0, hi=10),
    'a(2n)': seqfrac(lambda n: A[2 * n], hi=19),
    'J': seqfrac(lambda n: J[n], hi=33),
}


def monos(nv, Dset):
    out = []
    for D in sorted(Dset):
        for c in itertools.combinations_with_replacement(range(nv), D):
            out.append(c)
    return out


def rows_poly(s, shifts, mon, d):
    rows = []
    for n in range(len(s)):
        if n - max(shifts) < 0:
            continue
        v = [s[n - i] for i in shifts]
        if any(x is None for x in v):
            continue
        row = []
        for m in mon:
            val = Fraction(1)
            for t in m:
                val *= v[t]
            for j in range(d + 1):
                row.append(val * Fraction(n) ** j)
        rows.append(row)
    return rows


stats = {}


def run(tag, rows, desc):
    rows = [r for r in rows if any(r)]   # all-zero rows (c(N)=0 for N=3 mod 4) carry no information
    if not rows:
        return False
    K, E = len(rows[0]), len(rows)
    if E - K < SPARE:
        return False
    res = analyze(rows)
    st = stats.setdefault(tag, [0, -99, None, 0, 0])
    st[0] += 1
    st[3] += K
    st[4] = max(st[4], E)
    if res['excess'] > st[1]:
        st[1], st[2] = res['excess'], desc
    if res['kernel']:
        print('HIT', tag, desc, 'K', K, 'E', E, 'kernel dim', len(res['kernel']), 'first', [str(x)[:12] for x in res['kernel'][0]])
        sys.stdout.flush()
    return True


for name, s in SEQS.items():
    # 1a Somos/Hirota
    for k in range(2, 13):
        pairs = list(range(1, k // 2 + 1))
        for npair in (2, 3):
            for sel in itertools.combinations(pairs, npair - 1):
                shifts = list(range(k + 1))
                for d in range(0, 12):
                    mon = [(0, k)] + [(i, k - i) for i in sel]
                    if npair == 2 and len(sel) == 1:
                        pass
                    rows = rows_poly(s, shifts, mon, d)
                    if not run(f'{name} somos', rows, f'k={k} pairs={sel} d={d}'):
                        break
            # also the full 3-term Hirota with both pairs i<j (npair=3 covers it)
    # 1b Riccati
    for g in range(1, 5):
        for d in range(0, 12):
            rows = rows_poly(s, [0, g], [(0, 1), (0,), (1,), ()], d)
            if not run(f'{name} riccati', rows, f'gap={g} d={d}'):
                break
    # 1c general polynomial relations
    for Dname, Dset in (('hom2', {2}), ('hom3', {3}), ('<=2', {0, 1, 2}), ('<=3', {0, 1, 2, 3})):
        for r in range(1, 8):
            mon = monos(r + 1, Dset)
            for d in range(0, 12):
                rows = rows_poly(s, list(range(r + 1)), mon, d)
                if not run(f'{name} poly{Dname}', rows, f'r={r} d={d} (#mon={len(mon)})'):
                    break

print()
print(f"{'family':40s} {'boxes':>5s} {'maxK':>5s} {'maxE':>5s}  best excess (box)")
for tag, st in stats.items():
    print(f"{tag:40s} {st[0]:5d} {'':5s} {st[4]:5d}  {st[1]:+d} ({st[2]})")
