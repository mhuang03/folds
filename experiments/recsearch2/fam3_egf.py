"""Family 3: EGF-specific and Mahler-type functional equations.

A(x) = sum_{n>=0} a(n) x^n / n!  (EGF) and F(x) = sum a(n) x^n (OGF), with a(0) = 1
(and a(0) = 0 as a variant).  Series are exact to x^38.  Every ansatz is a finite set of
basis series B_k (built from the data), and a relation sum c_k B_k = 0 is tested on the
coefficients of x^0..x^38 (all-zero rows dropped), always with E - K >= 5.

 M1  linear 2-Mahler:      sum_{i<=m, j<=d} c_ij x^j G(x^{2^i}) [+ inhomogeneous x^j] = 0
 M2  theta-Mahler:         sum c_ijk x^j theta^k G(x^{2^i}) = 0   (theta = x d/dx)
     (for the OGF this is a linear recurrence mixing a(n-j) and a((n-j)/2^i) with
      polynomial coefficients in n, i.e. a P-recursive / Mahler hybrid)
 M3  nonlinear 2-Mahler:   polynomials of degree <= 2 (and homogeneous 2) in
                           G(x), G(x^2) [, G(x^4)] with coefficients in Q[x]_{<=d}
 M4  q-difference, q = 2 and q = -1 (EGF):  linear in G(x), G(-x), G(2x), G(4x) [, G(x^2)];
     quadratic in G(x), G(-x) (covers A(x)A(-x) = rational-function type relations)
 M5  the coefficient sequences of A(x)A(-x), A(x)/A(-x), A'(x)/A(x) (EGF), F'/F, F(x)F(-x)
     (OGF) and of exp-type substitution log A(x), log F(x) are run through the full
     P-recursive and C-finite box search (rec_search)
 M6  q-holonomic sequences (q = 2):  sum_{i<=r, k<=kd, l<=ld} c_ikl n^l 2^{kn} s(n-i) = 0
     for s = a and s = a/n!  (the coefficient form of q-difference equations)
G is the EGF or the OGF in each case.

A note on M1/M3 for the OGF: if F solves such an equation with the x^{N} coefficient
solved for a(N) (the generic case), a(N) is a bounded-length combination (or convolution)
of earlier terms with constant coefficients, hence a(N) = O(C^N).  a(N) is
super-exponential (proven), so the OGF cannot satisfy them; they are run as a control of
the machinery.  The EGF has coefficients a(N)/N! <= e^{-cN}, so no such obstruction."""
import itertools, sys
from fractions import Fraction
from math import factorial
from common2 import A, NMAX, analyze, rec_search, seqfrac

L = NMAX + 1   # coefficients 0..38


def mul(s, t):
    out = [Fraction(0)] * L
    for i, x in enumerate(s):
        if x:
            for j in range(L - i):
                if t[j]:
                    out[i + j] += x * t[j]
    return out


def inv(s):
    out = [Fraction(0)] * L
    out[0] = 1 / s[0]
    for n in range(1, L):
        out[n] = -sum(s[k] * out[n - k] for k in range(1, n + 1)) / s[0]
    return out


def deriv(s):
    return [s[n + 1] * (n + 1) for n in range(L - 1)] + [None]


def log1(s):   # log s, s[0] = 1, via s'/s integrated
    d = mul([x if x is not None else Fraction(0) for x in deriv(s)][:L], inv(s))
    out = [Fraction(0)] + [d[n - 1] / n for n in range(1, L)]
    out[-1] = None   # last coefficient needs s[L] (unknown): mark invalid
    return out


def sub2(s, i):
    out = [Fraction(0)] * L
    for n in range(L):
        if n * 2 ** i < L:
            out[n * 2 ** i] = s[n]
    return out


def scale(s, c):
    return [x * Fraction(c) ** n if x is not None else None for n, x in enumerate(s)]


def theta(s, k):
    return [x * Fraction(n) ** k for n, x in enumerate(s)]


def xshift(s, j):
    return [Fraction(0)] * j + s[:L - j]


def one():
    return [Fraction(1)] + [Fraction(0)] * (L - 1)


stats = {}


def test(tag, desc, basis, quiet=False):
    rows = []
    for n in range(L):
        row = [b[n] for b in basis]
        if any(x is None for x in row):
            continue
        if any(row):
            rows.append(row)
    K, E = len(basis), len(rows)
    if E - K < 5:
        return False
    res = analyze(rows)
    st = stats.setdefault(tag, [0, -99, '', 0])
    st[0] += 1
    st[3] = max(st[3], K)
    if res['excess'] > st[1]:
        st[1], st[2] = res['excess'], desc
    if res['kernel']:
        print('HIT', tag, desc, 'K', K, 'E', E, 'dim', len(res['kernel']), [str(v)[:10] for v in res['kernel'][0]])
        sys.stdout.flush()
    return True


def mahler_family(G, gname):
    for m in range(1, 4):
        for inh in (0, 1):
            for d in range(0, 30):
                basis = [xshift(sub2(G, i), j) for i in range(m + 1) for j in range(d + 1)]
                if inh:
                    basis += [xshift(one(), j) for j in range(d + 1)]
                if not test(f'{gname} M1 linear Mahler m={m}', f'inh={inh} d={d}', basis):
                    break
    for m in range(1, 3):
        for kd in range(1, 4):
            for d in range(0, 30):
                basis = [xshift(theta(sub2(G, i), k), j) for i in range(m + 1) for k in range(kd + 1) for j in range(d + 1)]
                if not test(f'{gname} M2 theta-Mahler m={m} k<={kd}', f'd={d}', basis):
                    break
    for vars_ in ((0, 1), (0, 1, 2)):
        gs = [sub2(G, i) for i in vars_]
        for kind in ('hom2', '<=2'):
            degs = (2,) if kind == 'hom2' else (0, 1, 2)
            mons = []
            for D in degs:
                for c in itertools.combinations_with_replacement(range(len(gs)), D):
                    t = one()
                    for v in c:
                        t = mul(t, gs[v])
                    mons.append(t)
            for d in range(0, 30):
                basis = [xshift(mm, j) for mm in mons for j in range(d + 1)]
                if not test(f'{gname} M3 nonlinear Mahler vars={vars_} {kind}', f'd={d}', basis):
                    break


for a0 in (1, 0):
    seq = [Fraction(a0)] + [Fraction(A[n]) for n in range(1, L)]
    EGF = [seq[n] / factorial(n) for n in range(L)]
    OGF = seq[:]
    mahler_family(EGF, f'EGF(a0={a0})')
    mahler_family(OGF, f'OGF(a0={a0})')
    # M4 q-difference
    for lin in (('x', '-x'), ('x', '2x'), ('x', '-x', '2x'), ('x', '2x', '4x'), ('x', '-x', '2x', 'x^2'), ('x', '-x', 'x^2')):
        fn = {'x': EGF, '-x': scale(EGF, -1), '2x': scale(EGF, 2), '4x': scale(EGF, 4), 'x^2': sub2(EGF, 1)}
        for d in range(0, 30):
            basis = [xshift(fn[v], j) for v in lin for j in range(d + 1)] + [xshift(one(), j) for j in range(d + 1)]
            if not test(f'EGF(a0={a0}) M4 linear in {lin}', f'd={d}', basis):
                break
    if a0 == 1:
        for vv in (('x', '-x'), ('x', '2x'), ('x', '-x', 'x^2')):
            fn = {'x': EGF, '-x': scale(EGF, -1), '2x': scale(EGF, 2), 'x^2': sub2(EGF, 1)}
            gs = [fn[v] for v in vv]
            mons = []
            for D in (0, 1, 2):
                for c in itertools.combinations_with_replacement(range(len(gs)), D):
                    t = one()
                    for v in c:
                        t = mul(t, gs[v])
                    mons.append(t)
            for d in range(0, 30):
                basis = [xshift(mm, j) for mm in mons for j in range(d + 1)]
                if not test(f'EGF M4 quadratic in {vv}', f'd={d}', basis):
                    break

print()
print(f"{'ansatz':58s} {'boxes':>5s} {'maxK':>5s}  best excess")
for tag, st in stats.items():
    print(f"{tag:58s} {st[0]:5d} {st[3]:5d}  {st[1]:+d} ({st[2]})")

# M5 derived series
print('\nM5: derived coefficient sequences, full P-rec / C-finite box search (K <= 30, spare >= 5)')
seq = [Fraction(1)] + [Fraction(A[n]) for n in range(1, L)]
EGF = [seq[n] / factorial(n) for n in range(L)]
Am = scale(EGF, -1)
derived = {
    'EGF A(x)A(-x) [even coeffs]*n!': [x * factorial(n) for n, x in enumerate(mul(EGF, Am))][0::2],
    'EGF A(x)/A(-x) *n!': [x * factorial(n) for n, x in enumerate(mul(EGF, inv(Am)))],
    "EGF A'/A *n!": [x * factorial(n) if x is not None else None for n, x in enumerate(mul([y or Fraction(0) for y in deriv(EGF)], inv(EGF)))][:L - 1],
    'OGF F(x)F(-x) [even]': mul(seq, scale(seq, -1))[0::2],
    'OGF F(x)/F(-x)': mul(seq, inv(scale(seq, -1))),
    "OGF F'/F": mul([y or Fraction(0) for y in deriv(seq)], inv(seq))[:L - 1],
    'EGF log A *n!': [x * factorial(n) if x is not None else None for n, x in enumerate(log1(EGF))],
    'EGF A(x)^2/A(2x) *n!': [x * factorial(n) for n, x in enumerate(mul(mul(EGF, EGF), inv(scale(EGF, 2))))],
    'EGF A(x)^2 - A(x^2)... (x^2-sub) A(x)^2/A(x^2)': mul(mul(EGF, EGF), inv(sub2(EGF, 1))),
    'OGF F(x)^2/F(x^2)': mul(mul(seq, seq), inv(sub2(seq, 1))),
}
for name, s in derived.items():
    s = [Fraction(x) if x is not None else None for x in s]
    for mode in ('P-rec', 'C-fin'):
        nb, best, hits = rec_search(s, cfinite=(mode == 'C-fin'))
        if nb:
            print(f"  {name:48s} {mode} boxes={nb:3d} best excess {best[2]['excess']:+d} hits={len(hits)}")
            for h in hits:
                print('    HIT', h[0], h[1], h[2]['genuine'][0])

# M6 q-holonomic
print('\nM6: q-holonomic (q=2): sum c_ikl n^l 2^{kn} s(n-i) = 0')
for sname, s in (('a', seqfrac(lambda n: A[n])), ('a/n!', seqfrac(lambda n: Fraction(A[n], factorial(n))))):
    best = -99
    nb = 0
    for r in range(1, 8):
        for kd in range(1, 6):
            for ld in range(0, 4):
                rows = []
                for n in range(1 + r, NMAX + 1):
                    rows.append([Fraction(n) ** l * 2 ** (k * n) * s[n - i] for i in range(r + 1) for k in range(kd + 1) for l in range(ld + 1)])
                K = len(rows[0])
                if len(rows) - K < 5:
                    break
                res = analyze(rows, target_cols=[k * (ld + 1) + l for k in range(kd + 1) for l in range(ld + 1)])
                nb += 1
                best = max(best, res['excess'])
                if res.get('genuine'):
                    print('  HIT', sname, r, kd, ld, res['genuine'][0])
    print(f'  {sname}: boxes={nb} best excess {best:+d}')

# control: exp(x) satisfies A(x)^2 = A(2x); the generating code must find it
E0 = [Fraction(1, factorial(n)) for n in range(L)]
stats.clear()
test('CONTROL exp', 'A(x)^2 - A(2x) in quad basis', [mul(E0, E0), scale(E0, 2), E0, one()])
# control: Stern-like Mahler series F(x) = (1+x+x^2) F(x^2)
Fs = [Fraction(0)] * L
Fs[0] = Fraction(1)
for n in range(1, L):
    Fs[n] = (Fs[n // 2] if n % 2 == 0 else 0) + (Fs[(n - 1) // 2] if n % 2 == 1 else 0) + (Fs[(n - 2) // 2] if n % 2 == 0 and n >= 2 else 0)
test('CONTROL stern', 'F(x) - (1+x+x^2)F(x^2)', [Fs] + [xshift(sub2(Fs, 1), j) for j in range(3)])
