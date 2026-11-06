"""Family 4: product-based structure.

 4a  a(n) = prod f(k) with f quasi-rational: on each residue class n = j (mod p), p = 1..6,
     a(n) Q_j(n) = a(n-1) P_j(n) with deg P, Q <= d (K = 2(d+1) per class, spare >= 5);
     and the subsequence form a(n) Q(n) = a(n-p) P(n) on each class (product over a
     progression).  Also full P-rec / C-finite box search on the subsequences a(pn+j), p=3,4.
 4b  multiplicative structure: b(n) = prod_{d|n} a(d)^{mu(n/d)} (multiplicative Moebius
     transform), Dirichlet inverse of a, and a(mn)/(a(m) a(n)^m).
 4c  2-regularity (Allouche-Shallit).  For a sequence s, the 2-kernel elements
     s(2^e n + j) (e <= 2: 7 sequences) evaluated at n = 1..8 give a 7 x 8 matrix whose rank
     is a LOWER bound for the 2-kernel rank.  Second test (affine rank <= 4):
     s(4n+j) in span{1, s(n), s(2n), s(2n+1)} for n = 1..8 (8 equations, 4 unknowns).
     Applied to r(n) = a(n)/a(n-1), n a(n-1)/a(n), v_2(a), v_3(a), a(2n)/a(n)^2-type ratios,
     c(N)/a(N), and a itself (a cannot be 2-regular: 2-regular sequences are O(n^C)).
     Controls: Stern's sequence, popcount, n^2 (found), random rationals (not found)."""
import random
from fractions import Fraction
from math import factorial
from common2 import A, C, NMAX, analyze, rec_search, seqfrac

print('4a  quasi-rational ratios  a(n)Q_j(n) = a(n-s)P_j(n) on n = j mod p')
for s_ in (1, 'p'):
    for p in range(1, 7):
        sh = p if s_ == 'p' else 1
        if s_ == 'p' and p == 1:
            continue
        for j in range(p):
            best, hit, nb = -99, 0, 0
            for d in range(0, 20):
                rows = []
                for n in range(1 + sh, NMAX + 1):
                    if n % p == j:
                        rows.append([Fraction(n) ** e * A[n] for e in range(d + 1)] + [Fraction(n) ** e * A[n - sh] for e in range(d + 1)])
                if not rows or len(rows) - 2 * (d + 1) < 5:
                    break
                res = analyze(rows, target_cols=list(range(d + 1)))
                nb += 1
                best = max(best, res['excess'])
                if res.get('genuine'):
                    hit += 1
                    print('   HIT', p, j, d, res['genuine'][0])
            if nb:
                print(f'   shift={sh} p={p} j={j}: boxes={nb} (d<= {nb-1}) best excess {best:+d} hits {hit}')

print('\n4a\' P-rec / C-finite box search on a(pn+j) (K <= E-5)')
for p in (3, 4):
    for j in range(p):
        s = seqfrac(lambda n: A[p * n + j] if p * n + j >= 1 else None, lo=0, hi=(NMAX - j) // p)
        for mode in ('P-rec', 'C-fin'):
            nb, best, hits = rec_search(s, cfinite=(mode == 'C-fin'))
            if nb:
                print(f'   a({p}n+{j}) {mode}: boxes={nb} best excess {best[2]["excess"]:+d} hits={len(hits)}')

print('\n4b  multiplicative structure')


def mobius(n):
    m, k = 1, 2
    while k * k <= n:
        if n % k == 0:
            n //= k
            if n % k == 0:
                return 0
            m = -m
        k += 1
    return -m if n > 1 else m


b = {}
for n in range(1, NMAX + 1):
    v = Fraction(1)
    for d in range(1, n + 1):
        if n % d == 0:
            v *= Fraction(A[d]) ** mobius(n // d)
    b[n] = v
comp = [n for n in range(2, NMAX + 1) if any(n % k == 0 for k in range(2, n))]
nonint = [n for n in comp if b[n].denominator != 1]
print(f'   b(n) = prod_(d|n) a(d)^mu(n/d): composite n with non-integer b(n): {len(nonint)} of {len(comp)}: {nonint}')
dinv = {1: Fraction(1, A[1])}
for n in range(2, NMAX + 1):
    dinv[n] = -sum(A[d] * dinv[n // d] for d in range(2, n + 1) if n % d == 0) / A[1]
print('   Dirichlet inverse of a (n<=16):', [int(dinv[n]) for n in range(1, 17)])
print('   a(mn)/(a(m) a(n)^m) for m=2,3 (should be >= 1 by a(qn) >= a(q)a(n)^q):')
for m in (2, 3):
    print('    m=%d:' % m, ' '.join(f'{float(Fraction(A[m*n], A[m]*A[n]**m)):.3g}' for n in range(1, NMAX // m + 1)))
    s = seqfrac(lambda n: Fraction(A[m * n], A[m] * A[n] ** m), hi=NMAX // m)
    nb, best, hits = rec_search(s)
    print(f'      P-rec search on it: boxes={nb} best excess {best[2]["excess"] if best else None} hits={len(hits)}')

print('\n4c  2-regularity')


def v_p(x, p):
    if x == 0:
        return None
    k = 0
    while x % p == 0:
        x //= p
        k += 1
    return k


def two_reg(s, name):
    def S(n):
        return s(n)
    # rank lower bound
    rows = []
    for e in range(3):
        for j in range(2 ** e):
            rows.append([Fraction(S(2 ** e * n + j)) for n in range(1, 9)])
    import flint
    den = 1
    for r in rows:
        for x in r:
            den = den * x.denominator // __import__('math').gcd(den, x.denominator)
    M = flint.fmpz_mat([[int(x * den) for x in r] for r in rows])
    rk = M.rank()
    # affine rank-4 closure test
    closed = []
    for j in range(4):
        rr = [[Fraction(1), Fraction(S(n)), Fraction(S(2 * n)), Fraction(S(2 * n + 1)), Fraction(S(4 * n + j))] for n in range(1, 9)]
        res = analyze(rr, target_cols=[4])
        closed.append(bool(res.get('genuine')))
    print(f'   {name:28s} kernel-rank lower bound (7x8 matrix): {rk}/7   s(4n+j) in span{{1,s(n),s(2n),s(2n+1)}}: {closed}')


A0 = [1] + A[1:]   # a(0) = 1 so that r(1) = 1
two_reg(lambda n: Fraction(A0[n], A0[n - 1]), 'r(n)=a(n)/a(n-1)')
two_reg(lambda n: Fraction(n * A0[n - 1], A0[n]), 'n a(n-1)/a(n)')
two_reg(lambda n: v_p(A[n], 2), 'v_2(a(n))')
two_reg(lambda n: v_p(A[n], 3), 'v_3(a(n))')
two_reg(lambda n: Fraction(A0[n], A0[n // 2] * A0[(n + 1) // 2]), 'a(n)/(a(fl)a(cl))')
two_reg(lambda n: Fraction(C[n], A[n]), 'c(N)/a(N)')
two_reg(lambda n: A[n], 'a(n) [impossible: growth]')
st = [0, 1]
for n in range(2, 80):
    st.append(st[n // 2] if n % 2 == 0 else st[n // 2] + st[n // 2 + 1])
two_reg(lambda n: st[n], 'CONTROL Stern')
two_reg(lambda n: bin(n).count('1'), 'CONTROL popcount')
two_reg(lambda n: n * n, 'CONTROL n^2')
random.seed(1)
rnd = [Fraction(random.randint(1, 10 ** 6), random.randint(1, 10 ** 6)) for _ in range(80)]
two_reg(lambda n: rnd[n], 'CONTROL random')
