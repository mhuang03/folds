"""Family 5: Hankel determinants and continued fractions (exact).

Moment sequences m_k (k >= 0):  (i) a(k+1) [a(1), a(2), ...], (ii) a(k) with a(0) = 1,
(iii) a(k+2), (iv) a(k)/k! with a(0) = 1.  For each:
  H_n^(0) = det(m_{i+j})_{0<=i,j<n} and H_n^(1) = det(m_{i+j+1}), n = 1..19/18.
  * sign pattern, small-prime part (trial division to 10^5) and cofactor size;
  * Somos-4/5/6-type bilinear relations in H_n (family-1 'somos' boxes, spare >= 5)
    and P-recursive / C-finite search on H_n;
  * J-fraction (b_n, lambda_n) and S-fraction (alpha_n) coefficients, from the Hankel
    ratios  lambda_n = H_{n+1}H_{n-1}/H_n^2,  alpha_{2n} = H_n^(1) H_{n-1}^(0)/(H_n^(0) H_{n-1}^(1)),
    alpha_{2n+1} = H_{n+1}^(0) H_{n-1}^(1)/(H_n^(0) H_n^(1));  integrality, sign, and
    P-rec / rational-in-n fits (rec_search, REC(1,d) included)."""
from fractions import Fraction
import functools
print = functools.partial(print, flush=True)
from math import factorial
import flint
from common2 import A, NMAX, analyze, rec_search

SMALLP = []
sieve = bytearray([1]) * 100001
for i in range(2, 100001):
    if sieve[i]:
        SMALLP.append(i)
        sieve[i * i::i] = bytearray(len(sieve[i * i::i]))


def smooth(x):
    x = abs(x)
    f = {}
    if x == 0:
        return {0: 1}, 1
    for p in SMALLP:
        if x == 1:
            break
        while x % p == 0:
            x //= p
            f[p] = f.get(p, 0) + 1
    return f, x


def hankel(m, shift, n):
    M = flint.fmpq_mat(n, n, [flint.fmpq(m[i + j + shift].numerator, m[i + j + shift].denominator)
                              for i in range(n) for j in range(n)])
    d = M.det()
    return Fraction(int(d.p), int(d.q))


moms = {
    'a(k+1)': [Fraction(A[k + 1]) for k in range(NMAX)],
    'a(k), a(0)=1': [Fraction(1)] + [Fraction(A[k]) for k in range(1, NMAX + 1)],
    'a(k+2)': [Fraction(A[k + 2]) for k in range(NMAX - 1)],
    'a(k)/k!, a(0)=1': [Fraction(1)] + [Fraction(A[k], factorial(k)) for k in range(1, NMAX + 1)],
}
for name, m in moms.items():
    L = len(m)
    n0 = (L + 1) // 2
    n1 = L // 2
    H0 = [Fraction(1)] + [hankel(m, 0, n) for n in range(1, n0 + 1)]
    H1 = [Fraction(1)] + [hankel(m, 1, n) for n in range(1, n1 + 1)]
    print(f'== moments {name}: {L} terms, H^(0)_1..{n0}, H^(1)_1..{n1}')
    for tag, H in (('H0', H0), ('H1', H1)):
        signs = ''.join('+' if h > 0 else ('-' if h < 0 else '0') for h in H[1:])
        print(f'  {tag} signs: {signs}')
        if name != 'a(k)/k!, a(0)=1':
            out = []
            for n in range(1, len(H)):
                f, cof = smooth(int(H[n]))
                sm = '*'.join(f'{p}^{e}' if e > 1 else str(p) for p, e in sorted(f.items()))
                out.append(f'n={n}: {sm or "1"} x [{len(str(cof))}-digit cofactor]')
            print('   ', '\n    '.join(out[:12]))
        s = [None] + H[1:]
        if any(h == 0 for h in H[1:]):
            print(f'  {tag}: contains zero determinants -> linear and Somos searches skipped')
            continue
        for mode in ('P-rec', 'C-fin'):
            nb, best, hits = rec_search(s, cfinite=(mode == 'C-fin'))
            if nb:
                print(f'  {tag} {mode}: boxes={nb} best excess {best[2]["excess"]:+d} hits={len(hits)}')
        # Somos-type: H(n)H(n-k) = al H(n-1)H(n-k+1) + be H(n-2)H(n-k+2) (+ ga ...), constant / poly coeffs
        best, nb, hit = -99, 0, 0
        for k in range(4, 8):
            for d in range(0, 4):
                rows = []
                for n in range(k + 1, len(H)):
                    rows.append([Fraction(n) ** e * H[n - i] * H[n - k + i] for i in range(0, k // 2 + 1) for e in range(d + 1)])
                rows = [r for r in rows if any(r)]
                if not rows or len(rows) - len(rows[0]) < 5:
                    break
                res = analyze(rows)
                nb += 1
                best = max(best, res['excess'])
                if res['kernel']:
                    hit += 1
                    print('   SOMOS HIT', k, d, res['kernel'][0])
        print(f'  {tag} Somos-k (k=4..7, all pairs, poly coeffs): boxes={nb} best excess {best:+d} hits={hit}')
    # continued-fraction coefficients
    if all(h != 0 for h in H0[1:]) and all(h != 0 for h in H1[1:]):
        alpha = []
        for n in range(1, min(n0, n1 + 1)):
            alpha.append(H1[n] * H0[n - 1] / (H0[n] * H1[n - 1]))      # alpha_{2n}  (index convention: alpha_1 = m1/m0)
            if n + 1 <= n0 and n <= n1:
                alpha.append(H0[n + 1] * H1[n - 1] / (H0[n] * H1[n]))
        lam = [H0[n + 1] * H0[n - 1] / H0[n] ** 2 for n in range(1, n0)]
        isint = lambda v: all(x.denominator == 1 for x in v)
        print(f'  S-fraction alpha_1..{len(alpha)}: integral={isint(alpha)}  signs='
              + ''.join('+' if x > 0 else '-' for x in alpha))
        print('    first:', ', '.join(f'{float(x):.4g}' for x in alpha[:12]))
        print(f'  J-fraction lambda_1..{len(lam)}: integral={isint(lam)}  first:', ', '.join(f'{float(x):.4g}' for x in lam[:10]))
        for tag, s in (('alpha', [None] + alpha), ('lambda', [None] + lam)):
            for mode in ('P-rec', 'C-fin'):
                nb, best, hits = rec_search(s, cfinite=(mode == 'C-fin'))
                if nb:
                    print(f'  {tag} {mode}: boxes={nb} best excess {best[2]["excess"]:+d} hits={len(hits)}')
    else:
        print('  zero Hankel determinant: S-fraction undefined')
    print()

# control: for m_k = k! the S-fraction is alpha = 1,1,2,2,3,3,... and must be detected
m = [Fraction(factorial(k)) for k in range(38)]
H0 = [Fraction(1)] + [hankel(m, 0, n) for n in range(1, 19)]
H1 = [Fraction(1)] + [hankel(m, 1, n) for n in range(1, 19)]
al = []
for n in range(1, 18):
    al += [H1[n] * H0[n - 1] / (H0[n] * H1[n - 1]), H0[n + 1] * H1[n - 1] / (H0[n] * H1[n])]
print('CONTROL k!: alpha =', [int(x) for x in al[:10]], ' P-rec hits on alpha:', len(rec_search([None] + al)[2]))
