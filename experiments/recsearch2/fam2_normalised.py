"""Family 2: normalisations, then P-recursive (REC(r,d), K <= 30, spare >= 5) and C-finite
(any order with spare >= 5) guessing on each normalised sequence.

Normalisations that are hypergeometric multiples of a (a/n!, a(n)n!/(2n)!, a^2/n! as the
square of a/sqrt(n!)) give the SAME P-recursive boxes as a, up to a shift of degree;
they are included anyway for the C-finite test and because the degree bound moves.
Genuinely new sequences (a P-recursion on them is a NONLINEAR relation for a):
  r(n) = a(n)/a(n-1), Delta r, n a(n-1)/a(n), r(n)/n, r(n)/(2^n - 1)  (q-analogue a/[n]_2!),
  a/n^n  (n^n is not hypergeometric with rational ratio),  a(n)/a(fl(n/2))^2,
  a(n)/(a(fl n/2) a(cl n/2)), a(n)/(n a(n-1)) - 1, r(n)/r(n-1), and log-ratio type
  rationals  a(n)a(n-2)/a(n-1)^2."""
from fractions import Fraction
from math import factorial
from common2 import A, NMAX, rec_search, seqfrac

S = {}
S['a/n!'] = seqfrac(lambda n: Fraction(A[n], factorial(n)))
S['a n!/(2n)!'] = seqfrac(lambda n: Fraction(A[n] * factorial(n), factorial(2 * n)))
S['a^2/n!'] = seqfrac(lambda n: Fraction(A[n] ** 2, factorial(n)))
S['a/n^n'] = seqfrac(lambda n: Fraction(A[n], n ** n))
q2 = [1]
for k in range(1, 60):
    q2.append(q2[-1] * (2 ** k - 1))
S['a/[n]_2!'] = seqfrac(lambda n: Fraction(A[n], q2[n]))
S['r=a(n)/a(n-1)'] = seqfrac(lambda n: Fraction(A[n], A[n - 1]), lo=2)
S['Delta r'] = seqfrac(lambda n: Fraction(A[n], A[n - 1]) - Fraction(A[n - 1], A[n - 2]), lo=3)
S['n a(n-1)/a(n)'] = seqfrac(lambda n: Fraction(n * A[n - 1], A[n]), lo=2)
S['r/n'] = seqfrac(lambda n: Fraction(A[n], n * A[n - 1]), lo=2)
S['r/n - 1'] = seqfrac(lambda n: Fraction(A[n], n * A[n - 1]) - 1, lo=2)
S['r/(2^n-1)'] = seqfrac(lambda n: Fraction(A[n], (2 ** n - 1) * A[n - 1]), lo=2)
S['r(n)/r(n-1)'] = seqfrac(lambda n: Fraction(A[n] * A[n - 2], A[n - 1] ** 2), lo=3)
S['a(n)/a(fl n/2)^2'] = seqfrac(lambda n: Fraction(A[n], A[n // 2] ** 2), lo=2)
S['a(n)/(a(fl)a(cl))'] = seqfrac(lambda n: Fraction(A[n], A[n // 2] * A[(n + 1) // 2]), lo=2)
S['a(2n)/a(n)^2'] = seqfrac(lambda n: Fraction(A[2 * n], A[n] ** 2), hi=NMAX // 2)
S['a(2n+1)/(a(n)a(n+1))'] = seqfrac(lambda n: Fraction(A[2 * n + 1], A[n] * A[n + 1]), hi=(NMAX - 1) // 2)
S['r(2n)'] = seqfrac(lambda n: Fraction(A[2 * n], A[2 * n - 1]), hi=NMAX // 2)
S['r(2n+1)'] = seqfrac(lambda n: Fraction(A[2 * n + 1], A[2 * n]), hi=(NMAX - 1) // 2)
S['a(n+1)a(n-1)-a(n)^2'] = seqfrac(lambda n: A[n + 1] * A[n - 1] - A[n] ** 2, lo=2, hi=NMAX - 1)

print(f"{'sequence':26s} {'mode':6s} {'boxes':>5s} {'terms':>5s}  best excess (r,d,K,E)   hits")
for name, s in S.items():
    nt = sum(1 for x in s if x is not None)
    for mode in ('P-rec', 'C-fin'):
        for skip in (0, 6):
            nb, best, hits = rec_search(s, cfinite=(mode == 'C-fin'), skip=skip, maxK=30, spare=5)
            if nb == 0:
                continue
            b = f"{best[2]['excess']:+d} ({best[0]},{best[1]},{best[2]['K']},{best[2]['E']})"
            print(f"{name:26s} {mode:6s} {nb:5d} {nt:5d}  {b:22s} {len(hits)}"
                  + ('' if skip == 0 else '   [first 6 eqs dropped]'))
            for r, d, res in hits:
                print('   HIT', r, d, res['K'], res['E'], res['genuine'][0])
