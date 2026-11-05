"""component.py K q PI [PI ...]: the order-q Fourier part of the constant term contributed by
the given order-type classes (K points), from their exact Normaliz Hilbert series.

The class of pi is the set of integer points of N.P_pi (Lemma 2 of PROOFS.txt); as an
inhomogeneous Normaliz input (strict a.x + cN > 0 becomes a.x + cN - 1 >= 0) its Hilbert series
graded by N is sum_N #(class on N panels) t^N.  For the constant term (pole order 1) at
zeta = exp(2 pi i/q), A = lim (1 - t/zeta) F(t) = zeta^shift num(zeta) prod' 1/(1 - zeta^d) * prod'' 1/d
(prod' over d with q not dividing d, prod'' over d with q | d; exactly one such d is expected).
Prints A per class and the total; by the face lemma only classes having a vertex with q | D
can contribute, so passing those classes gives the total of T(N,K)."""
import sys
import mpmath as mp
import PyNormaliz as PN
from poly import rows

mp.mp.dps = 50


def series(pi):
    K = len(pi)
    ineq = []
    for a, c, strict, t in rows(pi):
        ineq.append(list(a) + [c, -1 if strict else 0])
    C = PN.Cone(inhom_inequalities=ineq, grading=[[0] * K + [1]])
    num, den, shift = C.HilbertSeries()
    return [int(x) for x in num], [int(x) for x in den], int(shift)


def A(num, den, shift, q):
    z = mp.exp(2j * mp.pi / q)
    val = z ** shift * mp.polyval([mp.mpf(c) for c in reversed(num)], z)
    hits = 0
    for d in den:
        if d % q == 0:
            val /= d
            hits += 1
        else:
            val /= (1 - z ** d)
    return val, hits


if __name__ == '__main__':
    K, q = int(sys.argv[1]), int(sys.argv[2])
    tot = 0
    for s in sys.argv[3:]:
        pi = tuple(int(ch) for ch in s)
        assert len(pi) == K
        num, den, shift = series(pi)
        a, hits = A(num, den, shift, q)
        assert hits <= 1, 'pole of order > 1 at zeta: contradicts the face lemma'
        if hits == 0:
            a = 0
        print(s, 'den', den, 'A =', mp.nstr(a, 12), flush=True)
        tot += a
    print('total', mp.nstr(tot, 12))
