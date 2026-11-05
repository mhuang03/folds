"""fourier.py K: which classes carry which Fourier components of T(N,K), and do they cancel?

Input: ../prefix5/classes_K.json (Normaliz Hilbert series of every class, sum_N #P(N) t^N =
t^shift num(t) / prod (1 - t^d)).  For q >= 2 let m(q) = least m with q | B(m).  By the face
lemma (PROOFS.txt) the pole of each class series at a primitive q-th root of unity zeta has
order <= K + 1 - m(q).  The exact-order-q Fourier part of the coefficient of N^(K-m(q)) is
   sum over primitive zeta of  A(zeta) zeta^(-N) / (K - m(q))!,
   A(zeta) = lim_{t -> zeta} (1 - t/zeta)^(K+1-m(q)) F(t).
We evaluate A(zeta) for zeta = exp(2 pi i/q) per class (mpmath, t = zeta(1 - eps)), print the
classes with A != 0 and the total.  The component is present in T(N,K) iff the total != 0
(the other primitive roots are Galois conjugates: the total is a rational-coefficient function
of zeta, so it vanishes at one primitive root iff at all, provided it is exact -- the totals
here are checked to be ~0 or clearly nonzero).
"""
import sys
import json
import mpmath as mp
from faces import B

mp.mp.dps = 60


def mq(q):
    m = 0
    while B(m) % q:
        m += 1
    return m


def A(cl, zeta, r, eps=mp.mpf(10) ** -25):
    t = zeta * (1 - eps)
    num = mp.polyval(list(reversed([mp.mpf(c) for c in cl['num']])), t)
    den = mp.mpf(1)
    for d in cl['den']:
        den *= (1 - t ** d)
    return (1 - t / zeta) ** r * t ** cl['shift'] * num / den


if __name__ == '__main__':
    K = int(sys.argv[1])
    qs = [int(x) for x in sys.argv[2].split(',')]
    cls = [json.loads(l) for l in open(f'../prefix5/classes_{K}.json')]
    for q in qs:
        m = mq(q)
        r = K + 1 - m
        zeta = mp.exp(2j * mp.pi / q)
        tot = 0
        carriers = []
        for cl in cls:
            a = A(cl, zeta, r)
            if abs(a) > mp.mpf(10) ** -15:
                carriers.append((''.join(map(str, cl['pi'])), a))
            tot += a
        print(f'K={K} q={q}: m(q)={m}, coefficient of N^{K - m}, pole order {r}: '
              f'{len(carriers)} classes contribute, total |A| = {mp.nstr(abs(tot), 8)}')
        if len(carriers) <= 12:
            for p, a in carriers:
                print(f'    {p}: A = {mp.nstr(a, 10)}')
