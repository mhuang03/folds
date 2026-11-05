"""fourier2.py JSON K Q M: Laurent coefficient of sum_N T(N,K) t^N at zeta = e(1/Q), pole order
K + 1 - M (i.e. the coefficient of e(-N/Q) in the coefficient c_{K-M}(N) of N^(K-M), times
(K-M)!), per class and total, from a classes_K.json file of ../prefix5/ehrhart.py.
Same as ../periods/fourier.py but with explicit file and pole order."""
import sys
import json
import mpmath as mp

import os
mp.mp.dps = int(os.environ.get('DPS', '50'))          # use DPS=400 EPSDIG=150 for K >= 7
EPS = mp.mpf(10) ** -int(os.environ.get('EPSDIG', '22'))


def A(cl, zeta, r, eps=None, q=None):
    if q is not None and sum(1 for d in cl['den'] if d % q == 0) < r:
        return mp.mpf(0)          # no pole of order r at primitive q-th roots
    eps = EPS if eps is None else eps
    t = zeta * (1 - eps)
    num = mp.polyval(list(reversed([mp.mpf(c) for c in cl['num']])), t)
    den = mp.mpf(1)
    for d in cl['den']:
        den *= (1 - t ** d)
    return (1 - t / zeta) ** r * t ** cl['shift'] * num / den


def cyclo(q):
    """integer coefficients (low to high) of Phi_q."""
    import sympy as sp
    x = sp.symbols('x')
    return [int(c) for c in reversed(sp.Poly(sp.cyclotomic_poly(q, x), x).all_coeffs())]


def divmod_monic(a, b):
    """a, b: integer coefficient lists low->high, b monic.  Returns (quotient, remainder)."""
    a = list(a)
    db = len(b) - 1
    if len(a) - 1 < db:
        return [0], a
    qt = [0] * (len(a) - db)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i]
        if c:
            qt[i - db] = c
            for j in range(db + 1):
                a[i - db + j] -= c * b[j]
    return qt, a[:db]


def A_exact(cl, q, r, phi, zeta):
    """lim_{t->zeta} (1 - t/zeta)^r F(t), exactly reduced: divide num by Phi_q^(p-r)."""
    J = [d for d in cl['den'] if d % q == 0]
    p = len(J)
    if p < r:
        return mp.mpf(0)
    num = [int(c) for c in cl['num']]
    for _ in range(p - r):
        num, rem = divmod_monic(num, phi)
        assert not any(rem), 'numerator not divisible: pole order exceeds the face lemma'
    dphi = mp.polyval([mp.mpf(i * c) for i, c in reversed(list(enumerate(phi)))][:-1], zeta)
    val = zeta ** cl['shift'] * mp.polyval([mp.mpf(c) for c in reversed(num)], zeta)
    for d in cl['den']:
        if d % q:
            val /= (1 - zeta ** d)
        else:
            val /= -d / (zeta * dphi)          # (1 - t^d)/Phi_q(t) at zeta
    return val * (-1 / (zeta * dphi)) ** r      # (1 - t/zeta)^r / Phi_q(t)^r at zeta


if __name__ == '__main__' and os.environ.get('EXACT'):
    path, K, q, m = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    r = K + 1 - m
    zeta = mp.exp(2j * mp.pi / q)
    phi = cyclo(q)
    tot = 0
    n = 0
    for line in open(path):
        cl = json.loads(line)
        a = A_exact(cl, q, r, phi, zeta)
        if a != 0:
            n += 1
        tot += a
    print(f'K={K} q={q} pole order {r} (coefficient of N^{K-m}) [exact reduction]: '
          f'{n} classes with a pole, total = {mp.nstr(tot, 12)}')
    sys.exit()

if __name__ == '__main__':
    path, K, q, m = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    r = K + 1 - m
    zeta = mp.exp(2j * mp.pi / q)
    tot = 0
    car = []
    for line in open(path):
        cl = json.loads(line)
        a = A(cl, zeta, r, q=q)
        if abs(a) > mp.mpf(10) ** -12:
            car.append((''.join(map(str, cl['pi'])), a))
        tot += a
    print(f'K={K} q={q} pole order {r} (coefficient of N^{K-m}): {len(car)} classes, '
          f'total = {mp.nstr(tot, 12)}')
    for p, a in car[:40]:
        print('   ', p, mp.nstr(a, 10))
