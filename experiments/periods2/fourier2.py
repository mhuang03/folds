"""fourier2.py JSON K Q M: Laurent coefficient of sum_N T(N,K) t^N at zeta = e(1/Q), pole order
K + 1 - M (i.e. the coefficient of e(-N/Q) in the coefficient c_{K-M}(N) of N^(K-M), times
(K-M)!), per class and total, from a classes_K.json file of ../prefix5/ehrhart.py.
Same as ../periods/fourier.py but with explicit file and pole order."""
import sys
import json
import mpmath as mp

mp.mp.dps = 50


def A(cl, zeta, r, eps=mp.mpf(10) ** -22):
    t = zeta * (1 - eps)
    num = mp.polyval(list(reversed([mp.mpf(c) for c in cl['num']])), t)
    den = mp.mpf(1)
    for d in cl['den']:
        den *= (1 - t ** d)
    return (1 - t / zeta) ** r * t ** cl['shift'] * num / den


if __name__ == '__main__':
    path, K, q, m = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    r = K + 1 - m
    zeta = mp.exp(2j * mp.pi / q)
    tot = 0
    car = []
    for line in open(path):
        cl = json.loads(line)
        a = A(cl, zeta, r)
        if abs(a) > mp.mpf(10) ** -12:
            car.append((''.join(map(str, cl['pi'])), a))
        tot += a
    print(f'K={K} q={q} pole order {r} (coefficient of N^{K-m}): {len(car)} classes, '
          f'total = {mp.nstr(tot, 12)}')
    for p, a in car[:40]:
        print('   ', p, mp.nstr(a, 10))
