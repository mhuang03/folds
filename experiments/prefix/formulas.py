"""formulas.py: the exact quasi-polynomials found, checked against the data files.
T(N,k): valid prefixes of length k (T*.txt from prefix.c);  V(N,k): valid k-sets (V4*.txt from sets.c).
"""
from fractions import Fraction as Fr


def load(fn, col):
    d = {}
    for l in open(fn):
        t = l.split()
        if len(t) > col and t[0].isdigit():
            d[int(t[0])] = int(t[col])
    return d


def T2(N):
    return N * N // 2


def T3(N):
    lin = Fr(-5, 6) if N % 2 == 0 else Fr(-1, 3)
    c0 = (0 if N % 2 == 0 else Fr(-1, 4)) + [0, Fr(4, 9), Fr(2, 9)][N % 3]
    return Fr(2, 9) * N**3 - Fr(1, 12) * N**2 + lin * N + c0


T4_C24 = [0, Fr(-4399, 6912), Fr(193, 432), Fr(451, 256), Fr(-17, 54), Fr(8785, 6912), Fr(19, 16),
          Fr(785, 6912), Fr(-20, 27), Fr(-125, 256), Fr(161, 432), Fr(13969, 6912), Fr(1, 2),
          Fr(5969, 6912), Fr(193, 432), Fr(67, 256), Fr(-22, 27), Fr(-1583, 6912), Fr(19, 16),
          Fr(11153, 6912), Fr(-13, 54), Fr(259, 256), Fr(161, 432), Fr(3601, 6912)]
T4_C7 = [0, Fr(4, 7), 0, Fr(-2, 7), Fr(2, 7), Fr(-4, 7), 0]


def T4(N):
    c2 = Fr(-265, 672) if N % 2 == 0 else Fr(-631, 896)
    c1 = [Fr(7, 12), Fr(35, 32), Fr(7, 12), Fr(9, 32)][N % 4] + [0, Fr(-8, 27), Fr(-7, 27)][N % 3]
    c0 = T4_C24[N % 24] + T4_C7[N % 7]
    return Fr(4283, 48384) * N**4 - Fr(353, 3024) * N**3 + c2 * N**2 + c1 * N + c0


def V2(N):
    return N * N // 3


def V3(N):
    c1 = (Fr(-1, 3) if N % 2 == 0 else Fr(-5, 24)) + (0 if N % 3 == 0 else Fr(-1, 9))
    c0 = (Fr(-1, 2) if N % 4 == 3 else 0) + [0, Fr(8, 27), Fr(10, 27)][N % 3]
    return Fr(23, 216) * N**3 - Fr(1, 12) * N**2 + c1 * N + c0


if __name__ == '__main__':
    for name, f, fns, col in [('T2', T2, ['T5.txt', 'T5b.txt', 'T4.txt'], 2),
                              ('T3', T3, ['T5.txt', 'T5b.txt', 'T4.txt'], 3),
                              ('T4', T4, ['T5.txt', 'T5b.txt', 'T4.txt'], 4),
                              ('V2', V2, ['V4.txt', 'V4b.txt'], 2),
                              ('V3', V3, ['V4.txt', 'V4b.txt'], 3)]:
        d = {}
        for fn in fns:
            try:
                d.update(load(fn, col))
            except FileNotFoundError:
                pass
        for n, v in d.items():
            assert f(n) == v, (name, n, f(n), v)
        print(name, 'matches data for N =', min(d), '..', max(d), f'({len(d)} values)')
