"""analyze.py: tables derived from W(N,k) (output of weak.c).

  python3 analyze.py [files...]      default: W_small.txt W_19_22.txt W_d_19_20.txt

For each convention (a,b,c,d) and kind (semi, sym):
  * W(N,k) triangle, row sums (number of valid weak orders),
  * alternating sums  chi(N) = sum_k (-1)^(N-k) W(N,k)   (= (-1)^N A_N(-1)),
  * A_N(q) = sum_k W(N,k) C(q,k): values at q = -1, -2, 2, 3; factorisation over Q,
  * columns k = 2, 3 and diagonals W(N,N-1), W(N,N-2),
  * h-vector of the f-vector (f_{k-2} = W(N,k), simplicial convention, for d) .
"""
import sys, os
from math import comb
from fractions import Fraction
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))


def load(files=None):
    if not files:
        files = ['W_small.txt', 'W_19_22.txt', 'W_d_19_20.txt']
    W = {}
    for fn in files:
        p = os.path.join(HERE, fn)
        if not os.path.exists(p):
            continue
        for line in open(p):
            f = line.split()
            if len(f) < 4 or not f[0].isdigit():
                continue
            N, conv, kind = int(f[0]), f[1], f[2]
            row = [int(x) for x in f[3:]]
            if len(row) != N:
                continue
            W.setdefault((conv, kind), {})[N] = [0] + row     # row[k], k = 1..N
    return W


def binom_q(q, k):
    """C(q,k) for any integer q."""
    num = 1
    for i in range(k):
        num *= (q - i)
    f = 1
    for i in range(1, k + 1):
        f *= i
    return Fraction(num, f)


def A_val(row, q):
    v = sum(row[k] * binom_q(q, k) for k in range(1, len(row)))
    assert v.denominator == 1
    return int(v)


def A_poly(row):
    q = sp.symbols('q')
    return sp.expand(sum(row[k] * sp.binomial(q, k).expand(func=True) for k in range(1, len(row))))


def hvec(row):
    """h-vector of the simplicial complex with f_{k-2} = row[k] (k = 1..N), dimension N-2."""
    N = len(row) - 1
    d = N - 1                      # number of vertices in a facet
    f = [row[k] for k in range(1, N + 1)]          # f_{-1}, f_0, ..., f_{d-1}
    h = []
    for j in range(d + 1):
        h.append(sum((-1) ** (j - i) * comb(d - i, j - i) * f[i] for i in range(j + 1)))
    return h


def main():
    W = load(sys.argv[1:])
    for key in sorted(W):
        conv, kind = key
        T = W[key]
        print('=' * 100)
        print('convention (%s), %s' % (conv, kind))
        print('=' * 100)
        Ns = sorted(T)
        print('row sums            :', [sum(T[N]) for N in Ns])
        print('chi = sum (-1)^(N-k) W :', [sum((-1) ** (N - k) * T[N][k] for k in range(1, N + 1)) for N in Ns])
        print('A_N(-2)*(-1)^N      :', [(-1) ** N * A_val(T[N], -2) for N in Ns])
        print('A_N(-3)*(-1)^N      :', [(-1) ** N * A_val(T[N], -3) for N in Ns])
        print('A_N(2)              :', [A_val(T[N], 2) for N in Ns])
        print('A_N(3)              :', [A_val(T[N], 3) for N in Ns])
        for k in (1, 2, 3, 4):
            print('column k=%d          :' % k, [T[N][k] for N in Ns if N >= k])
        for j in (0, 1, 2, 3):
            print('diagonal W(N,N-%d)   :' % j, [T[N][N - j] for N in Ns if N - j >= 1])
        print('W(N,N-1)/a(N) :', ['%.4f' % (T[N][N - 1] / T[N][N]) for N in Ns if N >= 2])
        if conv == 'd':
            print('h-vectors:')
            for N in Ns:
                if N <= 12:
                    print('  N=%2d' % N, hvec(T[N]))
        print('A_N(q) factorisations (N <= 10):')
        q = sp.symbols('q')
        for N in Ns:
            if N <= 10:
                print('  N=%2d' % N, sp.factor(A_poly(T[N])))
        print()


if __name__ == '__main__':
    main()
