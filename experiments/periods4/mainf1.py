"""mainf1.py SMAX AMAX: one free point, main structure only (u = +-1, j = 0): the ratio of its
contribution to c_1(T(N, m+1)) (x 1!) to the vertex-level main term Phi_main of Lemma 2.3."""
import sys
import cmath
import math
from fractions import Fraction as Fr
from mixedface import structure_sum
from mixed import structures


def h(x):
    return 1 / (1 - cmath.exp(-2j * math.pi * float(x)))


def phimain(s, a):
    D = 2 ** s - 1
    q = 2 ** a * D
    t = (-1) ** (s + 1) / q * h(Fr(2 ** s, q))
    for e in range(s):
        t *= h(Fr(-2 ** e, q))
    for l in range(1, a + 1):
        t *= h(Fr(-1, 2 ** l))
    return 2 * t


S, A = int(sys.argv[1]), int(sys.argv[2])
for s in range(4, S + 1):
    for a in range(2, A + 1):
        D = 2 ** s - 1
        q = 2 ** a * D
        theta = Fr(1, D)
        tot = 0
        for orb, j, z in structures(s, a, theta):
            if j == 0 and z[-1] == Fr(1, q):
                t, W = structure_sum(orb, j, z, q, 1)
                tot += 2 * t                       # mirror
        r = tot / phimain(s, a)
        print(f's={s} a={a} m={s + a + 1}: main(f=1)/Phi_main = {r.real:+.6f} {r.imag:+.6f}i', flush=True)
