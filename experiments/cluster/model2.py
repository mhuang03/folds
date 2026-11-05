"""Second-order cluster model: a_2(N) = a_W(N) * prod_{m<m'} (1 + kappa(m,m')).
Caches exact kappas in kappa_cache.txt (N m m' num/den)."""
import sys, os, math
from fractions import Fraction
from math import factorial
from pair import kappa, radius, w

A = [1, 2, 4, 10, 28, 96, 256, 1120, 4256, 17878, 70960, 383476, 1620328, 9167908,
     47821296, 276182312, 1481994716, 10084180418, 55082188120, 398874108930,
     2505681033958, 18168130281086, 119006527671252, 979730153850974,
     6564449510287388, 55581983250573500, 413109755332919448, 3603074636066234798,
     27545080998591561856, 262878496654501774250, 2037247307316034896720,
     20222490725552617395966, 171668579369815966705184]

CF = os.path.join(os.path.dirname(os.path.abspath(__file__)), "kappa_cache.txt")
cache = {}
if os.path.exists(CF):
    for line in open(CF):
        N, m, mp, q = line.split()
        cache[(int(N), int(m), int(mp))] = Fraction(q)


def K(N, m, mp):
    """kappa with mirror symmetry and caching."""
    a, b = sorted((N + 1 - mp, N + 1 - m))
    key = min((N, m, mp), (N, a, b))
    if key not in cache:
        cache[key] = kappa(*key)
        with open(CF, "a") as f:
            f.write("%d %d %d %s\n" % (key + (cache[key],)))
    return cache[key]


def aW(N):
    v = Fraction(factorial(N))
    for m in range(1, N + 1):
        v *= w(radius(N, m))
    return v


if __name__ == "__main__":
    Nmax = int(sys.argv[1])
    print("N  y=log(a/aW)  S1=sum kappa  S2=sum log(1+kappa)  y-S2")
    for N in range(2, Nmax + 1):
        S1 = Fraction(0)
        S2 = 0.0
        for m in range(1, N + 1):
            for mp in range(m + 1, N + 1):
                k = K(N, m, mp)
                S1 += k
                S2 += math.log1p(float(k))
        y = math.log(A[N - 1] / aW(N))
        print("%2d %9.5f %9.5f %9.5f %9.5f" % (N, y, float(S1), S2, y - S2), flush=True)
