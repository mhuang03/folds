"""Look for arithmetic effects (2-adic structure of N, order of 2 mod N) in the residual
log(a(N)/a_W(N)) after removing a smooth fit, separately for each parity."""
import math
import numpy as np
from fractions import Fraction
from math import factorial
from common import A

def p(r):
    return Fraction(4 ** r * factorial(r) ** 2, factorial(2 * r + 1))

def aW(N):
    w = Fraction(factorial(N))
    for m in range(1, N + 1): w *= p(min(m - 1, N - m))
    return w

Ns = list(range(1, len(A) + 1))
y = np.array([math.log(A[n - 1] / float(aW(n))) for n in Ns]); Ns = np.array(Ns)
def ord2(n):
    if n % 2 == 0: return None
    if n == 1: return 1
    k, x = 1, 2 % n
    while x != 1: x = x * 2 % n; k += 1
    return k
for par in (0, 1):
    m = (Ns >= 6) & (Ns % 2 == par)
    X = np.stack([Ns ** 2 / 100., Ns, np.ones(len(Ns))], 1)[m]
    c, *_ = np.linalg.lstsq(X, y[m], rcond=None)
    res = y[m] - X @ c
    print("parity", par, "fit coeffs", np.round(c, 4))
    for n, r in zip(Ns[m].tolist(), res):
        v2 = (n & -n).bit_length() - 1
        print(f"  N={n:2d} resid={r:+.3f}  v2(N)={v2} v2(N+1)={((n+1)&-(n+1)).bit_length()-1} v2(N-1)={((n-1)&-(n-1)).bit_length()-1} ord2={ord2(n)}")
