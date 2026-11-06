"""constants.py -- the exponential constants c in a(N) <= N! exp(-(c + o(1)) N) given by the
level bounds
    k odd, N even:  V <= N/2                      (Growth.lean, card_moves_odd_le)
    k odd, N odd :  V <= (N+1)/2 + floor(k/2)     (Upper.lean, card_moves_odd_odd_le)
    k even, v2(k) = a >= 1:  V <= (a+1) N/(a+2)   (this directory; a = 1 is in Folds/MaxMoves.lean)
Each level class contributes  density * int_0^{x*} ln((1-x)/b(x)) dx  where b(x) N is the bound.
Also prints  ln(N!/prod) / N  for finite N as a check."""
import math
from scipy.integrate import quad

def cls(dens, b, xmax):
    return dens * quad(lambda x: math.log((1 - x) / b(x)), 0, xmax)[0]

odd_even = cls(0.5, lambda x: 0.5, 0.5)
odd_odd = cls(0.5, lambda x: (1 + x) / 2, 1 / 3)
terms = []
for a in range(1, 40):
    c = (a + 1) / (a + 2)
    terms.append(cls(2.0 ** (-a - 1), lambda x, c=c: c, 1 - c))
print("odd k, even N : %.6f" % odd_even)
print("odd k, odd N  : %.6f" % odd_odd)
print("k = 2 mod 4   : %.6f" % terms[0])
print("all a >= 2    : %.6f" % sum(terms[1:]))
print("even N: old %.6f  with a=1 %.6f  with all a %.6f" % (odd_even, odd_even + terms[0], odd_even + sum(terms)))
print("odd  N: old %.6f  with a=1 %.6f  with all a %.6f" % (odd_odd, odd_odd + terms[0], odd_odd + sum(terms)))

def v2(k):
    a = 0
    while k % 2 == 0:
        k //= 2; a += 1
    return a

def deficit(N, alla):
    L = 0.0
    for i in range(N):
        f = N - i
        if i % 2 == 1:
            b = N // 2 if N % 2 == 0 else (N + 1) // 2 + i // 2
        elif i > 0 and (v2(i) == 1 or (alla and v2(i) >= 1)):
            a = v2(i)
            b = (a + 1) * N // (a + 2)
        else:
            b = f
        L += math.log(f / min(f, b))
    return L / N

for N in (100, 101, 1000, 1001, 10000, 10001, 100000, 100001):
    print(N, "a=1: %.5f  all a: %.5f" % (deficit(N, False), deficit(N, True)))
