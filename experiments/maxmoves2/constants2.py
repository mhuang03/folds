"""constants2.py -- the constants c in a(N) <= N! exp(-(c + o(1)) N) given by the Lean products
semiCount_even_le_prod_two_adic / semiCount_odd_le_prod_two_adic (Folds/MaxMoves2.lean):
    i odd, N = 2h even:  B_i = min(N - i, h)
    i odd, N = 2h+1 odd: B_i = min(N - i, h + 1 + floor(i/2))
    i even, i >= 2:      B_i = min(N - i, floor((a+1) N / (a+2))),  a = v2(i)
    i = 0:               B_0 = N.
Limit: each level class contributes density * int_0^{x*} ln((1-x)/b(x)) dx (b(x) N = bound).
Also prints ln(N!/prod B_i)/N for finite N, computed from exactly these B_i.
Second version (semiCount_*_le_prod_two_adic_size): at even i >= 2,
    B_i = min(N - i, floor((2(a+1) N + a - 2(a-1) i) / (2(a+2)))),  i.e. b(x) = ((a+1) - (a-1) x)/(a+2),
which meets 1 - x at x* = 1/3 for every a."""
import math
from scipy.integrate import quad

def cls(dens, b, xmax):
    return dens * quad(lambda x: math.log((1 - x) / b(x)), 0, xmax)[0]

odd_even = cls(0.5, lambda x: 0.5, 0.5)
odd_odd = cls(0.5, lambda x: (1 + x) / 2, 1 / 3)
lev = [cls(2.0 ** (-a - 1), lambda x, c=(a + 1) / (a + 2): c, 1 / (a + 2)) for a in range(1, 60)]
print("odd i, even N           : %.6f" % odd_even)
print("odd i, odd N            : %.6f" % odd_odd)
for a in range(1, 6):
    print("v2(i) = %d               : %.6f" % (a, lev[a - 1]))
print("all even levels         : %.6f" % sum(lev))
print("LIMIT even N: %.6f   odd N: %.6f" % (odd_even + sum(lev), odd_odd + sum(lev)))
levs = [cls(2.0 ** (-a - 1), lambda x, a=a: ((a + 1) - (a - 1) * x) / (a + 2), 1 / 3)
        for a in range(1, 60)]
print("size version:")
for a in range(1, 6):
    print("v2(i) = %d               : %.6f" % (a, levs[a - 1]))
print("all even levels         : %.6f" % sum(levs))
print("LIMIT even N: %.6f   odd N: %.6f" % (odd_even + sum(levs), odd_odd + sum(levs)))

def v2(k):
    a = 0
    while k % 2 == 0:
        k //= 2; a += 1
    return a

def deficit(N, size=False):
    h = N // 2
    L = 0.0
    for i in range(N):
        f = N - i
        if i % 2 == 1:
            b = min(f, h) if N % 2 == 0 else min(f, h + 1 + i // 2)
        elif i == 0:
            b = f
        else:
            a = v2(i)
            if size:
                b = min(f, max(0, 2 * (a + 1) * N + a - 2 * (a - 1) * i) // (2 * (a + 2)))
            else:
                b = min(f, (a + 1) * N // (a + 2))
        L += math.log(f / b)
    return L / N

for N in (100, 101, 1000, 1001, 10000, 10001, 100000, 100001, 1000000, 1000001):
    print("N = %7d   ln(N!/prod B_i)/N = %.6f   size version %.6f" % (N, deficit(N), deficit(N, True)))
