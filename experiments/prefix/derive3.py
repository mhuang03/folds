"""Hand derivation of the leading coefficients of T(N,2) and T(N,3), checked with sympy,
plus a brute-force check of the discrete "dipole" formula for the number of valid 3rd steps.

Dipole picture.  For x in S and a candidate panel c != x:
  x lies in the window of c on c's RIGHT  iff  ceil((x+1)/2) <= c <= x-1      (arm A-_x)
  x lies in the window of c on c's LEFT   iff  x+1 <= c <= floor((N+x)/2)      (arm A+_x)
(x is in the window of c iff the mirror image 2c-x of x about c is still in [1,N].)
So  L(c) - R(c) = sum_{x in S} phi_x(c)  with  phi_x = +1 on A+_x, -1 on A-_x, 0 elsewhere,
and c is a valid step iff the sum vanishes.  |A-_x| = floor((x-1)/2), |A+_x| = floor((N-x)/2).
In the scaling limit (x -> N*alpha) the arms are (alpha/2, alpha) and (alpha, (1+alpha)/2):
every point "blocks" exactly half of the strip.
"""
import sympy as sp
from fractions import Fraction

al, be = sp.symbols('alpha beta', positive=True)

# ---- k = 2: b valid after a iff b not in A_a: probability exactly 1/2 for every a.
c2 = sp.integrate(1 - (al / 2 + (1 - al) / 2), (al, 0, 1))
print('c2 =', c2)

# ---- k = 3.  Z(a,b) = measure of valid c = |A-a & A-b| + |A+a & A+b| + 2|A+a & A-b| + 2|A-a & A+b|
# (because |A_a| = |A_b| = 1/2).  By the mirror symmetry it suffices to take beta < alpha/2
# and double.  For beta < alpha/2:
#    A-_b = (b/2, b) is left of A-_a = (a/2, a) and of A+_a, so only A+_b overlaps:
#    |A+_b & A-_a| = min(a, (1+b)/2) - a/2,   |A+_b & A+_a| = max(0, (1+b)/2 - a).
# => Z = (1+b)/2 if a <= (1+b)/2  (i.e. b >= 2a-1),  else Z = 1 + b - a.
# The switch line b = 2a-1 meets b = a/2 at a = 2/3: this is where the factor 3 in the
# period of T(N,3) comes from.
Z1 = (1 + be) / 2
Z2 = 1 + be - al
I = (sp.integrate(sp.integrate(Z1, (be, 0, al / 2)), (al, 0, sp.Rational(1, 2)))
     + sp.integrate(sp.integrate(Z2, (be, 0, 2 * al - 1)) + sp.integrate(Z1, (be, 2 * al - 1, al / 2)),
                    (al, sp.Rational(1, 2), sp.Rational(2, 3)))
     + sp.integrate(sp.integrate(Z2, (be, 0, al / 2)), (al, sp.Rational(2, 3), 1)))
print('c3 = 2 * I =', sp.nsimplify(2 * I))


# ---- discrete check of the Z(a,b) formula for the third step
def arms(x, N):
    return set(range((x + 2) // 2, x)), set(range(x + 1, (N + x) // 2 + 1))


def brute_T3(N):
    t = 0
    for a in range(1, N + 1):
        am, ap = arms(a, N)
        for b in range(1, N + 1):
            if b == a or b in am or b in ap:
                continue
            bm, bp = arms(b, N)
            for c in range(1, N + 1):
                if c in (a, b):
                    continue
                s = (c in ap) - (c in am) + (c in bp) - (c in bm)
                t += s == 0
    return t


def formula_T3(N):
    """sum over valid (a,b) of Z(a,b) = N-2-|A_a|-|A_b|+[a in A_b]+|same overlaps|+2|opposite overlaps|"""
    t = 0
    for a in range(1, N + 1):
        am, ap = arms(a, N)
        for b in range(1, N + 1):
            if b == a or b in am or b in ap:
                continue
            bm, bp = arms(b, N)
            t += (N - 2 - len(am) - len(ap) - len(bm) - len(bp) + (a in bm or a in bp)
                  + len(am & bm) + len(ap & bp) + 2 * len(ap & bm) + 2 * len(am & bp))
    return t


def qp(N):  # the fitted quasi-polynomial, see FINDINGS.txt
    lin = Fraction(-5, 6) if N % 2 == 0 else Fraction(-1, 3)
    c = (0 if N % 2 == 0 else Fraction(-1, 4)) + [0, Fraction(4, 9), Fraction(2, 9)][N % 3]
    return Fraction(2, 9) * N**3 - Fraction(1, 12) * N**2 + lin * N + c


for N in range(1, 31):
    assert brute_T3(N) == formula_T3(N) == qp(N), N
print('Z(a,b) formula and quasi-polynomial agree with brute force for N = 1..30')


# ---- exact discrete derivation: T(N,3) = 2*(P123 + P213 + P132) (the mirror images are
# 321, 231, 312).  Only these sign classes occur; each is the lattice-point set of one polytope.
def P213(N):   # x2 < x1 < x3, 2x2 <= x1 (x2 outside left arm), 2x3 > N+x1 (x3 outside right arm)
    return sum((a // 2) * ((N + 1 - a) // 2) for a in range(1, N + 1))


def P123(N):   # x1 < x2 < x3, 2x2 > N+x1, 2x3 > N+x2
    return sum((N - b + 1) // 2 for a in range(1, N + 1) for b in range(a + 1, N + 1) if 2 * b > N + a)


def P132(N):   # x1 < x3 < x2, 2x2 > N+x1, x3 in right arm of x1 and in left arm of x2
    t = 0
    for a in range(1, N + 1):
        for b in range(a + 1, N + 1):
            if 2 * b > N + a:
                t += max(0, (N + a) // 2 - max(a + 1, (b + 2) // 2) + 1)
    return t


for N in range(1, 41):
    assert 2 * (P123(N) + P213(N) + P132(N)) == qp(N), N
print('T(N,3) = 2*(P123+P213+P132) checked for N = 1..40')
