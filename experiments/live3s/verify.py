# verify.py NMAX: numerical check of the closed-form families of Live3s for N <= NMAX
#   F1: phi12 (1->1, 2->2, y->2y-1) : [p] -> [2p], every p >= 3: regular at every j != 2;
#       its image {1, 2, 5, 7, ..., 2p-1} satisfies Theorem G with centre 1/2 (c2 = 1).
#   F2: phiE (1->1, 2->2, y->2y) : [p] -> [2p+1], p odd: regular at every j not in {1, 2};
#       5 is a valid step for the image {1, 2, 6, 8, ..., 2p} and the result satisfies
#       Theorem G with centre 1/2.
import sys
from base import *
from maps import rel

def regular_except(N, p, f, exc):
    for j in range(1, p + 1):
        if j in exc: continue
        for y in range(1, p + 1):
            if y != j and rel(N, f(j), f(y)) != rel(p, j, y): return False
    return True

phi12 = lambda y: 2 if y == 2 else 2 * y - 1
phiE = lambda y: y if y <= 2 else 2 * y

NMAX = int(sys.argv[1])
bad = 0
for p in range(3, NMAX // 2 + 1):
    N = 2 * p
    img = {phi12(y) for y in range(1, p + 1)}
    ok = regular_except(N, p, phi12, {2}) and inward1(N, img)
    if not ok: print('F1 FAIL', N); bad += 1
for p in range(3, (NMAX - 1) // 2 + 1, 2):
    N = 2 * p + 1
    img = {phiE(y) for y in range(1, p + 1)}
    ok = regular_except(N, p, phiE, {1, 2}) and valid(N, img, 5) and inward1(N, img | {5})
    if not ok: print('F2 FAIL', N); bad += 1
print('checked F1, F2 up to N =', NMAX, 'failures:', bad)

# F3: N = 2p + 1, p odd: phiE with the odd panel g (7 <= g <= p - 2) moved to 2g - 1;
#     regular outside {1, 2, g}; 5 is a valid step, then Theorem G with the centre 1/2.
# F4: N = 2p: phi12 with the panel g (4 <= g <= p) moved to 2g - 2; regular outside
#     {1, 2, g}; the image satisfies Theorem G with the centre 1/2.
bad = 0
for p in range(3, (NMAX - 1) // 2 + 1, 2):
    N = 2 * p + 1
    for g in range(7, p - 1, 2):
        f = lambda y, g=g: 2 * g - 1 if y == g else phiE(y)
        img = {f(y) for y in range(1, p + 1)}
        if not (regular_except(N, p, f, {1, 2, g}) and valid(N, img, 5) and inward1(N, img | {5})):
            print('F3 FAIL', N, g); bad += 1
for p in range(4, NMAX // 2 + 1):
    N = 2 * p
    for g in range(4, p + 1):
        f = lambda y, g=g: 2 * g - 2 if y == g else phi12(y)
        img = {f(y) for y in range(1, p + 1)}
        if not (regular_except(N, p, f, {1, 2, g}) and inward1(N, img)):
            print('F4 FAIL', N, g); bad += 1
print('checked F3, F4 up to N =', NMAX, 'failures:', bad)
