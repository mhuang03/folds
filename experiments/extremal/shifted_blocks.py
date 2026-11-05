"""Check the shifted parity-block construction for even N = 2n.

k = 2j+1 = largest odd number <= n.
  X = {2,4,...,2j} u {2j+3, 2j+5, ..., 2n-1}      (n-1 panels), phi_X(y) = 2y + [y > j]
  Y = {1,3,...,2j+1} u {2j+2, 2j+4, ..., 2n}      (n+1 panels), phi_Y(y) = 2y - 1 - [y > j+1]
Claim: phi_X(sigma) ++ phi_Y(tau) is semi-symmetric iff sigma (on n-1) and tau (on n+1) are.
Then free(result) >= free(sigma) + 2 (panels 1 and N are in Y and have radius 0).
"""
import sys
import itertools
from fold import *


def maps(n):
    j = (n + 1) // 2 - 1 if n % 2 == 0 else (n - 1) // 2
    # largest odd k = 2j+1 <= n
    j = (n - 1) // 2 if n % 2 == 1 else (n - 2) // 2
    phX = lambda y: 2 * y + (1 if y > j else 0)
    phY = lambda y: 2 * y - 1 - (1 if y > j + 1 else 0)
    return j, phX, phY


def check(n, full=False):
    N = 2 * n
    j, phX, phY = maps(n)
    X = sorted(phX(y) for y in range(1, n))
    Y = sorted(phY(y) for y in range(1, n + 2))
    assert sorted(X + Y) == list(range(1, N + 1)), (X, Y)
    VS = enum(n - 1) if n > 1 else [[]]
    VT = enum(n + 1)
    tau0 = VT[0]
    sig0 = VS[0]
    ok = True
    # forward direction for all valid pairs (sampled when large)
    for s in VS:
        a = [phX(y) for y in s] + [phY(y) for y in tau0]
        if not is_valid(N, a):
            ok = False
            print('FAIL sigma', n, s)
            break
    for t in VT:
        a = [phX(y) for y in sig0] + [phY(y) for y in t]
        if not is_valid(N, a):
            ok = False
            print('FAIL tau', n, t)
            break
    if full:
        # converse: invalid sigma or tau gives invalid sequence
        for s in itertools.permutations(range(1, n)):
            a = [phX(y) for y in s] + [phY(y) for y in tau0]
            if is_valid(N, a) != is_valid(n - 1, list(s)):
                ok = False
                print('CONVERSE FAIL sigma', s)
                break
        for t in itertools.permutations(range(1, n + 2)):
            a = [phX(y) for y in sig0] + [phY(y) for y in t]
            if is_valid(N, a) != is_valid(n + 1, list(t)):
                ok = False
                print('CONVERSE FAIL tau', t)
                break
    return ok, X, Y


if __name__ == '__main__':
    for n in range(2, int(sys.argv[1]) + 1):
        ok, X, Y = check(n, full=(n <= 7))
        print(2 * n, ok, X, Y)
