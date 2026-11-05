"""cgsol.py k r [b]: one solution beta of the constrained problem of cgood.py, in k-strip
coordinates (V1: beta valid, V2: sigma beta valid, Prec1, Prec2), lexicographically first,
starting with b if given."""
import sys
from cgood import reach, bal_list, exc1, exc2

k, r = int(sys.argv[1]), int(sys.argv[2])
b0 = int(sys.argv[3]) if len(sys.argv) > 3 else None
sg = lambda i: (2 * r - i) % k + 1
full = (1 << k) - 1
memo = {}


def ok(S, i):
    placed = [j for j in range(1, k + 1) if S >> (j - 1) & 1]
    if not bal_list(k, placed, i):
        return False
    if not bal_list(k, [sg(j) for j in placed], sg(i)):
        return False
    if any(exc1(k, r, i, j) for j in placed):
        return False
    if any(exc2(k, r, sg(i), sg(j)) for j in placed):
        return False
    return True


def fin(S):
    if S == full:
        return []
    if S in memo:
        return memo[S]
    res = None
    for i in range(1, k + 1):
        if not S >> (i - 1) & 1 and ok(S, i):
            t = fin(S | 1 << (i - 1))
            if t is not None:
                res = [i] + t
                break
    memo[S] = res
    return res


starts = [b0] if b0 else range(1, k + 1)
for b in starts:
    if ok(0, b):
        t = fin(1 << (b - 1))
        if t is not None:
            beta = [b] + t
            print('b', b, 'beta', beta, ' sigma beta', [sg(i) for i in beta])
