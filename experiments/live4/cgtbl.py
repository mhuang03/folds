"""cgtbl.py K1 K2: the certificate table `cgTbl` of Folds/Live4.lean: for every k in [K1, K2],
every r >= 1 with 2r < k and every start b for which the constrained problem CG(k, r) of
cgood.py has a solution, one solution beta (lexicographically first), as Lean list literals
`(k, r, [beta])`.  The Lean side checks each entry by `decide`."""
import sys
from cgood import bal_list, exc1, exc2

K1, K2 = int(sys.argv[1]), int(sys.argv[2])


def solve(k, r):
    sg = lambda i: (2 * r - i) % k + 1
    full = (1 << k) - 1
    memo = {}

    def ok(S, placed, i):
        if not bal_list(k, placed, i):
            return False
        if not bal_list(k, [sg(j) for j in placed], sg(i)):
            return False
        if any(exc1(k, r, i, j) for j in placed):
            return False
        if any(exc2(k, r, sg(i), sg(j)) for j in placed):
            return False
        return True

    def fin(S, placed):
        if S == full:
            return []
        if S in memo:
            return memo[S]
        res = None
        for i in range(1, k + 1):
            if not S >> (i - 1) & 1 and ok(S, placed, i):
                t = fin(S | 1 << (i - 1), placed + [i])
                if t is not None:
                    res = [i] + t
                    break
        memo[S] = res
        return res

    out = []
    for b in range(1, k + 1):
        if ok(0, [], b):
            t = fin(1 << (b - 1), [b])
            if t is not None:
                out.append([b] + t)
    return out


entries = []
for k in range(K1, K2 + 1):
    for r in range(1, k):
        if 2 * r >= k:
            break
        for beta in solve(k, r):
            entries.append('(%d,%d,[%s])' % (k, r, ','.join(map(str, beta))))
print('[' + ',\n  '.join(entries) + ']')
