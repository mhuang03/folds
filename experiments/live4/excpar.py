"""excpar.py q Nmax: exceptional class C_1 (N = 1 mod q, q odd) and parity.
For Y = [N] - C_1 test whether Y has a valid ordering from scratch of the form
  (a) all of E - C_1 first (any order), then O - C_1   ('evens first')
  (b) all of O - C_1 first, then E - C_1               ('odds first')
(memoised DFS on subsets; the first phase is checked to be completable too)."""
import sys

sys.setrecursionlimit(100000)


def test(N, q, first):
    C = {x for x in range(1, N + 1) if x % q == 1 % q}
    Y = [x for x in range(1, N + 1) if x not in C]
    A = [x for x in Y if x % 2 == first]
    B = [x for x in Y if x % 2 != first]
    order = A + B
    idx = {x: i for i, x in enumerate(order)}
    arms = []
    for m in order:
        r = min(m - 1, N - m)
        L = sum(1 << idx[x] for x in range(m - r, m) if x in idx)
        R = sum(1 << idx[x] for x in range(m + 1, m + r + 1) if x in idx)
        arms.append((L, R))
    na = len(A)
    fullA = (1 << na) - 1
    full = (1 << len(order)) - 1
    seen = set()

    def go(S):
        if S == full:
            return True
        if S in seen:
            return False
        seen.add(S)
        lo, hi = (0, na) if (S & fullA) != fullA else (na, len(order))
        for i in range(lo, hi):
            if not S >> i & 1:
                L, R = arms[i]
                if bin(S & L).count('1') == bin(S & R).count('1') and go(S | 1 << i):
                    return True
        return False

    return go(0)


q, Nmax = int(sys.argv[1]), int(sys.argv[2])
for N in range(2 * q + 1, Nmax + 1):
    if N % q != 1:
        continue
    print(q, N, 'evens first', test(N, q, 0), 'odds first', test(N, q, 1), flush=True)
