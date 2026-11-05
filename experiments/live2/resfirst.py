"""resfirst.py N1 N2 K: residue chains.  Every residue class C_s = {m in [N] : m = s mod k} is a
window copy (it is symmetric about each of its points inside every window).  A residue chain is
an order of the k classes in which the union of the earlier classes is balanced around every
point of each later class.  For each N and k <= K print the classes s that can come FIRST in a
residue chain (equivalently last: chains reverse)."""
import sys
from lib import arms


def first_classes(N, k):
    cls = {s: frozenset(range(s, N + 1, k)) for s in range(1, min(k, N) + 1)}
    armsN = {m: arms(N, m) for m in range(1, N + 1)}

    def bal(U, X):
        for x in X:
            L, R = armsN[x]
            if len(L & U) != len(R & U):
                return False
        return True

    memo = {}

    def completable(U, used):
        if len(used) == len(cls):
            return True
        key = used
        if key in memo:
            return memo[key]
        res = False
        for s in cls:
            if s not in used and bal(U, cls[s]) and completable(U | cls[s], used | {s}):
                res = True
                break
        memo[key] = res
        return res

    return [s for s in cls if completable(cls[s], frozenset({s}))]


if __name__ == '__main__':
    N1, N2, K = map(int, sys.argv[1:4])
    for N in range(N1, N2 + 1):
        print(N, ' '.join(f'k{k}:{"".join(map(str, first_classes(N, k))) if k < 10 else first_classes(N, k)}'
                          for k in range(2, K + 1)))
