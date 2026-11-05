"""reslast.py N1 N2 K: exceptional classes.  For k <= K not a power of 2 and N = 1 or -1 mod k
the class E = C_1 resp. C_k mod k is never first in a residue chain mod k.  Is its complement
still reachable through a residue chain mod jk (j = 2, 3) whose LAST classes are the j
subclasses of E (so the complement of E is the union of the earlier classes)?"""
import sys
from lib import arms


def chain_with_last(N, K, last):
    """Is there a residue chain mod K whose final classes are exactly the set `last`?"""
    cls = {s: frozenset(range(s, N + 1, K)) for s in range(1, min(K, N) + 1)}
    armsN = {m: arms(N, m) for m in range(1, N + 1)}

    def bal(U, X):
        for x in X:
            L, R = armsN[x]
            if len(L & U) != len(R & U):
                return False
        return True

    target = frozenset(s for s in cls if s not in last)
    memo = {}

    def rec(used, U):
        if used == target:
            return True
        if used in memo:
            return memo[used]
        res = any(rec(used | {s}, U | cls[s]) for s in target - used if bal(U, cls[s]))
        memo[used] = res
        return res

    # the classes in `last` are automatically fine once the rest is placed?  No: only the
    # union is needed to be reachable; the last classes follow in any chain order or not at
    # all (the complement of E is what we need).
    return rec(frozenset(), frozenset())


N1, N2, K = map(int, sys.argv[1:4])
for N in range(N1, N2 + 1):
    out = []
    for k in range(3, K + 1):
        if k & (k - 1) == 0:
            continue
        for s in ([1] if N % k == 1 else []) + ([k] if N % k == k - 1 else []):
            res = []
            for j in (2, 3):
                if j * k > N:
                    continue
                last = {s + i * k for i in range(j)}
                res.append(f'j{j}:{"y" if chain_with_last(N, j * k, last) else "n"}')
            out.append(f'k{k}s{s}[{",".join(res)}]')
    print(N, ' '.join(out))
