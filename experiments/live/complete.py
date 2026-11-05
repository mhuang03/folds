"""complete.py N p1 p2 ... : print some completions of the prefix (DFS, candidates in a
preference order: optionally prefer the class of p[-1], etc.).  Prints up to K completions."""
import sys
from functools import lru_cache

N = int(sys.argv[1])
pre = [int(x) for x in sys.argv[2:]]
K = 5


def ok(S, m):
    r = min(m - 1, N - m)
    return sum(1 for d in range(1, r + 1) if (m - d) in S) == \
        sum(1 for d in range(1, r + 1) if (m + d) in S)


@lru_cache(None)
def live(S):
    if len(S) == N:
        return True
    return any(live(S | {m}) for m in range(1, N + 1) if m not in S and ok(S, m))


out = []


def dfs(seq):
    if len(out) >= K:
        return
    S = frozenset(seq)
    if len(seq) == N:
        out.append(list(seq))
        return
    for m in range(1, N + 1):
        if m not in S and ok(S, m) and live(S | {m}):
            dfs(seq + [m])
            if len(out) >= K:
                return


dfs(pre)
for a in out:
    print(" ".join(map(str, a)))
