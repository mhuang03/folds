"""insert.py N: for every valid sequence b of the (N-1)-world, count the positions where panel
N can be inserted (b unchanged otherwise) to give a valid N-sequence; same for inserting
panel 1 into b shifted by +1.  Prints how many b admit no insertion."""
import sys
from itertools import permutations

N = int(sys.argv[1])


def valid(n, a):
    S = set()
    for m in a:
        r = min(m - 1, n - m)
        if sum(1 for d in range(1, r + 1) if (m - d) in S) != \
                sum(1 for d in range(1, r + 1) if (m + d) in S):
            return False
        S.add(m)
    return True


def seqs(n):
    out = []

    def dfs(a, S):
        if len(a) == n:
            out.append(tuple(a))
            return
        for m in range(1, n + 1):
            if m in S:
                continue
            r = min(m - 1, n - m)
            if sum(1 for d in range(1, r + 1) if (m - d) in S) == \
                    sum(1 for d in range(1, r + 1) if (m + d) in S):
                S.add(m)
                a.append(m)
                dfs(a, S)
                a.pop()
                S.remove(m)
    dfs([], set())
    return out


B = seqs(N - 1)
noN = no1 = none = 0
for b in B:
    insN = [i for i in range(N) if valid(N, b[:i] + (N,) + b[i:])]
    bs = tuple(x + 1 for x in b)
    ins1 = [i for i in range(N) if valid(N, bs[:i] + (1,) + bs[i:])]
    noN += not insN
    no1 += not ins1
    none += not insN and not ins1
print(N, len(B), "noN", noN, "no1", no1, "neither", none)
