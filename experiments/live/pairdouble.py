"""pairdouble.py n: for every valid n-world sequence b, is the 'pair doubling'
D(b) = (2b1, 2b1-1, 2b2, 2b2-1, ...) valid in the 2n-world?  (Seen in completions of [2,1].)
Also the variant with the order inside a pair chosen per pair (search)."""
import sys

n = int(sys.argv[1])
N = 2 * n


def okstep(M, S, m):
    r = min(m - 1, M - m)
    return sum(1 for d in range(1, r + 1) if (m - d) in S) == \
        sum(1 for d in range(1, r + 1) if (m + d) in S)


def valid(M, a):
    S = set()
    for m in a:
        if not okstep(M, S, m):
            return False
        S.add(m)
    return True


def seqs(M):
    out = []

    def dfs(a, S):
        if len(a) == M:
            out.append(tuple(a))
            return
        for m in range(1, M + 1):
            if m not in S and okstep(M, S, m):
                S.add(m)
                a.append(m)
                dfs(a, S)
                a.pop()
                S.remove(m)
    dfs([], set())
    return out


B = seqs(n)
good = 0
anyorder = 0
for b in B:
    d = [x for k in b for x in (2 * k, 2 * k - 1)]
    if valid(N, d):
        good += 1
    # per-pair orientation: greedy DFS
    def rec(i, S, acc):
        if i == n:
            return True
        k = b[i]
        for o in ((2 * k, 2 * k - 1), (2 * k - 1, 2 * k)):
            if okstep(N, S, o[0]) and okstep(N, S | {o[0]}, o[1]):
                if rec(i + 1, S | set(o), acc):
                    return True
        return False
    if rec(0, frozenset(), []):
        anyorder += 1
print(n, len(B), "D(b) valid:", good, "some orientation valid:", anyorder)
