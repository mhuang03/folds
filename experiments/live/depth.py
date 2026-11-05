"""depth.py N a b c ...: maximum number of further valid steps after the prefix, and the
reachable sets at each level (sizes)."""
import sys

N = int(sys.argv[1])
pre = [int(x) for x in sys.argv[2:]]


def ok(S, m):
    r = min(m - 1, N - m)
    return sum(1 for d in range(1, r + 1) if (m - d) in S) == \
        sum(1 for d in range(1, r + 1) if (m + d) in S)


level = {frozenset(pre)}
k = len(pre)
while level:
    print(k, len(level), sorted(sorted(s) for s in level)[:6] if len(level) < 8 else "")
    nxt = set()
    for S in level:
        for m in range(1, N + 1):
            if m not in S and ok(S, m):
                nxt.add(S | {m})
    level = nxt
    k += 1
