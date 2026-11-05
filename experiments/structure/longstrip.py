"""Orderings of the prefix [1..n] inside a long strip (N >= 2n-1): all windows anchored at 1."""
import sys
from common import step_ok

def orderings(n, N):
    res = []
    def rec(S, seq):
        if len(seq) == n:
            res.append(tuple(seq)); return
        for m in range(1, n + 1):
            b = 1 << (m - 1)
            if not S & b and step_ok(S, m, N):
                seq.append(m); rec(S | b, seq); seq.pop()
    rec(0, [])
    return res

for n in range(1, int(sys.argv[1]) + 1):
    o = orderings(n, 2 * n - 1)
    print(n, len(o), o[:12])
