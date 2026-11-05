"""Parity-block structure (DEGS-type construction) and end-parity statistics.

block(N) = #valid sequences whose first floor/ceil(N/2) elements are exactly the evens or the odds
         = sum over S in {evens, odds} of g(S) g(S^c).
B(N)     = fully recursive parity-block count: B(1)=1, B(2n)=2B(n)^2, B(2n+1)=2B(n)B(n+1)
           (lower bound from iterating the construction).
ends     = fraction of valid sequences whose first and last panels have equal parity."""
import sys
from functools import lru_cache
import numpy as np
from common import *

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20

@lru_cache(None)
def B(n):
    if n <= 1: return 1
    h = n // 2
    return 2 * B(h) ** 2 if n % 2 == 0 else 2 * B(h) * B(h + 1)

def ends_stats(N):
    """returns (#sequences with first,last of equal parity, total) via DP from each start."""
    full = (1 << N) - 1
    ok = [[False] * N for _ in range(1 << N)]
    same = 0
    for x in range(1, N + 1):
        c = {1 << (x - 1): 1}
        for _ in range(N - 2):
            nc = {}
            for S, v in c.items():
                for m in range(1, N + 1):
                    b = 1 << (m - 1)
                    if not S & b and step_ok(S, m, N):
                        nc[S | b] = nc.get(S | b, 0) + v
            c = nc
        for S, v in c.items():
            y = (full ^ S).bit_length()
            if (x - y) % 2 == 0: same += v
    return same

print("N a(N) block(N) block/a  B(N) B/a  [ends same parity fraction]")
for N in range(2, NMAX + 1):
    g = g_array(N); full = (1 << N) - 1
    ev = sum(1 << (m - 1) for m in range(2, N + 1, 2))
    od = full ^ ev
    blk = int(g[ev]) * int(g[od]) + int(g[od]) * int(g[ev])
    # check g(evens) and g(odds) against a(.)
    assert int(g[ev]) == A[N // 2 - 1] and int(g[od]) == A[(N + 1) // 2 - 1]
    line = f"{N} {A[N-1]} {blk} {blk/A[N-1]:.4g} {B(N)} {B(N)/A[N-1]:.3g}"
    if N <= 12:
        line += f"  ends-same={ends_stats(N)/A[N-1]:.4f}"
    print(line)
