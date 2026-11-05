"""Deletion search: start from a valid sequence on N0 (popcount order of 2^K - 2 by default),
delete panels one at a time (renumbering the rest) keeping validity and des <= target.
Reports, for each size N, how many deletion-sets (as subsets of the original panels) survive."""
from common import *
from construct_bits import valid_fast
import sys
def popcount_order(N):
    return sorted(range(1, N + 1), key=lambda m: (-bin(m).count('1'), m))
def relabel(a, keep):
    idx = {p: i + 1 for i, p in enumerate(sorted(keep))}
    return [idx[p] for p in a if p in keep]
K = int(sys.argv[1]); N0 = (1 << K) - 2 + (int(sys.argv[2]) if len(sys.argv) > 2 else 0)
base = popcount_order(N0)
assert valid_fast(N0, base)
level = {frozenset(range(1, N0 + 1))}
N = N0
while N > 1:
    N -= 1; nxt = set()
    target = lg(N + 1) - 1
    for keep in level:
        for p in keep:
            k2 = keep - {p}
            if k2 in nxt: continue
            b = relabel(base, k2)
            if des(b) <= target and valid_fast(N, b): nxt.add(k2)
    print(N, 'surviving sets:', len(nxt), flush=True)
    if not nxt: break
    if N <= 20:
        ex = sorted(nxt, key=lambda s: sorted(set(range(1, N0+1)) - s))[0]
        print('   e.g. deleted', sorted(set(range(1, N0 + 1)) - ex), '->', relabel(base, ex))
    level = nxt
    if len(level) > 20000: level = set(list(level)[:20000])
