# Chain invariant search for {1, 2, c}.
# State: B with 1, 2 in B, B n [3, a) empty, a in B, B n (a, 2a-1] = {b, w}, a <= (N+1)/2,
# every t outside B with t > a has R <= L.  A chain step m < a needs b <= 2m - 1 < w.
import sys
from functools import lru_cache
from base import *

def term(a, b, w):
    return all(sum(1 for x in (a, b, w) if t < x <= 2 * t - 1) <= 2 for t in range(3, a))

@lru_cache(None)
def good(a, b, w):
    if term(a, b, w): return True
    for m in range(max(3, (b + 2) // 2), min(w // 2, a - 1) + 1):
        if 2 * m - 1 >= b and 2 * m - 1 < w and good(m, a, b): return True
    return False

def start_ok(N, B):
    rest = sorted(x for x in B if x > 2)
    if 1 not in B or 2 not in B or not rest: return None
    a = rest[0]
    if 2 * a > N + 1: return None
    up = [x for x in rest if a < x <= 2 * a - 1]
    if len(up) != 2: return None
    b, w = up
    for t in range(a + 1, N + 1):
        if t not in B and R(N, B, t) > L(N, B, t): return None
    if not good(a, b, w): return None
    return (a, b, w)

def search(N, c, depth):
    B0 = {1, 2, c}
    frontier = [((), frozenset(B0))]
    for d in range(depth + 1):
        for (ms, B) in frontier:
            s = start_ok(N, set(B))
            if s: return ms, s
        if d == depth: break
        nf = []
        for (ms, B) in frontier:
            for m in range(3, N + 1):
                if valid(N, B, m): nf.append((ms + (m,), B | {m}))
        frontier = nf
    return None

if __name__ == '__main__':
    N0, N1, dep = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    for N in range(N0, N1 + 1):
        bad = []
        out = []
        for c in cs12(N):
            r = search(N, c, dep)
            if r is None: bad.append(c)
            else: out.append((c, r))
        print(N, 'fail:', bad)
        if len(sys.argv) > 4:
            for c, r in out: print('  ', c, r)
