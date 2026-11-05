"""Check Theorem G constructively: for every B (2-sets and intervals) satisfying the inward
criterion, run the greedy on the background B (place the valid panel closest to c), reverse
the result and verify that it is a valid ordering of [N] \\ B from scratch."""
import sys
from lib import valid_seq
from covlean5 import inward


def arms(N, m):
    r = min(m - 1, N - m)
    return range(m - r, m), range(m + 1, m + r + 1)


def centre2(N, B):
    """twice a centre for the inward criterion (or None)."""
    maxneg, minpos = 0, N + 1
    for m in range(1, N + 1):
        if m in B:
            continue
        L, R = arms(N, m)
        i = sum(x in B for x in L) - sum(x in B for x in R)
        if i < 0:
            maxneg = m
        elif i > 0 and m < minpos:
            minpos = m
    if maxneg >= minpos:
        return None
    return 2 * maxneg + 1


def bg_greedy(N, B, c2):
    S = set(B)
    out = []
    T = [m for m in range(1, N + 1) if m not in B]
    while len(out) < len(T):
        best = None
        for m in T:
            if m in S:
                continue
            L, R = arms(N, m)
            if sum(x in S for x in L) == sum(x in S for x in R):
                k = abs(2 * m - c2)
                if best is None or k < best[0]:
                    best = (k, m)
        assert best is not None, (N, B, c2, out)
        S.add(best[1])
        out.append(best[1])
    return out


NMAX = int(sys.argv[1])
n = 0
for N in range(2, NMAX + 1):
    sets = [{u, v} for u in range(1, N + 1) for v in range(u + 1, N + 1) if inward(N, u, v)]
    sets += [set(range(a, b + 1)) for a in range(1, N + 1) for b in range(a, N + 1)]
    for B in sets:
        c2 = centre2(N, B)
        assert c2 is not None, (N, B)
        seq = bg_greedy(N, B, c2)
        assert valid_seq(N, list(reversed(seq))), (N, B)
        n += 1
print('checked', n, 'sets, N <=', NMAX)
