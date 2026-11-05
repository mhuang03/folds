"""Theorem G'' (PROOFS.txt): order U on the background B, with Z = [N] \\ (B u U) absent, if
the panels of U can be peeled off one at a time, each removed panel m having
    I_B(m) <= 0, I_Z(m) <= 0 and no remaining panel of U in its left arm,  or
    I_B(m) >= 0, I_Z(m) >= 0 and no remaining panel of U in its right arm.
Two-phase search for the 2-sets {u, v} that Theorem G misses: a first block A (any interval,
or the complement of an interval, avoiding D) ordered from scratch by G'' (B = {}, Z =
complement of A), then the rest on the background A (Z = D)."""
import sys
from covlean5 import inward


def peel2(N, B, U, Z):
    W = set(U)
    info = {}
    for m in W:
        r = min(m - 1, N - m)
        L, R = range(m - r, m), range(m + 1, m + r + 1)
        ib = sum(x in B for x in L) - sum(x in B for x in R)
        iz = sum(x in Z for x in L) - sum(x in Z for x in R)
        info[m] = (L, R, ib <= 0 and iz <= 0, ib >= 0 and iz >= 0)
    changed = True
    while W and changed:
        changed = False
        for m in sorted(W):
            L, R, le, ge = info[m]
            if (le and not any(x in W for x in L)) or (ge and not any(x in W for x in R)):
                W.discard(m)
                changed = True
    return not W


def dead(N, u, v):
    return u == 1 and v == N and ((N % 2 == 0 and N >= 4) or N == 7)


def two_phase(N, u, v):
    D = {u, v}
    full = set(range(1, N + 1))
    cands = []
    for p in range(1, N + 1):
        for q in range(p, N + 1):
            I = set(range(p, q + 1))
            cands.append(I - D)
            cands.append(full - I - D)
    for A in cands:
        if not A or A == full - D:
            continue
        if peel2(N, set(), A, full - A) and peel2(N, A, full - A - D, D):
            return A
    return None


if __name__ == '__main__':
    for N in map(int, sys.argv[1:]):
        miss = []
        found = 0
        for u in range(1, N + 1):
            for v in range(u + 1, N + 1):
                if dead(N, u, v) or inward(N, u, v):
                    continue
                A = two_phase(N, u, v)
                if A is None:
                    miss.append((u, v))
                else:
                    found += 1
        print('N=%d: two-phase finds %d more; still missing %d: %s' % (N, found, len(miss), miss[:20]))
