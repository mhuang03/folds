"""Theorem G' (PROOFS.txt): B is co-reachable if the panels outside B can be peeled off one at
a time (W = [N] \\ B initially), each removed panel m having
    I_B(m) <= 0 and no panel of W in its left arm,  or
    I_B(m) >= 0 and no panel of W in its right arm,
where I_B(m) = #(B n L(m)) - #(B n R(m)).  (The removal order, reversed, is the priority of a
greedy whose sign invariant is kept.)  Peeling is monotone, so a greedy peel decides it.
Compare with Theorem G (centre scheme) on 2-sets."""
import sys
from covlean5 import inward


def peel(N, B):
    W = set(range(1, N + 1)) - set(B)
    I = {}
    arm = {}
    for m in W:
        r = min(m - 1, N - m)
        L, R = range(m - r, m), range(m + 1, m + r + 1)
        I[m] = sum(x in B for x in L) - sum(x in B for x in R)
        arm[m] = (L, R)
    changed = True
    while W and changed:
        changed = False
        for m in sorted(W):
            L, R = arm[m]
            if (I[m] <= 0 and not any(x in W for x in L)) or \
               (I[m] >= 0 and not any(x in W for x in R)):
                W.discard(m)
                changed = True
    return not W


def dead(N, u, v):
    return u == 1 and v == N and ((N % 2 == 0 and N >= 4) or N == 7)


if __name__ == '__main__':
    for N in map(int, sys.argv[1:]):
        tot = g = gp = 0
        miss = []
        bad = []
        for u in range(1, N + 1):
            for v in range(u + 1, N + 1):
                p = peel(N, {u, v})
                if dead(N, u, v):
                    if p:
                        bad.append((u, v))
                    continue
                tot += 1
                g += inward(N, u, v)
                gp += p
                if not p:
                    miss.append((u, v))
        print('N=%d: non-dead %d, Theorem G %d, Theorem G\' %d; missing %s; dead but peeled %s'
              % (N, tot, g, gp, miss[:10], bad))
