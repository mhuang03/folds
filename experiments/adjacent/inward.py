"""The inward criterion (PROOFS.txt, Theorem G): B is co-reachable in [N] if for some c2
(twice a centre c) every panel m outside B has 2m != c2 and
    2m < c2  ->  #(B n L(m)) <= #(B n R(m)),      2m > c2  ->  #(B n L(m)) >= #(B n R(m)).
Count the 2-sets {u, v} satisfying it (some c2), against the non-dead 2-sets."""
import sys


def reach(N, m):
    return min(m - 1, N - m)


def inward_pair(N, u, v):
    """Return the set of c2 that work for B = {u, v} (u < v)."""
    good = []
    for c2 in range(2, 2 * N + 1):
        ok = True
        for m in range(1, N + 1):
            if m in (u, v):
                continue
            if 2 * m == c2:
                ok = False
                break
            r = reach(N, m)
            lc = sum(1 for x in (u, v) if m - r <= x < m)
            rc = sum(1 for x in (u, v) if m < x <= m + r)
            if 2 * m < c2 and lc > rc:
                ok = False
                break
            if 2 * m > c2 and lc < rc:
                ok = False
                break
        if ok:
            good.append(c2)
    return good


def dead(N, u, v):
    return u == 1 and v == N and ((N % 2 == 0 and N >= 4) or N == 7)


if __name__ == '__main__':
    for N in map(int, sys.argv[1:]):
        tot = cov = 0
        miss = []
        for u in range(1, N + 1):
            for v in range(u + 1, N + 1):
                if dead(N, u, v):
                    continue
                tot += 1
                if inward_pair(N, u, v):
                    cov += 1
                else:
                    miss.append((u, v))
        print('N=%d: inward pairs %d of %d non-dead; e.g. missing %s' % (N, cov, tot, miss[:12]))
