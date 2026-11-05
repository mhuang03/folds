"""The 'near' greedy: repeatedly place the valid panel closest to the centre c of the removed
pair (ties: smaller panel first).  Test for adjacent pairs, larger N; print sequences."""
import sys


def arms(N, m):
    r = min(m - 1, N - m)
    return range(m - r, m), range(m + 1, m + r + 1)


def greedy(N, D, c2, tie=1):
    """c2 = 2 * centre.  Returns the sequence or None."""
    S = set()
    seq = []
    T = [m for m in range(1, N + 1) if m not in D]
    while len(seq) < len(T):
        best = None
        for m in T:
            if m in S:
                continue
            L, R = arms(N, m)
            if sum(x in S for x in L) == sum(x in S for x in R):
                k = (abs(2 * m - c2), tie * m)
                if best is None or k < best[0]:
                    best = (k, m)
        if best is None:
            return None
        S.add(best[1])
        seq.append(best[1])
    return seq


if __name__ == '__main__':
    NMAX = int(sys.argv[1])
    show = len(sys.argv) > 2
    for tie in (1, -1):
        bad = []
        for N in range(2, NMAX + 1):
            for r in range(1, N):
                s = greedy(N, {r, r + 1}, 2 * r + 1, tie)
                if s is None:
                    bad.append((N, r))
                elif show and N == NMAX:
                    print(r, s)
        print('tie', tie, 'failures:', bad[:20], len(bad))
