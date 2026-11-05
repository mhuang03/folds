"""Greedy heuristics (no lookahead) for ordering [N] \\ {r, r+1}: which ones never get stuck?"""
import sys


def arms(N, m):
    r = min(m - 1, N - m)
    return range(m - r, m), range(m + 1, m + r + 1)


def run(N, D, key):
    S = set()
    T = [m for m in range(1, N + 1) if m not in D]
    while len(S) < len(T):
        cands = []
        for m in T:
            if m in S:
                continue
            L, R = arms(N, m)
            if sum(x in S for x in L) == sum(x in S for x in R):
                cands.append(m)
        if not cands:
            return False
        S.add(min(cands, key=lambda m: key(N, D, m, S)))
    return True


def reach(N, m):
    return min(m - 1, N - m)


H = {
    'maxreach': lambda N, D, m, S: (-reach(N, m), m),
    'minreach': lambda N, D, m, S: (reach(N, m), m),
    'maxm': lambda N, D, m, S: -m,
    'minm': lambda N, D, m, S: m,
    'far': lambda N, D, m, S: (-abs(m - min(D) - 0.5), m),
    'near': lambda N, D, m, S: (abs(m - min(D) - 0.5), m),
}
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 22
for name, key in H.items():
    fails = 0
    tot = 0
    for N in range(4, NMAX + 1):
        for r in range(1, N):
            tot += 1
            if not run(N, {r, r + 1}, key):
                fails += 1
    print(name, fails, 'of', tot)
