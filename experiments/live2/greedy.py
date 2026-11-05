"""greedy.py N1 N2: can the complement Y of each Beatty copy be ordered from scratch by a simple
greedy rule (always place the valid element of Y minimising a key)?  Reports failures per rule."""
import sys
from lib import valid_step


def beatty_copies(N):
    seen = set()
    for p in range(1, N):
        for g in range(2 * p - 1 - N, 1):
            X = tuple((r * N + g) // p for r in range(1, p + 1))
            if X not in seen:
                seen.add(X)
                yield p, g, X


def greedy(N, Y, key):
    S = set()
    rest = set(Y)
    while rest:
        c = [m for m in rest if valid_step(N, S, m)]
        if not c:
            return False
        m = min(c, key=key)
        S.add(m)
        rest.remove(m)
    return True


RULES = {
    'small': lambda N: (lambda m: m),
    'large': lambda N: (lambda m: -m),
    'outer': lambda N: (lambda m: min(m - 1, N - m) * 2 + (m > N / 2)),
    'inner': lambda N: (lambda m: -min(m - 1, N - m) * 2 + (m > N / 2)),
}

for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    fails = {k: 0 for k in RULES}
    tot = 0
    for p, g, X in beatty_copies(N):
        Y = set(range(1, N + 1)) - set(X)
        tot += 1
        for k, f in RULES.items():
            if not greedy(N, Y, f(N)):
                fails[k] += 1
    print(N, tot, fails)
