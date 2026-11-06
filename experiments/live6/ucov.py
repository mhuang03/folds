"""ucov.py NMAX [rules]: coverage of 2-sets by UNIFORM rules only (no residue certificates):
  base    N <= 12: every non-dead pair (Live2.coReach_base)
  inward  Theorem G for the pair: not (v >= 2u + 2 and 2v >= N + u + 3)
  one     {1, N}, N odd, N != 7
  beatty  right-aligned Beatty copies X(N, p, h), h in {0, 1}, 2p + h <= N + 1
  swap    Swap(N, p, h, c) and mirror (live6)
  dbl     doubling splits N = (2j+1) n (oddRes / evenRes)
  mirror  always
Rules given as a comma list (default all).  Prints per N the missing non-dead pairs (u <= mirror)."""
import sys


def dead(N, u, v):
    return u == 1 and v == N and ((N % 2 == 0 and N >= 4) or N == 7)


def inward(N, u, v):
    return not (v >= 2 * u + 2 and 2 * v >= N + u + 3)


def oddRes(j, y):
    return (2 * j + 1) * ((y - 1) // (j + 1)) + 2 * ((y - 1) % (j + 1)) + 1


def evenRes(j, y):
    return (2 * j + 1) * ((y - 1) // j) + 2 * ((y - 1) % j) + 2


def copies(N, rules):
    """list of (p, phi as list index 1..p)"""
    out = []
    if 'beatty' in rules:
        for p in range(2, (N + 1) // 2 + 1):
            for h in (0, 1):
                if h + 2 * p > N + 1:
                    continue
                out.append((p, [None] + [(r * N - h) // p for r in range(1, p + 1)]))
    if 'swap' in rules:
        # Swap(N, p, h, c): X(N, p, h) with its last element moved to N - c
        # (p odd, c >= 2, N + h >= 2 c p + 1), and its mirror (first element moved to c + 1)
        for p in range(3, N // 4 + 1, 2):
            for h in (0, 1):
                for c in range(2, (N + h - 1) // (2 * p) + 1):
                    X = [(r * N - h) // p for r in range(1, p + 1)]
                    X[-1] = N - c
                    out.append((p, [None] + X))
                    out.append((p, [None] + [N + 1 - x for x in reversed(X)]))
    if 'dbl' in rules:
        for d in range(3, N + 1, 2):
            if N % d:
                continue
            j, n = (d - 1) // 2, N // d
            out.append(((j + 1) * n, [None] + [oddRes(j, y) for y in range(1, (j + 1) * n + 1)]))
            out.append((j * n, [None] + [evenRes(j, y) for y in range(1, j * n + 1)]))
    return out


def run(NMAX, rules, extra=None, verbose=True):
    cov = {}
    for N in range(1, NMAX + 1):
        C = [[False] * (N + 2) for _ in range(N + 2)]

        def mark(a, b):
            if a > b:
                a, b = b, a
            C[a][b] = True
            C[N + 1 - b][N + 1 - a] = True
        for u in range(1, N + 1):
            for v in range(u + 1, N + 1):
                if dead(N, u, v):
                    continue
                if ('base' in rules and N <= 12) or ('inward' in rules and inward(N, u, v)):
                    mark(u, v)
        if 'one' in rules and N % 2 == 1 and N != 7 and N > 1:
            mark(1, N)
        for p, phi in copies(N, rules):
            Cp = cov[p]
            for a in range(1, p + 1):
                for b in range(a + 1, p + 1):
                    if Cp[a][b]:
                        mark(phi[a], phi[b])
        if extra:
            extra(N, C, cov, mark)
        cov[N] = C
        if verbose and N >= 13:
            miss = [(u, v) for u in range(1, N + 1) for v in range(u + 1, N + 1)
                    if not dead(N, u, v) and not C[u][v] and u <= N + 1 - v]
            print(N, len(miss), miss, flush=True)
    return cov


if __name__ == '__main__':
    rules = set(sys.argv[2].split(',')) if len(sys.argv) > 2 else \
        {'base', 'inward', 'one', 'beatty', 'dbl', 'swap'}
    run(int(sys.argv[1]), rules)
