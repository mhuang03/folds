"""beatty_cover.py N1 N2: which reachable 2-sets {u,v} lie in a Beatty window copy
X(N,p,g) = {floor((rN+g)/p)} (1 <= p < N, -N < g <= 0) with preimage pair live in the
p-world (assuming the 2-prefix conjecture there: dead iff {1,p} with p even >= 4, or p = 7)?
Copy test by the doubling criterion  c~(2x-1) = 2c(x)-1  for x in X (checked against
splits.is_copy for small N)."""
import sys


def copy_crit(N, X):
    S = set(X)
    c = [0] * (N + 1)
    for y in range(1, N + 1):
        c[y] = c[y - 1] + (y in S)
    p = len(X)

    def ct(y):
        if y <= 0:
            return 0
        if y <= N:
            return c[y]
        return p + c[y - N]
    return all(ct(2 * x - 1) == 2 * c[x] - 1 for x in X)


def dead_pair(p, a, b):
    return {a, b} == {1, p} and ((p % 2 == 0 and p >= 4) or p == 7)


def run(N, check=False):
    pairs = {}
    for p in range(2, N):
        seen = set()
        for g in range(-N + 1, 1):
            X = tuple((r * N + g) // p for r in range(1, p + 1))
            if X in seen or X[0] < 1 or len(set(X)) < p:
                continue
            seen.add(X)
            cc = copy_crit(N, X)
            if check:
                from splits import is_copy
                assert cc == is_copy(N, X), (N, X)
            if not cc:
                continue
            for i in range(p):
                for j in range(i + 1, p):
                    if not dead_pair(p, i + 1, j + 1):
                        pairs.setdefault((X[i], X[j]), (p, g))
                        if MIRROR:
                            pairs.setdefault((N + 1 - X[j], N + 1 - X[i]), (p, g, 'm'))
    missing = []
    for u in range(1, N + 1):
        for v in range(u + 1, N + 1):
            reach = (2 * v >= N + u + 1) or (2 * u <= v)
            dead = (u, v) == (1, N) and (N % 2 == 0 or N == 7)
            if PARITY and (u - v) % 2 == 0:
                c = u % 2
                n1 = (N + c) // 2
                if not dead_pair(n1, (u + c) // 2, (v + c) // 2):
                    continue
            if reach and not dead and (u, v) not in pairs:
                missing.append((u, v))
    return missing


if __name__ == "__main__":
    chk = 'check' in sys.argv[3:]
    MIRROR = 'mirror' in sys.argv[3:]
    PARITY = 'parity' in sys.argv[3:]
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        m = run(N, chk)
        print(N, len(m), m[:40])
