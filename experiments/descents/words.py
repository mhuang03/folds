"""Static word formulation.  A word rho in [k]^N is valid iff for every m
   #{1<=d<=r_m : rho(m-d) <= rho(m)} == #{1<=d<=r_m : rho(m+d) < rho(m)},
i.e. the order by (rho, position) is a valid fold sequence with <= k ascending runs.
Enumerate valid words (DFS, left-half constraints checked as soon as possible) and test
candidate projections rho' on N' = floor((N-1)/2) with labels in [k-1]."""
import sys, itertools
from collections import Counter
def ok_at(rho, m, N):
    r = min(m - 1, N - m); v = rho[m]
    return sum(rho[m-d] <= v for d in range(1, r+1)) == sum(rho[m+d] < v for d in range(1, r+1))
def valid_word(rho, N):
    return all(ok_at(rho, m, N) for m in range(1, N + 1))
def words(N, k):
    rho = [0] * (N + 1)
    def rec(p):
        if p > N:
            if all(ok_at(rho, m, N) for m in range(1, N + 1) if 2*m - 1 > N): yield list(rho)
            return
        for v in range(1, k + 1):
            rho[p] = v
            # left-half m with 2m-1 == p (window [1, p]) can be checked now
            if p % 2 == 1:
                m = (p + 1) // 2
                if 2*m - 1 <= N and m <= N - m + 1 and not ok_at(rho, m, N) and min(m-1, N-m) == m - 1:
                    continue
            yield from rec(p + 1)
    yield from rec(1)
projs = {
    'min': lambda a, b: min(a, b),
    'max-1': lambda a, b: max(a, b) - 1,
    'even-1': lambda a, b: a - 1,
    'odd': lambda a, b: b,
    'avgdown': lambda a, b: (a + b - 1) // 2,
    'avgup': lambda a, b: (a + b) // 2,
}
if __name__ == '__main__':
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        k = (N + 1).bit_length() - 1
        W = list(words(N, k)); Np = (N - 1) // 2
        c = Counter()
        for rho in W:
            for name, f in projs.items():
                rp = [0] + [f(rho[2*y], rho[2*y+1]) for y in range(1, Np + 1)]
                good = all(1 <= v <= k - 1 for v in rp[1:]) and valid_word(rp, Np)
                c[name] += good
        print(N, 'k', k, 'valid words', len(W), dict(c), flush=True)
