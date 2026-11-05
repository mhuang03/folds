"""Window-inequality words: c in [k]^N with, for every m,
    #{1<=d<=r : c(m-d) <= c(m)}  <=  #{1<=d<=r : c(m+d) < c(m)}.
(Every level labelling of a valid sequence satisfies this; see PROOFS.txt section 1.)
Enumerate them for k = lg(N+1) (the conjectured minimum) and test projections to
N' = floor((N-1)/2) (pairs {2y, 2y+1}) or N'' = floor(N/2) (pairs {2y-1, 2y}) with k-1 letters."""
import sys
from collections import Counter
def ok_at(c, m, N):
    r = min(m - 1, N - m); v = c[m]
    return sum(c[m-d] <= v for d in range(1, r+1)) <= sum(c[m+d] < v for d in range(1, r+1))
def ok(c, N): return all(ok_at(c, m, N) for m in range(1, N + 1))
def words(N, k):
    c = [0] * (N + 1)
    def rec(p):
        if p > N:
            if ok(c, N): yield list(c)
            return
        for v in range(1, k + 1):
            c[p] = v
            # every m whose whole window lies in [1, p] can be checked
            good = True
            for m in range(1, p + 1):
                r = min(m - 1, N - m)
                if m + r == p and not ok_at(c, m, N): good = False; break
            if good: yield from rec(p + 1)
    yield from rec(1)
projs = {
    'min': lambda a, b: min(a, b), 'max-1': lambda a, b: max(a, b) - 1,
    'first-1': lambda a, b: a - 1, 'second': lambda a, b: b, 'second-1': lambda a, b: b - 1,
    'first': lambda a, b: a,
}
if __name__ == '__main__':
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        k = (N + 1).bit_length() - 1
        W = list(words(N, k))
        res = Counter()
        for c in W:
            for off, Np in ((0, (N - 1) // 2), (-1, N // 2)):
                for name, f in projs.items():
                    cp = [0] + [f(c[2*y + off], c[2*y + 1 + off]) for y in range(1, Np + 1)]
                    if all(1 <= v <= k - 1 for v in cp[1:]) and ok(cp, Np):
                        res[(off, name)] += 1
        print(N, 'k', k, 'ineq words', len(W), dict(res), flush=True)
