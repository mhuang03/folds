"""Neutral sets (balanced around every panel) for N up to NMAX, via the doubling form.

X is neutral  <=>  y_{2k} = y_k for all k in Z/N, where y_k = x_k + x_{k+1}
(x = indicator of X, indices mod N in [1, N]).  So y is constant on the weakly connected
components of k -> 2k (mod N).  We enumerate y in {0,1,2}^components, rebuild x, and
compare with the conjectured list
    {evens, odds} ∪ {E_d, E_d^c : d | N, d odd, 3 <= d < N},
    E_d = {x : x mod d in {2, 4, ..., d-1}}.
For N <= BRUTE also checks the doubling form against the definition by brute force.
usage: python3 neutral.py NMAX [BRUTE]"""
import sys
from itertools import product


def balanced_everywhere(N, X):
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        l = sum(1 for d in range(1, r + 1) if m - d in X)
        rr = sum(1 for d in range(1, r + 1) if m + d in X)
        if l != rr:
            return False
    return True


def components(N):
    par = list(range(N))

    def find(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a

    for k in range(N):
        a, b = find(k), find((2 * k) % N)
        if a != b:
            par[a] = b
    comp = {}
    for k in range(N):
        comp.setdefault(find(k), []).append(k)
    return list(comp.values())


def neutral_sets(N):
    comps = components(N)
    out = set()
    for vals in product(range(3), repeat=len(comps)):
        y = [0] * N
        for c, v in zip(comps, vals):
            for k in c:
                y[k] = v
        # x index i in 1..N stored at i % N; y_k = x_k + x_{k+1}
        for x1 in (0, 1):
            x = {1: x1}
            ok = True
            for k in range(1, N):
                v = y[k % N] - x[k]
                if v not in (0, 1):
                    ok = False
                    break
                x[k + 1] = v
            if ok and x[N] + x[1] == y[0]:
                out.add(frozenset(i for i in range(1, N + 1) if x[i]))
    return out


def conjectured(N):
    full = frozenset(range(1, N + 1))
    s = {frozenset(), full}
    ev = frozenset(range(2, N + 1, 2))
    s |= {ev, full - ev}
    for d in range(3, N, 2):
        if N % d == 0:
            E = frozenset(x for x in range(1, N + 1) if (x % d) % 2 == 0 and x % d != 0)
            s |= {E, full - E}
    return s


if __name__ == "__main__":
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    BRUTE = int(sys.argv[2]) if len(sys.argv) > 2 else 14
    bad = 0
    for N in range(1, NMAX + 1):
        ns = neutral_sets(N)
        if N <= BRUTE:
            bf = set()
            for mask in range(1 << N):
                X = frozenset(i + 1 for i in range(N) if mask >> i & 1)
                if balanced_everywhere(N, X):
                    bf.add(X)
            assert bf == ns, N
        ok = ns == conjectured(N)
        bad += not ok
        print(N, len(ns) - 2, "components", len(components(N)), "OK" if ok else "MISMATCH")
        if not ok:
            for X in sorted(ns ^ conjectured(N), key=len):
                print("   ", sorted(X))
    print("mismatches:", bad)
