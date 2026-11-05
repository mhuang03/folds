"""Search for a slip lemma on ODD strips N = 2n+1.

Evens-first split: f_i = 2i + d_i (i in [1,n]), s_i = 2i-1-d_{i-1} (i in [1,n+1]),
d_0 = 0, D subset [1,n].  For single slips D = {k}: which tau in V_n give a valid
first block, which sigma in V_{n+1} give valid second blocks (on top of the full
first block)?  Try to characterise by one order condition 'x before y'.
"""
import sys
from itertools import permutations


def valid_step(S, m, N):
    r = min(m - 1, N - m)
    return sum(1 for d in range(1, r + 1) if m - d in S) == \
        sum(1 for d in range(1, r + 1) if m + d in S)


def valid_seq(seq, N, S0=()):
    S = set(S0)
    for m in seq:
        if not valid_step(S, m, N):
            return False
        S.add(m)
    return True


def V(n):
    out = []

    def rec(pre, S):
        if len(pre) == n:
            out.append(tuple(pre))
            return
        for m in range(1, n + 1):
            if m not in S and valid_step(S, m, n):
                S.add(m); pre.append(m)
                rec(pre, S)
                pre.pop(); S.discard(m)
    rec([], set())
    return out


def characterise(good, allseqs, size):
    """pairs (x,y) such that good(tau) <=> x before y"""
    res = []
    for x in range(1, size + 1):
        for y in range(1, size + 1):
            if x == y:
                continue
            if all((t.index(x) < t.index(y)) == (t in good) for t in allseqs):
                res.append((x, y))
    return res


def main(n):
    N = 2 * n + 1
    Vn, Vn1 = V(n), V(n + 1)
    for k in range(1, n + 1):
        d = lambda i: 1 if i == k else 0
        f = lambda i: 2 * i + d(i)
        s = lambda i: 2 * i - 1 - d(i - 1)
        goodF = set(t for t in Vn if valid_seq([f(i) for i in t], N))
        F = [f(i) for i in range(1, n + 1)]
        goodS = set(t for t in Vn1 if valid_seq([s(i) for i in t], N, F))
        cf = characterise(goodF, Vn, n) if 0 < len(goodF) < len(Vn) else len(goodF) == len(Vn)
        cs = characterise(goodS, Vn1, n + 1) if 0 < len(goodS) < len(Vn1) else len(goodS) == len(Vn1)
        print(f"N={N} k={k}: F ok {len(goodF)}/{len(Vn)} {cf} | S ok {len(goodS)}/{len(Vn1)} {cs}")


if __name__ == "__main__":
    for n in map(int, sys.argv[1:]):
        main(n)
