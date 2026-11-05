"""Exact pair probabilities P(C_m and C_m') for a uniformly random permutation of [1..N].

Only the relative order of the elements of U = W_m u W_m' matters.  Times are iid U(0,1).
Each element e of U other than m, m' has roles a = role in C_m (+1 left, -1 right, 0 none)
and b = role in C_m'.  If m comes first (t < t'), e is 'before t' (contributes (a,b)),
'between' (contributes (0,b)) or 'after' (nothing).  m contributes b_m to C_m'.
Discrete version: with I before, J between, K after (I+J+K = n = |U|-2), each assignment
has probability I! J! K! / (n+2)!.
"""
from fractions import Fraction
from math import factorial, comb
from collections import defaultdict


def radius(N, m):
    return min(m - 1, N - m)


def roles(N, m):
    r = radius(N, m)
    d = {}
    for k in range(1, r + 1):
        d[m - k] = 1
        d[m + k] = -1
    return d


def w(r):
    return Fraction(4 ** r * factorial(r) ** 2, factorial(2 * r + 1))


def _ordered(m, mp, rm, rmp):
    """P(C_m and C_mp and m before mp)."""
    U = (set(rm) | set(rmp)) - {m, mp}
    types = defaultdict(int)
    for e in U:
        types[(rm.get(e, 0), rmp.get(e, 0))] += 1
    n = len(U)
    b_m = rmp.get(m, 0)
    st = {(0, 0, 0, b_m): 1}   # (I, J, D1, D2) -> count
    for (a, b), c in types.items():
        new = defaultdict(int)
        for (I, J, D1, D2), v in st.items():
            for i in range(c + 1):
                ci = comb(c, i) * v
                for j in range(c - i + 1):
                    new[(I + i, J + j, D1 + a * i, D2 + b * (i + j))] += ci * comb(c - i, j)
        st = new
    tot = 0
    for (I, J, D1, D2), v in st.items():
        if D1 == 0 and D2 == 0:
            tot += v * factorial(I) * factorial(J) * factorial(n - I - J)
    return Fraction(tot, factorial(n + 2))


def pair_prob(N, m, mp):
    rm, rmp = roles(N, m), roles(N, mp)
    return _ordered(m, mp, rm, rmp) + _ordered(mp, m, rmp, rm)


def kappa(N, m, mp):
    return pair_prob(N, m, mp) / (w(radius(N, m)) * w(radius(N, mp))) - 1


if __name__ == "__main__":
    from itertools import permutations
    for N in range(3, 8):
        perms = list(permutations(range(1, N + 1)))
        for m in range(1, N + 1):
            for mp in range(m + 1, N + 1):
                rm, rmp = roles(N, m), roles(N, mp)
                cnt = 0
                for p in perms:
                    pos = {x: i for i, x in enumerate(p)}
                    ok = True
                    for c, rr in ((m, rm), (mp, rmp)):
                        if sum(v for e, v in rr.items() if pos[e] < pos[c]) != 0:
                            ok = False
                    cnt += ok
                assert Fraction(cnt, factorial(N)) == pair_prob(N, m, mp), (N, m, mp)
    print("pair_prob verified by brute force for N<=7")
