"""Exhaustive check of the chain recursion  B(2m) >= 2^m a(m)^2 B(m)  (PROOFS.txt, Thm 1).

(1) inclusions, m <= 6: for every D' ⊆ [1,m-1], every alpha in V_m and beta in condF(m,D'),
    PB(alpha,beta) is in condF(2m, odds ∪ 2D'); for every alpha' in condS(m,D'), beta' in V_m,
    PB(alpha',beta') is in condS(2m, odds ∪ 2D').  (E = all odds is the strongest case.)
(2) explicit family, N = 4m <= 16: all slip sequences slip(D, PB(alpha,beta), PB(alpha',beta'))
    with D = E ∪ 2D' are valid for N, pairwise distinct, and their number is
    2^m a(m)^2 B(m).
"""
import sys
from itertools import combinations


def valid_step(S, m, N):
    r = min(m - 1, N - m)
    return sum(1 for d in range(1, r + 1) if m - d in S) == \
        sum(1 for d in range(1, r + 1) if m + d in S)


def valid_seq(seq, N):
    S = set()
    for m in seq:
        if not valid_step(S, m, N):
            return False
        S.add(m)
    return sorted(seq) == list(range(1, N + 1))


def V(n):
    out = []

    def rec(pre, S):
        if len(pre) == n:
            out.append(tuple(pre)); return
        for m in range(1, n + 1):
            if m not in S and valid_step(S, m, n):
                S.add(m); pre.append(m); rec(pre, S); pre.pop(); S.discard(m)
    rec([], set())
    return out


def ms(x, n):
    return (x - 1) % n + 1


def okF(t, D, n):
    pos = {x: i for i, x in enumerate(t)}
    return all(pos[k] < pos[ms(2 * k, n)] for k in D)


def okS(s, D, n):
    pos = {x: i for i, x in enumerate(s)}
    return all(pos[ms(2 * k + 1, n)] < pos[k + 1] for k in D)


def PB(a, b):
    return tuple([2 * x - 1 for x in a] + [2 * y for y in b])


def subsets(xs):
    for r in range(len(xs) + 1):
        yield from combinations(xs, r)


def slip(D, t, s, n):
    d = lambda i: 1 if i in D else 0
    return tuple([2 * i + d(i) for i in t] + [2 * i - 1 - d(i - 1) for i in s])


def main():
    Vs = {k: V(k) for k in range(1, 9)}
    print("(1) inclusions")
    for m in range(1, 7):
        n = 2 * m
        odds = [k for k in range(1, n) if k % 2]
        bad = checked = 0
        for Dp in subsets(range(1, m)):
            D = set(odds) | {2 * i for i in Dp}
            for b in (x for x in Vs[m] if okF(x, Dp, m)):
                for a in Vs[m]:
                    checked += 1
                    bad += not okF(PB(a, b), D, n)
            for a in (x for x in Vs[m] if okS(x, Dp, m)):
                for b in Vs[m]:
                    checked += 1
                    bad += not okS(PB(a, b), D, n)
        print(f"  m={m}: {checked} implications, {bad} failures")
    print("(2) explicit families")
    for m in range(1, 5):
        n, N = 2 * m, 4 * m
        odds = [k for k in range(1, n) if k % 2]
        seen = set(); invalid = 0; total = 0
        Bm = 0
        for Dp in subsets(range(1, m)):
            Fm = [x for x in Vs[m] if okF(x, Dp, m)]
            Sm = [x for x in Vs[m] if okS(x, Dp, m)]
            Bm += len(Fm) * len(Sm)
            for E in subsets(odds):
                D = set(E) | {2 * i for i in Dp}
                for b in Fm:
                    for a in Vs[m]:
                        t = PB(a, b)
                        for a2 in Sm:
                            for b2 in Vs[m]:
                                seq = slip(D, t, PB(a2, b2), n)
                                total += 1
                                invalid += not valid_seq(seq, N)
                                seen.add(seq)
        am = len(Vs[m])
        print(f"  N={N}: {total} sequences, {len(seen)} distinct, {invalid} invalid; "
              f"2^m a(m)^2 B(m) = {2 ** m * am * am * Bm}")


if __name__ == "__main__":
    main()
