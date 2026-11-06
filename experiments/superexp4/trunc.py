"""Idea 2: does truncation (delete panels > N) preserve validity for the slip-chain family?
A(2n) = slip(P(n)),  P(2m) = {(PB(a,b), PB(a',b'), E ∪ 2D') : a,b' in A(m), (b,a',D') in P(m)}.
"""
import sys
from itertools import combinations


def valid_step(S, m, N):
    r = min(m - 1, N - m)
    return sum(1 for d in range(1, r + 1) if m - d in S) == sum(1 for d in range(1, r + 1) if m + d in S)


def valid_seq(seq, N):
    S = set()
    for m in seq:
        if not valid_step(S, m, N):
            return False
        S.add(m)
    return True


def PB(a, b): return tuple([2*x-1 for x in a] + [2*y for y in b])


def slip(D, t, s):
    def d(i): return 1 if i in D else 0
    return tuple([2*i+d(i) for i in t] + [2*i-1-d(i-1) for i in s])


def subsets(xs):
    for r in range(len(xs)+1):
        yield from combinations(xs, r)


def build(L, cap=3_000_000):
    A = {1: [(1,)]}
    P = {1: [((1,), (1,), frozenset())]}
    m = 1
    while 2*m <= 2**L:
        A[2*m] = [slip(D, t, s) for (t, s, D) in P[m]]
        odds = [k for k in range(1, 2*m) if k % 2]
        P2 = []
        for (b, a2, Dp) in P[m]:
            for a in A[m]:
                for b2 in A[m]:
                    for E in subsets(odds):
                        P2.append((PB(a, b), PB(a2, b2), frozenset(E) | frozenset(2*i for i in Dp)))
            if len(P2) > cap:
                break
        P[2*m] = P2
        m *= 2
    return A


def main(L):
    A = build(L)
    M = 2**L
    fam = A[M]
    print(f"M={M}: |A|={len(fam)} distinct {len(set(fam))}, valid: {all(valid_seq(s, M) for s in fam)}")
    for N in range(1, M):
        tr = set()
        bad = 0
        for s in fam:
            t = tuple(x for x in s if x <= N)
            if valid_seq(t, N):
                tr.add(t)
            else:
                bad += 1
        print(f"  N={N}: invalid truncations {bad}/{len(fam)}, distinct valid {len(tr)}")


if __name__ == "__main__":
    main(int(sys.argv[1]))
