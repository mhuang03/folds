"""Exhaustive check of the restricted chain (PROOFS.txt, Theorem 4):

For 2r <= x, 2r+1 <= y, D' ⊆ [1, floor(r/2)], D = (odds <= r) ∪ 2D':
   PB(alpha, beta),  alpha in V_{ceil(x/2)},  beta in condF(floor(x/2), D')   is in condF(x, D)
   PB(alpha', beta'), alpha' in condS(ceil(y/2), D'), beta' in V_{floor(y/2)} is in condS(y, D)
(no reduction mod x or y happens).  Also compares the exact
   M(x, y, r) = sum_{D ⊆ [1,r]} #condF(x,D) #condS(y,D)
with the recursive lower bound 2^{ceil(r/2)} a(ceil(x/2)) a(floor(y/2)) M(floor(x/2), ceil(y/2), floor(r/2)).
"""
from itertools import combinations
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from chaincheck import V, okF, okS, PB


def subsets(xs):
    for k in range(len(xs) + 1):
        yield from combinations(xs, k)


Vs = {k: V(k) for k in range(0, 11)}


def Mexact(x, y, r):
    return sum(sum(1 for t in Vs[x] if okF(t, D, x)) * sum(1 for s in Vs[y] if okS(s, D, y))
               for D in subsets(range(1, r + 1)))


def main():
    bad = tot = 0
    for x in range(1, 11):
        for y in (x, x + 1):
            if y > 10:
                continue
            for r in range(0, x // 2 + 1):
                if not (2 * r <= x and 2 * r + 1 <= y):
                    continue
                x1, x2, y1, y2 = (x + 1) // 2, x // 2, (y + 1) // 2, y // 2
                odds = [k for k in range(1, r + 1) if k % 2]
                for Dp in subsets(range(1, r // 2 + 1)):
                    D = set(odds) | {2 * i for i in Dp}
                    for b in (t for t in Vs[x2] if okF(t, Dp, x2)):
                        for a in Vs[x1]:
                            tot += 1; bad += not okF(PB(a, b), D, x)
                    for a in (s for s in Vs[y1] if okS(s, Dp, y1)):
                        for b in Vs[y2]:
                            tot += 1; bad += not okS(PB(a, b), D, y)
    print(f"inclusions: {tot} checked, {bad} failures")
    for x, y, r in [(6, 6, 2), (6, 7, 2), (7, 7, 3), (8, 8, 3), (8, 9, 4), (9, 9, 4), (9, 10, 4), (10, 10, 4)]:
        lhs = Mexact(x, y, r)
        x1, x2, y1, y2 = (x + 1) // 2, x // 2, (y + 1) // 2, y // 2
        rhs = 2 ** ((r + 1) // 2) * len(Vs[x1]) * len(Vs[y2]) * Mexact(x2, y1, r // 2)
        print(f"M({x},{y},{r}) = {lhs} >= {rhs}: {lhs >= rhs}")


if __name__ == "__main__":
    main()
