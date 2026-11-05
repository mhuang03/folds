"""splits.py N: list all splits [1..N] = X + Y where X (size p) and Y (size q) are window
copies of the p- and q-strips under their increasing enumerations, and each complete part is
balanced around every panel of the other (the `Split` structure of Growth.lean)."""
import sys
from itertools import combinations


def reach(N, m):
    return min(m - 1, N - m)


def is_copy(N, X):
    p = len(X)
    for j in range(1, p + 1):
        mj = X[j - 1]
        r, rp = reach(N, mj), reach(p, j)
        for y in range(1, p + 1):
            my = X[y - 1]
            if (mj - r <= my < mj) != (j - rp <= y < j):
                return False
            if (mj < my <= mj + r) != (j < y <= j + rp):
                return False
    return True


def balanced(N, U, m):
    r = reach(N, m)
    return sum(1 for x in U if m - r <= x < m) == sum(1 for x in U if m < x <= m + r)


def splits(N):
    out = []
    for p in range(1, N):
        for X in combinations(range(1, N + 1), p):
            if not is_copy(N, X):
                continue
            Xs = set(X)
            Y = tuple(x for x in range(1, N + 1) if x not in Xs)
            if not is_copy(N, Y):
                continue
            if all(balanced(N, X, m) for m in Y) and all(balanced(N, Y, m) for m in X):
                out.append((X, Y))
    return out


if __name__ == "__main__":
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        for X, Y in splits(N):
            print(N, len(X), "X=", X, "Y=", Y)
