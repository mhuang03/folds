"""swap.py N1 N2 c: right-aligned Beatty X(N, p, h) (h <= 1) with its last element N - h moved
to N - c.  For which (N, p, h) is the result an inward window copy?  Prints failures with
p >= 3 grouped by alpha = N / p."""
import sys
from twoside import is_inward_copy


def swapped(N, p, h, c):
    X = [(r * N - h) // p for r in range(1, p + 1)]
    X[-1] = N - c
    return X


if __name__ == '__main__':
    N1, N2, c = map(int, sys.argv[1:4])
    for N in range(N1, N2 + 1):
        bad = []
        for p in range(3, (N + 1) // 2 + 1):
            for h in (0, 1):
                if h + 2 * p > N + 1:
                    continue
                X = swapped(N, p, h, c)
                if X[-2] >= X[-1]:
                    continue
                if not is_inward_copy(N, X):
                    bad.append((p, h, round(N / p, 2)))
        print(N, bad)
