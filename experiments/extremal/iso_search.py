"""Search for 'generalised parity blocks': splits [1..N] = X u Y such that
  (1) X is window-isomorphic to the p-world (p = |X|): for the increasing bijection
      phi: [1..p] -> X, phi^{-1}(W_N(phi(y))) = W_p(y) for every y,
  (2) X is balanced in the N-window of every panel of Y,
  (3) Y is window-isomorphic to the q-world (q = |Y|).
Then 'X-part then Y-part' is valid iff both parts are valid in their own worlds.
Y-panels whose N-window misses X are listed ('Yfree'), they can be free steps of the Y-part.
usage: iso_search.py N
"""
import sys


def win(N, m):
    r = min(m - 1, N - m)
    return [m - d for d in range(r, 0, -1)] + [m + d for d in range(1, r + 1)]


def iso(N, X):
    p = len(X)
    idx = {x: i + 1 for i, x in enumerate(X)}
    for y in range(1, p + 1):
        w = [idx[z] for z in win(N, X[y - 1]) if z in idx]
        if w != win(p, y):
            return False
    return True


def balanced(N, X, Y):
    Xs = set(X)
    for m in Y:
        r = min(m - 1, N - m)
        if sum((m - d) in Xs for d in range(1, r + 1)) != sum((m + d) in Xs for d in range(1, r + 1)):
            return False
    return True


def main(N):
    res = []
    for mask in range(1, (1 << N) - 1):
        X = [m for m in range(1, N + 1) if mask >> (m - 1) & 1]
        Y = [m for m in range(1, N + 1) if not mask >> (m - 1) & 1]
        if iso(N, X) and balanced(N, X, Y) and iso(N, Y):
            Xs = set(X)
            yfree = [m for m in Y if not any(z in Xs for z in win(N, m))]
            res.append((X, Y, yfree))
    for X, Y, yf in res:
        print(N, 'p=%d q=%d' % (len(X), len(Y)), 'X=', X, 'Yfree=', yf)


if __name__ == '__main__':
    main(int(sys.argv[1]))
