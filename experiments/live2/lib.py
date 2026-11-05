"""Shared helpers: reachability bitsets R_N (from reach.c) and window arithmetic."""
import os
import numpy as np

DIR = os.environ.get('LIVE2_DATA', '.')
_R = {}


def R(N):
    if N not in _R:
        _R[N] = np.fromfile(os.path.join(DIR, f'R{N}.bin'), dtype=np.uint8)
    return _R[N]


def mask(S):
    m = 0
    for x in S:
        m |= 1 << (x - 1)
    return m


def reachable(N, S):
    """S (iterable of panels) has a semi-symmetric ordering from scratch."""
    if N <= 1:
        return True
    m = mask(S)
    return bool((R(N)[m >> 3] >> (m & 7)) & 1)


def arms(N, m):
    r = min(m - 1, N - m)
    return set(range(m - r, m)), set(range(m + 1, m + r + 1))


def valid_step(N, S, m):
    L, Rr = arms(N, m)
    return len(L & S) == len(Rr & S)


def valid_seq(N, seq, base=()):
    S = set(base)
    for m in seq:
        if not valid_step(N, S, m):
            return False
        S.add(m)
    return True


def live_pair(N, u, v):
    """{u,v} live: some valid ordering of the pair and the complement reachable."""
    if not (valid_step(N, {u}, v) or valid_step(N, {v}, u)):
        return False
    return reachable(N, set(range(1, N + 1)) - {u, v})


def is_copy(N, X):
    X = sorted(X)
    p = len(X)
    S = set(X)
    c = [0] * (N + 1)
    for y in range(1, N + 1):
        c[y] = c[y - 1] + (y in S)

    def ct(y):
        return c[y] if y <= N else p + c[y - N]
    return all(ct(2 * x - 1) == 2 * c[x] - 1 for x in X)


def load_copies(N):
    out = []
    with open(os.path.join(DIR, f'C{N}.txt')) as f:
        for line in f:
            m, p, g = map(int, line.split())
            X = [i + 1 for i in range(N) if m >> i & 1]
            out.append((X, g == 1))
    return out
