"""Shared helpers: load V_N (fold sequences) and the time words, descent sets, compositions."""
import os
import numpy as np
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))

A_KNOWN = [1, 2, 4, 10, 28, 96, 256, 1120, 4256, 17878, 70960, 383476, 1620328, 9167908]


def load(N):
    """a-encoding: array of shape (a(N), N), entry [i, k] = panel placed at step k+1 (values 1..N)."""
    A = np.fromfile(os.path.join(HERE, 'data', f'V{N}.bin'), dtype=np.uint8).reshape(-1, N)
    assert len(A) == A_KNOWN[N - 1]
    return A


def inverse(A):
    """t-encoding: T[i, m-1] = step at which panel m is placed (values 1..N)."""
    return (np.argsort(A, axis=1) + 1).astype(np.uint8)


def both(N):
    A = load(N)
    return {'a': A, 't': inverse(A)}


def des_mask(A):
    """descent set as a bitmask: bit i-1 set iff A[i] > A[i+1] (1-based position i in 1..N-1)."""
    N = A.shape[1]
    d = (A[:, :-1] > A[:, 1:]).astype(np.int64)
    return (d << np.arange(N - 1, dtype=np.int64)).sum(axis=1)


def peak_mask(A):
    """peak set: bit i-1 set iff A[i-1] < A[i] > A[i+1], 2 <= i <= N-1."""
    N = A.shape[1]
    if N < 3:
        return np.zeros(len(A), dtype=np.int64)
    p = ((A[:, 1:-1] > A[:, :-2]) & (A[:, 1:-1] > A[:, 2:])).astype(np.int64)
    return (p << np.arange(1, N - 1, dtype=np.int64)).sum(axis=1)


def comp_of_mask(D, N):
    """composition of N whose partial sums are the elements of the set with bitmask D."""
    parts, last = [], 0
    for i in range(1, N):
        if D >> (i - 1) & 1:
            parts.append(i - last)
            last = i
    parts.append(N - last)
    return tuple(parts)


def mask_of_comp(c):
    D, s = 0, 0
    for p in c[:-1]:
        s += p
        D |= 1 << (s - 1)
    return D


def subset_zeta(c, n):
    """m[D] = sum_{D' subset D} c[D'] over subsets of an n-element ground set."""
    m = np.array(c, dtype=object).copy()
    for i in range(n):
        bit = 1 << i
        for D in range(1 << n):
            if D & bit:
                m[D] += m[D ^ bit]
    return m


def subset_mobius(m, n):
    c = np.array(m, dtype=object).copy()
    for i in range(n):
        bit = 1 << i
        for D in range(1 << n):
            if D & bit:
                c[D] -= c[D ^ bit]
    return c


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest
