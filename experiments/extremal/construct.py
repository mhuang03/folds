"""Explicit constructions attaining the extremal values, and a checker.

  free_seq(N): valid sequence with F(N) = floor(log2(N+1)) + floor(log2((N+1)/3)) + 1 free steps.
  lr_seq(N):   valid sequence with floor(log2 N) + 1 left-to-right maxima.

usage: construct.py NMAX      (verifies both for N = 1..NMAX)
"""
import sys
from fold import is_valid, nfree, lrmax, F, lg

sys.setrecursionlimit(10000)


def blocks_E(sigma, tau):
    """evens (sigma on floor(N/2)) then odds (tau on ceil(N/2))."""
    return [2 * y for y in sigma] + [2 * y - 1 for y in tau]


def blocks_O(sigma, tau):
    """odds (sigma on ceil(N/2)) then evens (tau on floor(N/2))."""
    return [2 * y - 1 for y in sigma] + [2 * y for y in tau]


def any_seq(n):
    """some valid sequence on n panels (recursive parity blocks)."""
    if n <= 1:
        return list(range(1, n + 1))
    return blocks_E(any_seq(n // 2), any_seq(n - n // 2))


def free_seq(N):
    if N <= 2:
        return list(range(1, N + 1))
    if N % 2 == 1:                      # N = 2n+1: evens (free_seq(n)) then odds; +2 (panels 1, N)
        n = N // 2
        return blocks_E(free_seq(n), any_seq(n + 1))
    # N = 2n: shifted parity blocks.  j = floor(n/2).
    #   X = {2y + [y > j] : 1 <= y <= n-1}     ~ (n-1)-world   (evens <= 2j, odds >= 2j+3)
    #   Y = {2y - 1 - [y > j+1] : 1 <= y <= n+1} ~ (n+1)-world  (odds <= 2j+1, evens >= 2j+2)
    # For n even the middle Y-panel 2j+1 sees one extra X panel on its left; it is balanced
    # iff Y-index 1 (panel 1) was placed before Y-index j+1, so tau must place 1 before its middle.
    n = N // 2
    j = n // 2
    X = [2 * y + (1 if y > j else 0) for y in free_seq(n - 1)]
    tau = any_seq(n + 1)
    if n % 2 == 0 and tau.index(1) > tau.index(j + 1):
        tau = tau[::-1]
    Y = [2 * y - 1 - (1 if y > j + 1 else 0) for y in tau]
    return X + Y


def lr_seq(N):
    """block containing N goes second; lrmax(N) = lrmax(floor(N/2)) + 1."""
    if N <= 1:
        return list(range(1, N + 1))
    if N % 2 == 0:                      # odds first (sigma on N/2), then evens (contain N)
        return blocks_O(lr_seq(N // 2), any_seq(N // 2))
    return blocks_E(lr_seq(N // 2), any_seq(N - N // 2))


if __name__ == '__main__':
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    bad = 0
    for N in range(1, NMAX + 1):
        a = free_seq(N)
        b = lr_seq(N)
        okf = is_valid(N, a) and nfree(N, a) == F(N)
        okl = is_valid(N, b) and lrmax(b) == lg(N) + 1
        if not (okf and okl):
            bad += 1
            print('FAIL', N, okf, okl, nfree(N, a), F(N), is_valid(N, a))
    print('checked N = 1..%d, failures: %d' % (NMAX, bad))
