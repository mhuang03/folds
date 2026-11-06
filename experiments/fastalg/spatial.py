"""Spatial transfer matrices: what does a DP that sweeps the PANELS (instead of time) need?

Cut the panels into A = [1..k] and B = [k+1..N].  For a valid sequence let sigma be the
relative time order of the panels of A and tau that of B.  M_k[sigma, tau] = number of
valid sequences with these restrictions.  Any sweep over panels 1..N whose state after
panel k is a function of the A-part (summing out time) needs at least
   rows_k = #distinct nonzero rows of M_k       (exact state merging), and
   rank_k = rank M_k                            (any linear/weighted transfer state),
since a = sum_{sigma, tau} M_k[sigma, tau] factors through the state.  Compare with
k! (all orders of A), with 2^k (a set-like state) and with the time-DP layer sizes.
Also done for the doubling-tree cut A = odd panels (the "binary digits" order).
usage: python3 spatial.py N
"""
import sys
import numpy as np
from common import masks


def sequences(N):
    lm, rm = masks(N)
    pc = int.bit_count
    out = []
    seq = []

    def rec(s):
        if len(seq) == N:
            out.append(tuple(seq))
            return
        for p in range(N):
            if not s >> p & 1 and pc(s & lm[p]) == pc(s & rm[p]):
                seq.append(p)
                rec(s | 1 << p)
                seq.pop()
    rec(0)
    return out


def analyse(N, seqs, A, label):
    Aset = set(A)
    M = {}
    for w in seqs:
        sig = tuple(p for p in w if p in Aset)
        tau = tuple(p for p in w if p not in Aset)
        M[(sig, tau)] = M.get((sig, tau), 0) + 1
    rows = sorted({s for s, _ in M})
    cols = sorted({t for _, t in M})
    ri = {s: i for i, s in enumerate(rows)}
    ci = {t: i for i, t in enumerate(cols)}
    X = np.zeros((len(rows), len(cols)))
    for (s, t), v in M.items():
        X[ri[s], ci[t]] = v
    distinct = len({tuple(r) for r in X})
    rank = np.linalg.matrix_rank(X)
    from math import factorial
    k = len(A)
    print('%-10s |A|=%2d  rows(nonzero)=%6d  distinct rows=%6d  rank=%5d   |A|!=%d  2^|A|=%d'
          % (label, k, len(rows), distinct, rank, factorial(k), 2 ** k))


def main():
    N = int(sys.argv[1])
    seqs = sequences(N)
    print('N=%d  a(N)=%d' % (N, len(seqs)))
    for k in range(1, N):
        analyse(N, seqs, list(range(k)), 'prefix')
    analyse(N, seqs, list(range(0, N, 2)), 'odd panels')
    analyse(N, seqs, list(range(0, N // 2)), 'left half')


if __name__ == '__main__':
    main()
