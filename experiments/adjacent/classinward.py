"""Exceptional residue classes and Theorem G: for which (N, q) does the exceptional class
(C_1 with N = 1, C_q with N = -1 (mod q), q not a power of 2) satisfy the centre criterion (*)
(the negative-imbalance panels all left of the positive ones), resp. the peel criterion G'?"""
import sys
from peel import peel


def imb(N, B, m):
    r = min(m - 1, N - m)
    return sum(1 for x in B if m - r <= x < m) - sum(1 for x in B if m < x <= m + r)


def centre_ok(N, B):
    neg = [m for m in range(1, N + 1) if m not in B and imb(N, B, m) < 0]
    pos = [m for m in range(1, N + 1) if m not in B and imb(N, B, m) > 0]
    return not neg or not pos or max(neg) < min(pos)


NMAX = int(sys.argv[1])
for q in range(3, NMAX):
    if q & (q - 1) == 0:
        continue
    row1, row2 = [], []
    for N in range(q, NMAX + 1):
        if N % q == q - 1:
            C = set(range(q, N + 1, q))
            row2.append('%d%s%s' % (N, '*' if centre_ok(N, C) else '', "'" if peel(N, C) else ''))
        if N % q == 1:
            C = set(range(1, N + 1, q))
            row1.append('%d%s%s' % (N, '*' if centre_ok(N, C) else '', "'" if peel(N, C) else ''))
    print('q=%d  C_1 (N=1): %s   C_q (N=-1): %s' % (q, ' '.join(row1), ' '.join(row2)))
print("(* = centre criterion holds, ' = peel criterion G' holds)")
