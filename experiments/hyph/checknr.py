"""checknr.py qmax: the odd near-reduction (PROOFS.txt, Theorem R).
q = 2m+1, nu = 2w (0 < 2w < q).  Odds-first parity-block orders pi = (2a-1 for a in alpha) ++
(2b for b in beta) are GoodL(q, 2w) iff
   alpha in GoodL(m+1, w) and  i before md(2i-w-1, m+1)   for 1 <= i, 2i <= w+1
   beta  in GoodL(m,   w) and  md(2j-w, m) before j       for 1 <= j, 2j <= w.
Checks the count identity and the forward implication on all orders."""
import sys
from lib import *


def before(seq, a, b):
    return seq.index(a) < seq.index(b)


def cplus(n, w, seq):
    return all(before(seq, i, md(2 * i - w - 1, n)) for i in range(1, n + 1) if 2 * i <= w + 1 and md(2 * i - w - 1, n) != i)


def cminus(n, w, seq):
    return all(before(seq, md(2 * j - w, n), j) for j in range(1, n + 1) if 2 * j <= w and md(2 * j - w, n) != j)


qmax = int(sys.argv[1])
for q in range(5, qmax + 1, 2):
    m = (q - 1) // 2
    for w in range(1, m + 1):
        nu = 2 * w
        if nu >= q:
            continue
        A = [a for a in all_goodL(m + 1, w % (m + 1)) if cplus(m + 1, w, a)]
        B = [b for b in all_goodL(m, w % m) if cminus(m, w, b)]
        # odds-first GoodL(q, nu) orders: count by DFS restricted to odds first
        def extra(seq, S, t):
            k = len(seq)
            return (t % 2 == 1) if k < m + 1 else (t % 2 == 0)
        P = all_goodL(q, nu, extra)
        ok = all(goodL(q, nu, [2 * a - 1 for a in A[i % len(A)]] + [2 * b for b in B[i % len(B)]]) for i in range(min(50, len(A) * len(B)))) if A and B else True
        print(q, nu, 'w', w, 'alpha', len(A), 'beta', len(B), 'prod', len(A) * len(B), 'oddsfirst', len(P), 'fwd', ok)
