"""rescheck.py N1 N2 K: check the residue chain theorem (PROOFS.txt 2.2): for N >= 2k an order pi
of the classes mod k is a residue chain of [N] iff pi and sigma(pi) are semi-symmetric in the
k-strip, sigma(t) = ((nu - t) mod k) + 1, nu = N mod k.  (For k <= N < 2k: 'if' only.)"""
import sys
from itertools import permutations
from lib import arms


def semi_k(k, seq):
    S = set()
    for t in seq:
        r = min(t - 1, k - t)
        if sum(1 for d in range(1, r + 1) if t - d in S) != sum(1 for d in range(1, r + 1) if t + d in S):
            return False
        S.add(t)
    return True


def is_chain(N, k, pi):
    U = set()
    for s in pi:
        for x in range(s, N + 1, k):
            L, R = arms(N, x)
            if len(L & U) != len(R & U):
                return False
        U |= set(range(s, N + 1, k))
    return True


N1, N2, K = map(int, sys.argv[1:4])
for N in range(N1, N2 + 1):
    for k in range(2, min(K, N) + 1):
        nu = N % k
        sig = {t: (nu - t) % k + 1 for t in range(1, k + 1)}
        for pi in permutations(range(1, k + 1)):
            a = is_chain(N, k, pi)
            b = semi_k(k, pi) and semi_k(k, [sig[t] for t in pi])
            if a != b and (N >= 2 * k or b):
                print('MISMATCH', N, k, pi, a, b)
print('checked')
