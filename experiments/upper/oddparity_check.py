"""oddparity_check.py -- checks for the odd-N parity bound (Folds/Upper.lean, PROOFS.txt 1).

(1) exhaustive over all sets S of odd size, N = 2h+1 <= 15: V(S) <= h + 1 + floor(|S|/2),
    and the two pair lemmas (m, m+h+1 both valid => 2m in S; m, m+h both valid => 2m-1 in S);
(2) the saving of the product bound  prod_{i odd} min(N-i, h+1+i//2)/(N-i)  as -log(.)/N.
"""
import math


def valid_moves(N, S):
    res = []
    for m in range(1, N + 1):
        if m in S: continue
        r = min(m - 1, N - m)
        L = sum(1 for x in S if m - r <= x < m)
        R = sum(1 for x in S if m < x <= m + r)
        if L == R: res.append(m)
    return res


worst = 0
for h in range(0, 8):
    N = 2 * h + 1
    for mask in range(1 << N):
        S = {i + 1 for i in range(N) if mask >> i & 1}
        if len(S) % 2 == 0: continue
        Z = set(valid_moves(N, S))
        assert len(Z) <= h + 1 + len(S) // 2, (N, S)
        worst = max(worst, len(Z) - (h + 1 + len(S) // 2))
        assert h + 1 not in Z
        for m in range(1, h + 1):
            if m in Z and m + h + 1 in Z: assert 2 * m in S
        for m in range(2, h + 1):
            if m in Z and m + h in Z: assert 2 * m - 1 in S
print("exhaustive N <= 15 odd: bound holds; max(V - bound) =", worst, "(0 = sharp somewhere)")
for N in [101, 1001, 10001, 100001]:
    h = (N - 1) // 2
    s = sum(math.log((N - i) / min(N - i, h + 1 + i // 2)) for i in range(1, N, 2))
    print("N=%6d  saving of the odd parity bound: %.5f N" % (N, s / N))
for N in [100, 1000, 10000, 100000]:
    h = N // 2
    s = sum(math.log((N - i) / min(N - i, h)) for i in range(1, N, 2))
    print("N=%6d  saving of the even parity bound: %.5f N" % (N, s / N))
