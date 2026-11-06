#!/usr/bin/env python3
"""check_near.py: for odd N = 2n - 1, check C_N((N-1)/2) = 2a(n) + #{valid n-sequences with
1 before 2 and n before n-1} (brute force over permutations, n <= 9), and that the single-swap
copies have g(X^c) = a(n)/2."""
from itertools import permutations
from analyse import load, A

def valid(seq, n):
    S = set()
    for m in seq:
        r = min(m - 1, n - m)
        if sum(1 for d in range(1, r + 1) if m - d in S) != sum(1 for d in range(1, r + 1) if m + d in S):
            return False
        S.add(m)
    return True

for n in range(5, 10):
    N = 2 * n - 1
    cnt = both = 0
    for p in permutations(range(1, n + 1)):
        if valid(p, n):
            cnt += 1
            if p.index(1) < p.index(2) and p.index(n) < p.index(n - 1): both += 1
    assert cnt == A[n]
    D = load(N)
    k = (N - 1) // 2
    print(N, 'C_N(k) =', D['C'][k], ' 2a(n)+both =', 2 * A[n] + both, D['C'][k] == 2 * A[n] + both)
