"""suffix.py: check that the number of length-k sequences (b_1..b_k) that are valid as the LAST
k steps (step b_i taken with S = [N] minus {b_i..b_k}) equals T(N,k), for small N, k.
Reason: inside the window of b_i the complement of S is {b_{i+1},...,b_k}, and validity is
invariant under complementing inside the window (Folds/Cyclic.lean complement lemmas)."""
from itertools import permutations


def ok(N, S, m):
    r = min(m - 1, N - m)
    return sum(1 for d in range(1, r + 1) if m - d in S) == sum(1 for d in range(1, r + 1) if m + d in S)


for N in range(1, 10):
    for k in range(1, min(N, 5) + 1):
        T = suf = 0
        for p in permutations(range(1, N + 1), k):
            T += all(ok(N, set(p[:i]), p[i]) for i in range(k))
            suf += all(ok(N, set(range(1, N + 1)) - set(p[i:]), p[i]) for i in range(k))
        assert T == suf, (N, k, T, suf)
print('suffix count == T(N,k) for N <= 9, k <= 5')
