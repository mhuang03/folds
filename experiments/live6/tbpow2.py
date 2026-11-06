"""tbpow2.py: two-sided Beatty copies
    TB = {floor((A i - e)/D) : i <= L} + {N + 1 - floor((A' j - e')/D') : j <= R}
for the power-of-two pairs (3, N - 2) and (5, N - 4): for N = 2^k (k = 5..10) list the
(slopes, L, R) with L + R odd != 7 giving an inward window copy with ends u, N + 1 - u."""
from twoside import is_inward_copy

SLOPES = {3: [(A, D) for D in (1, 2, 3, 4, 6, 8) for A in range(3 * D + 1, 4 * D + 1)],
          5: [(A, D) for D in (1, 2, 3, 4, 6, 8) for A in range(5 * D + 1, 6 * D + 1)]}
for u in (3, 5):
    for k in range(5, 11):
        N = 2 ** k
        found = []
        for (A, D) in SLOPES[u]:
            for e in range(0, D + 1):
                if (A - e) // D != u:
                    continue
                for (A2, D2) in [(A, D)]:
                    for e2 in range(0, D2 + 1):
                        if (A2 - e2) // D2 != u:
                            continue
                        Lc = int((N + 1) * D / (2 * A))
                        for L in range(Lc - 2, Lc + 3):
                            for R in range(Lc - 2, Lc + 3):
                                p = L + R
                                if p % 2 == 0 or p == 7:
                                    continue
                                X = [(A * i - e) // D for i in range(1, L + 1)] + \
                                    [N + 1 - (A2 * j - e2) // D2 for j in range(R, 0, -1)]
                                if any(X[i] >= X[i + 1] for i in range(len(X) - 1)):
                                    continue
                                if is_inward_copy(N, X):
                                    found.append((f'{A}/{D}', e, e2, L, R))
        print(u, N, len(found), found[:4], flush=True)
