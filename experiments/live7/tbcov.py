"""tbcov.py u Dmax N0: for each slope A/D (D <= Dmax, floor((A - e)/D) = u) and phases e, e'
in {0, 1}, the residues N mod 2A (N in [N0, N0 + 4A)) for which some TB(N; A/D, e, e', L, R)
with p = L + R odd is an inward window copy (first element u, last N + 1 - u).  Then: which
k (mod the common period) have 2^k covered."""
import sys
from math import gcd
sys.path.insert(0, '../live6')
from twoside import is_inward_copy
from tbexp import tb


def covered(N, A, D, e, e2, spread=3):
    Lc = int((N + 1) * D / (2 * A))
    for L in range(Lc - spread, Lc + spread + 1):
        for R in range(Lc - spread, Lc + spread + 1):
            p = L + R
            if L < 1 or R < 1 or p % 2 == 0 or p == 7:
                continue
            X = tb(N, A, D, e, e2, L, R)
            if any(X[i] >= X[i + 1] for i in range(len(X) - 1)):
                continue
            if is_inward_copy(N, X):
                return (L, R)
    return None


def main():
    u, Dmax, N0 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    cov = {}
    for D in range(1, Dmax + 1):
        for A in range(u * D, (u + 1) * D + 1):
            if gcd(A, D) != 1 or A < 2 * D:
                continue
            for e in (0, 1):
                for e2 in (0, 1):
                    if (A - e) // D != u or (A - e2) // D != u or e2 < e:
                        continue
                    res = set()
                    for N in range(N0, N0 + 2 * A):
                        if covered(N, A, D, e, e2):
                            res.add(N % (2 * A))
                    # periodicity check
                    for N in range(N0 + 2 * A, N0 + 4 * A):
                        assert (covered(N, A, D, e, e2) is not None) == (N % (2 * A) in res), (A, D, e, e2, N)
                    cov[(A, D, e, e2)] = res
                    print((A, D, e, e2), sorted(res), flush=True)
    # powers of two
    for k in range(6, 40):
        N = 2 ** k
        ws = [s for s, r in cov.items() if N % (2 * s[0]) in r]
        print(k, ws[:6])


if __name__ == '__main__':
    main()
