"""tbsearch.py u N1 N2 [step]: for N in range, two-sided Beatty copies TB(N; A/D, e, e', L, R)
with first element u and last element N + 1 - u (b(1) = b'(1) = u), p = L + R odd != 7,
inward window copies.  Prints the solutions per N (slopes with D <= 6)."""
import sys
sys.path.insert(0, '../live6')
from twoside import is_inward_copy
from tbexp import tb


def solutions(N, u, Dmax=6):
    out = []
    for D in range(1, Dmax + 1):
        for A in range(u * D, (u + 1) * D):
            if A < 2 * D:
                continue
            for e in range(0, D):
                if (A - e) // D != u:
                    continue
                for e2 in range(0, D):
                    if (A - e2) // D != u:
                        continue
                    Lc = int((N + 1) * D / (2 * A))
                    for L in range(Lc - 2, Lc + 3):
                        for R in range(Lc - 2, Lc + 3):
                            p = L + R
                            if L < 1 or R < 1 or p % 2 == 0 or p == 7:
                                continue
                            X = tb(N, A, D, e, e2, L, R)
                            if any(X[i] >= X[i + 1] for i in range(len(X) - 1)):
                                continue
                            if is_inward_copy(N, X):
                                out.append((A, D, e, e2, L, R))
    return out


if __name__ == '__main__':
    u, N1, N2 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    step = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    Dmax = int(sys.argv[5]) if len(sys.argv) > 5 else 6
    for N in range(N1, N2 + 1, step):
        s = solutions(N, u, Dmax)
        print(N, len(s), s[:12], flush=True)
