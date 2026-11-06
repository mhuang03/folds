"""tbexp.py: two-sided Beatty copies TB = {b(i) : i <= L} + {N + 1 - b'(j) : j <= R},
b(i) = floor((A i - e)/D), b'(j) = floor((A j - e')/D).  For given slope A/D, phases and L, R,
list the N for which TB is an inward window copy, as the junction gap J = (N + 1 - b'(R)) - b(L)."""
import sys
sys.path.insert(0, '../live6')
from twoside import is_inward_copy


def tb(N, A, D, e, e2, L, R):
    left = [(A * i - e) // D for i in range(1, L + 1)]
    right = [N + 1 - (A * j - e2) // D for j in range(R, 0, -1)]
    return left + right


def scan(A, D, e, e2, Lmax=12):
    res = {}
    for L in range(1, Lmax + 1):
        for R in range(1, Lmax + 1):
            bl = (A * L - e) // D
            br = (A * R - e2) // D
            ok = []
            for J in range(1, 4 * A // D + 4):
                N = bl + br + J - 1
                X = tb(N, A, D, e, e2, L, R)
                if is_inward_copy(N, X):
                    ok.append(J)
            res[(L, R)] = ok
    return res


if __name__ == '__main__':
    A, D, e, e2 = map(int, sys.argv[1:5])
    Lmax = int(sys.argv[5]) if len(sys.argv) > 5 else 10
    r = scan(A, D, e, e2, Lmax)
    for L in range(1, Lmax + 1):
        print(L, ' '.join('%s' % (''.join(str(j) if j < 10 else chr(87 + j) for j in r[(L, R)]) or '-')
                          for R in range(1, Lmax + 1)))
