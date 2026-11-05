"""chainok.py Q: the Lean chain condition ChainOK q nu pi (Folds/Live2.lean), implemented
verbatim; (1) check it against brute-force residue chains in [N] (N <= 40), (2) for each
q <= Q, nu < q and class s, find an order pi of the other classes with ChainOK (or report
none).  Output used for the concrete instances in Live2.lean."""
import sys
from itertools import permutations
from lib import arms


def cycbal(q, A, s, rho):
    left = sum(((s + 2 * q - rho - 1 - t) % q + rho) // q for t in A)
    right = sum(((s + q - t) % q + rho) // q for t in A)
    return left == right


def chain_ok(q, nu, pi):
    for i, s in enumerate(pi):
        A = pi[:i]
        if not (cycbal(q, A, s, s - 1) and cycbal(q, A, s, (nu + q - s) % q)):
            return False
    return True


def brute_chain(N, q, pi):
    U = set()
    for s in pi:
        for x in range(s, N + 1, q):
            L, R = arms(N, x)
            if len(L & U) != len(R & U):
                return False
        U |= set(range(s, N + 1, q))
    return True


def find(q, nu, s):
    others = [t for t in range(1, q + 1) if t != s]

    def rec(seq):
        if len(seq) == len(others):
            return list(seq)
        for t in others:
            if t not in seq and chain_ok(q, nu, seq + [t]):
                r = rec(seq + [t])
                if r:
                    return r
        return None
    return rec([])


if __name__ == '__main__':
    Q = int(sys.argv[1])
    # (1) ChainOK implies a brute-force chain (sufficiency), all N <= 40, q <= 5
    for q in range(2, 6):
        for N in range(q, 41):
            for pi in permutations(range(1, q + 1)):
                if chain_ok(q, N % q, list(pi)) and not brute_chain(N, q, pi):
                    print('FAIL', N, q, pi)
    print('sufficiency checked')
    for q in range(2, Q + 1):
        for nu in range(q):
            row = []
            for s in range(1, q + 1):
                row.append(find(q, nu, s))
            print(q, nu, row)
