"""reschain.py N1 N2 K: residue classes mod k in [N] (any N).  For each k <= K: which classes
are window copies, and is there an order of all k classes forming a copy chain (each class a
copy, balanced by the union of the earlier ones)?  Prints the chain orders found."""
import sys
from itertools import permutations
from lib import is_copy, arms


def bal(N, U, X):
    for x in X:
        L, R = arms(N, x)
        if len(L & U) != len(R & U):
            return False
    return True


N1, N2, K = map(int, sys.argv[1:4])
for N in range(N1, N2 + 1):
    line = [str(N)]
    for k in range(2, K + 1):
        cls = {s: frozenset(range(s, N + 1, k)) for s in range(1, k + 1) if s <= N}
        cp = [s for s, C in cls.items() if len(C) == 1 or is_copy(N, C)]
        orders = []
        if len(cp) == len(cls):
            for perm in permutations(cls):
                U = frozenset()
                ok = True
                for s in perm:
                    if not bal(N, U, cls[s]):
                        ok = False
                        break
                    U |= cls[s]
                if ok:
                    orders.append(''.join(map(str, perm)))
        line.append(f'k={k}:copies={"".join(map(str, cp))} chains={orders[:3]}{"..." if len(orders) > 3 else ""}')
    print(' '.join(line))
