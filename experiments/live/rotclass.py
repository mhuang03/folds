"""rotclass.py N p g: rotation classes C_k = {x in [1,N] : floor(((g - x p) mod N) / p) = k'}
indexed so that C_0 = X(N,p,g) = {floor((rN+g)/p)}.  Report copies and the valid class
orders (earlier classes complete and balanced around each point of the next class)."""
import sys
from itertools import permutations
from splits import is_copy, balanced


def classes(N, p, g):
    q = -(-N // p)
    cls = [[] for _ in range(q)]
    for x in range(1, N + 1):
        cls[((g - x * p) % N) // p].append(x)
    return cls


def class_orders(N, cls):
    good = []
    for perm in permutations(range(len(cls))):
        placed = []
        ok = True
        for k in perm:
            if not all(balanced(N, placed, m) for m in cls[k]):
                ok = False
                break
            placed += cls[k]
        if ok:
            good.append(perm)
    return good


if __name__ == "__main__":
    N, p, g = map(int, sys.argv[1:4])
    cls = classes(N, p, g)
    for k, C in enumerate(cls):
        print(k, C, "copy" if is_copy(N, tuple(C)) else "NOT copy")
    print("valid class orders:", class_orders(N, cls))
