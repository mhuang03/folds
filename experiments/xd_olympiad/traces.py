"""Commutation classes (traces) of valid sequences.
Two panels x, y COMMUTE (are 'far') iff neither lies in the other's window:
|x-y| > max(r_x, r_y).  Swapping two adjacent far panels keeps a sequence valid, so V_N is
a union of classes of the partially commutative monoid; a class = a valid acyclic orientation
of the dependency graph G_N, and its size is the number of linear extensions.
Prints: tau(N) = #classes, #classes with nonzero sign imbalance, sum of |imbalance|, D(N),
class-size histogram summary."""
import sys
from common import *

def normal_form(N, a, far):
    # lexicographically least word of the class: repeatedly take the smallest minimal element
    rem = list(a); out = []
    while rem:
        best = None
        for j, x in enumerate(rem):
            if all(far[x][y] for y in rem[:j]):
                if best is None or x < rem[best]: best = j
        out.append(rem.pop(best))
    return tuple(out)

def main(Nmax):
    for N in range(2, Nmax + 1):
        far = [[not near(N, x, y) for y in range(N + 1)] for x in range(N + 1)]
        cls = {}
        for a in valid_seqs(N):
            nf = normal_form(N, a, far)
            c = cls.setdefault(nf, [0, 0])
            c[0] += 1; c[1] += sign(a)
        tau = len(cls)
        nz = sum(1 for c in cls.values() if c[1])
        sabs = sum(abs(c[1]) for c in cls.values())
        D = sum(c[1] for c in cls.values())
        sizes = sorted(c[0] for c in cls.values())
        print(N, "a", A[N], "tau", tau, "imbalanced classes", nz, "sum|imb|", sabs, "D", D,
              "min/median/max class size", sizes[0], sizes[len(sizes) // 2], sizes[-1])
        sys.stdout.flush()

main(int(sys.argv[1]) if len(sys.argv) > 1 else 10)
