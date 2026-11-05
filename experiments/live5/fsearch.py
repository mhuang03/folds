"""fsearch.py n1 n2: sets F of [n] with 2, n-1 in F, 1, n not in F, such that F and its
complement both satisfy the inward criterion (Theorem G).  Then a full semi-symmetric sequence
(order F by G reversed... ) with 2 before 1 and n-1 before n exists."""
import sys
from itertools import combinations
from zeroset import inward_set
for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    mid = list(range(3, n - 1))
    sols = []
    for k in range(len(mid) + 1):
        for G in combinations(mid, k):
            F = {2, n - 1} | set(G)
            Fc = set(range(1, n + 1)) - F
            if inward_set(n, F) and inward_set(n, Fc):
                sols.append(sorted(F))
    print(n, len(sols), flush=True)
    for s in sols: print("   ", s)
