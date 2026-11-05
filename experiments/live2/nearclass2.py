"""nearclass2.py N1 N2: window copies X of [N] that differ from a parity class C in a few
elements (X = C - A + B, |A| = |B| <= 2), with the reachability of the complement."""
import sys
from lib import load_copies

for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    E = set(range(2, N + 1, 2))
    O = set(range(1, N + 1, 2))
    for X, good in load_copies(N):
        S = set(X)
        for name, C in (('E', E), ('O', O)):
            A, B = sorted(C - S), sorted(S - C)
            if 1 <= len(B) <= 2 and len(A) == len(B):
                print(N, name, '-', A, '+', B, 'good' if good else 'BAD')
