"""beatty_copy.py N1 N2: for X(N,p,g) = {floor((rN+g)/p) : r=1..p} with 2p <= N and
-N/p < g/p... test the conjecture: X is a window copy iff -N < g*? ... prints the (p,g) with
2p <= N, 1 <= X, where copy status differs from the rule  'copy iff g > -(N - 2p)... '"""
import sys
from beatty_cover import copy_crit

for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    for p in range(1, N + 1):
        cop = []
        for g in range(-2 * N, N):
            X = [(r * N + g) // p for r in range(1, p + 1)]
            if X[0] < 1 or X[-1] > N or len(set(X)) < p:
                continue
            cop.append((g, copy_crit(N, X)))
        gs_copy = [g for g, c in cop if c]
        gs_not = [g for g, c in cop if not c]
        if 2 * p <= N:
            bad = [g for g in gs_not]
            if bad:
                print("N", N, "p", p, "slope>=2 non-copies at g =", bad, "copies at", gs_copy)
        else:
            if gs_copy:
                print("N", N, "p", p, "slope<2 copies at g =", gs_copy)
