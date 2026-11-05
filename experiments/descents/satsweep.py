"""Sweep (--ineq: only the window inequality #{W_L: <=} <= #{W_R: <}): for N in [N1, N2] decide SAT for k = lg(N+1) (construction) and k = lg(N+1)-1
(lower bound) with satwords.  Prints one line per (N, k).  usage: satsweep.py N1 N2 [lb|ub|both]"""
import sys, time
from satwords import solve
from construct_bits import valid_fast
N1, N2 = int(sys.argv[1]), int(sys.argv[2]); mode = sys.argv[3] if len(sys.argv) > 3 else 'both'
ineq = '--ineq' in sys.argv
for N in range(N1, N2 + 1):
    K = (N + 1).bit_length() - 1
    ks = {'lb': [K - 1], 'ub': [K], 'both': [K - 1, K]}[mode]
    for k in ks:
        if k < 1: continue
        rho, dt, E = solve(N, k, ineq=ineq)
        if rho is None:
            print(f'N={N} k={k} UNSAT {dt:.1f}s', flush=True)
        else:
            a = sorted(range(1, N + 1), key=lambda m: (rho[m], m))
            if not ineq: assert valid_fast(N, a)
            print(f'N={N} k={k} SAT {dt:.1f}s word={"".join(str(rho[m]) for m in range(1, N + 1))}', flush=True)
