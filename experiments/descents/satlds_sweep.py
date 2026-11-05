"""Sweep of the LDS lower bound: for N in [N1, N2] check that no valid sequence has
LDS <= lg(N+1) - 1 (SAT UNSAT).  (LDS <= lg(N+1) is attained whenever des = lg(N+1)-1 is,
since a sequence with t ascending runs has LDS <= t.)  usage: satlds_sweep.py N1 N2"""
import sys, time
from pysat.solvers import Solver
from satlds import build
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    L = (N + 1).bit_length() - 2
    if L < 1: continue
    E, b = build(N, L)
    with Solver(name='cadical153', bootstrap_with=E.cl) as s:
        t = time.time(); sat = s.solve(); dt = time.time() - t
    print(f'N={N} LDS<={L}: {"SAT !!!" if sat else "UNSAT"} ({dt:.1f}s)', flush=True)
