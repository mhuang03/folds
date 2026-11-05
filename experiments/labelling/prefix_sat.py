"""Prefix-only (left-half-only) window inequality: is there c:[1..N]->[t] satisfying the
window inequality at every panel m with 2m <= N+1 (the other panels are free)?
usage: prefix_sat.py t Nmin Nmax"""
import sys
from pysat.solvers import Solver
from core_ineq import build_guarded
t, a, b = map(int, sys.argv[1:4])
step = int(sys.argv[4]) if len(sys.argv) > 4 else 1
for N in range(a, b + 1, step):
    E, sel = build_guarded(N, t)
    with Solver(name='cadical153', bootstrap_with=E.cl) as s:
        ok = s.solve(assumptions=[sel[m] for m in sel if 2 * m <= N + 1])
    print(f'N={N} t={t} prefix-only:', 'SAT' if ok else 'UNSAT', flush=True)
