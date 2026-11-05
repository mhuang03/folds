"""Which families of panels already force k+1 runs (N = 2^(k+1)-1 etc.)?  Each panel's balance
constraint is guarded by a selector; we test UNSAT under assumptions = the family.
usage: satfamily.py N [k]"""
import sys
from pysat.solvers import Solver
from satcore import build_guarded
N = int(sys.argv[1]); k = int(sys.argv[2]) if len(sys.argv) > 2 else (N + 1).bit_length() - 2
M = N + 1
E, sel = build_guarded(N, k)
fams = {
    'even': [m for m in sel if m % 2 == 0],
    'odd': [m for m in sel if m % 2 == 1],
    'mult4': [m for m in sel if m % 4 == 0],
    'left half': [m for m in sel if 2 * m <= M],
    'right half': [m for m in sel if 2 * m >= M],
    '[M/8,7M/8]': [m for m in sel if M <= 8 * m <= 7 * M],
    '[M/4,3M/4]': [m for m in sel if M <= 4 * m <= 3 * M],
    'not 2^i, M-2^i': [m for m in sel if (m & (m - 1)) and ((M - m) & (M - m - 1))],
    'v2(m)>=1 or v2(M-m)>=1': [m for m in sel if m % 2 == 0 or (M - m) % 2 == 0],
}
with Solver(name='cadical153', bootstrap_with=E.cl) as s:
    for name, P in fams.items():
        r = s.solve(assumptions=[sel[m] for m in P])
        print(f'N={N} k={k} {name:28s} ({len(P)} panels): {"sat" if r else "UNSAT"}', flush=True)
