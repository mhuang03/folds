"""Attainment sweep: for N in [N1, N2], look for a valid word with k = lg(N+1) labels
(a valid sequence with lg(N+1)-1 descents).  Tries the reverse-mirror self-dual subproblem
first (smaller), then the full problem, each with a time limit (seconds).
Output per N: SAT (with word and which variant) / UNSAT (proved) / UNKNOWN (timeout).
usage: satsweep_ub.py N1 N2 [timeout]"""
import sys, time, threading
from pysat.solvers import Solver
from satwords import build
from construct_bits import valid_fast
def run(N, k, rm, tl):
    E, y = build(N, k, rm)
    with Solver(name='cadical153', bootstrap_with=E.cl) as s:
        timer = threading.Timer(tl, lambda: s.interrupt()); timer.start()
        t = time.time(); r = s.solve_limited(expect_interrupt=True); dt = time.time() - t
        timer.cancel()
        if r is None: return 'UNKNOWN', dt, None
        if r is False: return 'UNSAT', dt, None
        model = set(l for l in s.get_model() if l > 0)
        rho = {m: next((v for v in range(1, k) if y[m, v] in model), k) for m in range(1, N + 1)}
        return 'SAT', dt, rho
N1, N2 = int(sys.argv[1]), int(sys.argv[2]); tl = float(sys.argv[3]) if len(sys.argv) > 3 else 600
for N in range(N1, N2 + 1):
    k = (N + 1).bit_length() - 1
    res = []
    for rm in ((True, False) if N % 4 != 3 else (False,)):
        st, dt, rho = run(N, k, rm, tl)
        res.append(f'{"rm" if rm else "full"}:{st}({dt:.0f}s)')
        if st == 'SAT':
            a = sorted(range(1, N + 1), key=lambda m: (rho[m], m))
            assert valid_fast(N, a)
            res.append('word=' + ''.join(str(rho[m]) for m in range(1, N + 1)))
            break
        if st == 'UNSAT' and not rm: break
    print(f'N={N} k={k} ' + ' '.join(res), flush=True)
