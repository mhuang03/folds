"""SAT for admissible labellings (window inequality), reusing the encoding of
experiments/descents/satwords.py (ineq=True; labels 1..k there, printed here as 0..k-1).
usage: sat.py N t [--all [max]]   decide / enumerate all admissible labellings."""
import sys, os, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'descents'))
from satwords import build
from pysat.solvers import Solver

def solutions(N, t, limit=None, solver='cadical153'):
    E, y = build(N, t, ineq=True)
    with Solver(name=solver, bootstrap_with=E.cl) as s:
        n = 0
        while s.solve():
            model = set(l for l in s.get_model() if l > 0)
            rho = [next((v for v in range(1, t) if y[m, v] in model), t) for m in range(1, N + 1)]
            yield ''.join(str(v - 1) for v in rho)
            n += 1
            if limit and n >= limit: return
            # block this labelling
            cl = []
            for m in range(1, N + 1):
                for v in range(1, t):
                    lit = y[m, v]
                    cl.append(-lit if lit in model else lit)
            if not cl: return
            s.add_clause(cl)

if __name__ == '__main__':
    N, t = int(sys.argv[1]), int(sys.argv[2])
    if '--all' in sys.argv:
        i = sys.argv.index('--all')
        lim = int(sys.argv[i + 1]) if len(sys.argv) > i + 1 else None
        cnt = 0
        for s in solutions(N, t, lim):
            print(s); cnt += 1
        print(f'N={N} t={t}: {cnt} solutions', file=sys.stderr)
    else:
        t0 = time.time()
        s = next(solutions(N, t, 1), None)
        print(f'N={N} t={t}:', 'UNSAT' if s is None else 'SAT ' + s, f'({time.time() - t0:.1f}s)')
