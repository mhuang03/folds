"""SAT search for admissible labellings (t labels, panels 1..N) in which the interval
[a, a+L-1] has all labels < j (0-based).  usage: interval_sat.py t j L N a
Prints the labelling if one exists."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'descents'))
from satwords import build
from pysat.solvers import Solver

def search(t, j, L, N, a, solver='cadical153'):
    E, y = build(N, t, ineq=True)
    cl = list(E.cl)
    for m in range(a, a + L):
        cl.append([y[m, j]])          # rho(m) <= j  (1-based)  <=> label < j (0-based)
    for m in (a - 1, a + L):          # maximality: the neighbours have label >= j
        if 1 <= m <= N: cl.append([-y[m, j]])
    with Solver(name=solver, bootstrap_with=cl) as s:
        if not s.solve(): return None
        model = set(l for l in s.get_model() if l > 0)
        return ''.join(str(next((v for v in range(1, t) if y[m, v] in model), t) - 1)
                       for m in range(1, N + 1))

if __name__ == '__main__':
    t, j, L, N, a = map(int, sys.argv[1:6])
    r = search(t, j, L, N, a)
    print(f't={t} j={j} L={L} N={N} a={a}:', r if r else 'UNSAT')
