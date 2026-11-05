"""CP-SAT model of admissible labellings (window inequality), 1 worker.
le[m][v] = [c(m) <= v] (v = 0..t-2), b[m][v] = [c(m) = v].
(WI) at m:  b[m][v] -> sum_{x in L(m)} le[x][v] + sum_{x in R(m)} (1 - le[x][v-1]) <= r(m).
--norm: every panel of label >= v (v >= 1) has a panel of label <= v-1 to its right.
--left: only left-half panels' constraints (monotone relaxation).
usage: cpsat.py N t [--norm] [--left] [--time SECONDS]"""
import sys, time
from ortools.sat.python import cp_model

def solve(N, t, norm=False, left=False, tl=None):
    md = cp_model.CpModel()
    le = {}
    for m in range(1, N + 1):
        for v in range(t - 1):
            le[m, v] = md.NewBoolVar(f'le{m}_{v}')
        for v in range(t - 2):
            md.AddImplication(le[m, v], le[m, v + 1])
    def LE(m, v):
        if v < 0: return 0
        if v >= t - 1: return 1
        return le[m, v]
    b = {}
    for m in range(1, N + 1):
        for v in range(t):
            b[m, v] = md.NewBoolVar(f'b{m}_{v}')
            md.Add(b[m, v] == LE(m, v) - LE(m, v - 1))
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        if r == 0: continue
        if left and 2 * m > N + 1: continue
        for v in range(t):
            expr = sum(LE(x, v) for x in range(m - r, m)) + sum(1 - LE(x, v - 1) for x in range(m + 1, m + r + 1))
            md.Add(expr <= r).OnlyEnforceIf(b[m, v])
    if norm:
        for m in range(1, N + 1):
            for v in range(1, t):
                md.AddBoolOr([le[m, v - 1]] + [le[x, v - 1] for x in range(m + 1, N + 1)])
    s = cp_model.CpSolver()
    s.parameters.num_workers = 1
    if tl: s.parameters.max_time_in_seconds = tl
    t0 = time.time()
    st = s.Solve(md)
    dt = time.time() - t0
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        c = [next(v for v in range(t) if s.Value(b[m, v])) for m in range(1, N + 1)]
        return 'SAT ' + ''.join(map(str, c)), dt
    return {cp_model.INFEASIBLE: 'UNSAT', cp_model.UNKNOWN: 'UNKNOWN'}.get(st, str(st)), dt

if __name__ == '__main__':
    N, t = int(sys.argv[1]), int(sys.argv[2])
    tl = float(sys.argv[sys.argv.index('--time') + 1]) if '--time' in sys.argv else None
    res, dt = solve(N, t, '--norm' in sys.argv, '--left' in sys.argv, tl)
    print(f'N={N} t={t}{" left-half-only" if "--left" in sys.argv else ""}: {res} ({dt:.1f}s, cp-sat 1 worker{", norm" if "--norm" in sys.argv else ""})', flush=True)
