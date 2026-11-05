"""Leaner SAT encoding for admissible labellings (window inequality).
c : [1..N] -> {0..t-1};  y[m,v] = [c(m) <= v]  (v = 0..t-2).
(WI) at m with c(m) = v  <=>  #{x in L(m): c(x) <= v} + #{x in R(m): c(x) >= v} <= r(m).
Each such cardinality constraint is a one-directional totalizer capped at r+1 whose output
'sum >= r+1' is forbidden under the condition c(m) = v.
Optional normalisation (1.3 of labelling/PROOFS.txt): every panel of label v >= 1 has
a panel of label <= v-1 to its right (--norm); this keeps satisfiability.
--left: only the constraints of the left-half panels (2m <= N+1); this relaxation is
monotone in N (see PROOFS.txt), --norm must not be combined with it.
usage: sat2.py N t [--solver S] [--norm] [--left] [--dimacs FILE]"""
import sys, time
from pysat.solvers import Solver

class Enc:
    def __init__(self): self.n = 0; self.cl = []
    def new(self): self.n += 1; return self.n
    def tot(self, lits, cap):
        """upward totalizer: o[i] (1<=i<=min(len,cap)) is implied by sum >= i"""
        if len(lits) == 1: return [None, lits[0]]
        h = len(lits) // 2
        a = self.tot(lits[:h], cap); b = self.tot(lits[h:], cap)
        p, q = len(a) - 1, len(b) - 1
        n = min(p + q, cap)
        c = [None] + [self.new() for _ in range(n)]
        for i in range(p + 1):
            for j in range(q + 1):
                k = i + j
                if k == 0: continue
                k = min(k, n)
                cl = [c[k]]
                if i: cl.append(-a[i])
                if j: cl.append(-b[j])
                self.cl.append(cl)
        return c

def build(N, t, norm=False, left=False):
    E = Enc()
    y = {}
    for m in range(1, N + 1):
        for v in range(t - 1):
            y[m, v] = E.new()
        for v in range(t - 2):
            E.cl.append([-y[m, v], y[m, v + 1]])
    T, F = 'T', 'F'
    def le(m, v):           # literal [c(m) <= v]
        if v < 0: return F
        if v >= t - 1: return T
        return y[m, v]
    def neg(l): return F if l == T else T if l == F else -l
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        if r == 0: continue
        if left and 2 * m > N + 1: continue
        for v in range(t):
            lits = [le(x, v) for x in range(m - r, m)] + [neg(le(x, v - 1)) for x in range(m + 1, m + r + 1)]
            nT = lits.count(T); lits = [l for l in lits if l not in (T, F)]
            cond = []
            if le(m, v) != T: cond.append(-le(m, v))
            if le(m, v - 1) != F: cond.append(le(m, v - 1))
            bound = r - nT          # sum(lits) <= bound
            if bound < 0: E.cl.append(cond); continue
            if bound >= len(lits): continue
            o = E.tot(lits, bound + 1)
            E.cl.append(cond + [-o[bound + 1]])
    if norm:
        for m in range(1, N + 1):
            for v in range(1, t):
                cl = [le(m, v - 1)] + [le(x, v - 1) for x in range(m + 1, N + 1)]
                if T in cl: continue
                E.cl.append([l for l in cl if l != F])
    return E, y

def decode(model, y, N, t):
    s = set(l for l in model if l > 0)
    return [next((v for v in range(t - 1) if y[m, v] in s), t - 1) for m in range(1, N + 1)]

def check(c):
    N = len(c)
    for m in range(1, N + 1):
        r = min(m - 1, N - m); v = c[m - 1]
        if sum(c[x - 1] <= v for x in range(m - r, m)) > sum(c[x - 1] < v for x in range(m + 1, m + r + 1)):
            return False
    return True

if __name__ == '__main__':
    N, t = int(sys.argv[1]), int(sys.argv[2])
    solver = sys.argv[sys.argv.index('--solver') + 1] if '--solver' in sys.argv else 'cadical153'
    left = '--left' in sys.argv
    E, y = build(N, t, '--norm' in sys.argv, left)
    if '--dimacs' in sys.argv:
        fn = sys.argv[sys.argv.index('--dimacs') + 1]
        with open(fn, 'w') as f:
            f.write(f'p cnf {E.n} {len(E.cl)}\n')
            for cl in E.cl: f.write(' '.join(map(str, cl)) + ' 0\n')
        sys.exit()
    t0 = time.time()
    with Solver(name=solver, bootstrap_with=E.cl) as s:
        res = s.solve()
        dt = time.time() - t0
        if res:
            c = decode(s.get_model(), y, N, t)
            print(f'N={N} t={t}{" left-half-only" if left else ""}: SAT {"".join(map(str, c))} check={check(c)} ({dt:.1f}s)', flush=True)
        else:
            print(f'N={N} t={t}: UNSAT ({dt:.1f}s, {E.n} vars, {len(E.cl)} clauses, solver={solver}{", norm" if "--norm" in sys.argv else ""}{", LEFT-HALF ONLY" if left else ""})', flush=True)
