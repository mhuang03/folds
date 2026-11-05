"""Minimal sets of panels whose balance constraints alone already force >= k+1 runs.
For N and k (default k = lg(N+1) - 1), each panel m's constraint clauses are guarded by a
selector literal; we compute an UNSAT core over panels and shrink it to a minimal one
(deletion-based).  usage: satcore.py N [k]"""
import sys
from pysat.solvers import Solver
from satwords import Enc
def build_guarded(N, k):
    E = Enc(); M = N + 1; y = {}
    for m in range(1, N + 1):
        for v in range(1, k): y[m, v] = E.new()
        for v in range(1, k - 1): E.cl.append([-y[m, v], y[m, v + 1]])
    def Y(m, v):
        if v <= 0: return 'F'
        if v >= k: return 'T'
        return y[m, v]
    sel = {}
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        if r == 0: continue
        s = E.new(); sel[m] = s
        start = len(E.cl)
        for v in range(1, k + 1):
            cond = []
            if Y(m, v) != 'T': cond.append(-Y(m, v))
            if Y(m, v - 1) != 'F': cond.append(Y(m, v - 1))
            left = [Y(m - d, v) for d in range(1, r + 1)]
            right = [Y(m + d, v - 1) for d in range(1, r + 1)]
            nT_L = sum(1 for l in left if l == 'T'); left = [l for l in left if l not in ('T', 'F')]
            nT_R = sum(1 for l in right if l == 'T'); right = [l for l in right if l not in ('T', 'F')]
            oL = E.tot(left); oR = E.tot(right)
            def ge(o, i):
                if i <= 0: return 'T'
                if i >= len(o): return 'F'
                return o[i]
            for t in range(1, r + 1):
                a = ge(oL, t - nT_L); b = ge(oR, t - nT_R)
                for (p, q) in ((a, b), (b, a)):
                    if p == 'F' or q == 'T': continue
                    cl = list(cond) + [-s]
                    if p != 'T': cl.append(-p)
                    if q != 'F': cl.append(q)
                    E.cl.append(cl)
    return E, sel
def minimal_core(N, k):
    E, sel = build_guarded(N, k)
    inv = {s: m for m, s in sel.items()}
    with Solver(name='cadical153', bootstrap_with=E.cl) as s:
        assert not s.solve(assumptions=list(sel.values()))
        core = sorted(inv[l] for l in s.get_core())
        i = 0
        while i < len(core):
            trial = core[:i] + core[i + 1:]
            if not s.solve(assumptions=[sel[m] for m in trial]):
                core = sorted(inv[l] for l in s.get_core()) if s.get_core() else trial
                # keep order stable
            else:
                i += 1
        return core
if __name__ == '__main__':
    N = int(sys.argv[1]); k = int(sys.argv[2]) if len(sys.argv) > 2 else (N + 1).bit_length() - 2
    core = minimal_core(N, k)
    print(f'N={N} k={k}: minimal panel core ({len(core)} panels):', core)
