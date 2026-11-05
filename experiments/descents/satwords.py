"""SAT search for valid words rho in [k]^N (equivalently: valid fold sequences with at most k
ascending runs, i.e. at most k-1 descents).  Validity of the word:
   for every m:  #{1<=d<=r_m : rho(m-d) <= rho(m)}  ==  #{1<=d<=r_m : rho(m+d) < rho(m)}.
Encoding: order encoding y[m][v] = [rho(m) <= v]; for every (m, v) two full totalizers
(unary counters with both directions) and   [rho(m) = v] -> (left count == right count).
usage: satwords.py N k [solver] [--rm]   (--rm: also require reverse-mirror self-duality,
rho(M-m) = k+1-rho(m)).  Prints the sequence (runs separated by |) or UNSAT."""
import sys, time
from pysat.solvers import Solver
class Enc:
    def __init__(self): self.n = 0; self.cl = []
    def new(self): self.n += 1; return self.n
    def tot(self, lits):
        """full totalizer: returns o[1..len] with o[i] <-> sum >= i (o[0] unused)"""
        if not lits: return [None]
        if len(lits) == 1: return [None, lits[0]]
        h = len(lits) // 2
        a = self.tot(lits[:h]); b = self.tot(lits[h:])
        p, q = len(a) - 1, len(b) - 1
        c = [None] + [self.new() for _ in range(p + q)]
        T, F = 'T', 'F'
        def A(i): return T if i == 0 else (F if i > p else a[i])
        def B(j): return T if j == 0 else (F if j > q else b[j])
        for i in range(p + 1):
            for j in range(q + 1):
                if i + j >= 1:     # a>=i & b>=j -> c>=i+j
                    cl = [c[i + j]]
                    if A(i) != T: cl.append(-A(i))
                    if B(j) != T: cl.append(-B(j))
                    self.cl.append(cl)
                if i + j + 1 <= p + q:   # a<i+1 & b<j+1 -> c<i+j+1
                    cl = [-c[i + j + 1]]
                    if A(i + 1) != F: cl.append(A(i + 1))
                    if B(j + 1) != F: cl.append(B(j + 1))
                    self.cl.append(cl)
        return c
def build(N, k, rm=False):
    E = Enc(); M = N + 1
    y = {}
    for m in range(1, N + 1):
        for v in range(1, k):
            y[m, v] = E.new()
        for v in range(1, k - 1):
            E.cl.append([-y[m, v], y[m, v + 1]])
    def Y(m, v):   # literal for rho(m) <= v ; returns True/False constants as strings
        if v <= 0: return 'F'
        if v >= k: return 'T'
        return y[m, v]
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        if r == 0: continue
        for v in range(1, k + 1):
            # condition literal set for rho(m) = v : Y(m,v) & !Y(m,v-1)
            cond = []
            if Y(m, v) not in ('T',): cond.append(-Y(m, v))       # clause part: not(rho<=v)
            if Y(m, v - 1) not in ('F',): cond.append(Y(m, v - 1))  # clause part: rho<=v-1
            left = [Y(m - d, v) for d in range(1, r + 1)]
            right = [Y(m + d, v - 1) for d in range(1, r + 1)]
            nT_L = sum(1 for l in left if l == 'T'); left = [l for l in left if l not in ('T', 'F')]
            nT_R = sum(1 for l in right if l == 'T'); right = [l for l in right if l not in ('T', 'F')]
            oL = E.tot(left); oR = E.tot(right)
            # sum_L + nT_L == sum_R + nT_R ; express  [sum_L >= i - nT_L]  etc.
            def ge(o, i):
                if i <= 0: return 'T'
                if i >= len(o): return 'F'
                return o[i]
            for t in range(1, r + 1):
                a = ge(oL, t - nT_L); b = ge(oR, t - nT_R)
                # cond -> (a <-> b)
                for (p, q) in ((a, b), (b, a)):
                    # p -> q
                    if p == 'F' or q == 'T': continue
                    cl = list(cond)
                    if p != 'T': cl.append(-p)
                    if q != 'F': cl.append(q)
                    E.cl.append(cl)
    if rm:
        for m in range(1, N + 1):
            for v in range(1, k):
                # rho(M-m) <= k - v  <->  rho(m) >= v+1  <->  not(rho(m) <= v)
                a = Y(M - m, k - v); b = Y(m, v)
                if a in ('T', 'F') or b in ('T', 'F'): continue
                E.cl.append([a, b]); E.cl.append([-a, -b])
    return E, y
def solve(N, k, solver='cadical153', rm=False):
    E, y = build(N, k, rm)
    with Solver(name=solver, bootstrap_with=E.cl) as s:
        t = time.time(); sat = s.solve(); dt = time.time() - t
        if not sat: return None, dt, E
        model = set(l for l in s.get_model() if l > 0)
        rho = {}
        for m in range(1, N + 1):
            rho[m] = next((v for v in range(1, k) if y[m, v] in model), k)
        return rho, dt, E
if __name__ == '__main__':
    N, k = int(sys.argv[1]), int(sys.argv[2])
    solver = sys.argv[3] if len(sys.argv) > 3 and not sys.argv[3].startswith('--') else 'cadical153'
    rm = '--rm' in sys.argv
    rho, dt, E = solve(N, k, solver, rm)
    if rho is None:
        print(f'N={N} k={k}{" rm" if rm else ""}: UNSAT  ({dt:.1f}s, {E.n} vars, {len(E.cl)} clauses)')
    else:
        a = sorted(range(1, N + 1), key=lambda m: (rho[m], m))
        out = []
        for i, x in enumerate(a):
            if i and x < a[i - 1]: out.append('|')
            out.append(str(x))
        from construct_bits import valid_fast
        print(f'N={N} k={k}{" rm" if rm else ""}: SAT ({dt:.1f}s) valid={valid_fast(N, a)} word={"".join(str(rho[m]) for m in range(1, N+1))}')
        print('   ', ' '.join(out))
