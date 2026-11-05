"""SAT check of the LDS conjecture: is there a valid fold sequence on [1..N] whose longest
decreasing subsequence has length <= L?  (LDS <= L  <=>  the panels split into L classes, each
placed in increasing order -- Dilworth/Mirsky.)  Variables: b[x,y] (x<y) = 'x placed before y'
(a tournament made transitive), class indicators c[x,j].  Validity: for every m,
#{d : m-d before m} = #{d : m+d before m}  (full totalizers).
usage: satlds.py N [L]   (default L = lg(N+1) - 1; expected UNSAT)."""
import sys, time, itertools
from pysat.solvers import Solver
from satwords import Enc
def build(N, L):
    E = Enc(); b = {}
    for x in range(1, N + 1):
        for y in range(x + 1, N + 1): b[x, y] = E.new()
    def before(x, y): return b[x, y] if x < y else -b[y, x]
    for x, y, z in itertools.permutations(range(1, N + 1), 3):
        if x < y < z or True:
            E.cl.append([-before(x, y), -before(y, z), before(x, z)])
    c = {(x, j): E.new() for x in range(1, N + 1) for j in range(L)}
    for x in range(1, N + 1):
        E.cl.append([c[x, j] for j in range(L)])
    for x in range(1, N + 1):
        for y in range(x + 1, N + 1):
            for j in range(L):
                E.cl.append([-c[x, j], -c[y, j], b[x, y]])
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        if r == 0: continue
        left = [before(m - d, m) for d in range(1, r + 1)]
        right = [before(m + d, m) for d in range(1, r + 1)]
        oL = E.tot(left); oR = E.tot(right)
        for t in range(1, r + 1):
            E.cl.append([-oL[t], oR[t]]); E.cl.append([oL[t], -oR[t]])
    # symmetry breaking: class of panel 1 is 0 (classes are interchangeable)
    E.cl.append([c[1, 0]])
    return E, b
if __name__ == '__main__':
    N = int(sys.argv[1]); L = int(sys.argv[2]) if len(sys.argv) > 2 else (N + 1).bit_length() - 2
    E, b = build(N, L)
    with Solver(name='cadical153', bootstrap_with=E.cl) as s:
        t = time.time(); sat = s.solve(); dt = time.time() - t
        if not sat:
            print(f'N={N} LDS<={L}: UNSAT ({dt:.1f}s)', flush=True)
        else:
            mod = set(l for l in s.get_model() if l > 0)
            key = lambda x: sum(1 for y in range(1, N + 1) if y != x and ((y < x and b[y, x] in mod) or (y > x and b[x, y] not in mod)))
            a = sorted(range(1, N + 1), key=key)
            from construct_bits import valid_fast
            from common import lds
            print(f'N={N} LDS<={L}: SAT ({dt:.1f}s) seq={a} valid={valid_fast(N, a)} lds={lds(a)}', flush=True)
