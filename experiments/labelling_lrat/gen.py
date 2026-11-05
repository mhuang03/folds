"""Generate LRAT certificates for the labelling checks, as Lean `Cert`s (Folds/LabellingSAT.lean).

The encoding mirrors `Folds.LSAT.gen` exactly (clause tags `CTag`, variables `VarTag`):
  y m u            = [c m < u]                              (u = 0..t)
  inLit m v p      = p < r : ( y (m-1-p) (v+1), + )         left window, [c x <= v]
                     p >= r: ( y (m+1+(p-r)) v, - )         right window, [c x >= v]
  oLit m v lo hi i = leaf (hi = lo+1, i = 1): inLit m v lo, else ( o m v lo hi i, + )
  lo m   : -y m 0          hi m : y m t          ord m u : -y m u | y m (u+1)
  tot m v lo mid hi i j k : -oLit(lo,mid,i) [i>0] | -oLit(mid,hi,j) [j>0] | oLit(lo,hi,k)
  win m v : -y m (v+1) | y m v | -oLit(0, 2r, r+1)
The totalizer tree halves [0, 2r); outputs are capped at r+1 (as in labelling2/sat2.py).

Pipeline: CNF -> cadical --lrat (ASCII) -> lrat-trim (ASCII) -> keep the used input clauses,
renumber clauses (inputs 1..u, then the proof steps) and variables (by first use), emit Lean.

usage: gen.py N t [--left] [--name NAME]      (writes Lean `def NAME : Cert` to stdout)
env:   CADICAL, LRAT_TRIM: paths of the binaries (default: in PATH)
"""
import os, subprocess, sys, tempfile


def reach(N, m):
    return min(m - 1, N - m)


def checked(left, N, m):
    return reach(N, m) > 0 and (not left or 2 * m <= N + 1)


def build(N, t, left):
    """list of (tag, clause), clause = list of (vartag, sign)"""
    cls = []

    def inLit(m, v, p):
        r = reach(N, m)
        if p < r:
            return (('y', m - 1 - p, v + 1), True)
        return (('y', m + 1 + (p - r), v), False)

    def oLit(m, v, lo, hi, i):
        if hi == lo + 1 and i == 1:
            return inLit(m, v, lo)
        return (('o', m, v, lo, hi, i), True)

    def neg(x):
        return (x[0], not x[1])

    for m in range(1, N + 1):
        cls.append((('lo', m), [(('y', m, 0), False)]))
        cls.append((('hi', m), [(('y', m, t), True)]))
        for u in range(t):
            cls.append((('ord', m, u), [(('y', m, u), False), (('y', m, u + 1), True)]))
    for m in range(1, N + 1):
        if not checked(left, N, m):
            continue
        r = reach(N, m)
        cap = r + 1
        for v in range(t):
            def node(lo, hi):
                if hi - lo == 1:
                    return 1
                mid = (lo + hi) // 2
                p, q = node(lo, mid), node(mid, hi)
                n = min(p + q, cap)
                for i in range(p + 1):
                    for j in range(q + 1):
                        if i + j == 0:
                            continue
                        k = min(i + j, n)
                        cl = []
                        if i:
                            cl.append(neg(oLit(m, v, lo, mid, i)))
                        if j:
                            cl.append(neg(oLit(m, v, mid, hi, j)))
                        cl.append(oLit(m, v, lo, hi, k))
                        cls.append((('tot', m, v, lo, mid, hi, i, j, k), cl))
                return n
            node(0, 2 * r)
            cls.append((('win', m, v), [(('y', m, v + 1), False), (('y', m, v), True),
                                        neg(oLit(m, v, 0, 2 * r, r + 1))]))
    return cls


def solve(N, t, left, tmp):
    cls = build(N, t, left)
    var = {}
    dim = []
    for _, cl in cls:
        row = []
        for g, s in cl:
            if g not in var:
                var[g] = len(var) + 1
            row.append(var[g] if s else -var[g])
        dim.append(row)
    cnf = os.path.join(tmp, 'f.cnf')
    with open(cnf, 'w') as f:
        f.write(f'p cnf {len(var)} {len(dim)}\n')
        for row in dim:
            f.write(' '.join(map(str, row)) + ' 0\n')
    lrat = os.path.join(tmp, 'f.lrat')
    trim = os.path.join(tmp, 'f.trim')
    res = subprocess.run([os.environ.get('CADICAL', 'cadical'), '-q', '--lrat', '--binary=false',
                          cnf, lrat], stdout=subprocess.DEVNULL)
    assert res.returncode == 20, f'cadical: not UNSAT (rc={res.returncode})'
    res = subprocess.run([os.environ.get('LRAT_TRIM', 'lrat-trim'), '-q', '-a', cnf, lrat, trim],
                         stdout=subprocess.DEVNULL)
    assert res.returncode == 20, f'lrat-trim failed (rc={res.returncode})'
    steps = []
    for line in open(trim):
        xs = line.split()
        if len(xs) > 1 and xs[1] == 'd':
            continue
        xs = list(map(int, xs))
        z = xs.index(0, 1)
        lits, hints = xs[1:z], xs[z + 1:-1]
        assert all(h > 0 for h in hints), 'RAT step'
        steps.append((xs[0], lits, hints))
        if not lits:
            break
    assert not steps[-1][1], 'no empty clause'
    norig = len(dim)
    used = sorted({h for _, _, hs in steps for h in hs if h <= norig})
    cid = {h: i + 1 for i, h in enumerate(used)}
    for k, (i, _, _) in enumerate(steps):
        cid[i] = len(used) + k + 1
    inv = {v: g for g, v in var.items()}
    nv = {}

    def lit(x):
        v = abs(x)
        if v not in nv:
            nv[v] = len(nv) + 1
        return 2 * nv[v] + (0 if x > 0 else 1)
    init = [(cls[h - 1][0], [lit(x) for x in dim[h - 1]]) for h in used]
    stp = [([lit(x) for x in lits], [cid[h] for h in hs]) for _, lits, hs in steps]
    vt = [None] * (len(nv) + 1)
    for v, k in nv.items():
        vt[k] = inv[v]
    return vt, init, stp, len(var), len(dim)


def lean_vt(g):
    if g is None:
        return '.none'
    return '.' + g[0] + ' ' + ' '.join(map(str, g[1:]))


def lean_tag(g):
    return '.' + g[0] + ' ' + ' '.join(map(str, g[1:]))


def lst(xs):
    return '[' + ', '.join(map(str, xs)) + ']'


def emit(name, vt, init, stp):
    out = [f'def {name} : Cert where']
    out.append('  vt := [' + ',\n    '.join(lean_vt(g) for g in vt) + ']')
    out.append('  init := [' + ',\n    '.join(f'({lean_tag(g)}, {lst(c)})' for g, c in init) + ']')
    out.append('  steps := [' + ',\n    '.join(f'({lst(c)}, {lst(h)})' for c, h in stp) + ']')
    return '\n'.join(out) + '\n'


if __name__ == '__main__':
    N, t = int(sys.argv[1]), int(sys.argv[2])
    left = '--left' in sys.argv
    name = sys.argv[sys.argv.index('--name') + 1] if '--name' in sys.argv else 'cert'
    with tempfile.TemporaryDirectory() as tmp:
        vt, init, stp, nvars, ncls = solve(N, t, left, tmp)
    sys.stderr.write(f'N={N} t={t} left={left}: {nvars} vars {ncls} clauses -> used {len(init)} '
                     f'clauses, {len(vt) - 1} vars, {len(stp)} steps, '
                     f'{sum(len(h) for _, h in stp)} hints\n')
    print(emit(name, vt, init, stp))
