"""The interface descriptor of an ordering sigma of X, for a cut [N] = X u Y.

For x in X let W(x) be its window, YL(x), YR(x) the Y-panels in the left / right arm, and
    c_x(sigma) = #{X-panels of the left arm placed before x} - #{... right arm ...}.
A shuffle is valid at the step of x iff  #(YR(x) placed before x) - #(YL(x) placed before x) = c_x.
For y in Y the step of y sees sigma only through the number of placed X-panels in each arm
of y, i.e. through kappa(x) = (the set of y whose left arm contains x, the set of y whose
right arm contains x) of the placed X-panels.

Descriptor  D(sigma) = ( (kappa(sigma_p), YL(sigma_p), YR(sigma_p), c_{sigma_p}(sigma)) )_p.

Interface lemma [proven; Lean: XdRank.cutCount_map_eq]: D(sigma) = D(sigma') implies that
sigma and sigma' have the same row of the cut matrix.

This script checks, on the dumps of cutmat.bin, that the lemma holds and whether the
converse holds too (distinct rows <-> distinct descriptors among nonzero rows).
usage: python3 descriptor.py N kind [params]      (same cut syntax as cutmat.bin)
"""
import subprocess
import sys
import os


def cut_set(N, kind, params):
    if kind == 'parity':
        return [x for x in range(1, N + 1) if x % 2 == 1]
    if kind == 'spatial':
        return list(range(1, int(params[0]) + 1))
    if kind == 'res':
        q, r = int(params[0]), int(params[1])
        return [x for x in range(1, N + 1) if x % q == r]
    if kind == 'ed':
        d = int(params[0])
        return [x for x in range(1, N + 1) if x % d and (x % d) % 2 == 0]
    raise ValueError(kind)


def arms(N, m):
    r = min(m - 1, N - m)
    return set(range(m - r, m)), set(range(m + 1, m + r + 1))


def make_descriptor(N, X):
    Xs = set(X)
    Y = [y for y in range(1, N + 1) if y not in Xs]
    A = {m: arms(N, m) for m in range(1, N + 1)}
    kappa = {x: (frozenset(y for y in Y if x in A[y][0]), frozenset(y for y in Y if x in A[y][1])) for x in X}
    # canonical small ids for kappa classes
    kid = {}
    for x in X:
        kid.setdefault(kappa[x], len(kid))
    yl = {x: frozenset(A[x][0] - Xs) for x in X}
    yr = {x: frozenset(A[x][1] - Xs) for x in X}
    sid = {}
    for x in X:
        sid.setdefault((yl[x], yr[x]), len(sid))

    def D(sigma):
        placed = set()
        out = []
        for x in sigma:
            c = len(placed & A[x][0]) - len(placed & A[x][1])
            out.append((kid[kappa[x]], sid[(yl[x], yr[x])], c))
            placed.add(x)
        return tuple(out)
    return D, kid, sid


def main():
    N = int(sys.argv[1])
    kind = sys.argv[2]
    params = sys.argv[3:]
    X = cut_set(N, kind, params)
    here = os.path.dirname(os.path.abspath(__file__))
    fn = os.path.join(here, 'out', 'dump_%d_%s_%s.txt' % (N, kind, '_'.join(params)))
    subprocess.run([os.path.join(here, 'cutmat.bin'), str(N), kind] + params + ['dump', fn],
                   check=True, stdout=subprocess.DEVNULL)
    D, kid, sid = make_descriptor(N, X)
    rows = {}
    for line in open(fn):
        if line.startswith('#'):
            continue
        s, r = line.split(' :')
        sigma = tuple(int(v) for v in s.split(','))
        rows[sigma] = r.strip()
    os.remove(fn)
    byD = {}
    for sigma, r in rows.items():
        byD.setdefault(D(sigma), set()).add(r)
    bad = sum(1 for v in byD.values() if len(v) > 1)
    drows = len(set(rows.values()))
    # how many descriptor classes share a row
    byrow = {}
    for d, v in byD.items():
        for r in v:
            byrow.setdefault(r, set()).add(d)
    print('N=%d cut=%s %s: nonzero rows=%d distinct rows=%d descriptors=%d kappa-classes=%d '
          'signatures=%d lemma violations=%d  rows with >1 descriptor=%d'
          % (N, kind, ' '.join(params), len(rows), drows, len(byD), len(kid), len(sid), bad,
             sum(1 for v in byrow.values() if len(v) > 1)))
    return byrow


if __name__ == '__main__':
    main()
