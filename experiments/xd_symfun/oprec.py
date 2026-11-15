"""Part 3: search for linear operator recurrences for the statistic polynomials A_N(x):

    sum_{j=0..s} sum_{i=0..I} p_{ij}(x, N) (d/dx)^i A_{N+j}(x) = 0,
    p_{ij} polynomial of degree <= dx in x and <= dn in N        (homogeneous form;
    it contains A_{N+s} = sum_i p_i(x,N) A_N^{(i)}  and three-term versions).

Method: exact nullspace modulo the prime 2^61 - 1 of the coefficient-extraction system on
N = N0..Nmax-s-1 (training); a nullspace vector is then tested on the held-out last shift
N = Nmax-s.  Only searches with (#equations) >= (#unknowns) + MARGIN are run.
The code is validated on the Eulerian polynomials (it must find
A_{n+1} = (1+nx) A_n + x(1-x) A_n').

usage: python3 oprec.py
"""
import os, sys, itertools
from collections import defaultdict
from flint import nmod_mat
from common import HERE

P = (1 << 61) - 1
MARGIN = 12


def read(fn):
    d = defaultdict(dict)
    with open(os.path.join(HERE, 'data', fn)) as f:
        for line in f:
            p = line.split()
            if len(p) >= 3:
                d[p[1]][int(p[0])] = [int(v) for v in p[2:]]
    return d


def deriv(c, i):
    c = list(c)
    for _ in range(i):
        c = [k * c[k] for k in range(1, len(c))]
    return c


def rows_for(polys, N, s, I, dx, dn, step=1):
    """coefficient-extraction rows for index N (uses A_N, A_{N+step}, ..., A_{N+s*step})."""
    cols = []
    maxlen = 0
    for j in range(s + 1):
        A = polys[N + j * step]
        for i in range(I + 1):
            dA = deriv(A, i)
            for a in range(dx + 1):
                shifted = [0] * a + dA
                maxlen = max(maxlen, len(shifted))
                for b in range(dn + 1):
                    cols.append((shifted, pow(N, b)))
    rows = []
    for k in range(maxlen):
        row = [((sh[k] if k < len(sh) else 0) * nb) % P for sh, nb in cols]
        if any(row):
            rows.append(row)
    return rows


def search(polys, s, I, dx, dn, step=1, N0=None):
    Ns = sorted(polys)
    if N0 is None:
        N0 = Ns[0]
    usable = [N for N in Ns if N >= N0 and all((N + j * step) in polys for j in range(s + 1))]
    if len(usable) < 3:
        return None
    train, test = usable[:-1], usable[-1]
    U = (s + 1) * (I + 1) * (dx + 1) * (dn + 1)
    rows = []
    for N in train:
        rows += rows_for(polys, N, s, I, dx, dn, step)
    E = len(rows)
    if E < U + MARGIN:
        return None
    M = nmod_mat(rows, P)
    rank = M.rank()
    null = U - rank
    res = dict(U=U, E=E, null=null, holdout=None)
    if null > 0:
        # test on the held-out index: stack and recompute the rank
        rows2 = rows + rows_for(polys, test, s, I, dx, dn, step)
        res['holdout'] = U - nmod_mat(rows2, P).rank()
    return res


def eulerian(nmax):
    polys = {1: [1]}
    for n in range(1, nmax):
        A = polys[n]
        d = deriv(A, 1)
        new = [0] * (n + 2)
        for k in range(len(A)):          # (1 + n x) A
            new[k] += A[k]; new[k + 1] += n * A[k]
        for k in range(len(d)):          # x(1-x) A'
            new[k + 1] += d[k]; new[k + 2] -= d[k]
        while new and new[-1] == 0:
            new.pop()
        polys[n + 1] = new
    return polys


def gamma_poly(c):
    c = list(c)
    while c and c[-1] == 0: c.pop()
    lo = next(i for i, v in enumerate(c) if v)
    c = c[lo:]
    d = len(c) - 1
    from math import comb
    g = []
    for j in range(d // 2 + 1):
        gj = c[j]; g.append(gj)
        for i in range(d - 2 * j + 1):
            c[j + i] -= gj * comb(d - 2 * j, i)
    return [0] * lo + g


def main():
    grid = [(s, I, dx, dn) for s in (1, 2) for I in (0, 1, 2, 3) for dx in (0, 1, 2, 3, 4) for dn in (0, 1, 2, 3)]
    # validation
    E = eulerian(16)
    assert E[4] == [1, 11, 11, 1]
    r = search(E, 1, 1, 2, 1)
    print("validation on Eulerian polynomials n<=16, (s,I,dx,dn)=(1,1,2,1):", r)
    assert r and r['null'] >= 1 and r['holdout'] >= 1
    dp = read('dp_polys.txt')
    fam = {}
    for name in ('a_des', 't_des', 'a_exc', 't_exc', 'a_lrmax', 't_lrmax', 'a_pk', 't_pk', 'a_fix', 'inv', 'a_maj', 't_maj'):
        fam[name] = dp[name]
    fam['gamma(a_des)'] = {N: gamma_poly(c) for N, c in dp['a_des'].items()}
    fam['gamma(t_des)'] = {N: gamma_poly(c) for N, c in dp['t_des'].items()}
    total = 0; hits = []
    for name, polys in fam.items():
        variants = [('all N, step 1', polys, 1)]
        variants.append(('even N, step 2', {N: c for N, c in polys.items() if N % 2 == 0}, 2))
        variants.append(('odd N, step 2', {N: c for N, c in polys.items() if N % 2 == 1}, 2))
        for vname, pl, step in variants:
            ran = 0; best = None
            for (s, I, dx, dn) in grid:
                if name in ('inv', 'a_maj', 't_maj') and (dx > 2 or I > 2):
                    continue
                r = search(pl, s, I, dx, dn, step=step, N0=4)
                if r is None:
                    continue
                ran += 1; total += 1
                if best is None or r['E'] - r['U'] < best:
                    best = r['E'] - r['U']
                if r['null'] > 0:
                    hits.append((name, vname, s, I, dx, dn, r))
                    print("  NULLSPACE", name, vname, (s, I, dx, dn), r)
            print(f"{name:14s} {vname:15s}: {ran} searches run (unknowns up to "
                  f"{max([ (s+1)*(I+1)*(dx+1)*(dn+1) for (s,I,dx,dn) in grid])}), smallest surplus of equations {best}")
            sys.stdout.flush()
    print(f"\ntotal searches: {total}; with nontrivial nullspace on the training range: {len(hits)}; "
          f"surviving the hold-out: {sum(1 for h in hits if h[-1]['holdout'])}")


if __name__ == '__main__':
    main()
