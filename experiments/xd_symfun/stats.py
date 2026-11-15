"""Part 3/4 (enumeration): distributions of classical statistics on V_N in both encodings.

Writes data/enum_polys.txt ("N name c_0 c_1 ...") and prints equidistribution classes.
usage: python3 stats.py [Nmax]  (default 12)
"""
import sys, os
from collections import defaultdict
import numpy as np
from common import load, inverse, HERE


def stat_table(X):
    """dict name -> integer vector (one value per permutation) for the array X (rows = perms)."""
    n, N = X.shape
    X = X.astype(np.int64)
    pos = np.arange(1, N + 1)
    d = X[:, :-1] > X[:, 1:]
    st = {}
    st['des'] = d.sum(axis=1)
    st['maj'] = (d * pos[:-1]).sum(axis=1)
    inv = np.zeros(n, dtype=np.int64)
    for i in range(N):
        for j in range(i + 1, N):
            inv += X[:, i] > X[:, j]
    st['inv'] = inv
    st['exc'] = (X > pos).sum(axis=1)
    st['aexc'] = (X < pos).sum(axis=1)
    st['fix'] = (X == pos).sum(axis=1)
    if N >= 3:
        st['pk'] = ((X[:, 1:-1] > X[:, :-2]) & (X[:, 1:-1] > X[:, 2:])).sum(axis=1)
        st['val'] = ((X[:, 1:-1] < X[:, :-2]) & (X[:, 1:-1] < X[:, 2:])).sum(axis=1)
        st['ddes'] = ((X[:, 1:-1] < X[:, :-2]) & (X[:, 1:-1] > X[:, 2:])).sum(axis=1)
        st['dasc'] = ((X[:, 1:-1] > X[:, :-2]) & (X[:, 1:-1] < X[:, 2:])).sum(axis=1)
    else:
        for k in ('pk', 'val', 'ddes', 'dasc'):
            st[k] = np.zeros(n, dtype=np.int64)
    # left peaks (a_0 = 0 convention) and exterior peaks
    Y = np.concatenate([np.zeros((n, 1), dtype=np.int64), X, np.zeros((n, 1), dtype=np.int64)], axis=1)
    st['lpk'] = ((Y[:, 1:-2] > Y[:, :-3]) & (Y[:, 1:-2] > Y[:, 2:-1])).sum(axis=1)
    st['epk'] = ((Y[:, 1:-1] > Y[:, :-2]) & (Y[:, 1:-1] > Y[:, 2:])).sum(axis=1)
    st['lrmax'] = (X == np.maximum.accumulate(X, axis=1)).sum(axis=1)
    st['lrmin'] = (X == np.minimum.accumulate(X, axis=1)).sum(axis=1)
    st['rlmax'] = (X[:, ::-1] == np.maximum.accumulate(X[:, ::-1], axis=1)).sum(axis=1)
    st['rlmin'] = (X[:, ::-1] == np.minimum.accumulate(X[:, ::-1], axis=1)).sum(axis=1)
    cur = X - 1
    m = np.tile(np.arange(N), (n, 1))
    for _ in range(N):
        m = np.minimum(m, np.take_along_axis(m, cur, axis=1))
    st['cyc'] = (m == np.arange(N)).sum(axis=1)
    st['first'] = X[:, 0]
    st['last'] = X[:, -1]
    # longest increasing / alternating runs
    asc = ~d
    run = np.ones(n, dtype=np.int64); best = np.ones(n, dtype=np.int64)
    for i in range(N - 1):
        run = np.where(asc[:, i], run + 1, 1)
        best = np.maximum(best, run)
    st['lir'] = best                       # longest increasing run
    if N >= 2:
        st['ir1'] = np.where(d.any(axis=1), d.argmax(axis=1) + 1, N)   # initial increasing run
    else:
        st['ir1'] = np.ones(n, dtype=np.int64)
    return st


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    dist = defaultdict(dict)       # name -> N -> tuple
    lines = []
    joint_lines = []
    for N in range(1, nmax + 1):
        A = load(N); T = inverse(A)
        sa = stat_table(A); stt = stat_table(T)
        allst = {('a_' + k): v for k, v in sa.items()}
        allst.update({('t_' + k): v for k, v in stt.items()})
        for name, v in allst.items():
            c = np.bincount(v)
            dist[name][N] = tuple(int(x) for x in c)
            lines.append(f"{N} {name} " + " ".join(str(int(x)) for x in c))
        # joint distributions
        for (x, y) in [('a_des', 't_des'), ('a_des', 'a_first'), ('t_des', 't_first'),
                       ('a_des', 'a_exc'), ('a_pk', 't_pk'), ('a_des', 'a_pk'), ('t_des', 't_pk')]:
            J = np.zeros((allst[x].max() + 1, allst[y].max() + 1), dtype=np.int64)
            np.add.at(J, (allst[x], allst[y]), 1)
            joint_lines.append(f"{N} {x},{y} " + " | ".join(" ".join(str(int(v)) for v in row) for row in J))
    with open(os.path.join(HERE, 'data', 'enum_polys.txt'), 'w') as f:
        f.write("\n".join(lines) + "\n")
    with open(os.path.join(HERE, 'data', 'enum_joint.txt'), 'w') as f:
        f.write("\n".join(joint_lines) + "\n")
    # equidistribution classes (exact, and up to reversal k -> max-k), over N = 4..nmax
    def key(name, flip):
        out = []
        for N in range(4, nmax + 1):
            v = dist[name][N]
            # strip leading zeros (shift-invariant comparison) and trailing zeros
            lo = next(i for i, x in enumerate(v) if x)
            w = v[lo:]
            out.append(w[::-1] if flip else w)
        return tuple(out)
    classes = defaultdict(list)
    for name in dist:
        k0, k1 = key(name, False), key(name, True)
        classes[min(k0, k1)].append(name + ('' if k0 <= k1 else '~') + ('*' if k0 == k1 else ''))
    print(f"Equidistribution classes on V_N, N = 4..{nmax} (up to shift; '~' = reflected; '*' = palindromic):")
    for k, names in sorted(classes.items(), key=lambda kv: -len(kv[1])):
        print("  ", ", ".join(sorted(names)))
    print()
    for name in sorted(dist):
        print(name, " ".join(str(x) for x in dist[name][min(nmax, 9)]))


if __name__ == '__main__':
    main()
