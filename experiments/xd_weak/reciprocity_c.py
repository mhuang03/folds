"""reciprocity_c.py: check the reciprocity theorem for convention (c).

  python3 reciprocity_c.py [NMAX=8] [semi|sym]

VISIBILITY GRAPH G_N: vertices [N], edge {x,y} iff x lies in the window of y or y in the
window of x (|x-y| <= max(reach(x), reach(y))).
A fold sequence induces the acyclic orientation O of G_N "x -> y iff x is placed before y";
validity depends only on O (panel m is balanced iff it has as many in-neighbours in its left
window arm as in its right arm).  Call such O BALANCED.  Then

   A^c_N(q)          = sum over balanced acyclic O of  #{t:[N]->[q] strictly compatible with O}
   (-1)^N A^c_N(-q)  = sum over balanced acyclic O of  #{t:[N]->[q] weakly  compatible with O}
   (-1)^N A^c_N(-1)  = number of balanced acyclic orientations = number of commutation classes
   a(N)              = sum over balanced acyclic O of  #linear extensions of O.

This script enumerates the valid sequences, groups them by O, checks that every linear
extension of O is valid (so the classes are exactly the sets of linear extensions), and
compares both sides for q = 1, 2, 3 with the values computed from W_c(N,k) (weak.c).
"""
import sys
from itertools import product
from analyze import load, A_val

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 8
KIND = sys.argv[2] if len(sys.argv) > 2 else 'semi'
W = load()[('c', KIND)]


def reach(N, m):
    return min(m - 1, N - m)


def ok(N, S, m):
    r = reach(N, m)
    if KIND == 'semi':
        return sum(1 for d in range(1, r + 1) if m - d in S) == sum(1 for d in range(1, r + 1) if m + d in S)
    return all(((m - d) in S) == ((m + d) in S) for d in range(1, r + 1))


def valid_seqs(N):
    out, seq = [], []

    def rec(S):
        if len(seq) == N:
            out.append(tuple(seq))
            return
        for m in range(1, N + 1):
            if m not in S and ok(N, S, m):
                seq.append(m)
                rec(S | {m})
                seq.pop()
    rec(frozenset())
    return out


def main():
    for N in range(1, NMAX + 1):
        edges = [(x, y) for x in range(1, N + 1) for y in range(x + 1, N + 1)
                 if y - x <= max(reach(N, x), reach(N, y))]
        classes = {}
        for s in valid_seqs(N):
            pos = {m: i for i, m in enumerate(s)}
            O = tuple(pos[x] < pos[y] for x, y in edges)
            classes.setdefault(O, []).append(s)
        tot = {1: 0, 2: 0, 3: 0}
        strict = {2: 0, 3: 0}
        all_le = True
        for O, seqs in classes.items():
            rel = [(x, y) if o else (y, x) for (x, y), o in zip(edges, O)]     # u before v
            # number of linear extensions of the orientation (brute force by DP over subsets)
            pred = {m: 0 for m in range(1, N + 1)}
            for u, v in rel:
                pred[v] |= 1 << u
            cnt = {0: 1}
            full = sum(1 << m for m in range(1, N + 1))
            order = sorted(range(0, full + 1, 2), key=lambda S: bin(S).count('1'))
            for S in order:
                c = cnt.get(S)
                if not c:
                    continue
                for m in range(1, N + 1):
                    if not (S >> m) & 1 and (pred[m] & ~S) == 0:
                        cnt[S | (1 << m)] = cnt.get(S | (1 << m), 0) + c
            if cnt.get(full, 0) != len(seqs):
                all_le = False
            for q in (1, 2, 3):
                for t in product(range(q), repeat=N):
                    if all(t[u - 1] <= t[v - 1] for u, v in rel):
                        tot[q] += 1
                    if q > 1 and all(t[u - 1] < t[v - 1] for u, v in rel):
                        strict[q] += 1
        lhs = {q: (-1) ** N * A_val(W[N], -q) for q in (1, 2, 3)}
        print('N=%d %s: classes=%d  classes are full sets of linear extensions: %s' % (N, KIND, len(classes), all_le))
        print('     weak  pairs q=1,2,3: %s   (-1)^N A^c_N(-q): %s   equal: %s' % (
            [tot[q] for q in (1, 2, 3)], [lhs[q] for q in (1, 2, 3)], all(tot[q] == lhs[q] for q in (1, 2, 3))))
        print('     strict pairs q=2,3 : %s   A^c_N(q): %s   equal: %s' % (
            [strict[q] for q in (2, 3)], [A_val(W[N], q) for q in (2, 3)],
            all(strict[q] == A_val(W[N], q) for q in (2, 3))))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
