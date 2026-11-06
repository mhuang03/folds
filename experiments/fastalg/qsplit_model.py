"""Memory/work model of recomputation schemes for the MITM pairing (NOTES.txt section 5).

Pairing: even N = 2h:  a = sum_{|S|=h} g(S) g(S^c);  odd N = 2h+1 (fused form):
a = sum_{|U|=h+1} g(U) g(U^c), |U^c| = h.

Split the pairing sum by a statistic of S on a fixed panel set Q (|Q| = q):
  pattern split: S cap Q = sigma exactly (2^q pieces),
  count split:   |S cap Q| = u            (q+1 pieces; Q = left half gives the
                 (i, j) blocks of rust/src/block.rs, and each piece is a rectangle).
Each piece needs g only on the DOWN-SET of its two target families (the targets and
their complements), which is closed under the pull DP.  Scheme:
  1. DP for ALL sets up to a checkpoint layer j0, keep layer j0;
  2. for each piece: DP on layers j0+1..top restricted to the down-set, pair, discard.
Accounting is OPTIMISTIC in the way rust/src/sub.rs is: a DP whose largest layer is X
is charged X (sub-block scheduling gets within a few % of one layer).  So
   peak = max( C(N, j0),  C(N, j0) + max_j |restricted layer j| ),
   work = sum_{j <= j0} j C(N,j) + sum_pieces sum_{j > j0} j |restricted layer j|,
both relative to the current scheme: peak ~ C(N, h) (one stored layer),
work ~ sum_{j <= h+1} j C(N, j).  Mirror symmetry halves both alike and is ignored.
usage: python3 qsplit_model.py N [q_max]
"""
import sys
from math import comb


def tops(N):
    h = N // 2
    return (h, h) if N % 2 == 0 else (h + 1, h)


def piece_layers(N, q, kind, x, j0):
    """Restricted layer sizes j0+1..top for one piece (pattern of size x, or count x)."""
    tA, tB = tops(N)
    out = []
    for j in range(j0 + 1, max(tA, tB) + 1):
        tot = 0
        # count sets T of size j by u = |T cap Q|; membership in down-set A or B
        for u in range(0, min(q, j) + 1):
            v = j - u
            if v > N - q:
                continue
            if kind == 'pattern':
                # A: T cap Q subset sigma (|sigma| = x), |T - Q| <= tA - x
                # B: T cap Q subset Q - sigma,          |T - Q| <= tB - (q - x)
                a = comb(x, u) if (v <= tA - x and j <= tA) else 0
                b = comb(q - x, u) if (v <= tB - (q - x) and j <= tB) else 0
                both = 1 if (u == 0 and a and b) else 0
                tot += (a + b - both) * comb(N - q, v)
            else:
                # A: |T cap Q| <= x, |T - Q| <= tA - x ; B: complement count q - x
                a = (u <= x and v <= tA - x and j <= tA)
                b = (u <= q - x and v <= tB - (q - x) and j <= tB)
                if a or b:
                    tot += comb(q, u) * comb(N - q, v)
        out.append(tot)
    return out


def model(N, q, j0, kind):
    full = [comb(N, j) for j in range(N + 1)]
    work = sum(j * full[j] for j in range(j0 + 1))
    run = 0
    if kind == 'pattern':
        pieces = [(x, comb(q, x)) for x in range(q + 1)]
    else:
        pieces = [(x, 1) for x in range(q + 1)]
    for x, mult in pieces:
        L = piece_layers(N, q, kind, x, j0)
        run = max(run, max(L) if L else 0)
        work += mult * sum((j0 + 1 + i) * L[i] for i in range(len(L)))
    peak = full[j0] + run
    h = N // 2
    base_peak = full[h]
    base_work = sum(j * full[j] for j in range(h + 2))
    return peak / base_peak, work / base_work


def main():
    N = int(sys.argv[1])
    qmax = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    h = N // 2
    print('N=%d: current scheme peak ~ C(N,%d) = %.3e sets = %.3e mirror words' % (N, h, comb(N, h), comb(N, h) / 2))
    for kind, qs in (('pattern', range(1, qmax + 1)), ('count', range(2, N + 1))):
        pts = []
        for q in qs:
            for j0 in range(1, h + 1):
                p, w = model(N, q, j0, kind)
                pts.append((p, w, q, j0))
        pts.sort()
        print('%s split: Pareto front (peak fraction of one layer, work factor)' % kind)
        lo = 1e18
        for p, w, q, j0 in pts:
            if w < lo - 1e-9:
                lo = w
                print('   peak %.3f  work x%6.2f   q=%2d j0=%2d' % (p, w, q, j0))


if __name__ == '__main__':
    main()
