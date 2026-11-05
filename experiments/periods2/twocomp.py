"""twocomp.py S1 S2: the order-Q Fourier component of c_0(T(N,K)), K = S1 + S2 + 2, carried by
the vertices made of two disjoint halving cycles (periods S1, S2), Q = lcm(2^S1 - 1, 2^S2 - 1).
For (2,5): Q = 93, for (3,4): Q = 105 -- moduli that divide B(9) but no single 2^a(2^s - 1)
with a + s <= 8.  By the face lemma these vertices are the ONLY carriers of order-Q modes at
codimension 9, so the total below is the exact order-Q part of c_0(T(N,9)).
Uses the vertex formula of local.py (Brion + characters; all character coordinates are nonzero
for the order-Q characters).  Prints, per valid vertex, the coefficient of e(-N/Q), the order
type of its (unique) valid cell, and the total.  Writes the order types to twocomp_S1S2.txt
for an independent Normaliz check (check93.py)."""
import sys
from fractions import Fraction as Fr
from math import gcd
from itertools import combinations
from twocycle import orbit_points, accidental, check
from local import vertex_modes, local_cells, solve


def order_type(y):
    s = sorted(y)
    return tuple(s.index(v) + 1 for v in y)


def run(S1, S2):
    QA, QB = 2 ** S1 - 1, 2 ** S2 - 1
    Q = QA * QB // gcd(QA, QB)
    K = S1 + S2 + 2
    OA, OB = orbit_points(S1), orbit_points(S2)
    target = Fr(-1, Q) % 1
    tot = 0
    types = []
    nv = 0
    for vA, bA in OA:
        for vB, bB in OB:
            if accidental(vA, vB):
                continue
            for posA in combinations(range(K), S1 + 1):
                rest = [p for p in range(K) if p not in posA]
                for posB in combinations(rest, S2 + 1):
                    seq = [None] * K
                    for p, x in zip(posA, vA):
                        seq[p] = x
                    for p, x in zip(posB, vB):
                        seq[p] = x
                    if not check(seq, [(list(posA), bA), (list(posB), bB)]):
                        continue
                    v = tuple(seq)
                    modes, nc = vertex_modes(v)
                    M, b, kinds, cells = local_cells(v)
                    eta = Fr(1, 10 ** 12)
                    for eps in cells:
                        y = solve(M, [b[r] + eps[r] * eta * (1 + Fr(r, 7)) for r in range(K)])
                        types.append(order_type(y))
                    c = modes.get(target, 0)
                    nv += 1
                    tot += c
                    print(', '.join(map(str, v)), ' cells', nc, ' A =', c, flush=True)
    print(f'S1={S1} S2={S2}: K={K}, Q={Q}: {nv} valid vertices, {len(types)} cells; '
          f'total coefficient of e(-N/Q) in c_0 = {tot}')
    with open(f'twocomp_{S1}{S2}.txt', 'w') as f:
        for t in types:
            f.write(''.join(map(str, t)) + '\n')
    return tot


if __name__ == '__main__':
    run(int(sys.argv[1]), int(sys.argv[2]))
