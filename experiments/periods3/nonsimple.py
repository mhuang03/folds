"""nonsimple.py: the vertex formula of ../periods2/local.py for NON-SIMPLE vertices with k + 1
tight rows of rank k (one linear dependency), as at the "cycle + pendant chain" vertices
(theta, ..., theta, theta/2, ...) of index 40, 120 at k = 8, where x_(s+2) = x_1/2 = x_(s+1)/2 makes
two halvings and the closing equality dependent: u_a - u_b = u_e.

Every class through v has as tangent cone one sign pattern eps of the k + 1 rows.  For a
consistent pattern one row r0 of the dependency is a combination of the others with sign
implied by them; dropping it, the cone is the eps-orthant of the remaining basis B, and all its
lattice points automatically satisfy r0 with its strictness (one of the two B-rows in the
relation is strict: an equality row, or a halving row on its open side).  So the cell term is
the simple-vertex term of local.py computed in the basis B.  Characters with some w_r = 0 belong
to edges of the class polytope, whose indices are not divisible by 40 (face lemma), so the
order-40/120 modes only see the characters with all w_r != 0.
"""
import sys
from fractions import Fraction as Fr
from itertools import product

sys.path.insert(0, '../periods2')
from local import tight_rows, solve, characters, side_sum, valid   # noqa: E402


def combo(rows, r0, basis):
    """coefficients c with rows[r0] = sum c_i rows[basis[i]] (exact)."""
    M = [list(rows[b][0]) for b in basis]
    MT = [list(col) for col in zip(*M)]
    return solve(MT, list(rows[r0][0]))


def vertex_modes_ns(v, eta=Fr(1, 10 ** 12)):
    k = len(v)
    R = tight_rows(v)
    assert len(R) == k + 1
    # the bases obtained by dropping one row, with the dropped row as a combination of the rest
    drops = []
    for drop in range(k + 1):
        basis = [r for r in range(k + 1) if r != drop]
        try:
            c = combo(R, drop, basis)
        except StopIteration:
            continue
        assert R[drop][1] == sum(ci * R[b][1] for ci, b in zip(c, basis))
        drops.append((drop, basis, c))
    modes = {}
    ncell = 0
    cache = {}
    for full in product((1, -1), repeat=k + 1):
        if any(R[r][2] == 'box0' and full[r] < 0 for r in range(k + 1)):
            continue
        if any(R[r][2] == 'box1' and full[r] > 0 for r in range(k + 1)):
            continue
        pick = None
        for drop, basis, c in drops:
            sg = {ci * full[r] for ci, r in zip(c, basis) if ci != 0}
            if len(sg) == 1:
                if sg.pop() != full[drop]:
                    pick = 'inconsistent'
                else:
                    pick = (drop, basis)
                break
        if pick is None or pick == 'inconsistent':
            continue
        drop, basis = pick
        eps = [full[r] for r in basis]
        M = [list(R[r][0]) for r in basis]
        b = [R[r][1] for r in basis]
        kinds = [R[r][2] for r in basis]
        y = solve(M, [b[i] + eps[i] * eta * (1 + Fr(i, 7)) for i in range(k)])
        if not valid(y):
            continue
        ncell += 1
        if drop not in cache:
            cache[drop] = characters(M)
        chars = cache[drop]
        D = len(chars)
        for w in chars:
            if any(x == 0 for x in w):
                continue
            p = 1
            for r in range(k):
                kd = kinds[r]
                closed = (eps[r] < 0) if kd == 'half' else (kd == 'box1')
                p *= side_sum(w[r], eps[r], closed)
            mode = sum(wr * br for wr, br in zip(w, b)) % 1
            modes[mode] = modes.get(mode, 0) + p / D
    return modes, ncell


if __name__ == '__main__':
    tot = {120: 0, 40: 0}
    for line in open('verts8_40.txt'):
        p = line.split()
        v = tuple(Fr(x) for x in p[1:])
        if len(tight_rows(v)) == len(v):
            continue
        modes, nc = vertex_modes_ns(v)
        out = {q: modes.get(Fr(-1, q) % 1, 0) for q in (120, 40)}
        print(p[0], '(' + ', '.join(p[1:]) + ')', 'cells', nc, ' A_120 =', out[120], ' A_40 =', out[40])
        for q in (120, 40):
            tot[q] += out[q]
    print('non-simple totals:', tot)
