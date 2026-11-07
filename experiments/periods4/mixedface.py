"""mixedface.py S A [F] [all|main]: the mixed order q = 2^A (2^S - 1) (m = S + A + 1 structured
points) in c_F(T(N, m + F)) with F = 0 or 1 free point, by the local face formula
(../periods2 section 1): for every cycle + pendant chain structure, every time order of the
structured points, every gap and every z-interval of the free point, the valid cell (unique by
the column rule) is found and its weight (the length of the z-interval) is added to that cell's
term (1/q) prod_r F_r(w_r), w the character of the structured rows with mode -1/q.
Output: coefficient of e(-N/q) in c_F times F!, total and per structure family (u, j).
'main' restricts to the main structure (u = +-1, j = 0)."""
import sys
from fractions import Fraction as Fr
from mixed import (tight, column_options, rowvec, nullvec, det, char_at, F as Ffac,
                   structures, thetas)
from census import ujof


def all_orders(orb, j, z):
    """all time orders of the structured points (cycle in order, chain in order, z_1 after t_j)."""
    s, a = len(orb) - 1, len(z)

    def rec(ci, zi, y, lab):
        if ci == s + 1 and zi == a:
            yield tuple(y), tuple(lab)
            return
        if ci <= s:
            yield from rec(ci + 1, zi, y + [orb[ci]], lab + [('c', ci)])
        if zi < a and (zi > 0 or ci > j):
            yield from rec(ci, zi + 1, y + [z[zi]], lab + [('z', zi)])
    yield from rec(0, 0, [], [])


def cell_term(y, R, cell, q):
    k = len(y)
    vecs = [rowvec(r, k) for r in R]
    if len(R) == k:
        basis = list(range(k))
    else:
        lam = nullvec([vecs[r][0] for r in range(k + 1)])
        sig = {}
        for r, l in enumerate(lam):
            if l:
                sig[r] = (1 if l > 0 else -1) * (-1 if cell[r] in ('le', 'lt') else 1)
        pos = [r for r in sig if sig[r] > 0]
        neg = [r for r in sig if sig[r] < 0]
        if not pos or not neg:
            return None
        drop = pos[0] if len(pos) == 1 else neg[0]
        basis = [r for r in range(k + 1) if r != drop]
    M = [vecs[r][0] for r in basis]
    assert abs(det(M)) == q
    w = char_at(M, y, q)
    t = 1 / q
    for idx, r in enumerate(basis):
        t *= Ffac(R[r], cell[r], w[idx])
    return t


def breakpoints(vals):
    B = {Fr(0), Fr(1)}
    for v in vals:
        for b in (v, v / 2, (1 + v) / 2, 2 * v, 2 * v - 1):
            if 0 <= b <= 1:
                B.add(b)
    return sorted(B)


def structure_sum(orb, j, z, q, f):
    """sum over time orders / free configurations of weight * term; also the exact weights."""
    tot = 0
    weights = {}
    reps = {}
    for ys, lab in all_orders(orb, j, z):
        m = len(ys)
        Rs = tight(ys)
        if f == 0:
            confs = [(ys, None, Fr(1))]
        else:
            Bp = breakpoints(ys)
            confs = []
            for p in range(m + 1):
                for x0, x1 in zip(Bp, Bp[1:]):
                    zz = (x0 + x1) / 2
                    confs.append((ys[:p] + (zz,) + ys[p:], p, x1 - x0))
        for y, p, length in confs:
            R = tight(y)
            if len(R) != len(Rs):
                continue
            cols = [column_options(y, R, c) for c in range(len(y))]
            if any(not c for c in cols):
                continue
            cells = [{}]
            for c in cols:
                cells = [{**a, **b} for a in cells for b in c]
            # map rows of y to rows of ys (remove the free point)
            def red(i):
                return i if p is None or i < p else i - 1
            for cell in cells:
                key = tuple(sorted(((lab[red(R[r][0])], lab[red(R[r][1])], R[r][2], R[r][3]), sd)
                                   for r, sd in cell.items()))
                if key not in reps:
                    cs = {}
                    for r, sd in cell.items():
                        rr = (red(R[r][0]), red(R[r][1]), R[r][2], R[r][3])
                        cs[Rs.index(rr)] = sd
                    reps[key] = cell_term(ys, Rs, cs, q)
                if reps[key] is None:
                    continue
                weights[key] = weights.get(key, 0) + length
    for key, wt in weights.items():
        tot += wt * reps[key]
    return tot, weights


if __name__ == '__main__':
    s, a = int(sys.argv[1]), int(sys.argv[2])
    f = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    mode = sys.argv[4] if len(sys.argv) > 4 else 'all'
    D = 2 ** s - 1
    q = 2 ** a * D
    total = 0
    fam = {}
    for theta in thetas(s, D):
        for orb, j, z in structures(s, a, theta):
            u, jj = ujof({'q': q, 'z': z, 'j': j}, s, a)
            if mode == 'main' and not (abs(u) == 1 and j == 0):
                continue
            t, W = structure_sum(orb, j, z, q, f)
            if t != 0:
                total += t
                key = (abs(u), j)
                fam[key] = fam.get(key, 0) + t
                if mode == 'main':
                    for kk, wt in W.items():
                        print('   weight', wt, kk)
    for key in sorted(fam, key=lambda kk: -abs(fam[kk]))[:12]:
        print(f'  |u|={key[0]} j={key[1]}: {fam[key]:.8f}')
    print(f'(s,a)=({s},{a}) m={s + a + 1} f={f} q={q}: coefficient of e(-N/q) in c_{f} (x {f}!) = {total}')
