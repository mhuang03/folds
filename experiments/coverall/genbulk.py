"""genbulk.py: the leaf theorems of the bulk covering (LP supports -> linarith hints).

python3 genbulk.py OUT.lean   (appends after the cell code of genlean.py)
"""
import sys
import sympy as sp
from gencell import lean_poly, Nn, uu, vv
import leaves as LV
import genlean as GLN

N, u, v = Nn, uu, vv


def nat_ineq(f):
    """linear form f (sympy, integer coeffs) >= 0  ->  Lean ℕ inequality string 'lhs ≤ rhs'."""
    p = sp.Poly(sp.expand(f), N, u, v)
    pos, neg = [], []
    const = 0
    for mon, c in zip(p.monoms(), p.coeffs()):
        c = int(c)
        if sum(mon) == 0:
            const = c
            continue
        var = 'NUV'[mon.index(1)].replace('U', 'u').replace('V', 'v')
        t = var if abs(c) == 1 else '%d * %s' % (abs(c), var)
        (pos if c > 0 else neg).append(t)
    if const > 0:
        pos.append(str(const))
    elif const < 0:
        neg.append(str(-const))
    lhs = ' + '.join(neg) if neg else '0'
    rhs = ' + '.join(pos) if pos else '0'
    return '%s ≤ %s' % (lhs, rhs)


def polys_of(cell):
    if cell == 'D':
        return [('D1', 'dP1'), ('D2', 'dP2'), ('D3', 'dP3')]
    if cell == 'B':
        return [('B1', 'bP1'), ('B2', 'bP2'), ('B3', 'bP3'), ('B4', 'bP4'), ('Bn', 'bP5')]
    sh = GLN.SHORT
    return [(k, 'k%s%s%s' % (cell, sh[k[:-1]], k[-1])) for k in
            ['chord8', 'bot8', 'botR8', 'amin8', 'chord9', 'bot9', 'botR9', 'amin9']]


def leaf_theorem(name):
    forms, cell = LV.LEAVES[name]
    res = LV.run(name, verbose=False)
    gh = ' '.join('(g%d : %s)' % (i, nat_ineq(f)) for i, f in enumerate(forms))
    out = 'theorem leaf_%s {N u v : ℕ} %s :\n' % (name, gh)
    concl = {'D': 'DPolys N u v', 'B': 'BPolys N u v'}.get(cell, 'Key%s N u v' % cell)
    out += '    %s := by\n' % concl
    for i, f in enumerate(forms):
        out += ('  have h%d : (0 : ℚ) ≤ %s := by\n    have h := (Nat.cast_le (α := ℚ)).mpr g%d; push_cast at h; linarith\n'
                % (i, lean_poly(f), i))
    pl = polys_of(cell)
    if cell in ('D', 'B'):
        out += '  refine ⟨%s⟩\n' % ', '.join('?_' for _ in pl)
    else:
        out += '  refine ⟨by omega, by omega, by omega, by omega, %s⟩\n' % ', '.join('?_' for _ in pl)
    for nm, dn in pl:
        deg, supp = res[nm]
        hs = []
        for comb, _ in supp:
            if len(comb) >= 2:
                t = 'h%d' % comb[0]
                for i in comb[1:]:
                    t = 'mul_nonneg (%s) h%d' % (t, i)
                hs.append(t)
        out += '  · unfold %s; linarith [%s]\n' % (dn, ', '.join(hs))
    return out + '\n'


if __name__ == "__main__":
    out = ''
    for nm in sys.argv[2:] or list(LV.LEAVES):
        out += leaf_theorem(nm)
    open(sys.argv[1], 'w').write(out)
