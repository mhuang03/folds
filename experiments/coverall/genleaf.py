"""genleaf.py: Lean lemmas `0 ≤ P N u v` on a leaf polyhedron from the LP supports."""
import sympy as sp
from gencell import lean_poly, Nn, uu, vv
import leaves as LV


def lean_lin(e):
    return lean_poly(e)


def hint(comb):
    """product term for linarith: comb = tuple of hypothesis indices."""
    if len(comb) == 0:
        return None
    t = 'h%d' % comb[0]
    for i in comb[1:]:
        t = 'mul_nonneg (%s) h%d' % (t, i)
    return t


def leaf_lemma(name, forms, polyname, P, supp, defname=None):
    hyps = ' '.join('(h%d : 0 ≤ %s)' % (i, lean_lin(f)) for i, f in enumerate(forms))
    hs = [hint(c) for c, _ in supp]
    hs = [h for h in hs if h is not None and ' ' in h]  # single hyps are already in context
    goal = '0 ≤ %s N u v' % defname if defname else '0 ≤ %s' % lean_poly(P)
    unfold = '  unfold %s\n' % defname if defname else ''
    return ('theorem %s_%s (N u v : ℚ) %s :\n    %s := by\n%s  linarith [%s]\n' %
            (name, polyname, hyps, goal, unfold, ', '.join(hs)))
