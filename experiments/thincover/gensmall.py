"""gensmall.py: the class u <= 3 by the old regions D0 (u = 2, 3), B2, B (u = 3): Lean lemmas
(hand-written skeletons, Handelman hints for each polynomial condition computed here).
python3 gensmall.py -> prints the Lean text (appended to Folds/ThinCoverShapes.lean by genall)."""
import sympy as sp
from gen import handelman, lean_poly, nat_ineq, save_cache

N, v = sp.symbols('N v')
V = [N, v]


def hints(P, forms):
    r = handelman(sp.expand(P), forms, V, 4)
    if r is None:
        raise RuntimeError('no certificate for %s' % sp.factor(P))
    out = []
    for comb in r[1]:
        if len(comb) >= 2:
            t = 'f%d' % comb[0]
            for i in comb[1:]:
                t = 'mul_nonneg (%s) f%d' % (t, i)
            out.append(t)
    return out


def lemma(name, doc, hyps, concl, pre, conds, extra_nat=()):
    """conds: list of (lean_tactic_prefix, P) with P >= 0 the polynomial (in ℤ) after zify."""
    forms = hyps + list(V)
    L = ['/-- %s -/' % doc]
    hs = ' '.join('(h%d : %s)' % (i, nat_ineq(h, V)) for i, h in enumerate(hyps))
    L.append('theorem %s {N v : ℕ} %s :\n    %s := by' % (name, hs, concl))
    for i, fm in enumerate(forms):
        L.append('  have f%d : (0 : ℤ) ≤ %s := by' % (i, lean_poly(fm, V).replace('ℚ', 'ℤ')))
        if i < len(hyps):
            L.append('    have h := (Nat.cast_le (α := ℤ)).mpr h%d; push_cast at h; linarith' % i)
        else:
            L.append('    positivity')
    for t in extra_nat:
        L.append('  ' + t)
    L.append('  ' + pre)
    for tac, P in conds:
        L.append('  · %s' % tac)
        L.append('    nlinarith [%s]' % ', '.join(hints(P, forms)))
    return '\n'.join(L) + '\n'


def main():
    out = []
    # u = 2, D0: 2 ≤ 2 ∧ 4 ≤ v ∧ 2 ≤ N ∧ 2(N+1+2)(v-2) + 2(2+1)N ≤ (2+1)(N+1-2)(v-2+1) ∧ 2((v-2)(v-2)+N) ≤ (N+1-2)(v-2+1)
    hy = [N - 301, v - 6, N - 2 * v - 3]
    c1 = 3 * (N - 1) * (v - 1) - (2 * (N + 3) * (v - 2) + 6 * N)
    c2 = (N - 1) * (v - 1) - 2 * ((v - 2) ** 2 + N)
    zt = 'zify [show 2 ≤ v by omega, show 2 ≤ N + 1 by omega]; push_cast'
    out.append(lemma('u2_D0', 'The line `u = 2`, `u\' ≥ 6`: region D0.', hy, 'ArithCover.RegionD0 N 2 v',
                     'refine ⟨le_refl _, by omega, by omega, ?_, ?_⟩', [(zt, c1), (zt, c2)]))
    # u = 3, D0: N >= 3v + 7, v >= 11
    hy = [N - 301, v - 11, N - 3 * v - 7]
    c1 = 4 * (N - 2) * (v - 1) - (3 * (N + 4) * (v - 2) + 12 * N)
    c2 = (N - 2) * (v - 1) - 3 * ((v - 2) ** 2 + N)
    zt = 'zify [show 2 ≤ v by omega, show 3 ≤ N + 1 by omega]; push_cast'
    out.append(lemma('u3_D0', 'The line `u = 3`, `u\' ≥ 11`, `N ≥ 3u\' + 7`: region D0.', hy, 'ArithCover.RegionD0 N 3 v',
                     'refine ⟨by norm_num, by omega, by omega, ?_, ?_⟩', [(zt, c1), (zt, c2)]))
    # u = 3, B2: 3v >= N + 7, 8v <= 3N + 2, 2v + 4 <= N
    hy = [N - 301, 3 * v - N - 7, 3 * N + 2 - 8 * v, N - 2 * v - 4]
    n = N + 2 - 2 * v
    c1 = 4 * (n - 1) - (N + 2)
    c2 = (N + 2 - 6) * n - 3 * (n * (n - 2) + (N + 2) + 1)
    c3 = (n - 1) * v - 2 * (N + 2)
    zt = ('(try rw [show (3 : ℕ) / 2 = 1 by norm_num] at *); zify [show 2 * v ≤ N + 2 by omega, '
          'show 1 ≤ N + 2 - 2 * v by omega, show 2 ≤ N + 2 - 2 * v by omega, show 2 * 3 ≤ 1 * (N + 2) by omega]; push_cast')
    out.append(lemma('u3_B2', 'The line `u = 3`, `N + 7 ≤ 3u\'`, `8u\' ≤ 3N + 2`: region B2.', hy, 'ArithCover.RegionB2 N 3 v',
                     'refine ⟨le_refl _, by omega, by omega, ?_, ?_⟩', [(zt, c2), (zt, c3)]))
    # u = 3, B: 8v >= 3N + 2, 2v + 5 <= N
    hy = [N - 301, 8 * v - 3 * N - 2, N - 2 * v - 5]
    c1 = (N + 2) - 4 * (n - 1)
    c2 = (N + 2) - 12
    c3 = (N + 2) * (n + 6) - (3 * (7 * n - 6) + 12 * (2 * n + (N + 2) - 1))
    zt = ('(try rw [show (3 : ℕ) / 2 = 1 by norm_num] at *); zify [show 2 * v ≤ N + 2 by omega, '
          'show 1 ≤ N + 2 - 2 * v by omega, show 2 * 3 ≤ (2 * 3 + 1) * (N + 2 - 2 * v) by omega, '
          'show 1 ≤ 2 * (N + 2 - 2 * v) + (N + 2) by omega]; push_cast')
    out.append(lemma('u3_B', 'The line `u = 3`, `8u\' ≥ 3N + 2`: region B.', hy, 'ArithCover.RegionB N 3 v',
                     'refine ⟨le_refl _, by omega, by omega, by omega, ?_, by omega⟩', [(zt, c3)]))
    save_cache()
    return '\n'.join(out)


if __name__ == '__main__':
    print(main())
