"""gend1.py: the d = 1 line (u' = u + 1) by the slice X0, orientation (u', u), a = c + 1, w1 = (1, 0):
corners (s0, c0), (s0 + 1, c0), (s1, c0 + 1), (s1 + 1, c0 + 1) with
    c0 = (2u - 5)/6,  s0 = (N(2u + 1) + 6)/(6(u + 2)),  s1 = N(2u + 1)/(6(u - 1)).
Generates the Lean lemma `d1_line` (32 cleared polynomial inequalities with LP hints).
python3 gend1.py OUT.lean"""
import sys
import sympy as sp
from handel import certify_exact, certify, products
from gencell import lean_poly

N, u = sp.symbols('N u')
S = N / 2          # lower bound of smax = (N + 1)/2 (floor)
K, L, R, al, be, amin, p, j = N, u + 1, u - 2, 0, 1, 1, 1, 1
CONS = [(-L, p * K, j * K - al), (L + 1, -p * K, al - 1 - j * K), (-R, K, -be), (R + 1, -K, be - 1),
        (1, 0, -2), (1, 0, -R), (-1, 0, S), (0, p, j - amin)]
c0 = (2 * u - 5) / sp.Integer(6)
s0 = (N * (2 * u + 1) + 6) / (6 * (u + 2))
s1 = N * (2 * u + 1) / (6 * (u - 1))
CORNERS = [(s0, c0), (s0 + 1, c0), (s1, c0 + 1), (s1 + 1, c0 + 1)]
FORMS = [u - 5, N - 3 * u - 21, N - 301, u, N]


def lean_q(e):
    rep = {N: sp.Symbol('Nq'), u: sp.Symbol('uq')}
    s = sp.sstr(e.subs(rep)).replace('**', '^')
    return s.replace('Nq', '(N : ℚ)').replace('uq', '(u : ℚ)')


def main(out):
    lines = []
    lines.append('/-- The line `u\' = u + 1` (`d = 1`), `5 ≤ u`, `3u + 21 ≤ N`: the slice `a = c + 1` of `X(N, s, 0)` in\n'
                 'orientation `(u\', u)` contains the parallelogram with sides `(1, 0)` and `(δ, 1)` at\n'
                 '`c₀ = (2u - 5)/6`, `s₀ = (N(2u + 1) + 6)/(6(u + 2))`, `s₁ = N(2u + 1)/(6(u - 1))`. -/')
    hyps = []
    lemmas = []
    k = 0
    for i, (A, C, D) in enumerate(CONS):
        for kk, (s, c) in enumerate(CORNERS):
            E = sp.together(A * s + C * c + D)
            n, den = sp.fraction(E)
            n = sp.expand(n)
            # make den manifestly positive
            if den.subs({N: 1001, u: 200}) < 0:
                n, den = -n, -den
            if n.is_number:
                assert n >= 0
            r = certify_exact(n, FORMS, (N, u), 4)
            if r is None:
                print('FAIL', i, kk, n)
                continue
            deg, supp = r
            hs = []
            for comb in supp:
                if len(comb) >= 2:
                    t = 'f%d' % comb[0]
                    for ii in comb[1:]:
                        t = 'mul_nonneg (%s) f%d' % (t, ii)
                    hs.append(t)
            lemmas.append((i, kk, E, n, sp.factor(den), hs))
    return lemmas


def lean(ls):
    sq = {k: lean_q(e) for k, e in (('s0', s0), ('c0', c0), ('s1', s1))}
    out = []
    out.append("/-- The line `u' = u + 1` (`d = 1`), `5 ≤ u`, `3u + 21 ≤ N`: the slice `a = c + 1` of `X(N, s, 0)`")
    out.append("in orientation `(u', u)` contains the parallelogram with sides `(1, 0)`, `(δ, 1)` at")
    out.append("`c₀ = (2u - 5)/6`, `s₀ = (N(2u + 1) + 6)/(6(u + 2))` and `s₁ = N(2u + 1)/(6(u - 1))` (`gend1.py`). -/")
    out.append("theorem d1_line {N u : ℕ} (hN : 301 ≤ N) (hu : 5 ≤ u) (h3 : 3 * u + 21 ≤ N) :")
    out.append("    RegionSL N u (u + 1) := by")
    out.append("  have huq : (5 : ℚ) ≤ u := by exact_mod_cast hu")
    out.append("  have f0 : (0 : ℚ) ≤ (u : ℚ) - 5 := by linarith")
    out.append("  have f1 : (0 : ℚ) ≤ (N : ℚ) - 3 * u - 21 := by")
    out.append("    have h := (Nat.cast_le (α := ℚ)).mpr h3; push_cast at h; linarith")
    out.append("  have f2 : (0 : ℚ) ≤ (N : ℚ) - 301 := by")
    out.append("    have h := (Nat.cast_le (α := ℚ)).mpr hN; push_cast at h; linarith")
    out.append("  have f3 : (0 : ℚ) ≤ (u : ℚ) := by positivity")
    out.append("  have f4 : (0 : ℚ) ≤ (N : ℚ) := by positivity")
    out.append("  have hS : (N : ℚ) / 2 ≤ (((N + 1) / 2 : ℕ) : ℚ) := by")
    out.append("    have h : N ≤ 2 * ((N + 1) / 2) := by omega")
    out.append("    have : (N : ℚ) ≤ 2 * (((N + 1) / 2 : ℕ) : ℚ) := by exact_mod_cast h")
    out.append("    linarith")
    out.append("  have hR : ((u - 2 : ℕ) : ℚ) = (u : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num")
    out.append("  have hd1 : (0 : ℚ) < %s := by linarith" % lean_q(6 * (u + 2)))
    out.append("  have hd2 : (0 : ℚ) < %s := by linarith" % lean_q(6 * (u - 1)))
    out.append("  have hne1 : (u : ℚ) - 1 ≠ 0 := by linarith")
    out.append("  have hne2 : (u : ℚ) + 2 ≠ 0 := by linarith")
    out.append("  have hne3 : %s ≠ 0 := by linarith" % lean_q(6 * (u - 1)))
    out.append("  have hne4 : %s ≠ 0 := by linarith" % lean_q(6 * (u + 2)))
    out.append("  refine Or.inr (Or.inl ⟨by omega, 1, 1, Or.inl ⟨%s, %s, %s - (%s), 1, 0, 0, 1, by norm_num, ?_⟩⟩)"
               % (sq['s0'], sq['c0'], sq['s1'], sq['s0']))
    out.append("  simp only [sliceCons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,")
    out.append("    Aff.eval, hR]")
    out.append("  push_cast")
    out.append("  refine ⟨%s⟩" % ', '.join('⟨?_, ?_, ?_, ?_⟩' for _ in range(8)))
    byk = {(i, kk): (E, n, den, hs) for i, kk, E, n, den, hs in ls}
    for i in range(8):
        for kk in range(4):
            E, n, den, hs = byk[(i, kk)]
            dl = sp.sstr(den).replace('**', '^')
            dlq = lean_q(den)
            dpos = {lean_q(6 * (u + 2)): 'hd1', lean_q(6 * (u - 1)): 'hd2'}.get(dlq, '(by norm_num)')
            if i == 6:
                # smax: prove N/2 - s >= 0, then use hS
                sk, ck = CORNERS[kk]
                Ek = lean_q(N / 2 - sk)
                out.append("  · have h := nonneg_of_cleared (E := %s) (D := %s) (P := %s) %s" % (Ek, dlq, lean_q(n), dpos))
                out.append("      (by linarith [%s]) (by field_simp; ring)" % ', '.join(hs))
                out.append("    have hS' := hS")
                out.append("    ring_nf at h hS' ⊢; linarith")
            else:
                out.append("  · refine nonneg_of_cleared (D := %s) (P := %s) %s (by linarith [%s]) ?_" % (dlq, lean_q(n), dpos, ', '.join(hs)))
                out.append("    field_simp; ring")
    return '\n'.join(out) + '\n'


if __name__ == "__main__":
    ls = main(None)
    open(sys.argv[1], 'w').write(lean(ls))
