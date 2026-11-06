"""genlean.py: generate the Lean code of the bulk covering (cells A, B4, B1; leaves; bulk theorem).

python3 genlean.py OUT.lean
"""
import sys
import sympy as sp
from gencell import keys, fam, lean_poly, Nn, uu, vv
import leaves as LV
import genleaf as GL

SHORT = {'chord': 'c', 'bot': 'b', 'botR': 'r', 'amin': 'a'}
CELLS = {
    'A': (('Z', 1, 1, 1, 4), (1, 1, 0, 1), {Nn: 3001, uu: 800, vv: 900}),
    'B4': (('Z', 1, 2, 1, 4), (2, 1, 1, 1), {Nn: 3001, uu: 500, vv: 1200}),
    'B1': (('Z', 1, 2, 1, 1), (2, 1, 1, 1), {Nn: 3001, uu: 700, vv: 1200}),
}


def cell_defs(cname):
    cell, (p, q, p2, q2), sample = CELLS[cname]
    ks, Dl, v8, v9 = keys(*cell)
    defs = []
    info = {}
    for nm, P, n, den, sig, ce in ks:
        if den.subs(sample) < 0:
            n, den, P = -n, -den, -P
        dn = 'k%s%s%s' % (cname, SHORT[nm[:-1]], nm[-1])
        info[nm] = (dn, P, sp.factor(den))
        defs.append('/-- Key polynomial `%s` of cell %s. -/\ndef %s (N u v : ℚ) : ℚ :=\n  %s\n' %
                    (nm, cname, dn, lean_poly(P)))
    return defs, info


def den_lean(den):
    s = sp.sstr(den).replace('**', '^')
    return s


def cell_lean(cname):
    cell, (p, q, p2, q2), sample = CELLS[cname]
    edge = cell[4]
    defs, info = cell_defs(cname)
    out = '\n'.join(defs)
    pn = ['chord8', 'bot8', 'botR8', 'amin8', 'chord9', 'bot9', 'botR9', 'amin9']
    keyconj = ' ∧\n  '.join('0 ≤ %s N u v' % info[k][0] for k in pn)
    if edge == 4:
        lin = '2 ≤ u ∧ u ≤ v ∧ %d * (u + 1) ≤ %d * v ∧ 2 * u + 5 ≤ N' % (p, q)
    else:
        lin = '2 ≤ u ∧ u ≤ v ∧ %d * (v + 1) ≤ %d * u ∧ 2 * u + 5 ≤ N' % (q, p)
    out += ('\n/-- Cell %s: family `Z`, orientation `(u\', u)`, `w₁ = (%d, %d)`, %s-edge. -/\n'
            'def Key%s (N u v : ℕ) : Prop :=\n  %s ∧\n  %s\n' %
            (cname, p, q, 'f4' if edge == 4 else 'f1', cname, lin, keyconj))
    d8 = den_lean(info['chord8'][2])
    d9 = den_lean(info['chord9'][2])
    Kp = '((N : ℚ) + 2) * %d' % p
    Kq = '((N : ℚ) + 2) * %d' % q
    if edge == 4:
        Dl = '(%s((v : ℚ) + 1) - %su)' % ('' if q == 1 else '%d * ' % q, '' if p == 1 else '%d * ' % p)
        s8 = '((N : ℚ) + 1) / 2 - 1 - %s / (v + 1)' % Kp
        s9 = '((((N : ℚ) + 1) / 2 - 1) * (u + 1) - %s - 1) / u - 1' % Kq
        S3 = '(σ1 - ((N : ℚ) + 2) / %s)' % Dl
        hc = '0 ≤ (%s * (v + 1) - 1 + %s) * (u + 1) - ((%s + 1) * u + 1 + %s) * v - v * (u + 1)' % (S3, Kp, S3, Kq)
        ha = '(2 : ℚ) * ((N : ℚ) + 2) ≤ %s * (v + 1) + 0 - 1' % S3
        hb = '(v : ℚ) + 1 ≤ %s' % S3
        hr = '(u : ℚ) + 1 ≤ %s' % S3
        lemma = 'parOK_edge4'
        sig3 = '(σ3 := σ1 - ((N : ℚ) + 2) / %s)' % Dl
        sig1 = '(σ1 := σ1)'
        regs = ('(by push_cast; linarith)', )
    else:
        Dl = '(%s((u : ℚ) + 1) - %sv)' % ('' if p == 1 else '%d * ' % p, '' if q == 1 else '%d * ' % q)
        s8 = '((((N : ℚ) + 1) / 2 - 1) * (v + 1) - %s - 1) / v - 1' % Kp
        s9 = '((N : ℚ) + 1) / 2 - 1 - %s / (u + 1)' % Kq
        S3 = '(σ1 - ((N : ℚ) + 2) / %s)' % Dl
        hc = '0 ≤ (%s * (u + 1) - 1 + %s) * (v + 1) - ((%s + 1) * v + 1 + %s) * u - u * (v + 1)' % (S3, Kq, S3, Kp)
        ha = '(2 : ℚ) * ((N : ℚ) + 2) ≤ (%s + 1) * v + 0' % S3
        hb = '(v : ℚ) + 1 ≤ %s' % S3
        hr = '(u : ℚ) + 1 ≤ %s' % S3
        lemma = 'parOK_edge1'
        sig3 = '(τ1 := σ1 - ((N : ℚ) + 2) / %s)' % Dl
        sig1 = '(τ3 := σ1)'
    D8, D9 = 'hD8', 'hD9'

    def cl(k, var):
        dn = info[k][0]
        base = 'nonneg_of_cleared %s %s (by rw [hs%s]; unfold %s; field_simp; ring)' % (
            'hD' + var, {'chord': 'c', 'bot': 'b', 'botR': 'r', 'amin': 'a'}[k[:-1]] + var, var, dn)
        return base if k.startswith('chord') else 'sub_nonneg.mp (%s)' % base

    nonzero = []
    for dd in (info['chord8'][2], info['chord9'][2]):
        for fct in sp.Mul.make_args(dd):
            if fct.is_number:
                continue
            nonzero.append(fct)
    out += '''
theorem parOK_of_key{c} {{N u v : ℕ}} (h : Key{c} N u v) : ParOK (consZ N v u) := by
  obtain ⟨hu, huv, hv, hN, c8, b8, r8, a8, c9, b9, r9, a9⟩ := h
  have huq : (2 : ℚ) ≤ u := by exact_mod_cast hu
  have huvq : (u : ℚ) ≤ v := by exact_mod_cast huv
  have hvq : ({lhsv} : ℚ) ≤ {rhsv} := by exact_mod_cast hv
  have hNq : 2 * (u : ℚ) + 5 ≤ N := by exact_mod_cast hN
  have hD : (0 : ℚ) < {Dl} := by linarith
  have hv1 : (0 : ℚ) < v + 1 := by linarith
  have hu1 : (0 : ℚ) < u + 1 := by linarith
  have hv0 : (0 : ℚ) < v := by linarith
  have hu0 : (0 : ℚ) < u := by linarith
  have hD8 : (0 : ℚ) < {d8} := by nlinarith
  have hD9 : (0 : ℚ) < {d9} := by nlinarith
  set s8 : ℚ := {s8} with hs8
  set s9 : ℚ := {s9} with hs9
  have key : ∀ σ1 : ℚ, σ1 ≤ s8 → σ1 ≤ s9 → {hc} →
      {hb} → {hr} → {ha} → ParOK (consZ N v u) := by
    intro σ1 h8 h9 hc hb hr ha
    unfold consZ
    refine {lemma} (K := N + 2) (L := v) (R := u) (p := {p}) (q := {q}) (p2 := {p2}) (q2 := {q2})
      (Δ := {Dl}) (s0 := ((N : ℚ) + 1) / 2) {sig1}
      {sig3} (by omega) (by omega) (by omega) (by norm_num)
      (by norm_num) (by norm_num) (by push_cast; ring) hD (by push_cast; linarith) (s0_le_Z N)
      (by push_cast; linarith) (by linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; ring) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith)
  rcases le_total s8 s9 with hle | hle
  · apply key s8 le_rfl hle
    · exact {c8}
    · exact {b8}
    · exact {r8}
    · exact {a8}
  · apply key s9 hle le_rfl
    · exact {c9}
    · exact {b9}
    · exact {r9}
    · exact {a9}
'''.format(c=cname, Dl=Dl, d8=d8, d9=d9, s8=s8, s9=s9, hc=hc, hb=hb, hr=hr, ha=ha, lemma=lemma,
           p=p, q=q, p2=p2, q2=q2, sig1=sig1, sig3=sig3,
           lhsv=('%d * ((u : ℚ) + 1)' % p) if edge == 4 else ('%d * ((v : ℚ) + 1)' % q),
           rhsv=('%d * (v : ℚ)' % q) if edge == 4 else ('%d * (u : ℚ)' % p),
           c8=cl('chord8', '8'), b8=cl('bot8', '8'), r8=cl('botR8', '8'), a8=cl('amin8', '8'),
           c9=cl('chord9', '9'), b9=cl('bot9', '9'), r9=cl('botR9', '9'), a9=cl('amin9', '9'))
    return out


HEADER = '''import Folds.CoverAll

namespace Folds.CoverAll
open Folds.Residual

theorem nonneg_of_cleared {E P D : ℚ} (hD : 0 < D) (hP : 0 ≤ P) (hE : E * D = P) : 0 ≤ E := by
  by_contra h
  push Not at h
  have : E * D < 0 := mul_neg_of_neg_of_pos h hD
  linarith

theorem s0_le_Z (N : ℕ) : ((N : ℚ) + 1) / 2 ≤ (((N + 2) / 2 : ℕ) : ℚ) := by
  have h : N + 1 ≤ 2 * ((N + 2) / 2) := by omega
  have : ((N : ℚ) + 1) ≤ 2 * (((N + 2) / 2 : ℕ) : ℚ) := by exact_mod_cast h
  linarith

'''

if __name__ == "__main__":
    out = HEADER
    for c in sys.argv[2:] or ['A', 'B4', 'B1']:
        out += cell_lean(c) + '\n'
    out += 'end Folds.CoverAll\n'
    open(sys.argv[1], 'w').write(out)
