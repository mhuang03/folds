"""genasm.py: Folds/ThinCoverSmall.lean (old regions on u <= 3, gensmall.py) and the assembly
Folds/ThinCover.lean (the case analysis of ThinCover and the final theorems).
python3 genasm.py"""
import os
import sympy as sp
import pieces as PC
import gensmall
from gen import lean_nat
from genall import HEADER, FOOTER, ROOT

N, w = PC.N, PC.w


def strip_case(e):
    a, b = PC.strip_shift(e)
    code, umin = PC.STRIP[e]
    nm = 'strip%s' % (('m%d' % -e) if e < 0 else str(e))
    vstr = lean_nat(2 * w + b, [N, w])
    L = []
    L.append('  · -- e = %d' % e)
    L.append('    by_cases hm : %d ≤ u' % umin)
    if a > 0:
        L.append('    · obtain ⟨w, rfl⟩ : ∃ w, u = w + %d := ⟨u - %d, by omega⟩' % (a, a))
        L.append('      obtain rfl : v = %s := by omega' % vstr)
    else:
        L.append('    · obtain rfl : v = %s := by omega' % vstr.replace('w', 'u'))
    L.append('      exact p2_SL (%s (by omega) (by omega) (by omega) (by omega) (by omega))' % nm)
    small = [us for us in range(4, umin) if us + e >= 10]
    if not small:
        L.append('    · omega')
    else:
        L.append('    · have hu4 : u < %d := by omega' % umin)
        L.append('      interval_cases u')
        for us in small:
            L.append('      · obtain rfl : v = %d := by omega' % (2 * us + e))
            L.append('        exact p2_SL (sshape_%d_%d hN (by omega))' % (us, 2 * us + e))
        nimp = len([us for us in range(4, umin) if us + e < 10])
        for _ in range(nimp):
            L.append('      · omega')
    return '\n'.join(L)


DIAG_SMALL = {0: [(4, 'p2_SL (shape_4_4 hN)'), (5, 'p2_S ⟨hN, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩')],
              3: [(4, 'p2_SL (shape_4_7 hN)'), (5, 'p2_SL (shape_5_8 hN)')],
              6: [(4, 'p2_SL (shape_4_10 hN)'), (5, 'p2_SL (shape_5_11 hN)')],
              8: [(4, 'p2_SL (shape_4_12 hN)'), (5, 'p2_SL (shape_5_13 hN)'), (6, 'p2_SL (shape_6_14 hN)'),
                  (7, 'p2_SL (shape_7_15 hN)')],
              9: [(4, 'p2_SL (shape_4_13 hN)')]}


def diag_case(d):
    L = ['  · -- d = %d' % d]
    if d == 1:
        L += ['    by_cases h5 : 5 ≤ u',
              '    · by_cases hc : N ≤ 3 * u + 3',
              '      · exact p2_S ⟨hN, Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩)))⟩',
              '      · exact p2_SL (d1_corner hN h5 (by omega) (by omega))',
              '    · obtain rfl : u = 4 := by omega',
              '      exact p2_SL (shape_4_5 hN)']
        return '\n'.join(L)
    code, umin = PC.DIAG[d]
    L.append('    by_cases hm : %d ≤ u' % umin)
    L.append('    · exact p2_SL (diag%d hN hm (by omega))' % d)
    if umin == 4:
        L.append('    · omega')
    else:
        L.append('    · have hu' + ' : u < %d := by omega' % umin)
        L.append('      interval_cases u')
        for us, t in DIAG_SMALL[d]:
            L.append('      · exact %s' % t)
    return '\n'.join(L)


ASM = r'''import Folds.ThinCoverDiag
import Folds.ThinCoverStripA
import Folds.ThinCoverStripB
import Folds.ThinCoverStripC
import Folds.ThinCoverShapes
import Folds.ThinCoverSmall
import Folds.ThinCoverClusterAsm
import Folds.ThinCoverKernel

/-!
# The thin sets: `ThinCover N` (`N ≥ 1000`), `Residual2 N` (`N > 300`), Conjecture C for all `N`

`experiments/thincover/PROOFS.txt`.  The thin sets of `CoverAll.Thin` (minus the line `d1_line`) are
covered piece by piece:

* `u ≤ 3` (`small_cover`): the old regions `D0` (`u = 2`; `u = 3`, `N ≥ 3u' + 7`), `B2`, `B`
  (`u = 3`, `u' > N/3`), `RegionS` and two slice shapes;
* the diagonal lines `u' = u + d`, `d ≤ 9` (`diag_cover`): one slice certificate per line
  (side `(1, 0)`, explicit corners linear/rational in `(N, u)`), fixed shapes for small `u`, the corner
  `3u + 4 ≤ N ≤ 3u + 20` of `d = 1` (side `(3, 1)`);
* the strip `u' = 2u + e`, `-12 ≤ e ≤ 15` (`strip_cover`): one slice certificate per line (split
  along `N/u` where needed), finitely many shapes for small `u`;
* the cluster box: for `N ≥ 1000` (`cluster_cover`) parallelogram certificates in the witness polygon
  (`RegionPF`) on polyhedral pieces of `(N, u, u')`; for `301 ≤ N < 1000` a kernel check that every
  pair of the box passes `dirAny` (`clCheck_small`), so `Residual2 N` holds there directly.

Every certificate condition is a polynomial inequality on a polyhedron, proven by `linarith` with
products of the defining linear forms (a Handelman-type certificate found by LP).
-/

set_option maxHeartbeats 1000000

namespace Folds
namespace ThinCover

open Residual CoverAll Live2 Live8 ArithCover

theorem p2_SL {N u v : ℕ} (h : RegionSL N u v) : Proven2 N u v := Or.inr (Or.inr (Or.inl h))
theorem p2_PF {N u v : ℕ} (h : RegionPF N u v) : Proven2 N u v := Or.inr (Or.inl h)
theorem p2_S {N u v : ℕ} (h : RegionS N u v) : Proven2 N u v := Or.inr (Or.inr (Or.inr h))

/-- The class `u ≤ 3`. -/
theorem small_cover {N u v : ℕ} (hN : 301 ≤ N) (h2 : 2 ≤ u) (h3 : u ≤ 3) (huv : u ≤ v)
    (ht : u + 2 * v + 1 ≤ N) (hp : (u + (N + 1 - v)) % 2 = 1) (hs : ¬ Special N u v) :
    Proven2 N u v := by
  unfold Special at hs
  interval_cases u
  · by_cases hv : v ≤ 5
    · exact p2_S ⟨hN, Or.inl ⟨rfl, by omega⟩⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (u2_D0 hN (by omega) (by omega))))))
  · by_cases hv : v ≤ 8
    · exact p2_S ⟨hN, Or.inr (Or.inl ⟨rfl, by omega, hv⟩)⟩
    by_cases hv' : v ≤ 10
    · have : v = 9 ∨ v = 10 := by omega
      rcases this with rfl | rfl
      · exact p2_SL (shape_3_9 hN)
      · exact p2_SL (shape_3_10 hN)
    by_cases hm : 3 * v + 7 ≤ N
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (u3_D0 hN (by omega) hm)))))
    by_cases hm' : N + 7 ≤ 3 * v
    · by_cases hb : 8 * v ≤ 3 * N + 2
      · exact Or.inl (Or.inr (Or.inl (u3_B2 hN hm' hb (by omega))))
      · exact Or.inl (Or.inl (u3_B hN (by omega) (by omega)))
    · exact p2_S ⟨hN, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))⟩

/-- The diagonal lines `u' = u + d`, `d ≤ 9`, `u ≥ 4` (without the line `d1_line`). -/
theorem diag_cover {N u v : ℕ} (hN : 301 ≤ N) (hu : 4 ≤ u) (huv : u ≤ v) (hv : v ≤ u + 9)
    (ht : u + 2 * v + 1 ≤ N) (hr : ¬ (v = u + 1 ∧ 5 ≤ u ∧ 3 * u + 21 ≤ N)) : Proven2 N u v := by
  obtain ⟨d, rfl⟩ : ∃ d, v = u + d := ⟨v - u, by omega⟩
  have hd : d ≤ 9 := by omega
  interval_cases d
%DIAG%

/-- The strip `u' = 2u + e`, `-12 ≤ e ≤ 15`, `N ≤ 8u + 320` (outside the diagonal strip). -/
theorem strip_cover {N u v : ℕ} (hN : 301 ≤ N) (hu : 4 ≤ u) (hd : u + 10 ≤ v) (h1 : 2 * u ≤ v + 12)
    (h2 : v ≤ 2 * u + 15) (h3 : N ≤ 8 * u + 320) (ht : u + 2 * v + 1 ≤ N) : Proven2 N u v := by
  obtain ⟨k, hk⟩ : ∃ k, v + 12 = 2 * u + k := ⟨v + 12 - 2 * u, by omega⟩
  have hk' : k ≤ 27 := by omega
  interval_cases k
%STRIP%

/-- The thin sets outside the cluster box are in `Proven2`; the rest lies in the cluster box. -/
theorem thin_split {N u v : ℕ} (hN : 301 ≤ N) (h2 : 2 ≤ u) (huv : u ≤ v) (ht : u + 2 * v + 1 ≤ N)
    (hp : (u + (N + 1 - v)) % 2 = 1) (hs : ¬ Special N u v) (hT : ThinRest N u v) :
    Proven2 N u v ∨ (N ≤ 4 * u + 80 ∧ 4 * u ≤ N + 40 ∧ N ≤ u + 2 * v + 81 ∧ 4 ≤ u ∧ u + 10 ≤ v ∧
      v + 13 ≤ 2 * u) := by
  obtain ⟨hT, hr⟩ := hT
  by_cases hu : u ≤ 3
  · exact Or.inl (small_cover hN h2 hu huv ht hp hs)
  by_cases hd : v ≤ u + 9
  · exact Or.inl (diag_cover hN (by omega) huv hd ht hr)
  by_cases hst : 2 * u ≤ v + 12 ∧ v ≤ 2 * u + 15 ∧ N ≤ 8 * u + 320
  · exact Or.inl (strip_cover hN (by omega) (by omega) hst.1 hst.2.1 hst.2.2 ht)
  unfold Thin at hT
  exact Or.inr (by omega)

/-- **The thin sets are covered** for `N ≥ 1000`: `ThinCover N`. -/
theorem thinCover {N : ℕ} (hN : 1000 ≤ N) : ThinCover N := by
  intro u v h2 huv ht hp hs hT
  rcases thin_split (by omega) h2 huv ht hp hs hT with h | ⟨c1, c2, c3, hu, hd, hns⟩
  · exact h
  · exact cluster_cover hN hu hd hns c1 c2 c3 ht

/-- For `301 ≤ N < 1000` the thin sets are in `Proven2` or (the cluster box) pass `dirAny` by a
kernel check (`clCheck_small`). -/
theorem thinCover_small {N : ℕ} (h1 : 300 < N) (h2' : N < 1000) (u v : ℕ) (h2 : 2 ≤ u) (huv : u ≤ v)
    (ht : u + 2 * v + 1 ≤ N) (hp : (u + (N + 1 - v)) % 2 = 1) (hs : ¬ Special N u v)
    (hT : ThinRest N u v) : Proven2 N u v ∨ (dirAny N u v = true ∨ dirAny N v u = true) := by
  rcases thin_split (by omega) h2 huv ht hp hs hT with h | ⟨c1, c2, c3, hu, hd, hns⟩
  · exact Or.inl h
  · exact Or.inr (clCheck_spec (clCheck_small (by omega) h2') c1 c2 c3 ht hns hd)

/-- `Residual2 N` for `300 < N < 1000`. -/
theorem residual2_small {N : ℕ} (h1 : 300 < N) (h2 : N < 1000) : Residual2 N := by
  intro u v h1' h2' h3 h4 h5 h6 h7 h8
  have hu' : u + 2 * (N + 1 - v) + 1 ≤ N := by omega
  by_cases hth : Thin N u (N + 1 - v)
  · by_cases hd : N + 1 - v = u + 1 ∧ 5 ≤ u ∧ 3 * u + 21 ≤ N
    · exfalso
      apply h8
      obtain ⟨he, h5', h21⟩ := hd
      rw [he]
      exact Or.inr (Or.inr (Or.inl (d1_line (by omega) h5' h21)))
    · rcases thinCover_small h1 h2 u (N + 1 - v) h1' (by omega) hu' (by omega) h7 ⟨hth, hd⟩ with h | h
      · exact absurd h h8
      · exact h
  · exfalso
    apply h8
    rcases bulk (by omega) hu' hth with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl h))

/-- `Residual2 N` for every `N > 300`. -/
theorem residual2 {N : ℕ} (hN : 300 < N) : Residual2 N := by
  by_cases h : N < 1000
  · exact residual2_small hN h
  · exact residual2_of_coverAll (coverAll_of_thinCover hN (thinCover (by omega)))

/-- **Conjecture C (2-prefixes), for all `N`**: a valid 2-prefix `[m₁, m₂]` extends to a full
semi-symmetric sequence iff it is not one of the explicit dead pairs. -/
theorem conjectureC {N m₁ m₂ : ℕ} (h1 : 1 ≤ m₁ ∧ m₁ ≤ N) (h2 : 1 ≤ m₂ ∧ m₂ ≤ N) (h12 : m₁ ≠ m₂)
    (hval : SemiSymmetric N [m₁, m₂]) :
    Extends N [m₁, m₂] ↔ deadB N (min m₁ m₂) (max m₁ m₂) = false :=
  conjectureC_of_residual2 (fun _ hN => residual2 hN) h1 h2 h12 hval

/-- `CoverAll N` (every mixed-parity wide non-special pair lies in `Proven2`) for all `N ≥ 1000`. -/
theorem coverAll {N : ℕ} (hN : 1000 ≤ N) : CoverAll N := coverAll_of_thinCover (by omega) (thinCover hN)

end ThinCover
end Folds
'''


def main():
    small = gensmall.main()
    open(os.path.join(ROOT, 'ThinCoverSmall.lean'), 'w').write(
        HEADER.replace('import Folds.ThinCoverBase', 'import Folds.ThinCoverBase') + small + FOOTER)
    diag = '\n'.join(diag_case(d) for d in range(10))
    strip = '\n'.join(strip_case(e) for e in range(-12, 16))
    open(os.path.join(ROOT, 'ThinCover.lean'), 'w').write(ASM.replace('%DIAG%', diag).replace('%STRIP%', strip))


if __name__ == '__main__':
    main()
