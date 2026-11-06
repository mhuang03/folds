import Folds.ThinCoverDiag
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
  · -- d = 0
    by_cases hm : 6 ≤ u
    · exact p2_SL (diag0 hN hm (by omega))
    · have hu : u < 6 := by omega
      interval_cases u
      · exact p2_SL (shape_4_4 hN)
      · exact p2_S ⟨hN, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  · -- d = 1
    by_cases h5 : 5 ≤ u
    · by_cases hc : N ≤ 3 * u + 3
      · exact p2_S ⟨hN, Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩)))⟩
      · exact p2_SL (d1_corner hN h5 (by omega) (by omega))
    · obtain rfl : u = 4 := by omega
      exact p2_SL (shape_4_5 hN)
  · -- d = 2
    by_cases hm : 4 ≤ u
    · exact p2_SL (diag2 hN hm (by omega))
    · omega
  · -- d = 3
    by_cases hm : 6 ≤ u
    · exact p2_SL (diag3 hN hm (by omega))
    · have hu : u < 6 := by omega
      interval_cases u
      · exact p2_SL (shape_4_7 hN)
      · exact p2_SL (shape_5_8 hN)
  · -- d = 4
    by_cases hm : 4 ≤ u
    · exact p2_SL (diag4 hN hm (by omega))
    · omega
  · -- d = 5
    by_cases hm : 4 ≤ u
    · exact p2_SL (diag5 hN hm (by omega))
    · omega
  · -- d = 6
    by_cases hm : 6 ≤ u
    · exact p2_SL (diag6 hN hm (by omega))
    · have hu : u < 6 := by omega
      interval_cases u
      · exact p2_SL (shape_4_10 hN)
      · exact p2_SL (shape_5_11 hN)
  · -- d = 7
    by_cases hm : 4 ≤ u
    · exact p2_SL (diag7 hN hm (by omega))
    · omega
  · -- d = 8
    by_cases hm : 8 ≤ u
    · exact p2_SL (diag8 hN hm (by omega))
    · have hu : u < 8 := by omega
      interval_cases u
      · exact p2_SL (shape_4_12 hN)
      · exact p2_SL (shape_5_13 hN)
      · exact p2_SL (shape_6_14 hN)
      · exact p2_SL (shape_7_15 hN)
  · -- d = 9
    by_cases hm : 5 ≤ u
    · exact p2_SL (diag9 hN hm (by omega))
    · have hu : u < 5 := by omega
      interval_cases u
      · exact p2_SL (shape_4_13 hN)

/-- The strip `u' = 2u + e`, `-12 ≤ e ≤ 15`, `N ≤ 8u + 320` (outside the diagonal strip). -/
theorem strip_cover {N u v : ℕ} (hN : 301 ≤ N) (hu : 4 ≤ u) (hd : u + 10 ≤ v) (h1 : 2 * u ≤ v + 12)
    (h2 : v ≤ 2 * u + 15) (h3 : N ≤ 8 * u + 320) (ht : u + 2 * v + 1 ≤ N) : Proven2 N u v := by
  obtain ⟨k, hk⟩ : ∃ k, v + 12 = 2 * u + k := ⟨v + 12 - 2 * u, by omega⟩
  have hk' : k ≤ 27 := by omega
  interval_cases k
  · -- e = -12
    by_cases hm : 4 ≤ u
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 6 := ⟨u - 6, by omega⟩
      obtain rfl : v = 2 * w := by omega
      exact p2_SL (stripm12 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = -11
    by_cases hm : 4 ≤ u
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 6 := ⟨u - 6, by omega⟩
      obtain rfl : v = 2 * w + 1 := by omega
      exact p2_SL (stripm11 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = -10
    by_cases hm : 4 ≤ u
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 5 := ⟨u - 5, by omega⟩
      obtain rfl : v = 2 * w := by omega
      exact p2_SL (stripm10 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = -9
    by_cases hm : 4 ≤ u
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 5 := ⟨u - 5, by omega⟩
      obtain rfl : v = 2 * w + 1 := by omega
      exact p2_SL (stripm9 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = -8
    by_cases hm : 4 ≤ u
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 4 := ⟨u - 4, by omega⟩
      obtain rfl : v = 2 * w := by omega
      exact p2_SL (stripm8 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = -7
    by_cases hm : 4 ≤ u
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 4 := ⟨u - 4, by omega⟩
      obtain rfl : v = 2 * w + 1 := by omega
      exact p2_SL (stripm7 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = -6
    by_cases hm : 4 ≤ u
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 3 := ⟨u - 3, by omega⟩
      obtain rfl : v = 2 * w := by omega
      exact p2_SL (stripm6 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = -5
    by_cases hm : 4 ≤ u
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 3 := ⟨u - 3, by omega⟩
      obtain rfl : v = 2 * w + 1 := by omega
      exact p2_SL (stripm5 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = -4
    by_cases hm : 4 ≤ u
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 2 := ⟨u - 2, by omega⟩
      obtain rfl : v = 2 * w := by omega
      exact p2_SL (stripm4 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = -3
    by_cases hm : 4 ≤ u
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 2 := ⟨u - 2, by omega⟩
      obtain rfl : v = 2 * w + 1 := by omega
      exact p2_SL (stripm3 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = -2
    by_cases hm : 4 ≤ u
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
      obtain rfl : v = 2 * w := by omega
      exact p2_SL (stripm2 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = -1
    by_cases hm : 4 ≤ u
    · obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
      obtain rfl : v = 2 * w + 1 := by omega
      exact p2_SL (stripm1 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = 0
    by_cases hm : 4 ≤ u
    · obtain rfl : v = 2 * u := by omega
      exact p2_SL (strip0 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = 1
    by_cases hm : 4 ≤ u
    · obtain rfl : v = 2 * u + 1 := by omega
      exact p2_SL (strip1 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = 2
    by_cases hm : 4 ≤ u
    · obtain rfl : v = 2 * u + 2 := by omega
      exact p2_SL (strip2 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = 3
    by_cases hm : 4 ≤ u
    · obtain rfl : v = 2 * u + 3 := by omega
      exact p2_SL (strip3 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = 4
    by_cases hm : 4 ≤ u
    · obtain rfl : v = 2 * u + 4 := by omega
      exact p2_SL (strip4 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = 5
    by_cases hm : 4 ≤ u
    · obtain rfl : v = 2 * u + 5 := by omega
      exact p2_SL (strip5 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = 6
    by_cases hm : 7 ≤ u
    · obtain rfl : v = 2 * u + 6 := by omega
      exact p2_SL (strip6 (by omega) (by omega) (by omega) (by omega) (by omega))
    · have hu4 : u < 7 := by omega
      interval_cases u
      · obtain rfl : v = 14 := by omega
        exact p2_SL (sshape_4_14 hN (by omega))
      · obtain rfl : v = 16 := by omega
        exact p2_SL (sshape_5_16 hN (by omega))
      · obtain rfl : v = 18 := by omega
        exact p2_SL (sshape_6_18 hN (by omega))
  · -- e = 7
    by_cases hm : 4 ≤ u
    · obtain rfl : v = 2 * u + 7 := by omega
      exact p2_SL (strip7 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = 8
    by_cases hm : 4 ≤ u
    · obtain rfl : v = 2 * u + 8 := by omega
      exact p2_SL (strip8 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = 9
    by_cases hm : 5 ≤ u
    · obtain rfl : v = 2 * u + 9 := by omega
      exact p2_SL (strip9 (by omega) (by omega) (by omega) (by omega) (by omega))
    · have hu4 : u < 5 := by omega
      interval_cases u
      · obtain rfl : v = 17 := by omega
        exact p2_SL (sshape_4_17 hN (by omega))
  · -- e = 10
    by_cases hm : 4 ≤ u
    · obtain rfl : v = 2 * u + 10 := by omega
      exact p2_SL (strip10 (by omega) (by omega) (by omega) (by omega) (by omega))
    · omega
  · -- e = 11
    by_cases hm : 6 ≤ u
    · obtain rfl : v = 2 * u + 11 := by omega
      exact p2_SL (strip11 (by omega) (by omega) (by omega) (by omega) (by omega))
    · have hu4 : u < 6 := by omega
      interval_cases u
      · obtain rfl : v = 19 := by omega
        exact p2_SL (sshape_4_19 hN (by omega))
      · obtain rfl : v = 21 := by omega
        exact p2_SL (sshape_5_21 hN (by omega))
  · -- e = 12
    by_cases hm : 5 ≤ u
    · obtain rfl : v = 2 * u + 12 := by omega
      exact p2_SL (strip12 (by omega) (by omega) (by omega) (by omega) (by omega))
    · have hu4 : u < 5 := by omega
      interval_cases u
      · obtain rfl : v = 20 := by omega
        exact p2_SL (sshape_4_20 hN (by omega))
  · -- e = 13
    by_cases hm : 8 ≤ u
    · obtain rfl : v = 2 * u + 13 := by omega
      exact p2_SL (strip13 (by omega) (by omega) (by omega) (by omega) (by omega))
    · have hu4 : u < 8 := by omega
      interval_cases u
      · obtain rfl : v = 21 := by omega
        exact p2_SL (sshape_4_21 hN (by omega))
      · obtain rfl : v = 23 := by omega
        exact p2_SL (sshape_5_23 hN (by omega))
      · obtain rfl : v = 25 := by omega
        exact p2_SL (sshape_6_25 hN (by omega))
      · obtain rfl : v = 27 := by omega
        exact p2_SL (sshape_7_27 hN (by omega))
  · -- e = 14
    by_cases hm : 6 ≤ u
    · obtain rfl : v = 2 * u + 14 := by omega
      exact p2_SL (strip14 (by omega) (by omega) (by omega) (by omega) (by omega))
    · have hu4 : u < 6 := by omega
      interval_cases u
      · obtain rfl : v = 22 := by omega
        exact p2_SL (sshape_4_22 hN (by omega))
      · obtain rfl : v = 24 := by omega
        exact p2_SL (sshape_5_24 hN (by omega))
  · -- e = 15
    by_cases hm : 8 ≤ u
    · obtain rfl : v = 2 * u + 15 := by omega
      exact p2_SL (strip15 (by omega) (by omega) (by omega) (by omega) (by omega))
    · have hu4 : u < 8 := by omega
      interval_cases u
      · obtain rfl : v = 23 := by omega
        exact p2_SL (sshape_4_23 hN (by omega))
      · obtain rfl : v = 25 := by omega
        exact p2_SL (sshape_5_25 hN (by omega))
      · obtain rfl : v = 27 := by omega
        exact p2_SL (sshape_6_27 hN (by omega))
      · obtain rfl : v = 29 := by omega
        exact p2_SL (sshape_7_29 hN (by omega))

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
