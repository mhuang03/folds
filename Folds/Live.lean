import Folds.WindowRule
import Folds.Blocks
import Folds.Extremal
import Folds.RevMirror

/-!
# Live prefixes

`Extends N p` (from `WindowRule.lean`): the partial sequence `p` can be completed to a
semi-symmetric fold sequence.

* `extends_scale`: liveness transfers through the parity-class embedding
  `y ↦ scale c y = 2y - c` (parity blocks).
* `extends_single`: every panel is a live first step, `Extends N [m]` for `1 ≤ m ≤ N`.
-/

namespace Folds

/-- **Parity transfer.**  A live prefix of the class-`c` world `[1..(N+c)/2]` stays live
after scaling into `[1..N]`: complete it there, then append any semi-symmetric sequence of
the other class. -/
theorem extends_scale {N c : Nat} (hc : c ≤ 1) {p : List Nat}
    (hp : Extends ((N + c) / 2) p)
    (hτ : ∃ τ, IsFoldSeq ((N + (1 - c)) / 2) τ ∧ SemiSymmetric ((N + (1 - c)) / 2) τ) :
    Extends N (p.map (scale c)) := by
  obtain ⟨σ, hσf, hσs, hpre⟩ := hp
  obtain ⟨τ, hτf, hτs⟩ := hτ
  exact ⟨_, hσf.blocks hc hτf, (semiSymmetric_blocks_iff hc hσf hτf).2 ⟨hσs, hτs⟩,
    (hpre.map _).trans (List.prefix_append _ _)⟩

theorem semiSymmetric_one : SemiSymmetric 1 [1] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  obtain rfl : k = 0 := by omega
  simp [SemiStep, leftCount, rightCount, reach]

/-- **Every panel is a live first step.** -/
theorem extends_single (N : Nat) : ∀ m, 1 ≤ m → m ≤ N → Extends N [m] := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro m hm1 hmN
    by_cases hN : N = 1
    · subst hN
      obtain rfl : m = 1 := by omega
      exact ⟨[1], List.Perm.refl _, semiSymmetric_one, List.prefix_refl _⟩
    · have hc : m % 2 ≤ 1 := by omega
      have h1 := ih ((N + m % 2) / 2) (by omega) ((m + m % 2) / 2) (by omega) (by omega)
      obtain ⟨τ, hτf, hτs, -⟩ :=
        ih ((N + (1 - m % 2)) / 2) (by omega) 1 le_rfl (by omega)
      have := extends_scale hc h1 ⟨τ, hτf, hτs⟩
      have e : scale (m % 2) ((m + m % 2) / 2) = m := by unfold scale; omega
      simpa [e] using this

/-- Every strip has a semi-symmetric fold sequence. -/
theorem exists_semiSymmetric (N : Nat) : ∃ a, IsFoldSeq N a ∧ SemiSymmetric N a := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨[], List.Perm.refl _, fun k hk => absurd hk (by simp)⟩
  · obtain ⟨a, hf, hs, -⟩ := extends_single N 1 le_rfl hN
    exact ⟨a, hf, hs⟩

/-! ## Mirror invariance of `Extends` -/

theorem Extends.mirror {N : Nat} {p : List Nat} (h : Extends N p) :
    Extends N (p.map (N + 1 - ·)) := by
  obtain ⟨a, hf, hs, hpre⟩ := h
  exact ⟨_, hf.mirror, hs.mirror hf, hpre.map _⟩

/-! ## Dead blocks `{1, 2j, 2j+1}`

If panels `1`, `2j`, `2j+1` are bisected before every panel of `G = [2, 2j-1]`
(`j ≥ 2`, `4j ≤ N + 3`), the first panel `m` of `G` to be bisected sees exactly one
bisected panel (`1`) on its left arm `[1, m-1]`, and on its right arm `[m+1, 2m-1]` none
(`m ≤ j`) or at least two (`2j`, `2j+1`, when `m > j`). -/

theorem dead_block {N j : Nat} {a : List Nat} (hf : IsFoldSeq N a) (h : SemiSymmetric N a)
    (hj : 2 ≤ j) (hN : 4 * j ≤ N + 3) {k : Nat}
    (h1 : 1 ∈ a.take k) (h2 : 2 * j ∈ a.take k) (h3 : 2 * j + 1 ∈ a.take k) :
    ∃ m ∈ a.take k, 2 ≤ m ∧ m < 2 * j := by
  have hnd := nodup_of_foldSeq hf
  by_contra hcon
  push Not at hcon
  have hex : ∃ i, ∃ hi : i < a.length, 2 ≤ a[i] ∧ a[i] < 2 * j := by
    have h2a : 2 ∈ a := (mem_range'_of_perm hf).2 ⟨by omega, by
      have := (mem_range'_of_perm hf).1 (List.mem_of_mem_take h3); omega⟩
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 h2a
    exact ⟨i, hi, by omega, by omega⟩
  classical
  obtain ⟨i, hi, hm2, hmj, hmin⟩ : ∃ i, ∃ hi : i < a.length, 2 ≤ a[i] ∧ a[i] < 2 * j ∧
      ∀ i' (hi' : i' < a.length), i' < i → ¬ (2 ≤ a[i'] ∧ a[i'] < 2 * j) := by
    obtain ⟨hi, hP⟩ := Nat.find_spec hex
    exact ⟨Nat.find hex, hi, hP.1, hP.2, fun i' hi' hlt hP' => Nat.find_min hex hlt ⟨hi', hP'⟩⟩
  -- no panel of `G` before step `i`
  have hS : ∀ x ∈ a.take i, ¬ (2 ≤ x ∧ x < 2 * j) := by
    intro x hx
    obtain ⟨i', hi', e⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_take] at hi'
    rw [List.getElem_take] at e
    rw [← e]; exact hmin i' (by omega) (by omega)
  -- `k ≤ i`
  have hki : k ≤ i := by
    by_contra hlt
    exact absurd (hcon a[i] ((getElem_mem_take_iff hnd hi).2 (by omega)) hm2) (by omega)
  have sub : ∀ x ∈ a.take k, x ∈ a.take i := fun x hx => by
    obtain ⟨i', hi', e⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_take] at hi'
    rw [List.getElem_take] at e
    rw [← e]; exact (getElem_mem_take_iff hnd (by omega)).2 (by omega)
  have hs := h i hi
  have hndS := take_nodup hnd i
  generalize a[i] = m at hs hm2 hmj
  unfold SemiStep at hs
  rw [leftCount_eq hndS, rightCount_eq hndS] at hs
  have hr : reach N m = m - 1 := by unfold reach; omega
  rw [hr] at hs
  have L : (a.take i).countP (fun x => decide (m - (m - 1) ≤ x ∧ x < m)) = 1 := by
    have e : (a.take i).countP (fun x => decide (m - (m - 1) ≤ x ∧ x < m)) =
        (a.take i).countP (fun x => decide (1 ≤ x ∧ x < m)) := by
      apply List.countP_congr; intro x _; simp only [decide_eq_true_eq]; omega
    rw [e, countP_split_one hndS (sub 1 h1) m (by omega)]
    have : (a.take i).countP (fun z => decide (2 ≤ z ∧ z < m)) = 0 := by
      rw [List.countP_eq_zero]
      intro x hx; have := hS x hx; simp only [decide_eq_true_eq]; omega
    omega
  rw [L] at hs
  by_cases hmj' : m ≤ j
  · have : (a.take i).countP (fun x => decide (m < x ∧ x ≤ m + (m - 1))) = 0 := by
      rw [List.countP_eq_zero]
      intro x hx; have := hS x hx; simp only [decide_eq_true_eq]; omega
    omega
  · rw [countP_split _ _ (fun x => decide (x = 2 * j))] at hs
    have e1 : (a.take i).countP
        (fun x => decide (m < x ∧ x ≤ m + (m - 1)) && decide (x = 2 * j)) =
        (a.take i).countP (fun x => decide (x = 2 * j)) := by
      apply List.countP_congr; intro x _; simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by omega, h⟩
    rw [e1, countP_eq_nodup hndS, ite_pos' (sub _ h2)] at hs
    have : 0 < (a.take i).countP
        (fun x => decide (m < x ∧ x ≤ m + (m - 1)) && !decide (x = 2 * j)) :=
      List.countP_pos_iff.2 ⟨2 * j + 1, sub _ h3, by simp; omega⟩
    omega

/-- **Dead blocks.**  A prefix that contains `1`, `2j`, `2j+1` (`j ≥ 2`, `4j ≤ N + 3`)
but no panel of `[2, 2j-1]` cannot be completed. -/
theorem not_extends_block {N j : Nat} (hj : 2 ≤ j) (hN : 4 * j ≤ N + 3) {p : List Nat}
    (h1 : 1 ∈ p) (h2 : 2 * j ∈ p) (h3 : 2 * j + 1 ∈ p)
    (hG : ∀ m ∈ p, ¬ (2 ≤ m ∧ m < 2 * j)) : ¬ Extends N p := by
  rintro ⟨a, hf, hs, hpre⟩
  rw [List.prefix_iff_eq_take.1 hpre] at h1 h2 h3 hG
  obtain ⟨m, hm, hm2, hmj⟩ := dead_block hf hs hj hN h1 h2 h3
  exact hG m hm ⟨hm2, hmj⟩

/-- Mirror image: a prefix that contains `N`, `N+1-2j`, `N-2j` but no panel of
`[N+2-2j, N-1]` cannot be completed. -/
theorem not_extends_block_mirror {N j : Nat} (hj : 2 ≤ j) (hN : 4 * j ≤ N + 3)
    {p : List Nat} (hpN : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N)
    (h1 : N ∈ p) (h2 : N + 1 - 2 * j ∈ p) (h3 : N - 2 * j ∈ p)
    (hG : ∀ m ∈ p, ¬ (N + 2 - 2 * j ≤ m ∧ m ≤ N - 1)) : ¬ Extends N p := by
  intro h
  have hm := h.mirror
  refine not_extends_block (p := p.map (N + 1 - ·)) hj hN ?_ ?_ ?_ ?_ hm
  · exact List.mem_map.2 ⟨N, h1, by omega⟩
  · exact List.mem_map.2 ⟨N + 1 - 2 * j, h2, by omega⟩
  · exact List.mem_map.2 ⟨N - 2 * j, h3, by omega⟩
  · intro m hm'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm'
    have := hG x hx; have := hpN x hx; omega

/-- The dead 3-prefixes `(2j+1, 1, 2j)` (and, when valid, `(1, 2j+1, 2j)`) and their
mirror images. -/
theorem not_extends_three_block {N j : Nat} (hj : 2 ≤ j) (hN : 4 * j ≤ N + 3) :
    ¬ Extends N [2 * j + 1, 1, 2 * j] ∧ ¬ Extends N [1, 2 * j + 1, 2 * j] ∧
      ¬ Extends N [N - 2 * j, N, N + 1 - 2 * j] ∧ ¬ Extends N [N, N - 2 * j, N + 1 - 2 * j] := by
  refine ⟨not_extends_block hj hN (by simp) (by simp) (by simp)
      (by intro m hm; simp at hm; omega),
    not_extends_block hj hN (by simp) (by simp) (by simp) (by intro m hm; simp at hm; omega),
    not_extends_block_mirror hj hN (by simp; omega) (by simp) (by simp) (by simp)
      (by intro m hm; simp at hm; omega),
    not_extends_block_mirror hj hN (by simp; omega) (by simp) (by simp) (by simp)
      (by intro m hm; simp at hm; omega)⟩

end Folds
