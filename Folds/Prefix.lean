import Folds.Recursion
import Mathlib.Tactic.Ring

/-!
# Valid prefixes of length 2

A length-2 prefix `[m₁, m₂]` (distinct panels in `1..N`) is valid iff the second step is
semi-symmetric relative to `{m₁}` (the first step is always valid).

* `semiStep_pair_iff`: for distinct `m₁, m₂ ∈ [1..N]`, the step `({m₁}, m₂)` is
  semi-symmetric iff `m₁` lies outside the window of `m₂`, i.e.
  `2·m₂ ≤ m₁ ∨ m₁ + N + 1 ≤ 2·m₂`.
* `card_prefixTwo`: the number of valid length-2 prefixes is `⌊N²/2⌋`.
* `card_reachTwo`: the number of reachable 2-sets `{x, y}` (some ordering valid) is
  `⌊N²/3⌋`.
-/

namespace Folds

theorem semiSymmetric_pair_iff {N m₁ m₂ : Nat} :
    SemiSymmetric N [m₁, m₂] ↔ SemiStep N [m₁] m₂ := by
  have : [m₁, m₂] = [m₁] ++ [m₂] := rfl
  rw [this, semiSymmetric_concat_iff]
  constructor
  · exact fun h => h.2
  · intro h; refine ⟨fun k hk => ?_, h⟩
    obtain rfl : k = 0 := by simp at hk; omega
    simp [SemiStep, leftCount, rightCount, reach]

/-- The step `({m₁}, m₂)` is semi-symmetric iff `m₁` is outside the window of `m₂`. -/
theorem semiStep_pair_iff {N m₁ m₂ : Nat} (h1 : 1 ≤ m₁) (h2 : 1 ≤ m₂) (h1N : m₁ ≤ N)
    (h2N : m₂ ≤ N) (hne : m₁ ≠ m₂) :
    SemiStep N [m₁] m₂ ↔ (2 * m₂ ≤ m₁ ∨ m₁ + N + 1 ≤ 2 * m₂) := by
  unfold SemiStep
  rw [leftCount_eq (List.nodup_singleton _), rightCount_eq (List.nodup_singleton _)]
  simp only [List.countP_cons, List.countP_nil]
  unfold reach
  split_ifs <;> simp_all <;> omega

/-- The valid length-2 prefixes, as ordered pairs `(m₁, m₂)`. -/
def prefixTwo (N : Nat) : Finset (Nat × Nat) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter fun p => p.1 ≠ p.2 ∧ SemiStep N [p.1] p.2

/-- Pairs with `2·m₂ ≤ m₁` (the first panel lies right of the window of the second). -/
def pairsLow (N : Nat) : Finset (Nat × Nat) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter fun p => 2 * p.2 ≤ p.1

/-- Pairs with `m₁ + N + 1 ≤ 2·m₂` (the first panel lies left of the window). -/
def pairsHigh (N : Nat) : Finset (Nat × Nat) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter fun p => p.1 + N + 1 ≤ 2 * p.2

theorem sq_div_four_succ (N : Nat) : (N + 1) * (N + 1) / 4 = N * N / 4 + (N + 1) / 2 := by
  rcases Nat.even_or_odd' N with ⟨k, rfl | rfl⟩
  · have e1 : (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 := by ring
    have e2 : 2 * k * (2 * k) = 4 * (k * k) := by ring
    rw [e1, e2]; omega
  · have e1 : (2 * k + 1 + 1) * (2 * k + 1 + 1) = 4 * (k * k + 2 * k + 1) := by ring
    have e2 : (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 := by ring
    rw [e1, e2]; omega

theorem card_pairsLow : ∀ N, (pairsLow N).card = N * N / 4
  | 0 => rfl
  | N + 1 => by
    have e : pairsLow (N + 1) = pairsLow N ∪ ({N + 1} ×ˢ Finset.Icc 1 ((N + 1) / 2)) := by
      ext ⟨x, y⟩
      simp only [pairsLow, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_singleton]
      omega
    have hd : Disjoint (pairsLow N) ({N + 1} ×ˢ Finset.Icc 1 ((N + 1) / 2)) := by
      rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [pairsLow, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_singleton] at h1 h2
      omega
    rw [e, Finset.card_union_of_disjoint hd, card_pairsLow N, Finset.card_product,
      Finset.card_singleton, Nat.card_Icc, sq_div_four_succ]
    omega

theorem card_pairsHigh (N : Nat) : (pairsHigh N).card = (pairsLow N).card := by
  apply Finset.card_nbij' (fun p => (N + 1 - p.1, N + 1 - p.2))
    (fun p => (N + 1 - p.1, N + 1 - p.2))
  · rintro ⟨x, y⟩ h
    simp only [pairsHigh, pairsLow, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨x, y⟩ h
    simp only [pairsHigh, pairsLow, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨x, y⟩ h
    simp only [pairsHigh, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_ofPred_eq] at h
    simp only [Prod.mk.injEq]; omega
  · rintro ⟨x, y⟩ h
    simp only [pairsLow, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_ofPred_eq] at h
    simp only [Prod.mk.injEq]; omega

theorem two_mul_sq_div_four (N : Nat) : 2 * (N * N / 4) = N * N / 2 := by
  rcases Nat.even_or_odd' N with ⟨k, rfl | rfl⟩
  · have e : 2 * k * (2 * k) = 4 * (k * k) := by ring
    rw [e]; omega
  · have e : (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 := by ring
    rw [e]; omega

/-- **Length-2 prefixes.**  The number of valid length-2 prefixes `[m₁, m₂]` is
`⌊N²/2⌋`. -/
theorem card_prefixTwo (N : Nat) : (prefixTwo N).card = N * N / 2 := by
  have e : prefixTwo N = pairsLow N ∪ pairsHigh N := by
    ext ⟨x, y⟩
    simp only [prefixTwo, pairsLow, pairsHigh, Finset.mem_union, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨hb, hne, hs⟩
      have := (semiStep_pair_iff hb.1.1 hb.2.1 hb.1.2 hb.2.2 hne).1 hs
      rcases this with h | h
      · exact Or.inl ⟨hb, h⟩
      · exact Or.inr ⟨hb, h⟩
    · intro h
      have hb : (1 ≤ x ∧ x ≤ N) ∧ 1 ≤ y ∧ y ≤ N := by rcases h with h | h <;> exact h.1
      have hne : x ≠ y := by omega
      refine ⟨hb, hne, (semiStep_pair_iff hb.1.1 hb.2.1 hb.1.2 hb.2.2 hne).2 ?_⟩
      rcases h with h | h
      · exact Or.inl h.2
      · exact Or.inr h.2
  have hd : Disjoint (pairsLow N) (pairsHigh N) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [pairsLow, pairsHigh, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at h1 h2
    omega
  rw [e, Finset.card_union_of_disjoint hd, card_pairsHigh, card_pairsLow,
    ← two_mul_sq_div_four]
  omega

/-- The same count phrased with lists: the semi-symmetric repetition-free lists
`[m₁, m₂]` of panels of `1..N`. -/
theorem prefixTwo_mem_iff {N m₁ m₂ : Nat} :
    (m₁, m₂) ∈ prefixTwo N ↔
      (1 ≤ m₁ ∧ m₁ ≤ N) ∧ (1 ≤ m₂ ∧ m₂ ≤ N) ∧ [m₁, m₂].Nodup ∧ SemiSymmetric N [m₁, m₂] := by
  simp only [prefixTwo, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    semiSymmetric_pair_iff, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true]
  tauto

/-! ## Reachable 2-sets -/

/-- The reachable 2-sets `{x, y}` (`x < y`), i.e. those with at least one valid
ordering `[x, y]` or `[y, x]`, represented by the sorted pair `(x, y)`. -/
def reachTwo (N : Nat) : Finset (Nat × Nat) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
    fun p => p.1 < p.2 ∧ (SemiStep N [p.1] p.2 ∨ SemiStep N [p.2] p.1)

/-- Arithmetic description of `reachTwo`. -/
def reachTwoArith (N : Nat) : Finset (Nat × Nat) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
    fun p => p.1 < p.2 ∧ (2 * p.1 ≤ p.2 ∨ p.1 + N + 1 ≤ 2 * p.2)

theorem reachTwo_eq (N : Nat) : reachTwo N = reachTwoArith N := by
  ext ⟨x, y⟩
  simp only [reachTwo, reachTwoArith, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨hb, hlt, h⟩
    refine ⟨hb, hlt, ?_⟩
    rcases h with h | h
    · have := (semiStep_pair_iff hb.1.1 hb.2.1 hb.1.2 hb.2.2 (by omega)).1 h; omega
    · have := (semiStep_pair_iff hb.2.1 hb.1.1 hb.2.2 hb.1.2 (by omega)).1 h; omega
  · rintro ⟨hb, hlt, h⟩
    refine ⟨hb, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inr ((semiStep_pair_iff hb.2.1 hb.1.1 hb.2.2 hb.1.2 (by omega)).2 (Or.inl h))
    · exact Or.inl ((semiStep_pair_iff hb.1.1 hb.2.1 hb.1.2 hb.2.2 (by omega)).2 (Or.inr h))

theorem sq_div_three_succ (N : Nat) :
    (N + 1) * (N + 1) / 3 = N * N / 3 + (2 * N + 2) / 3 := by
  obtain ⟨k, hk | hk | hk⟩ : ∃ k, N = 3 * k ∨ N = 3 * k + 1 ∨ N = 3 * k + 2 :=
    ⟨N / 3, by omega⟩ <;> subst hk
  · have e1 : (3 * k + 1) * (3 * k + 1) = 3 * (3 * k * k + 2 * k) + 1 := by ring
    have e2 : 3 * k * (3 * k) = 3 * (3 * k * k) := by ring
    rw [e1, e2]; omega
  · have e1 : (3 * k + 1 + 1) * (3 * k + 1 + 1) = 3 * (3 * k * k + 4 * k + 1) + 1 := by ring
    have e2 : (3 * k + 1) * (3 * k + 1) = 3 * (3 * k * k + 2 * k) + 1 := by ring
    rw [e1, e2]; omega
  · have e1 : (3 * k + 2 + 1) * (3 * k + 2 + 1) = 3 * (3 * k * k + 6 * k + 3) := by ring
    have e2 : (3 * k + 2) * (3 * k + 2) = 3 * (3 * k * k + 4 * k + 1) + 1 := by ring
    rw [e1, e2]; omega

theorem card_reachTwoArith : ∀ N, (reachTwoArith N).card = N * N / 3
  | 0 => rfl
  | N + 1 => by
    -- pairs that stop being reachable when the strip grows: `2y = x + N + 1`, `y < 2x`
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := reachTwoArith N) (fun p => 2 * p.2 = p.1 + N + 1 ∧ p.2 < 2 * p.1)
    have hlost : ((reachTwoArith N).filter
        fun p => 2 * p.2 = p.1 + N + 1 ∧ p.2 < 2 * p.1).card = N + 1 - (2 * N + 5) / 3 := by
      rw [← Nat.card_Icc]
      apply Finset.card_nbij' (fun p => p.2) (fun y => (2 * y - N - 1, y))
      · rintro ⟨x, y⟩ h
        simp only [reachTwoArith, Finset.coe_filter, Finset.mem_filter, Finset.mem_product,
          Finset.mem_Icc, Set.mem_ofPred_eq, Finset.coe_Icc, Set.mem_Icc] at h ⊢
        omega
      · intro y h
        simp only [reachTwoArith, Finset.coe_filter, Finset.mem_filter, Finset.mem_product,
          Finset.mem_Icc, Set.mem_ofPred_eq, Finset.coe_Icc, Set.mem_Icc] at h ⊢
        omega
      · rintro ⟨x, y⟩ h
        simp only [reachTwoArith, Finset.coe_filter, Finset.mem_filter, Finset.mem_product,
          Finset.mem_Icc, Set.mem_ofPred_eq] at h
        show (2 * y - N - 1, y) = (x, y); rw [Prod.mk.injEq]; omega
      · intro y _; rfl
    have e : reachTwoArith (N + 1) =
        (reachTwoArith N).filter (fun p => ¬(2 * p.2 = p.1 + N + 1 ∧ p.2 < 2 * p.1)) ∪
          (Finset.Icc 1 N ×ˢ {N + 1}) := by
      ext ⟨x, y⟩
      simp only [reachTwoArith, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_singleton]
      omega
    have hd : Disjoint
        ((reachTwoArith N).filter (fun p => ¬(2 * p.2 = p.1 + N + 1 ∧ p.2 < 2 * p.1)))
        (Finset.Icc 1 N ×ˢ {N + 1}) := by
      rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [reachTwoArith, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_singleton] at h1 h2
      omega
    rw [e, Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_singleton,
      Nat.card_Icc, sq_div_three_succ, ← card_reachTwoArith N]
    omega

/-- **Reachable 2-sets.**  The number of 2-element sets `{x, y} ⊆ [1..N]` that can be
bisected first (in some order, both steps semi-symmetric) is `⌊N²/3⌋`. -/
theorem card_reachTwo (N : Nat) : (reachTwo N).card = N * N / 3 := by
  rw [reachTwo_eq, card_reachTwoArith]

end Folds
