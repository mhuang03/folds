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

end Folds
