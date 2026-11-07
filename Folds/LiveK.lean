import Folds.Adjacent

/-!
# Live k-prefixes: explicit families of co-reachable sets of any size

`experiments/livek/PROOFS.txt`.

All results hold for every strip length `N` and every set size `k`.

* `armL_eq`, `armR_eq`: the arm counts of a finite set as cardinalities of filters.
* `inward_of_sep`, `coReach_of_sep`: **Theorem G in separation form**: if every panel outside
  `B` that `B` pulls to the right (`I_B < 0`: more of `B` in its right arm) lies left of every
  panel outside `B` that `B` pulls to the left (`I_B > 0`), then `B` is co-reachable.
* `coReach_compact` (**compact sets**): if `B ⊆ [a, b]` with `1 ≤ a`, `b ≤ N`, `b ≤ 2a + 1` and
  `2b ≤ N + a + 2`, then `B` is co-reachable: every free panel strictly inside `[a, b]` sees
  all of `B` in its two arms, so its imbalance is monotone; panels outside `[a, b]` see `B` in
  one arm only.
* `coReach_middle` (**the middle third**): every subset of `[a, N + 1 - a]` with `N ≤ 3a`, i.e.
  of `[⌈N/3⌉, N + 1 - ⌈N/3⌉]`, is co-reachable.
* `coReach_dyadic` (**dyadic sets**): if `2x ≤ y` for all `x < y` in `B`, and every element
  `y` of `B` that is not the least has a smaller element `x` of `B` with `2y ≤ N + x + 2`, then
  `B` is co-reachable (centre: the least element).  `coReach_dyadic_half`: every dyadic set in
  the left half `2y ≤ N + 1`; `coReach_dyadic_mirror`: the mirror images.
* `coReach_sparse` (**doubling-sparse sets** of the left half, `d_{2i+1} ≥ 2 d_{i+1} - 2`) and
  `coReach_anchored` (**anchored sets**: two counting conditions at each element; contains the
  dyadic and the sparse sets): Theorem G with the centre at the least element.
* `CovK`, `CovK.coReach`, `CovK.extends`: the family of all these sets and their mirror
  images; every valid prefix (of any length) whose set is in it is live.  Specialisations
  `extends_compact`, `extends_middle`, `extends_dyadic(_half, _mirror)`, `extends_sparse`,
  `extends_anchored`.
* `semiSymmetric_halving`, `extends_halving`: halving sequences (`2 x_{j+1} ≤ x_j`, `x₁` in the
  left half) are valid and live prefixes, for every `k`: a positive proportion of all valid
  `k`-prefixes is live.
-/

namespace Folds
namespace LiveK

open Live2 Live4 Adjacent

/-! ## Arm counts of a finite set -/

theorem countP_toList (B : Finset Nat) (p : Nat → Prop) [DecidablePred p] :
    B.toList.countP (fun x => decide (p x)) = (B.filter p).card := by
  rw [← Multiset.coe_countP, Finset.coe_toList, Multiset.countP_eq_card_filter,
    ← Finset.filter_val, Finset.card_val]

theorem armL_eq (N m : Nat) (B : Finset Nat) :
    leftCount N B.toList m = (B.filter (fun x => m - reach N m ≤ x ∧ x < m)).card := by
  rw [leftCount_eq (Finset.nodup_toList B), countP_toList]

theorem armR_eq (N m : Nat) (B : Finset Nat) :
    rightCount N B.toList m = (B.filter (fun x => m < x ∧ x ≤ m + reach N m)).card := by
  rw [rightCount_eq (Finset.nodup_toList B), countP_toList]

theorem reach_cases (N m : Nat) :
    (reach N m = m - 1 ∧ m - 1 ≤ N - m) ∨ (reach N m = N - m ∧ N - m ≤ m - 1) := by
  unfold reach
  rcases le_total (m - 1) (N - m) with h | h
  · exact Or.inl ⟨min_eq_left h, h⟩
  · exact Or.inr ⟨min_eq_right h, h⟩

/-! ## Theorem G in separation form -/

/-- **Theorem G, separation form.**  If every free panel with negative imbalance lies left of
every free panel with positive imbalance, the criterion `Inward` holds for some centre. -/
theorem inward_of_sep {N : Nat} {B : Finset Nat}
    (h : ∀ m m', 1 ≤ m → m ≤ N → m ∉ B → 1 ≤ m' → m' ≤ N → m' ∉ B →
      leftCount N B.toList m < rightCount N B.toList m →
      rightCount N B.toList m' < leftCount N B.toList m' → m < m') :
    ∃ c2, Inward N c2 B := by
  classical
  set Neg := (Finset.Icc 1 N \ B).filter
    (fun m => leftCount N B.toList m < rightCount N B.toList m) with hNeg
  have memNeg : ∀ m, m ∈ Neg ↔ (1 ≤ m ∧ m ≤ N) ∧ m ∉ B ∧
      leftCount N B.toList m < rightCount N B.toList m := by
    intro m; rw [hNeg, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc, and_assoc]
  by_cases hne : Neg.Nonempty
  · refine ⟨2 * Neg.max' hne + 1, ?_⟩
    have hM := (memNeg _).1 (Finset.max'_mem Neg hne)
    intro m hm1 hmN hmB
    refine ⟨by omega, fun hlt => ?_, fun hgt => ?_⟩
    · by_contra hc
      push Not at hc
      have := h _ m hM.1.1 hM.1.2 hM.2.1 hm1 hmN hmB hM.2.2 hc
      omega
    · by_contra hc
      push Not at hc
      have := Finset.le_max' Neg m ((memNeg m).2 ⟨⟨hm1, hmN⟩, hmB, hc⟩)
      omega
  · refine ⟨0, fun m hm1 hmN hmB => ⟨by omega, fun h' => by omega, fun _ => ?_⟩⟩
    by_contra hc
    push Not at hc
    exact hne ⟨m, (memNeg m).2 ⟨⟨hm1, hmN⟩, hmB, hc⟩⟩

theorem coReach_of_sep {N : Nat} {B : Finset Nat} (hB : B ⊆ Finset.Icc 1 N)
    (h : ∀ m m', 1 ≤ m → m ≤ N → m ∉ B → 1 ≤ m' → m' ≤ N → m' ∉ B →
      leftCount N B.toList m < rightCount N B.toList m →
      rightCount N B.toList m' < leftCount N B.toList m' → m < m') :
    CoReach N B := by
  obtain ⟨c2, hc⟩ := inward_of_sep h
  exact coReach_of_inward hB hc

/-! ## Compact sets and the middle third -/

/-- **Compact sets are co-reachable.**  `B ⊆ [a, b]` with `b ≤ 2a + 1` and `2b ≤ N + a + 2`. -/
theorem coReach_compact {N a b : Nat} {B : Finset Nat} (hB : B ⊆ Finset.Icc a b)
    (ha : 1 ≤ a) (hbN : b ≤ N) (h1 : b ≤ 2 * a + 1) (h2 : 2 * b ≤ N + a + 2) :
    CoReach N B := by
  have hB' : ∀ x ∈ B, a ≤ x ∧ x ≤ b := fun x hx => Finset.mem_Icc.1 (hB hx)
  refine coReach_of_sep (fun x hx => by
    have := hB' x hx; rw [Finset.mem_Icc]; omega) ?_
  intro m m' _ _ _ _ _ _ hneg hpos
  rw [armL_eq, armR_eq] at hneg hpos
  by_contra hc
  push Not at hc
  -- the positive panel `m'` is right of `a`: otherwise its left arm misses `B`
  have hm'a : a < m' := by
    by_contra h'
    have : (B.filter (fun x => m' - reach N m' ≤ x ∧ x < m')).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx; have := hB' x hx; omega
    omega
  -- the negative panel `m` is left of `b`: otherwise its right arm misses `B`
  have hmb : m < b := by
    by_contra h'
    have : (B.filter (fun x => m < x ∧ x ≤ m + reach N m)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx; have := hB' x hx; omega
    omega
  -- inner panels see all of `B`
  have inner : ∀ y, a < y → y < b →
      B.filter (fun x => y - reach N y ≤ x ∧ x < y) = B.filter (fun x => x < y) ∧
      B.filter (fun x => y < x ∧ x ≤ y + reach N y) = B.filter (fun x => y < x) := by
    intro y hy1 hy2
    constructor
    · apply Finset.filter_congr
      intro x hx; have := hB' x hx; unfold reach; constructor
      · exact fun h => h.2
      · intro h; exact ⟨by omega, h⟩
    · apply Finset.filter_congr
      intro x hx; have := hB' x hx; unfold reach; constructor
      · exact fun h => h.1
      · intro h; exact ⟨h, by omega⟩
  obtain ⟨e1, e2⟩ := inner m (by omega) hmb
  obtain ⟨e3, e4⟩ := inner m' hm'a (by omega)
  rw [e1, e2] at hneg
  rw [e3, e4] at hpos
  have l1 : (B.filter (fun x => x < m')).card ≤ (B.filter (fun x => x < m)).card :=
    Finset.card_le_card fun x hx => by
      rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩
  have l2 : (B.filter (fun x => m < x)).card ≤ (B.filter (fun x => m' < x)).card :=
    Finset.card_le_card fun x hx => by
      rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩
  omega

/-- **The middle third.**  Every set of panels inside `[a, N + 1 - a]` with `N ≤ 3a` (e.g.
`a = ⌈N/3⌉`) is co-reachable, whatever its size. -/
theorem coReach_middle {N a : Nat} {B : Finset Nat} (hB : B ⊆ Finset.Icc a (N + 1 - a))
    (ha : 1 ≤ a) (h3 : N ≤ 3 * a) : CoReach N B :=
  coReach_compact hB ha (by omega) (by omega) (by omega)

/-! ## Dyadic sets -/

/-- **Dyadic sets are co-reachable.**  `2x ≤ y` for all `x < y` in `B`, and every non-least
`y ∈ B` has a smaller `x ∈ B` with `2y ≤ N + x + 2`.  Centre: the least element of `B`. -/
theorem coReach_dyadic {N : Nat} {B : Finset Nat} (hB : B ⊆ Finset.Icc 1 N)
    (hdy : ∀ x ∈ B, ∀ y ∈ B, x < y → 2 * x ≤ y)
    (htop : ∀ y ∈ B, (∃ x ∈ B, x < y) → ∃ x ∈ B, x < y ∧ 2 * y ≤ N + x + 2) :
    CoReach N B := by
  have hBN : ∀ x ∈ B, 1 ≤ x ∧ x ≤ N := fun x hx => Finset.mem_Icc.1 (hB hx)
  by_cases hne : B.Nonempty
  · obtain ⟨d, hdB, hdmin⟩ : ∃ d ∈ B, ∀ x ∈ B, d ≤ x :=
      ⟨B.min' hne, Finset.min'_mem B hne, fun x hx => Finset.min'_le B x hx⟩
    refine coReach_of_inward hB (c2 := 2 * d) ?_
    intro m hm1 hmN hmB
    have hmd : m ≠ d := fun e => hmB (e ▸ hdB)
    refine ⟨by omega, fun hlt => ?_, fun hgt => ?_⟩
    · rw [armL_eq]
      have : (B.filter (fun x => m - reach N m ≤ x ∧ x < m)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x hx; have := hdmin x hx; omega
      omega
    · rw [armL_eq, armR_eq]
      -- at most one element of `B` in the right arm
      have hle : (B.filter (fun x => m < x ∧ x ≤ m + reach N m)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        rw [Finset.mem_filter] at hx hy
        have hr : reach N m ≤ m - 1 := by unfold reach; omega
        by_contra hxy
        rcases Nat.lt_or_gt_of_ne hxy with h | h
        · have := hdy x hx.1 y hy.1 h; omega
        · have := hdy y hy.1 x hx.1 h; omega
      rcases Nat.lt_or_ge (B.filter (fun x => m < x ∧ x ≤ m + reach N m)).card 1 with h0 | h1
      · omega
      · obtain ⟨y, hy⟩ := Finset.card_pos.1 (by omega :
          0 < (B.filter (fun x => m < x ∧ x ≤ m + reach N m)).card)
        rw [Finset.mem_filter] at hy
        suffices hpos : 0 < (B.filter (fun x => m - reach N m ≤ x ∧ x < m)).card by omega
        rw [Finset.card_pos]
        by_cases hdl : m - reach N m ≤ d
        · exact ⟨d, Finset.mem_filter.2 ⟨hdB, hdl, by omega⟩⟩
        · have hr : reach N m = N - m := by
            have := hBN d hdB
            rcases reach_cases N m with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
          obtain ⟨x, hxB, hxy, hx2⟩ := htop y hy.1 ⟨d, hdB, by have := hy.2.1; omega⟩
          have := hdy x hxB y hy.1 hxy
          have := hBN y hy.1
          refine ⟨x, Finset.mem_filter.2 ⟨hxB, ?_, ?_⟩⟩
          · rw [hr]; omega
          · omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    refine coReach_of_inward hB (c2 := 0) ?_
    intro m hm1 _ _
    simp [leftCount_eq, rightCount_eq]
    omega

/-- Every dyadic set inside the left half `2y ≤ N + 1` is co-reachable. -/
theorem coReach_dyadic_half {N : Nat} {B : Finset Nat} (hB : B ⊆ Finset.Icc 1 N)
    (hdy : ∀ x ∈ B, ∀ y ∈ B, x < y → 2 * x ≤ y) (hhalf : ∀ y ∈ B, 2 * y ≤ N + 1) :
    CoReach N B :=
  coReach_dyadic hB hdy fun y hy ⟨x, hx, hxy⟩ => ⟨x, hx, hxy, by have := hhalf y hy; omega⟩

/-- The mirror images of dyadic sets: `N + 1 - ·` maps a set satisfying the hypotheses of
`coReach_dyadic` to a co-reachable set. -/
theorem coReach_dyadic_mirror {N : Nat} {B : Finset Nat} (hB : B ⊆ Finset.Icc 1 N)
    (hdy : ∀ x ∈ B, ∀ y ∈ B, x < y → 2 * x ≤ y)
    (htop : ∀ y ∈ B, (∃ x ∈ B, x < y) → ∃ x ∈ B, x < y ∧ 2 * y ≤ N + x + 2) :
    CoReach N (B.image (N + 1 - ·)) :=
  coReach_mirror (coReach_dyadic hB hdy htop)

/-! ## Doubling-sparse sets in the left half -/

/-- **Doubling-sparse sets are co-reachable.**  `B` lies in the left half (`2y ≤ N + 1`), and
for every element `y` of `B` other than the least, `B` has at most as many elements in
`[y, 2y - 3]` as below `y`.  Sorted `d₁ < d₂ < ⋯`, this says `d_{2i+1} ≥ 2 d_{i+1} - 2`; it
contains every dyadic set of the left half.  Centre: the least element. -/
theorem coReach_sparse {N : Nat} {B : Finset Nat} (hB : B ⊆ Finset.Icc 1 N)
    (hhalf : ∀ y ∈ B, 2 * y ≤ N + 1)
    (hsp : ∀ y ∈ B, (∃ x ∈ B, x < y) →
      (B.filter (fun z => y ≤ z ∧ z + 2 < 2 * y)).card ≤ (B.filter (fun z => z < y)).card) :
    CoReach N B := by
  have hBN : ∀ x ∈ B, 1 ≤ x ∧ x ≤ N := fun x hx => Finset.mem_Icc.1 (hB hx)
  by_cases hne : B.Nonempty
  · obtain ⟨d, hdB, hdmin⟩ : ∃ d ∈ B, ∀ x ∈ B, d ≤ x :=
      ⟨B.min' hne, Finset.min'_mem B hne, fun x hx => Finset.min'_le B x hx⟩
    refine coReach_of_inward hB (c2 := 2 * d) ?_
    intro m hm1 hmN hmB
    have hmd : m ≠ d := fun e => hmB (e ▸ hdB)
    refine ⟨by omega, fun hlt => ?_, fun hgt => ?_⟩
    · rw [armL_eq]
      have : (B.filter (fun x => m - reach N m ≤ x ∧ x < m)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x hx; have := hdmin x hx; omega
      omega
    · rw [armL_eq, armR_eq]
      by_cases hR : (B.filter (fun x => m < x)).Nonempty
      · rcases reach_cases N m with ⟨hr, hr'⟩ | ⟨hr, hr'⟩
        · -- left half: the left arm is `[1, m - 1]`
          obtain ⟨y, hyR, hymin⟩ : ∃ y ∈ B.filter (fun x => m < x),
              ∀ x ∈ B.filter (fun x => m < x), y ≤ x :=
            ⟨_, Finset.min'_mem _ hR, fun x hx => Finset.min'_le _ x hx⟩
          rw [Finset.mem_filter] at hyR
          have h1 := hsp y hyR.1 ⟨d, hdB, by omega⟩
          have e1 : B.filter (fun x => m - reach N m ≤ x ∧ x < m) =
              B.filter (fun z => z < y) := by
            apply Finset.filter_congr
            intro x hx
            have := hBN x hx
            constructor
            · intro h; omega
            · intro h
              refine ⟨by omega, ?_⟩
              by_contra hxm
              have hxm' : m < x := by
                rcases Nat.lt_or_ge m x with h' | h'
                · exact h'
                · exact absurd (show x = m by omega ▸ hx) hmB
              have := hymin x (Finset.mem_filter.2 ⟨hx, hxm'⟩)
              omega
          have l1 : (B.filter (fun x => m < x ∧ x ≤ m + reach N m)).card ≤
              (B.filter (fun z => y ≤ z ∧ z + 2 < 2 * y)).card := by
            apply Finset.card_le_card
            intro x hx
            rw [Finset.mem_filter] at hx ⊢
            have := hymin x (Finset.mem_filter.2 ⟨hx.1, hx.2.1⟩)
            exact ⟨hx.1, this, by omega⟩
          rw [e1]; omega
        · -- right half: nothing of `B` is right of `m`
          exfalso
          obtain ⟨y, hy⟩ := hR
          rw [Finset.mem_filter] at hy
          have := hhalf y hy.1
          have := hBN d hdB
          omega
      · have : (B.filter (fun x => m < x ∧ x ≤ m + reach N m)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x hx h
          exact hR ⟨x, Finset.mem_filter.2 ⟨hx, h.1⟩⟩
        omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    refine coReach_of_inward hB (c2 := 0) ?_
    intro m hm1 _ _
    simp [leftCount_eq, rightCount_eq]
    omega

/-- The mirror images of doubling-sparse sets are co-reachable. -/
theorem coReach_sparse_mirror {N : Nat} {B : Finset Nat} (hB : B ⊆ Finset.Icc 1 N)
    (hhalf : ∀ y ∈ B, 2 * y ≤ N + 1)
    (hsp : ∀ y ∈ B, (∃ x ∈ B, x < y) →
      (B.filter (fun z => y ≤ z ∧ z + 2 < 2 * y)).card ≤ (B.filter (fun z => z < y)).card) :
    CoReach N (B.image (N + 1 - ·)) :=
  coReach_mirror (coReach_sparse hB hhalf hsp)

/-! ## Anchored sets: Theorem G with the centre at the least element -/

/-- **Anchored sets are co-reachable.**  For every element `y` of `B` other than the least,
(i) `B` has at most as many elements in `[y, 2y - 3]` as below `y`, and (ii) if `2y ≥ N + 4`,
at most as many in `[y, N]` as in `[2y - N - 2, y - 1]`.  Then every free panel right of the
least element `d` is pulled to the left by `B` (or not at all), and Theorem G applies with
centre `d`: for a free `m > d` let `y` be the next element of `B` after `m`; the right arm of
`m` holds at most the elements of `[y, 2y - 3]` (left half) resp. `[y, N]` (right half), the
left arm at least those below `y` resp. in `[2y - N - 2, y - 1]`.  This contains the
doubling-sparse sets (`coReach_sparse`) and the dyadic sets (`coReach_dyadic`). -/
theorem coReach_anchored {N : Nat} {B : Finset Nat} (hB : B ⊆ Finset.Icc 1 N)
    (h1 : ∀ y ∈ B, (∃ x ∈ B, x < y) →
      (B.filter (fun z => y ≤ z ∧ z + 3 ≤ 2 * y)).card ≤ (B.filter (fun z => z < y)).card)
    (h2 : ∀ y ∈ B, (∃ x ∈ B, x < y) → N + 4 ≤ 2 * y →
      (B.filter (fun z => y ≤ z)).card ≤
        (B.filter (fun z => 2 * y ≤ N + 2 + z ∧ z < y)).card) :
    CoReach N B := by
  have hBN : ∀ x ∈ B, 1 ≤ x ∧ x ≤ N := fun x hx => Finset.mem_Icc.1 (hB hx)
  by_cases hne : B.Nonempty
  · obtain ⟨d, hdB, hdmin⟩ : ∃ d ∈ B, ∀ x ∈ B, d ≤ x :=
      ⟨B.min' hne, Finset.min'_mem B hne, fun x hx => Finset.min'_le B x hx⟩
    refine coReach_of_inward hB (c2 := 2 * d) ?_
    intro m hm1 hmN hmB
    have hmd : m ≠ d := fun e => hmB (e ▸ hdB)
    refine ⟨by omega, fun hlt => ?_, fun hgt => ?_⟩
    · rw [armL_eq]
      have : (B.filter (fun x => m - reach N m ≤ x ∧ x < m)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x hx; have := hdmin x hx; omega
      omega
    · rw [armL_eq, armR_eq]
      by_cases hR : (B.filter (fun x => m < x)).Nonempty
      · obtain ⟨y, hyR, hymin⟩ : ∃ y ∈ B.filter (fun x => m < x),
            ∀ x ∈ B.filter (fun x => m < x), y ≤ x :=
          ⟨_, Finset.min'_mem _ hR, fun x hx => Finset.min'_le _ x hx⟩
        rw [Finset.mem_filter] at hyR
        -- below `y` means below `m`
        have hbelow : ∀ x ∈ B, x < y → x < m := by
          intro x hx hxy
          by_contra hxm
          have hxm' : m < x := by
            rcases Nat.lt_or_ge m x with h' | h'
            · exact h'
            · exact absurd (show x = m by omega ▸ hx) hmB
          have := hymin x (Finset.mem_filter.2 ⟨hx, hxm'⟩)
          omega
        have hd' := hBN d hdB
        by_cases hhalf : m - 1 ≤ N - m
        · have hr : reach N m = m - 1 := by unfold reach; exact min_eq_left hhalf
          have e1 : B.filter (fun x => m - reach N m ≤ x ∧ x < m) =
              B.filter (fun z => z < y) := by
            apply Finset.filter_congr
            intro x hx
            have := hBN x hx
            constructor
            · intro h; omega
            · intro h; have := hbelow x hx h; omega
          have l1 : (B.filter (fun x => m < x ∧ x ≤ m + reach N m)).card ≤
              (B.filter (fun z => y ≤ z ∧ z + 3 ≤ 2 * y)).card := by
            apply Finset.card_le_card
            intro x hx
            rw [Finset.mem_filter] at hx ⊢
            have := hymin x (Finset.mem_filter.2 ⟨hx.1, hx.2.1⟩)
            exact ⟨hx.1, this, by omega⟩
          have := h1 y hyR.1 ⟨d, hdB, by omega⟩
          rw [e1]; omega
        · have hr : reach N m = N - m := by unfold reach; exact min_eq_right (by omega)
          have e2 : B.filter (fun x => m < x ∧ x ≤ m + reach N m) =
              B.filter (fun z => y ≤ z) := by
            apply Finset.filter_congr
            intro x hx
            have := hBN x hx
            constructor
            · intro h; exact hymin x (Finset.mem_filter.2 ⟨hx, h.1⟩)
            · intro h; omega
          have l2 : (B.filter (fun z => 2 * y ≤ N + 2 + z ∧ z < y)).card ≤
              (B.filter (fun x => m - reach N m ≤ x ∧ x < m)).card := by
            apply Finset.card_le_card
            intro x hx
            rw [Finset.mem_filter] at hx ⊢
            have := hbelow x hx.1 hx.2.2
            exact ⟨hx.1, by omega, this⟩
          have := h2 y hyR.1 ⟨d, hdB, by omega⟩ (by omega)
          rw [e2]; omega
      · have : (B.filter (fun x => m < x ∧ x ≤ m + reach N m)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x hx h
          exact hR ⟨x, Finset.mem_filter.2 ⟨hx, h.1⟩⟩
        omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    refine coReach_of_inward hB (c2 := 0) ?_
    intro m hm1 _ _
    simp [leftCount_eq, rightCount_eq]
    omega

/-! ## Live prefixes of any length -/

theorem extends_of_coReach {N : Nat} {p : List Nat} (hnd : p.Nodup)
    (hp : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N) (hv : SemiSymmetric N p) (h : CoReach N p.toFinset) :
    Extends N p :=
  (extends_iff_coReach hnd hp hv).2 h

/-- Every valid prefix (any length) inside a compact window `[a, b]` is live. -/
theorem extends_compact {N a b : Nat} {p : List Nat} (hnd : p.Nodup) (hv : SemiSymmetric N p)
    (hp : ∀ x ∈ p, a ≤ x ∧ x ≤ b) (ha : 1 ≤ a) (hbN : b ≤ N) (h1 : b ≤ 2 * a + 1)
    (h2 : 2 * b ≤ N + a + 2) : Extends N p :=
  extends_of_coReach hnd (fun x hx => by have := hp x hx; omega) hv
    (coReach_compact (fun x hx => by
      rw [List.mem_toFinset] at hx; rw [Finset.mem_Icc]; exact hp x hx) ha hbN h1 h2)

/-- Every valid prefix (any length) inside the middle third `[a, N + 1 - a]`, `N ≤ 3a`, is
live. -/
theorem extends_middle {N a : Nat} {p : List Nat} (hnd : p.Nodup) (hv : SemiSymmetric N p)
    (hp : ∀ x ∈ p, a ≤ x ∧ x ≤ N + 1 - a) (ha : 1 ≤ a) (h3 : N ≤ 3 * a) : Extends N p :=
  extends_compact hnd hv hp ha (by omega) (by omega) (by omega)

/-- Every valid prefix whose set is dyadic (in the sense of `coReach_dyadic`) is live. -/
theorem extends_dyadic {N : Nat} {p : List Nat} (hnd : p.Nodup) (hv : SemiSymmetric N p)
    (hp : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N) (hdy : ∀ x ∈ p, ∀ y ∈ p, x < y → 2 * x ≤ y)
    (htop : ∀ y ∈ p, (∃ x ∈ p, x < y) → ∃ x ∈ p, x < y ∧ 2 * y ≤ N + x + 2) :
    Extends N p :=
  extends_of_coReach hnd hp hv (coReach_dyadic
    (fun x hx => by rw [List.mem_toFinset] at hx; rw [Finset.mem_Icc]; exact hp x hx)
    (fun x hx y hy => hdy x (List.mem_toFinset.1 hx) y (List.mem_toFinset.1 hy))
    (fun y hy ⟨x, hx, hxy⟩ => by
      obtain ⟨z, hz, h⟩ := htop y (List.mem_toFinset.1 hy) ⟨x, List.mem_toFinset.1 hx, hxy⟩
      exact ⟨z, List.mem_toFinset.2 hz, h⟩))

/-- Every valid prefix whose panels lie in the left half and are pairwise at least doubling
is live. -/
theorem extends_dyadic_half {N : Nat} {p : List Nat} (hnd : p.Nodup) (hv : SemiSymmetric N p)
    (hp : ∀ x ∈ p, 1 ≤ x ∧ 2 * x ≤ N + 1) (hdy : ∀ x ∈ p, ∀ y ∈ p, x < y → 2 * x ≤ y) :
    Extends N p :=
  extends_dyadic hnd hv (fun x hx => by have := hp x hx; omega) hdy
    fun y hy ⟨x, hx, hxy⟩ => ⟨x, hx, hxy, by have := hp y hy; omega⟩

/-- Every valid prefix whose mirror image is dyadic is live. -/
theorem extends_dyadic_mirror {N : Nat} {p : List Nat} (hnd : p.Nodup) (hv : SemiSymmetric N p)
    (hp : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N)
    (hdy : ∀ x ∈ p, ∀ y ∈ p, x < y → 2 * (N + 1 - y) ≤ N + 1 - x)
    (htop : ∀ y ∈ p, (∃ x ∈ p, y < x) →
      ∃ x ∈ p, y < x ∧ 2 * (N + 1 - y) ≤ N + (N + 1 - x) + 2) :
    Extends N p := by
  refine extends_of_coReach hnd hp hv ?_
  set B := p.toFinset.image (N + 1 - ·) with hBdef
  have hmemB : ∀ z, z ∈ B ↔ ∃ x ∈ p, N + 1 - x = z := by
    intro z; rw [hBdef, Finset.mem_image]; simp only [List.mem_toFinset]
  have hBs : B ⊆ Finset.Icc 1 N := by
    intro z hz; obtain ⟨x, hx, rfl⟩ := (hmemB z).1 hz; have := hp x hx
    rw [Finset.mem_Icc]; omega
  have hinv : B.image (N + 1 - ·) = p.toFinset := by
    ext z
    rw [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hmemB w).1 hw
      have := hp x hx
      rwa [show N + 1 - (N + 1 - x) = x by omega]
    · intro hz
      have := hp z hz
      exact ⟨N + 1 - z, (hmemB _).2 ⟨z, hz, rfl⟩, by omega⟩
  rw [← hinv]
  refine coReach_dyadic_mirror hBs ?_ ?_
  · intro u hu w hw huw
    obtain ⟨x, hx, rfl⟩ := (hmemB u).1 hu
    obtain ⟨y, hy, rfl⟩ := (hmemB w).1 hw
    have := hp x hx; have := hp y hy
    have := hdy y hy x hx (by omega)
    omega
  · intro w hw ⟨u, hu, huw⟩
    obtain ⟨y, hy, rfl⟩ := (hmemB w).1 hw
    obtain ⟨x, hx, rfl⟩ := (hmemB u).1 hu
    have := hp x hx; have := hp y hy
    obtain ⟨z, hz, hyz, h⟩ := htop y hy ⟨x, hx, by omega⟩
    have := hp z hz
    exact ⟨N + 1 - z, (hmemB _).2 ⟨z, hz, rfl⟩, by omega, by omega⟩

/-! ## The explicit family -/

/-- `CovK N D`: the explicit families of this file (compact, dyadic, doubling-sparse, anchored)
and their
mirror images, for sets of any size. -/
inductive CovK : Nat → Finset Nat → Prop
  | compact {N a b : Nat} {D : Finset Nat} : D ⊆ Finset.Icc a b → 1 ≤ a → b ≤ N →
      b ≤ 2 * a + 1 → 2 * b ≤ N + a + 2 → CovK N D
  | dyadic {N : Nat} {D : Finset Nat} : D ⊆ Finset.Icc 1 N →
      (∀ x ∈ D, ∀ y ∈ D, x < y → 2 * x ≤ y) →
      (∀ y ∈ D, (∃ x ∈ D, x < y) → ∃ x ∈ D, x < y ∧ 2 * y ≤ N + x + 2) → CovK N D
  | sparse {N : Nat} {D : Finset Nat} : D ⊆ Finset.Icc 1 N → (∀ y ∈ D, 2 * y ≤ N + 1) →
      (∀ y ∈ D, (∃ x ∈ D, x < y) →
        (D.filter (fun z => y ≤ z ∧ z + 2 < 2 * y)).card ≤ (D.filter (fun z => z < y)).card) →
      CovK N D
  | anchored {N : Nat} {D : Finset Nat} : D ⊆ Finset.Icc 1 N →
      (∀ y ∈ D, (∃ x ∈ D, x < y) →
        (D.filter (fun z => y ≤ z ∧ z + 3 ≤ 2 * y)).card ≤ (D.filter (fun z => z < y)).card) →
      (∀ y ∈ D, (∃ x ∈ D, x < y) → N + 4 ≤ 2 * y →
        (D.filter (fun z => y ≤ z)).card ≤
          (D.filter (fun z => 2 * y ≤ N + 2 + z ∧ z < y)).card) → CovK N D
  | mirror {N : Nat} {D : Finset Nat} : CovK N D → CovK N (D.image (N + 1 - ·))

theorem CovK.coReach {N : Nat} {D : Finset Nat} (h : CovK N D) : CoReach N D := by
  induction h with
  | compact hD ha hb h1 h2 => exact coReach_compact hD ha hb h1 h2
  | dyadic hD hdy htop => exact coReach_dyadic hD hdy htop
  | sparse hD hh hsp => exact coReach_sparse hD hh hsp
  | anchored hD h1 h2 => exact coReach_anchored hD h1 h2
  | mirror _ ih => exact coReach_mirror ih

/-- **Prefix liveness for every length.**  Every valid prefix of any length `k`, for any `N`,
whose set is in the family `CovK` is live. -/
theorem CovK.extends {N : Nat} {p : List Nat} (hnd : p.Nodup) (hp : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N)
    (hv : SemiSymmetric N p) (h : CovK N p.toFinset) : Extends N p :=
  extends_of_coReach hnd hp hv h.coReach

/-- Every valid prefix whose set is doubling-sparse in the left half is live. -/
theorem extends_sparse {N : Nat} {p : List Nat} (hnd : p.Nodup) (hv : SemiSymmetric N p)
    (hp : ∀ x ∈ p, 1 ≤ x ∧ 2 * x ≤ N + 1)
    (hsp : ∀ y ∈ p.toFinset, (∃ x ∈ p.toFinset, x < y) →
      (p.toFinset.filter (fun z => y ≤ z ∧ z + 2 < 2 * y)).card ≤
        (p.toFinset.filter (fun z => z < y)).card) :
    Extends N p :=
  CovK.extends hnd (fun x hx => by have := hp x hx; omega) hv
    (CovK.sparse (fun x hx => by
      rw [List.mem_toFinset] at hx; have := hp x hx; rw [Finset.mem_Icc]; omega)
      (fun y hy => (hp y (List.mem_toFinset.1 hy)).2) hsp)

/-- Every valid prefix whose set is anchored (`coReach_anchored`) is live. -/
theorem extends_anchored {N : Nat} {p : List Nat} (hnd : p.Nodup) (hv : SemiSymmetric N p)
    (hp : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N)
    (h1 : ∀ y ∈ p.toFinset, (∃ x ∈ p.toFinset, x < y) →
      (p.toFinset.filter (fun z => y ≤ z ∧ z + 3 ≤ 2 * y)).card ≤
        (p.toFinset.filter (fun z => z < y)).card)
    (h2 : ∀ y ∈ p.toFinset, (∃ x ∈ p.toFinset, x < y) → N + 4 ≤ 2 * y →
      (p.toFinset.filter (fun z => y ≤ z)).card ≤
        (p.toFinset.filter (fun z => 2 * y ≤ N + 2 + z ∧ z < y)).card) :
    Extends N p :=
  CovK.extends hnd hp hv (CovK.anchored (fun x hx => by
    rw [List.mem_toFinset] at hx; rw [Finset.mem_Icc]; exact hp x hx) h1 h2)

/-! ## Halving prefixes: a positive proportion of live prefixes for every `k` -/

/-- A halving sequence `x₁, x₂, …` (`2 x_{j+1} ≤ x_j`, all `≥ 1`) is a valid prefix: the
window of each new panel `m` lies inside `[1, 2m - 1]`, and every earlier panel is `≥ 2m`. -/
theorem semiSymmetric_halving {N : Nat} {p : List Nat}
    (hpw : p.Pairwise (fun a b => 2 * b ≤ a)) (hp : ∀ x ∈ p, 1 ≤ x) : SemiSymmetric N p := by
  intro k hk
  have hnd : (p.take k).Nodup := by
    have : p.Nodup := hpw.imp_of_mem fun {a b} ha _ h => by
      intro e; subst e
      have := hp a ha
      omega
    exact this.sublist (List.take_sublist k p)
  have hm1 := hp _ (List.getElem_mem hk)
  have hbig : ∀ x ∈ p.take k, 2 * p[k] ≤ x := by
    have e := List.take_append_drop k p
    rw [← e] at hpw
    have := (List.pairwise_append.1 hpw).2.2
    intro x hx
    exact this x hx _ (by rw [List.drop_eq_getElem_cons hk]; exact List.mem_cons_self)
  unfold SemiStep
  rw [leftCount_eq hnd, rightCount_eq hnd]
  have hr : reach N p[k] ≤ p[k] - 1 := by unfold reach; omega
  rw [List.countP_eq_zero.2 (fun x hx => by have := hbig x hx; simp; omega),
    List.countP_eq_zero.2 (fun x hx => by have := hbig x hx; simp; omega)]

/-- **Halving prefixes are live.**  If `x₁ ≤ (N+1)/2` and `2 x_{j+1} ≤ x_j`, the prefix
`[x₁, …, x_k]` is valid and live, for every `N` and `k`.  (There are about
`N^k / (k! 2^{k(k+1)/2})` of them, a positive proportion of the `≈ c_k N^k` valid prefixes.) -/
theorem extends_halving {N : Nat} {p : List Nat}
    (hpw : p.Pairwise (fun a b => 2 * b ≤ a)) (hp : ∀ x ∈ p, 1 ≤ x ∧ 2 * x ≤ N + 1) :
    Extends N p := by
  have hnd : p.Nodup := hpw.imp_of_mem fun {a b} ha _ h => by
    intro e; subst e
    have := (hp a ha).1
    omega
  have hsym : (p.Pairwise (fun a b => 2 * b ≤ a ∨ 2 * a ≤ b)) := hpw.imp Or.inl
  exact extends_dyadic_half hnd (semiSymmetric_halving hpw fun x hx => (hp x hx).1) hp
    fun x hx y hy hxy => by
      have := (hp y hy).1
      have : Std.Symm (fun a b : Nat => 2 * b ≤ a ∨ 2 * a ≤ b) := ⟨fun _ _ h => h.symm⟩
      rcases hsym.forall hx hy (by omega) with h | h
      · omega
      · exact h

/-! ## Examples -/

/-- The middle third for `N = 40`: every subset of `[14, 27]` is co-reachable. -/
example (B : Finset Nat) (hB : B ⊆ Finset.Icc 14 27) : CoReach 40 B :=
  coReach_middle hB (by omega) (by omega)

/-- A dyadic 5-set reaching into the right half: `{1, 3, 6, 13, 27}` for `N = 40`. -/
example : CoReach 40 {1, 3, 6, 13, 27} := by
  apply coReach_dyadic
  · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Icc]; omega
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    omega
  · intro y hy hex
    obtain ⟨x, hx, hxy⟩ := hex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    by_cases h : y = 27
    · exact ⟨13, by simp, by omega, by omega⟩
    · exact ⟨1, by simp, by omega, by omega⟩

end LiveK
end Folds
