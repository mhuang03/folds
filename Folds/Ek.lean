import Folds.LiveK
import Folds.Live7

/-!
# Conjecture E_k: dead sets avoiding the end panels

`experiments/ek/PROOFS.txt`.

* `bg_of_coReach`: the background form of co-reachability: if `D` is co-reachable, the panels
  outside `D` can be placed one by one on the background `D`, every step valid.
* `coReach_of_insert`, `coReach_of_insert_one`, `coReach_of_insert_N`: **removing a valid panel
  keeps co-reachability**; in particular removing an end panel (`1` or `N`, empty window).  So a
  dead set avoiding `1` stays dead when `1` is added (and likewise `N`).
* `not_coReach_b4` (**the B4 family**): for `j ≥ 3` and `2j + 3 ≤ N`, every set `D` with
  `2 ∈ D`, `1 ∉ D`, `{2j, 2j+1, 2j+2, 2j+3} ⊆ D` and nothing of `D` in `[3, 2j-1]` is dead.
  `not_coReach_b4_mirror`: the mirror images.  In particular the 5-sets
  `{2, 2j, 2j+1, 2j+2, 2j+3}` (`2j + 3 ≤ N - 1`) are dead and avoid both end panels.
* `not_finite_exceptions_five`: **Conjecture E_5 fails with any finite exception list.**
* `anchor_step`, `not_coReach_anchor` (**the anchored-block family `B_a`**, every `a ≥ 1`): if
  `a ∈ D`, `[2j, 2j + 2a - 1] ⊆ D`, `D ∩ [a + 1, 2j - 1] = ∅`, `j ≥ a + 1` and
  `2j + 2a - 1 ≤ N`, then `D` is dead (invariant: the placed panels of `[a + 1, 2j - 1]` lie in
  `[j + 1, j + p]` and number at most `p`, where `p ≤ a - 1` counts the placed panels below `a`).
  `not_coReach_anchorSet`, `exists_dead_far`: dead `(2a+1)`-sets inside `[a, N - a]`, so no
  fixed distance from the ends works for all `k`; the radius must grow like `k / 2`.
* `card_dead_le`: **the counting corollary.**  If every dead `k`-subset of `[N]` meets
  `[1, c] ∪ [N+1-c, N]` or lies in a list `E` of exceptions, then the number of dead `k`-subsets
  is at most `2c · C(N-1, k-1) + |E|`.  `card_dead_le_of_Ek`: the case `c = 1` (Conjecture E_k
  as stated); `card_dead_pairs_le_64`: unconditionally for `k = 2`, `N ≤ 64` (Conjecture C,
  `Live7.coReach_le_64`): at most `2(N-1)` dead pairs.
-/

namespace Folds
namespace Ek

open Live2 Live4 Adjacent LiveK

/-! ## The background form of co-reachability -/

theorem foldSeq_bg {N : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 N) {a : List Nat}
    (hnd : a.Nodup) (hmem : ∀ x, x ∈ a ↔ (1 ≤ x ∧ x ≤ N) ∧ x ∉ D) :
    IsFoldSeq N (D.toList ++ a) := by
  unfold IsFoldSeq
  have hnd' : (D.toList ++ a).Nodup := by
    rw [List.nodup_append]
    refine ⟨Finset.nodup_toList D, hnd, ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact ((hmem x).1 hy).2 (Finset.mem_toList.1 hx)
  rw [List.perm_ext_iff_of_nodup hnd' List.nodup_range']
  intro x
  rw [List.mem_append, Finset.mem_toList, List.mem_range'_1, hmem]
  constructor
  · rintro (hx | hx)
    · have := Finset.mem_Icc.1 (hD hx); omega
    · omega
  · intro hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr ⟨⟨hx.1, by omega⟩, hxD⟩

/-- **Background form.**  If `D` is co-reachable, the panels outside `D` can be placed on the
background `D`, every step valid. -/
theorem bg_of_coReach {N : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 N) (h : CoReach N D) :
    ∃ a : List Nat, a.Nodup ∧ (∀ x, x ∈ a ↔ (1 ≤ x ∧ x ≤ N) ∧ x ∉ D) ∧
      ∀ k (hk : k < a.length), SemiStep N (D.toList ++ a.take k) a[k] := by
  unfold CoReach g at h
  rw [Finset.card_pos] at h
  obtain ⟨l, hl⟩ := h
  rw [mem_semiOrders] at hl
  obtain ⟨⟨hnd, hs⟩, hv⟩ := hl
  have hm : ∀ x, x ∈ l ↔ (1 ≤ x ∧ x ≤ N) ∧ x ∉ D := by
    intro x; rw [← List.mem_toFinset, hs]; simp
  have hmB : ∀ x, x ∈ l.reverse ↔ (1 ≤ x ∧ x ≤ N) ∧ x ∉ D := by
    intro x; rw [List.mem_reverse]; exact hm x
  refine ⟨l.reverse, List.nodup_reverse.2 hnd, hmB, ?_⟩
  have hf := foldSeq_bg hD (List.nodup_reverse.2 hnd) hmB
  have hB : SemiSymmetric N l.reverse.reverse := by rw [List.reverse_reverse]; exact hv
  generalize l.reverse = B at hf hB
  intro i hi
  have e : D.toList ++ B = (D.toList ++ B.take i) ++ [B[i]] ++ B.drop (i + 1) := by
    simp only [List.append_assoc, List.singleton_append]
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  rw [e] at hf
  rw [semiStep_compl hf]
  have hj : B.length - 1 - i < B.reverse.length := by simp; omega
  have := hB (B.length - 1 - i) hj
  rw [List.take_reverse, List.getElem_reverse] at this
  rw [show B.length - (B.length - 1 - i) = i + 1 by omega] at this
  have e2 : B.length - 1 - (B.length - 1 - i) = i := by omega
  simp only [e2] at this
  exact (semiStep_congr fun x => by simp).1 this

/-! ## Removing a valid panel, in particular an end panel -/

/-- **Removing a valid panel keeps co-reachability.**  If `x ∉ D` is a valid step on the
background `D` and `D ∪ {x}` is co-reachable, so is `D`: append `x` to the ordering. -/
theorem coReach_of_insert {N x : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 N)
    (hx1 : 1 ≤ x) (hxN : x ≤ N) (hxD : x ∉ D) (hv : SemiStep N D.toList x)
    (h : CoReach N (insert x D)) : CoReach N D := by
  unfold CoReach g at h ⊢
  rw [Finset.card_pos] at h ⊢
  obtain ⟨l, hl⟩ := h
  rw [mem_semiOrders] at hl
  obtain ⟨⟨hnd, hs⟩, hsv⟩ := hl
  have hm : ∀ y, y ∈ l ↔ (1 ≤ y ∧ y ≤ N) ∧ y ≠ x ∧ y ∉ D := by
    intro y; rw [← List.mem_toFinset, hs]; simp
  have hxl : x ∉ l := fun h' => ((hm x).1 h').2.1 rfl
  have hnd' : (l ++ [x]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, List.nodup_singleton x, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    subst hb hab
    exact hxl ha
  refine ⟨l ++ [x], mem_semiOrders.2 ⟨⟨hnd', ?_⟩, ?_⟩⟩
  · ext y
    simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset, hm,
      List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton,
      Finset.mem_sdiff, Finset.mem_Icc]
    constructor
    · rintro (⟨h1, _, h3⟩ | rfl)
      · exact ⟨h1, h3⟩
      · exact ⟨⟨hx1, hxN⟩, hxD⟩
    · rintro ⟨h1, h3⟩
      by_cases hyx : y = x
      · exact Or.inr hyx
      · exact Or.inl ⟨h1, hyx, h3⟩
  · refine semiSymmetric_concat_iff.2 ⟨hsv, ?_⟩
    have hmB : ∀ y, y ∈ D.toList.reverse ↔ (1 ≤ y ∧ y ≤ N) ∧ y ∉ l ++ [x] := by
      intro y
      rw [List.mem_reverse, Finset.mem_toList, List.mem_append, List.mem_singleton, hm]
      constructor
      · intro hy
        have := Finset.mem_Icc.1 (hD hy)
        refine ⟨this, ?_⟩
        rintro (⟨_, _, h3⟩ | rfl)
        · exact h3 hy
        · exact hxD hy
      · rintro ⟨h1, h2⟩
        by_contra hyD
        by_cases hyx : y = x
        · exact h2 (Or.inr hyx)
        · exact h2 (Or.inl ⟨h1, hyx, hyD⟩)
    have hf : IsFoldSeq N (l ++ [x] ++ D.toList) := by
      have hf0 := foldSeq_bg (D := (l ++ [x]).toFinset) (a := D.toList.reverse)
        (fun y hy => by
          rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · exact Finset.mem_Icc.2 ((hm y).1 hy).1
          · exact Finset.mem_Icc.2 ⟨hx1, hxN⟩)
        (List.nodup_reverse.2 (Finset.nodup_toList D))
        (fun y => by rw [hmB, List.mem_toFinset])
      have hp : ((l ++ [x]).toFinset.toList ++ D.toList.reverse).Perm (l ++ [x] ++ D.toList) :=
        List.Perm.append (List.toFinset_toList hnd') (List.reverse_perm _)
      exact hp.symm.trans hf0
    rw [semiStep_compl hf]
    exact hv

/-- An end panel has an empty window: every step at it is valid. -/
theorem semiStep_of_reach_zero {N m : Nat} {S : List Nat} (h : reach N m = 0) :
    SemiStep N S m := by
  unfold SemiStep leftCount rightCount
  rw [h]; rfl

/-- Removing panel `1` keeps co-reachability. -/
theorem coReach_of_insert_one {N : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 N) (hN : 1 ≤ N)
    (h1 : 1 ∉ D) (h : CoReach N (insert 1 D)) : CoReach N D :=
  coReach_of_insert hD le_rfl hN h1 (semiStep_of_reach_zero (by unfold reach; omega)) h

/-- Removing panel `N` keeps co-reachability. -/
theorem coReach_of_insert_N {N : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 N) (hN : 1 ≤ N)
    (hND : N ∉ D) (h : CoReach N (insert N D)) : CoReach N D :=
  coReach_of_insert hD hN le_rfl hND (semiStep_of_reach_zero (by unfold reach; omega)) h

/-- Contrapositive: a dead set avoiding `1` stays dead when `1` is added. -/
theorem not_coReach_insert_one {N : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 N) (hN : 1 ≤ N)
    (h1 : 1 ∉ D) (h : ¬ CoReach N D) : ¬ CoReach N (insert 1 D) :=
  fun h' => h (coReach_of_insert_one hD hN h1 h')

/-- Contrapositive: a dead set avoiding `N` stays dead when `N` is added. -/
theorem not_coReach_insert_N {N : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 N) (hN : 1 ≤ N)
    (hND : N ∉ D) (h : ¬ CoReach N D) : ¬ CoReach N (insert N D) :=
  fun h' => h (coReach_of_insert_N hD hN hND h')

/-! ## Counting helpers -/

theorem card_le_countP {S : List Nat} (hnd : S.Nodup) (p : Nat → Bool) (T : Finset Nat)
    (hT : ∀ x ∈ T, x ∈ S ∧ p x = true) : T.card ≤ S.countP p := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter p)]
  apply Finset.card_le_card
  intro x hx; rw [List.mem_toFinset, List.mem_filter]; exact hT x hx

theorem countP_le_card {S : List Nat} (hnd : S.Nodup) (p : Nat → Bool) (T : Finset Nat)
    (hT : ∀ x ∈ S, p x = true → x ∈ T) : S.countP p ≤ T.card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter p)]
  apply Finset.card_le_card
  intro x hx; rw [List.mem_toFinset, List.mem_filter] at hx; exact hT x hx.1 hx.2

/-- The first index of a list at which a property holds. -/
theorem first_index (a : List Nat) (P : Nat → Prop) [DecidablePred P] (hex : ∃ x ∈ a, P x) :
    ∃ i, ∃ hi : i < a.length, P a[i] ∧ ∀ x ∈ a.take i, ¬ P x := by
  have hex' : ∃ i, ∃ hi : i < a.length, P a[i] := by
    obtain ⟨x, hx, hP⟩ := hex
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hx
    exact ⟨i, hi, e ▸ hP⟩
  classical
  obtain ⟨hi, hP⟩ := Nat.find_spec hex'
  refine ⟨Nat.find hex', hi, hP, fun x hx hPx => ?_⟩
  obtain ⟨i', hi', e⟩ := List.mem_iff_getElem.1 hx
  simp only [List.length_take] at hi'
  rw [List.getElem_take] at e
  exact Nat.find_min hex' (m := i') (by omega) ⟨by omega, e ▸ hPx⟩

theorem bg_nodup {D : Finset Nat} {a : List Nat} (hnd : a.Nodup) (hmem : ∀ x ∈ a, x ∉ D)
    (i : Nat) : (D.toList ++ a.take i).Nodup := by
  rw [List.nodup_append]
  refine ⟨Finset.nodup_toList D, hnd.sublist (List.take_sublist _ _), ?_⟩
  intro x hx y hy hxy
  subst hxy
  exact hmem x (List.mem_of_mem_take hy) (Finset.mem_toList.1 hx)

/-! ## The B4 family: `{2} ∪ {2j, ..., 2j+3}` with a gap, `1` free -/

/-- **The B4 family is dead.**  Let `j ≥ 3`, `2j + 3 ≤ N`, and let `D ⊆ [1, N]` contain `2` and
the block `2j, 2j+1, 2j+2, 2j+3`, but neither `1` nor anything of `[3, 2j-1]`.  Then `D` is not
co-reachable.  On the background `D` the first panel `m` of `G = [3, 2j-1]` sees at most
`1, 2` on its left arm, and on its right arm nothing (`m ≤ j`), the whole block (`m ≥ j+2`,
or `m` in the right half), or exactly `2j, 2j+1` (`m = j+1`, so `1` was placed before).  The
second panel of `G` then sees `1, 2` and at most `j + 1` (left of `j + 1`), or at most three
panels on its left and the whole block on its right. -/
theorem not_coReach_b4 {N j : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 N) (hj : 3 ≤ j)
    (hN : 2 * j + 3 ≤ N) (h1 : 1 ∉ D) (h2 : 2 ∈ D) (hb : ∀ i, i < 4 → 2 * j + i ∈ D)
    (hgap : ∀ x ∈ D, x < 3 ∨ 2 * j ≤ x) : ¬ CoReach N D := by
  intro h
  obtain ⟨a, hnd, hmem, hstep⟩ := bg_of_coReach hD h
  have haD : ∀ x ∈ a, x ∉ D := fun x hx => ((hmem x).1 hx).2
  have haN : ∀ x ∈ a, 1 ≤ x ∧ x ≤ N := fun x hx => ((hmem x).1 hx).1
  have hDN : ∀ x ∈ D, 1 ≤ x ∧ x ≤ N := fun x hx => Finset.mem_Icc.1 (hD hx)
  have hmemS : ∀ i x, x ∈ D.toList ++ a.take i ↔ x ∈ D ∨ x ∈ a.take i := by
    intro i x; rw [List.mem_append, Finset.mem_toList]
  have hblk : ∀ i, ∀ t, t < 4 → 2 * j + t ∈ D.toList ++ a.take i :=
    fun i t ht => (hmemS i _).2 (Or.inl (hb t ht))
  have h3a : 3 ∈ a := (hmem 3).2 ⟨by omega, fun h3 => by have := hgap 3 h3; omega⟩
  -- the first panel of `G`
  obtain ⟨i1, hi1, hG1, hpre1⟩ := first_index a (fun x => 3 ≤ x ∧ x < 2 * j)
    ⟨3, h3a, by omega, by omega⟩
  have hS1 := bg_nodup hnd haD i1
  have hlow1 : ∀ x ∈ D.toList ++ a.take i1, x < 2 * j → x = 1 ∨ x = 2 := by
    intro x hx hxj
    rcases (hmemS i1 x).1 hx with hx | hx
    · have := hgap x hx; have := hDN x hx
      have : x ≠ 1 := fun e => h1 (e ▸ hx)
      omega
    · have := hpre1 x hx; have := haN x (List.mem_of_mem_take hx); omega
  have h2S1 : 2 ∈ D.toList ++ a.take i1 := (hmemS i1 2).2 (Or.inl h2)
  have hv1 := hstep i1 hi1
  generalize hm : a[i1] = m at hv1 hG1
  unfold SemiStep at hv1
  rw [leftCount_eq hS1, rightCount_eq hS1] at hv1
  -- left arm: at most `{1, 2}`
  have lc1 : (D.toList ++ a.take i1).countP (fun x => decide (m - reach N m ≤ x ∧ x < m)) ≤
      ({1, 2} : Finset Nat).card :=
    countP_le_card hS1 _ _ (fun x hx hp => by
      simp only [decide_eq_true_eq] at hp
      rcases hlow1 x hx (by omega) with rfl | rfl <;> simp)
  have hc12 : ({1, 2} : Finset Nat).card = 2 := by decide
  -- right arm: the whole block once it reaches `2j + 3`
  have rc4 : ∀ (i : Nat) (m : Nat), m < 2 * j → 2 * j + 3 ≤ m + reach N m →
      4 ≤ (D.toList ++ a.take i).countP (fun x => decide (m < x ∧ x ≤ m + reach N m)) := by
    intro i m hm1 hm2
    have hT : ({2 * j, 2 * j + 1, 2 * j + 2, 2 * j + 3} : Finset Nat).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
        Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    rw [← hT]
    refine card_le_countP (bg_nodup hnd haD i) _ _ (fun x hx => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨by simpa using hblk i 0 (by omega), by simp; omega⟩
    · exact ⟨hblk i 1 (by omega), by simp; omega⟩
    · exact ⟨hblk i 2 (by omega), by simp; omega⟩
    · exact ⟨hblk i 3 (by omega), by simp; omega⟩
  -- so `m = j + 1` in the left half, and `1` was placed before
  have key1 : m = j + 1 ∧ 1 ∈ a.take i1 := by
    rcases reach_cases N m with ⟨hr, _⟩ | ⟨hr, _⟩
    · by_cases hmj : m ≤ j
      · -- right arm empty, left arm contains `2`
        have r0 : (D.toList ++ a.take i1).countP
            (fun x => decide (m < x ∧ x ≤ m + reach N m)) ≤ (∅ : Finset Nat).card :=
          countP_le_card hS1 _ _ (fun x hx hp => by
            simp only [decide_eq_true_eq] at hp
            rcases hlow1 x hx (by omega) with rfl | rfl <;> omega)
        have l1 : ({2} : Finset Nat).card ≤ (D.toList ++ a.take i1).countP
            (fun x => decide (m - reach N m ≤ x ∧ x < m)) :=
          card_le_countP hS1 _ _ (fun x hx => by
            simp only [Finset.mem_singleton] at hx; subst hx
            exact ⟨h2S1, by simp; omega⟩)
        rw [Finset.card_empty] at r0; rw [Finset.card_singleton] at l1; omega
      · by_cases hmj2 : m = j + 1
        · refine ⟨hmj2, ?_⟩
          by_contra h1a
          have l1 : (D.toList ++ a.take i1).countP
              (fun x => decide (m - reach N m ≤ x ∧ x < m)) ≤ ({2} : Finset Nat).card :=
            countP_le_card hS1 _ _ (fun x hx hp => by
              simp only [decide_eq_true_eq] at hp
              rcases hlow1 x hx (by omega) with rfl | rfl
              · exfalso; rcases (hmemS i1 1).1 hx with h' | h'
                · exact h1 h'
                · exact h1a h'
              · simp)
          have r2 : ({2 * j, 2 * j + 1} : Finset Nat).card ≤ (D.toList ++ a.take i1).countP
              (fun x => decide (m < x ∧ x ≤ m + reach N m)) :=
            card_le_countP hS1 _ _ (fun x hx => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact ⟨by simpa using hblk i1 0 (by omega), by simp; omega⟩
              · exact ⟨hblk i1 1 (by omega), by simp; omega⟩)
          have : ({2 * j, 2 * j + 1} : Finset Nat).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
          rw [Finset.card_singleton] at l1; omega
        · have := rc4 i1 m (by omega) (by omega); omega
    · have := rc4 i1 m (by omega) (by omega); omega
  obtain ⟨hmj1, h1a⟩ := key1
  -- the second panel of `G`
  have hex2 : ∃ x ∈ a, (3 ≤ x ∧ x < 2 * j) ∧ x ≠ j + 1 :=
    ⟨3, h3a, ⟨by omega, by omega⟩, by omega⟩
  obtain ⟨i2, hi2, ⟨hG2, hne2⟩, hpre2⟩ := first_index a
    (fun x => (3 ≤ x ∧ x < 2 * j) ∧ x ≠ j + 1) hex2
  have hS2 := bg_nodup hnd haD i2
  have hi12 : i1 < i2 := by
    rcases Nat.lt_or_ge i1 i2 with h' | h'
    · exact h'
    · exfalso
      rcases Nat.lt_or_ge i2 i1 with h'' | h''
      · exact hpre1 _ ((getElem_mem_take_iff hnd hi2).2 h'') hG2
      · have e : i1 = i2 := by omega
        subst e; exact hne2 (by rw [hm]; exact hmj1)
  have hsub : ∀ x ∈ a.take i1, x ∈ a.take i2 := fun x hx =>
    List.take_subset_take_left a (by omega) hx
  have hlow2 : ∀ x ∈ D.toList ++ a.take i2, x < 2 * j → x = 1 ∨ x = 2 ∨ x = j + 1 := by
    intro x hx hxj
    rcases (hmemS i2 x).1 hx with hx | hx
    · have := hgap x hx; have := hDN x hx
      have : x ≠ 1 := fun e => h1 (e ▸ hx)
      omega
    · have := haN x (List.mem_of_mem_take hx)
      by_cases hxG : 3 ≤ x ∧ x < 2 * j
      · by_contra hc; exact hpre2 x hx ⟨hxG, by omega⟩
      · omega
  have h1S2 : 1 ∈ D.toList ++ a.take i2 := (hmemS i2 1).2 (Or.inr (hsub 1 h1a))
  have h2S2 : 2 ∈ D.toList ++ a.take i2 := (hmemS i2 2).2 (Or.inl h2)
  have hv2 := hstep i2 hi2
  generalize hm' : a[i2] = m' at hv2 hG2 hne2
  unfold SemiStep at hv2
  rw [leftCount_eq hS2, rightCount_eq hS2] at hv2
  have lc2 : (D.toList ++ a.take i2).countP (fun x => decide (m' - reach N m' ≤ x ∧ x < m')) ≤
      ({1, 2, j + 1} : Finset Nat).card :=
    countP_le_card hS2 _ _ (fun x hx hp => by
      simp only [decide_eq_true_eq] at hp
      rcases hlow2 x hx (by omega) with rfl | rfl | rfl <;> simp)
  have hc3 : ({1, 2, j + 1} : Finset Nat).card ≤ 3 := Finset.card_le_three
  rcases reach_cases N m' with ⟨hr, _⟩ | ⟨hr, _⟩
  · by_cases hmj : m' ≤ j + 1
    · have l2 : ({1, 2} : Finset Nat).card ≤ (D.toList ++ a.take i2).countP
          (fun x => decide (m' - reach N m' ≤ x ∧ x < m')) :=
        card_le_countP hS2 _ _ (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ⟨h1S2, by simp; omega⟩
          · exact ⟨h2S2, by simp; omega⟩)
      have r1 : (D.toList ++ a.take i2).countP
          (fun x => decide (m' < x ∧ x ≤ m' + reach N m')) ≤ ({j + 1} : Finset Nat).card :=
        countP_le_card hS2 _ _ (fun x hx hp => by
          simp only [decide_eq_true_eq] at hp
          rcases hlow2 x hx (by omega) with rfl | rfl | rfl
          · omega
          · omega
          · simp)
      rw [hc12] at l2; rw [Finset.card_singleton] at r1; omega
    · have := rc4 i2 m' (by omega) (by omega); omega
  · have := rc4 i2 m' (by omega) (by omega); omega

/-- **Mirror image of the B4 family**: `N - 1 ∈ D`, `N ∉ D`, the block
`N+1-2j-3, ..., N+1-2j` in `D`, nothing of `[N+2-2j, N-2]` in `D`. -/
theorem not_coReach_b4_mirror {N j : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 N)
    (hj : 3 ≤ j) (hN : 2 * j + 3 ≤ N) (h1 : N ∉ D) (h2 : N - 1 ∈ D)
    (hb : ∀ i, i < 4 → N + 1 - (2 * j + i) ∈ D)
    (hgap : ∀ x ∈ D, N - 2 < x ∨ x + 2 * j ≤ N + 1) : ¬ CoReach N D := by
  intro h
  have hm := coReach_mirror h
  have hDN : ∀ x ∈ D, 1 ≤ x ∧ x ≤ N := fun x hx => Finset.mem_Icc.1 (hD hx)
  have memI : ∀ y, y ∈ D.image (N + 1 - ·) ↔ 1 ≤ y ∧ y ≤ N ∧ N + 1 - y ∈ D := by
    intro y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := hDN x hx
      refine ⟨by omega, by omega, ?_⟩
      rwa [show N + 1 - (N + 1 - x) = x by omega]
    · rintro ⟨h1', h2', h3⟩
      exact ⟨_, h3, by omega⟩
  refine not_coReach_b4 (D := D.image (N + 1 - ·)) (j := j) ?_ hj hN ?_ ?_ ?_ ?_ hm
  · intro y hy; rw [memI] at hy; exact Finset.mem_Icc.2 ⟨hy.1, hy.2.1⟩
  · rw [memI]; rintro ⟨_, _, h'⟩; exact h1 (by rwa [show N + 1 - 1 = N by omega] at h')
  · rw [memI]; refine ⟨by omega, by omega, ?_⟩
    rwa [show N + 1 - 2 = N - 1 by omega]
  · intro i hi; rw [memI]; exact ⟨by omega, by omega, hb i hi⟩
  · intro y hy; rw [memI] at hy
    have := hgap _ hy.2.2
    omega

/-- The 5-set `{2, 2j, 2j+1, 2j+2, 2j+3}`. -/
def b4set (j : Nat) : Finset Nat := {2, 2 * j, 2 * j + 1, 2 * j + 2, 2 * j + 3}

theorem mem_b4set {j x : Nat} :
    x ∈ b4set j ↔ x = 2 ∨ x = 2 * j ∨ x = 2 * j + 1 ∨ x = 2 * j + 2 ∨ x = 2 * j + 3 := by
  simp [b4set]

/-- **The 5-sets `{2, 2j, ..., 2j+3}` are dead** (`j ≥ 3`, `2j + 3 ≤ N`); for `2j + 3 < N` they
avoid both end panels. -/
theorem not_coReach_b4set {N j : Nat} (hj : 3 ≤ j) (hN : 2 * j + 3 ≤ N) :
    ¬ CoReach N (b4set j) :=
  not_coReach_b4 (fun x hx => by rw [mem_b4set] at hx; rw [Finset.mem_Icc]; omega) hj hN
    (by rw [mem_b4set]; omega) (by rw [mem_b4set]; omega)
    (fun i hi => by rw [mem_b4set]; omega) (fun x hx => by rw [mem_b4set] at hx; omega)

theorem card_b4set {j : Nat} (hj : 3 ≤ j) : (b4set j).card = 5 := by
  unfold b4set
  rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_singleton]

theorem b4set_subset {N j : Nat} (hj : 3 ≤ j) (hN : 2 * j + 4 ≤ N) :
    b4set j ⊆ Finset.Icc 2 (N - 1) := fun x hx => by
  rw [mem_b4set] at hx; rw [Finset.mem_Icc]; omega

/-- **Conjecture E_5 fails with every finite list of exceptions**: there is no finite family `E`
of sets such that, for every `N`, every dead 5-subset of `[2, N - 1]` belongs to `E`. -/
theorem not_finite_exceptions_five :
    ¬ ∃ E : Finset (Finset Nat), ∀ N (D : Finset Nat), D ⊆ Finset.Icc 2 (N - 1) →
      D.card = 5 → ¬ CoReach N D → D ∈ E := by
  rintro ⟨E, hE⟩
  set M := E.sup (fun D => D.sup id)
  have hj : 3 ≤ M + 3 := by omega
  have hmem := hE (2 * (M + 3) + 4) (b4set (M + 3)) (b4set_subset hj le_rfl) (card_b4set hj)
    (not_coReach_b4set hj (by omega))
  have h1 : 2 * (M + 3) ≤ (b4set (M + 3)).sup id :=
    Finset.le_sup (f := id) (mem_b4set.2 (Or.inr (Or.inl rfl)))
  have h2 : (b4set (M + 3)).sup id ≤ M := Finset.le_sup (f := fun D => D.sup id) hmem
  omega

/-! ## The general anchored-block family `B_a`

`D` contains an anchor `a`, the block `[2j, 2j + 2a - 1]` and nothing of `[a + 1, 2j - 1]`.
On the background `D`, let `p` be the number of placed panels below `a` and `s` the number of
placed panels of `G = [a + 1, 2j - 1]`.  Invariant: every placed panel of `G` lies in
`[j + 1, j + p]`, and `s ≤ p`.  As `p ≤ a - 1 < |G|`, the panels of `G` are never all placed. -/

theorem countP_eq_card_filter {l : List Nat} (hnd : l.Nodup) (P : Nat → Prop) [DecidablePred P] :
    l.countP (fun x => decide (P x)) = (l.toFinset.filter P).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _)]
  congr 1
  ext x; simp

/-- The step lemma of the invariant: a valid step at a panel `m` of `G` lands in `[j+1, j+p]`
and keeps `s + 1 ≤ p`. -/
theorem anchor_step {N a j m : Nat} {X : Finset Nat} (hX : X ⊆ Finset.Icc 1 N) (ha1 : 1 ≤ a)
    (hj : a + 1 ≤ j) (hN : 2 * j + 2 * a ≤ N + 1) (ha : a ∈ X)
    (hb : ∀ t, t < 2 * a → 2 * j + t ∈ X)
    (hinv : ∀ x ∈ X, a < x → x < 2 * j → j + 1 ≤ x ∧ x ≤ j + (X.filter (· < a)).card)
    (hs : (X.filter (fun x => a < x ∧ x < 2 * j)).card ≤ (X.filter (· < a)).card)
    (hm1 : a < m) (hm2 : m < 2 * j) (hmX : m ∉ X)
    (hv : (X.filter (fun x => m - reach N m ≤ x ∧ x < m)).card =
      (X.filter (fun x => m < x ∧ x ≤ m + reach N m)).card) :
    j + 1 ≤ m ∧ m ≤ j + (X.filter (· < a)).card ∧
      (X.filter (fun x => a < x ∧ x < 2 * j)).card + 1 ≤ (X.filter (· < a)).card := by
  classical
  have hXN : ∀ x ∈ X, 1 ≤ x ∧ x ≤ N := fun x hx => Finset.mem_Icc.1 (hX hx)
  set p := (X.filter (· < a)).card with hp
  set s := (X.filter (fun x => a < x ∧ x < 2 * j)).card with hsdef
  set Lf := X.filter (fun x => m - reach N m ≤ x ∧ x < m)
  set Rt := X.filter (fun x => m < x ∧ x ≤ m + reach N m)
  -- `p ≤ a - 1`
  have hpa : p ≤ a - 1 := by
    calc p ≤ (Finset.Icc 1 (a - 1)).card := Finset.card_le_card (fun x hx => by
            rw [Finset.mem_filter] at hx; have := hXN x hx.1; rw [Finset.mem_Icc]; omega)
      _ = a - 1 := by rw [Nat.card_Icc]; omega
  -- panels `≤ a` in `X`: exactly `p + 1`
  have hle : (X.filter (· ≤ a)).card = p + 1 := by
    have e : X.filter (· ≤ a) = insert a (X.filter (· < a)) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hx, hxa⟩; by_cases h : x = a
        · exact Or.inl h
        · exact Or.inr ⟨hx, by omega⟩
      · rintro (rfl | ⟨hx, hxa⟩)
        · exact ⟨ha, le_rfl⟩
        · exact ⟨hx, by omega⟩
    rw [e, Finset.card_insert_of_notMem (by simp)]
  -- the left arm is inside `X ∩ [1, 2j)` : at most `p + 1 + s`
  have hLf_le : Lf.card ≤ p + 1 + s := by
    calc Lf.card ≤ (X.filter (· ≤ a) ∪ X.filter (fun x => a < x ∧ x < 2 * j)).card :=
          Finset.card_le_card (fun x hx => by
            rw [Finset.mem_filter] at hx
            rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
            by_cases h : x ≤ a
            · exact Or.inl ⟨hx.1, h⟩
            · exact Or.inr ⟨hx.1, by omega, by omega⟩)
      _ ≤ _ := Finset.card_union_le _ _
      _ = p + 1 + s := by rw [hle]
  -- the block inside the right arm
  have hblk : ∀ c, c ≤ 2 * a → 2 * j + c ≤ m + reach N m + 1 → c ≤ Rt.card := by
    intro c hc hcr
    calc c = (Finset.Ico (2 * j) (2 * j + c)).card := by rw [Nat.card_Ico]; omega
      _ ≤ Rt.card := Finset.card_le_card (fun x hx => by
          rw [Finset.mem_Ico] at hx
          rw [Finset.mem_filter]
          refine ⟨?_, by omega, by omega⟩
          have := hb (x - 2 * j) (by omega)
          rwa [show 2 * j + (x - 2 * j) = x by omega] at this)
  rcases reach_cases N m with ⟨hr, _⟩ | ⟨hr, _⟩
  · by_cases hmj : m ≤ j
    · -- left arm contains everything `≤ a`, right arm only placed panels of `G`
      exfalso
      have h1 : p + 1 ≤ Lf.card := by
        rw [← hle]
        exact Finset.card_le_card (fun x hx => by
          rw [Finset.mem_filter] at hx ⊢
          have := hXN x hx.1
          exact ⟨hx.1, by omega, by omega⟩)
      have h2 : Rt.card ≤ s := Finset.card_le_card (fun x hx => by
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, by omega, by omega⟩)
      omega
    · obtain ⟨t, rfl⟩ : ∃ t, m = j + t := ⟨m - j, by omega⟩
      by_cases htp : p < t
      · exfalso
        have := hblk (2 * p + 2) (by omega) (by omega)
        omega
      · refine ⟨by omega, by omega, ?_⟩
        -- `G` splits at `m`
        have hbelow : (X.filter (fun x => a < x ∧ x < j + t)).card ≤ t - 1 := by
          calc _ ≤ (Finset.Icc (j + 1) (j + t - 1)).card := Finset.card_le_card (fun x hx => by
                  rw [Finset.mem_filter] at hx
                  have := hinv x hx.1 hx.2.1 (by omega)
                  rw [Finset.mem_Icc]; omega)
            _ = t - 1 := by rw [Nat.card_Icc]; omega
        have hsplit : s ≤ (X.filter (fun x => a < x ∧ x < j + t)).card +
            (X.filter (fun x => j + t < x ∧ x < 2 * j)).card := by
          calc s ≤ (X.filter (fun x => a < x ∧ x < j + t) ∪
                X.filter (fun x => j + t < x ∧ x < 2 * j)).card :=
                Finset.card_le_card (fun x hx => by
                  rw [Finset.mem_filter] at hx
                  have : x ≠ j + t := fun e => hmX (e ▸ hx.1)
                  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
                  by_cases h : x < j + t
                  · exact Or.inl ⟨hx.1, hx.2.1, h⟩
                  · exact Or.inr ⟨hx.1, by omega, hx.2.2⟩)
            _ ≤ _ := Finset.card_union_le _ _
        have hLf2 : Lf.card ≤ p + 1 + (X.filter (fun x => a < x ∧ x < j + t)).card := by
          calc Lf.card ≤ (X.filter (· ≤ a) ∪ X.filter (fun x => a < x ∧ x < j + t)).card :=
                Finset.card_le_card (fun x hx => by
                  rw [Finset.mem_filter] at hx
                  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
                  by_cases h : x ≤ a
                  · exact Or.inl ⟨hx.1, h⟩
                  · exact Or.inr ⟨hx.1, by omega, hx.2.2⟩)
            _ ≤ _ := Finset.card_union_le _ _
            _ = _ := by rw [hle]
        have hRt2 : 2 * t + (X.filter (fun x => j + t < x ∧ x < 2 * j)).card ≤ Rt.card := by
          have hdisj : Disjoint (Finset.Ico (2 * j) (2 * j + 2 * t))
              (X.filter (fun x => j + t < x ∧ x < 2 * j)) := by
            rw [Finset.disjoint_left]
            intro x hx hx'
            rw [Finset.mem_Ico] at hx; rw [Finset.mem_filter] at hx'; omega
          calc _ = (Finset.Ico (2 * j) (2 * j + 2 * t) ∪
                X.filter (fun x => j + t < x ∧ x < 2 * j)).card := by
                rw [Finset.card_union_of_disjoint hdisj, Nat.card_Ico]; omega
            _ ≤ Rt.card := Finset.card_le_card (fun x hx => by
                rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_filter] at hx
                rw [Finset.mem_filter]
                rcases hx with hx | hx
                · refine ⟨?_, by omega, by omega⟩
                  have := hb (x - 2 * j) (by omega)
                  rwa [show 2 * j + (x - 2 * j) = x by omega] at this
                · exact ⟨hx.1, by omega, by omega⟩)
        omega
  · exfalso
    have := hblk (2 * a) le_rfl (by omega)
    omega

/-- **The anchored-block family `B_a` is dead.**  Let `1 ≤ a`, `a + 1 ≤ j`,
`2j + 2a - 1 ≤ N`, and let `D ⊆ [1, N]` contain `a` and the block `[2j, 2j + 2a - 1]` but
nothing of `[a + 1, 2j - 1]` (anything below `a` or above `2j - 1` is allowed).  Then `D` is not
co-reachable.  For `a = 1` these are the blocks `{1, 2j, 2j+1}` of `Live`, for `a = 2` the B4
family; the `(2a+1)`-sets `{a} ∪ [2j, 2j+2a-1]` have least element `a`. -/
theorem not_coReach_anchor {N a j : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 N)
    (ha1 : 1 ≤ a) (hj : a + 1 ≤ j) (hN : 2 * j + 2 * a ≤ N + 1) (ha : a ∈ D)
    (hb : ∀ t, t < 2 * a → 2 * j + t ∈ D) (hgap : ∀ x ∈ D, x ≤ a ∨ 2 * j ≤ x) :
    ¬ CoReach N D := by
  classical
  intro h
  obtain ⟨l, hnd, hmem, hstep⟩ := bg_of_coReach hD h
  set X : Nat → Finset Nat := fun i => D ∪ (l.take i).toFinset with hXdef
  have hXsub : ∀ i, X i ⊆ Finset.Icc 1 N := by
    intro i x hx
    rw [hXdef, Finset.mem_union, List.mem_toFinset] at hx
    rcases hx with hx | hx
    · exact hD hx
    · exact Finset.mem_Icc.2 ((hmem x).1 (List.mem_of_mem_take hx)).1
  have hDX : ∀ i, D ⊆ X i := fun i => Finset.subset_union_left
  have hlist : ∀ i, (D.toList ++ l.take i).toFinset = X i := by
    intro i; ext x; simp [hXdef]
  -- the invariant
  have inv : ∀ i, i ≤ l.length →
      (∀ x ∈ X i, a < x → x < 2 * j → j + 1 ≤ x ∧ x ≤ j + ((X i).filter (· < a)).card) ∧
      ((X i).filter (fun x => a < x ∧ x < 2 * j)).card ≤ ((X i).filter (· < a)).card := by
    intro i
    induction i with
    | zero =>
      intro _
      have e : X 0 = D := by simp [hXdef]
      rw [e]
      have h0 : D.filter (fun x => a < x ∧ x < 2 * j) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro x hx; have := hgap x hx; omega
      refine ⟨fun x hx h1 h2 => by have := hgap x hx; omega, ?_⟩
      rw [h0, Finset.card_empty]; exact Nat.zero_le _
    | succ i ih =>
      intro hi
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hil : i < l.length := by omega
      have hXs : X (i + 1) = insert l[i] (X i) := by
        simp only [hXdef, List.take_succ_eq_append_getElem hil, List.toFinset_append,
          List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
        ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
      have hmD : l[i] ∉ D := ((hmem _).1 (List.getElem_mem hil)).2
      have hmT : l[i] ∉ l.take i := by
        rw [getElem_mem_take_iff hnd hil]; omega
      have hmX : l[i] ∉ X i := by
        rw [hXdef, Finset.mem_union, List.mem_toFinset]; tauto
      have hmN := ((hmem _).1 (List.getElem_mem hil)).1
      rw [hXs]
      generalize hmdef : l[i] = m at hmX hmD hmN
      by_cases hma : m < a
      · -- a panel below the anchor: `p` grows
        have ep : ((insert m (X i)).filter (· < a)).card = ((X i).filter (· < a)).card + 1 := by
          rw [Finset.filter_insert, ite_eq_left hma, Finset.card_insert_of_notMem (by simp [hmX])]
        have es : (insert m (X i)).filter (fun x => a < x ∧ x < 2 * j) =
            (X i).filter (fun x => a < x ∧ x < 2 * j) := by
          rw [Finset.filter_insert, ite_eq_right (by omega)]
        rw [ep, es]
        refine ⟨fun x hx h1 h2 => ?_, by omega⟩
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · omega
        · have := ih1 x hx h1 h2; omega
      · have hma' : a < m := by
          rcases Nat.lt_or_ge a m with h' | h'
          · exact h'
          · exfalso; have : m = a := by omega
            exact hmD (this ▸ ha)
        have ep : (insert m (X i)).filter (· < a) = (X i).filter (· < a) := by
          rw [Finset.filter_insert, ite_eq_right hma]
        rw [ep]
        by_cases hm2 : m < 2 * j
        · -- a panel of `G`: the step lemma
          have hS := bg_nodup hnd (fun x hx => ((hmem x).1 hx).2) i
          have hv := hstep i hil
          rw [hmdef] at hv
          unfold SemiStep at hv
          rw [leftCount_eq hS, rightCount_eq hS, countP_eq_card_filter hS,
            countP_eq_card_filter hS, hlist] at hv
          obtain ⟨k1, k2, k3⟩ := anchor_step (hXsub i) ha1 hj hN (hDX i ha)
            (fun t ht => hDX i (hb t ht)) ih1 ih2 hma' hm2 hmX hv
          have es : ((insert m (X i)).filter (fun x => a < x ∧ x < 2 * j)).card =
              ((X i).filter (fun x => a < x ∧ x < 2 * j)).card + 1 := by
            rw [Finset.filter_insert, ite_eq_left ⟨hma', hm2⟩,
              Finset.card_insert_of_notMem (by simp [hmX])]
          rw [es]
          refine ⟨fun x hx h1 h2 => ?_, k3⟩
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact ⟨k1, k2⟩
          · exact ih1 x hx h1 h2
        · have es : (insert m (X i)).filter (fun x => a < x ∧ x < 2 * j) =
              (X i).filter (fun x => a < x ∧ x < 2 * j) := by
            rw [Finset.filter_insert, ite_eq_right (by omega)]
          rw [es]
          refine ⟨fun x hx h1 h2 => ?_, ih2⟩
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · omega
          · exact ih1 x hx h1 h2
  -- at the end every panel of `G` is placed
  obtain ⟨-, hfin⟩ := inv l.length le_rfl
  have hall : Finset.Ioo a (2 * j) ⊆ (X l.length).filter (fun x => a < x ∧ x < 2 * j) := by
    intro x hx
    rw [Finset.mem_Ioo] at hx
    rw [Finset.mem_filter]
    refine ⟨?_, hx⟩
    rw [hXdef, Finset.mem_union, List.mem_toFinset, List.take_length]
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr ((hmem x).2 ⟨⟨by omega, by omega⟩, hxD⟩)
  have h1 := Finset.card_le_card hall
  have h2 : ((X l.length).filter (· < a)).card ≤ (Finset.Icc 1 (a - 1)).card :=
    Finset.card_le_card (fun x hx => by
      rw [Finset.mem_filter] at hx
      have := Finset.mem_Icc.1 (hXsub _ hx.1)
      rw [Finset.mem_Icc]; omega)
  rw [Nat.card_Ioo] at h1
  rw [Nat.card_Icc] at h2
  omega

/-- The `(2a+1)`-set `{a} ∪ [2j, 2j + 2a - 1]`. -/
def anchorSet (a j : Nat) : Finset Nat := insert a (Finset.Ico (2 * j) (2 * j + 2 * a))

theorem not_coReach_anchorSet {N a j : Nat} (ha1 : 1 ≤ a) (hj : a + 1 ≤ j)
    (hN : 2 * j + 2 * a ≤ N + 1) : ¬ CoReach N (anchorSet a j) := by
  refine not_coReach_anchor (fun x hx => ?_) ha1 hj hN (Finset.mem_insert_self _ _)
    (fun t ht => Finset.mem_insert_of_mem (Finset.mem_Ico.2 ⟨by omega, by omega⟩))
    (fun x hx => ?_)
  · rw [anchorSet, Finset.mem_insert, Finset.mem_Ico] at hx; rw [Finset.mem_Icc]; omega
  · rw [anchorSet, Finset.mem_insert, Finset.mem_Ico] at hx; omega

theorem card_anchorSet {a j : Nat} (hj : a + 1 ≤ j) : (anchorSet a j).card = 2 * a + 1 := by
  rw [anchorSet, Finset.card_insert_of_notMem (by rw [Finset.mem_Ico]; omega), Nat.card_Ico]
  omega

/-- **No fixed radius works for all `k`.**  For every `a ≥ 1` there are dead `(2a+1)`-sets whose
least element is `a` and whose greatest element is at most `N - a` (so they avoid
`[1, a-1] ∪ [N+1-a, N]`), for every `N ≥ 6a + 1`. -/
theorem exists_dead_far {a N : Nat} (ha1 : 1 ≤ a) (hN : 6 * a + 1 ≤ N) :
    ∃ D : Finset Nat, D.card = 2 * a + 1 ∧ ¬ CoReach N D ∧ (∀ x ∈ D, a ≤ x ∧ x + a ≤ N) := by
  refine ⟨anchorSet a (a + 1), card_anchorSet le_rfl, not_coReach_anchorSet ha1 le_rfl
    (by omega), fun x hx => ?_⟩
  rw [anchorSet, Finset.mem_insert, Finset.mem_Ico] at hx
  omega

/-! ## The counting corollary -/

instance (N : Nat) (D : Finset Nat) : Decidable (CoReach N D) :=
  inferInstanceAs (Decidable (0 < g N (Finset.Icc 1 N \ D)))

/-- The `k`-subsets of `[N]` containing a given panel number at most `C(N-1, k-1)`. -/
theorem card_filter_mem_le (N k t : Nat) :
    ((Finset.powersetCard k (Finset.Icc 1 N)).filter (fun D => t ∈ D)).card ≤
      (N - 1).choose (k - 1) := by
  classical
  by_cases ht : t ∈ Finset.Icc 1 N
  · calc _ ≤ ((Finset.powersetCard (k - 1) ((Finset.Icc 1 N).erase t)).image (insert t)).card := by
          apply Finset.card_le_card
          intro D hD
          rw [Finset.mem_filter, Finset.mem_powersetCard] at hD
          rw [Finset.mem_image]
          refine ⟨D.erase t, Finset.mem_powersetCard.2 ⟨Finset.erase_subset_erase _ hD.1.1, ?_⟩,
            Finset.insert_erase hD.2⟩
          rw [Finset.card_erase_of_mem hD.2, hD.1.2]
      _ ≤ _ := Finset.card_image_le
      _ = _ := by
          rw [Finset.card_powersetCard, Finset.card_erase_of_mem ht, Nat.card_Icc]
          congr 1
  · have : (Finset.powersetCard k (Finset.Icc 1 N)).filter (fun D => t ∈ D) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro D hD htD
      exact ht ((Finset.mem_powersetCard.1 hD).1 htD)
    rw [this, Finset.card_empty]
    exact Nat.zero_le _

/-- **The counting corollary.**  If every dead `k`-subset of `[N]` has an element within `c` of
an end (in `[1, c]` or in `[N + 1 - c, N]`) or belongs to the exceptional family `E`, then there
are at most `2c · C(N-1, k-1) + |E|` dead `k`-subsets of `[N]`. -/
theorem card_dead_le (N k c : Nat) (E : Finset (Finset Nat))
    (h : ∀ D ∈ Finset.powersetCard k (Finset.Icc 1 N), ¬ CoReach N D →
      (∃ x ∈ D, x ≤ c ∨ N + 1 ≤ x + c) ∨ D ∈ E) :
    ((Finset.powersetCard k (Finset.Icc 1 N)).filter (fun D => ¬ CoReach N D)).card ≤
      2 * c * (N - 1).choose (k - 1) + E.card := by
  classical
  set P := Finset.powersetCard k (Finset.Icc 1 N)
  set T : Finset Nat := Finset.Icc 1 c ∪ Finset.Icc (N + 1 - c) N
  have hsub : P.filter (fun D => ¬ CoReach N D) ⊆
      T.biUnion (fun t => P.filter (fun D => t ∈ D)) ∪ E := by
    intro D hD
    rw [Finset.mem_filter] at hD
    rcases h D hD.1 hD.2 with ⟨x, hx, hxc⟩ | hE
    · have hxN := Finset.mem_Icc.1 ((Finset.mem_powersetCard.1 hD.1).1 hx)
      refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨x, ?_, Finset.mem_filter.2 ⟨hD.1, hx⟩⟩)
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
      omega
    · exact Finset.mem_union_right _ hE
  have hT : T.card ≤ 2 * c := by
    calc T.card ≤ (Finset.Icc 1 c).card + (Finset.Icc (N + 1 - c) N).card := Finset.card_union_le _ _
      _ ≤ 2 * c := by rw [Nat.card_Icc, Nat.card_Icc]; omega
  calc _ ≤ (T.biUnion (fun t => P.filter (fun D => t ∈ D)) ∪ E).card := Finset.card_le_card hsub
    _ ≤ (T.biUnion (fun t => P.filter (fun D => t ∈ D))).card + E.card := Finset.card_union_le _ _
    _ ≤ (∑ t ∈ T, (P.filter (fun D => t ∈ D)).card) + E.card := by
        gcongr; exact Finset.card_biUnion_le
    _ ≤ (∑ _t ∈ T, (N - 1).choose (k - 1)) + E.card := by
        gcongr with t _; exact card_filter_mem_le N k t
    _ = T.card * (N - 1).choose (k - 1) + E.card := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 * c * (N - 1).choose (k - 1) + E.card := by gcongr

/-- **Conjecture E_k implies the counting bound.**  If every dead `k`-subset of `[2, N - 1]`
lies in `E`, then there are at most `2 C(N-1, k-1) + |E|` dead `k`-subsets of `[N]`. -/
theorem card_dead_le_of_Ek (N k : Nat) (E : Finset (Finset Nat))
    (h : ∀ D ⊆ Finset.Icc 2 (N - 1), D.card = k → ¬ CoReach N D → D ∈ E) :
    ((Finset.powersetCard k (Finset.Icc 1 N)).filter (fun D => ¬ CoReach N D)).card ≤
      2 * (N - 1).choose (k - 1) + E.card := by
  have := card_dead_le N k 1 E (fun D hD hd => by
    rw [Finset.mem_powersetCard] at hD
    by_cases hend : ∃ x ∈ D, x ≤ 1 ∨ N + 1 ≤ x + 1
    · exact Or.inl hend
    · push Not at hend
      refine Or.inr (h D (fun x hx => ?_) hD.2 hd)
      have := hend x hx; have := Finset.mem_Icc.1 (hD.1 hx)
      rw [Finset.mem_Icc]; omega)
  simpa using this

/-- **Pairs, unconditionally for `N ≤ 64`** (Conjecture C, `Live7.coReach_le_64`): every pair
avoiding the end panels is co-reachable, so there are at most `2 (N - 1)` dead pairs. -/
theorem coReach_pair_le_64 {N : Nat} (hN : N ≤ 64) {D : Finset Nat}
    (hD : D ⊆ Finset.Icc 2 (N - 1)) (h2 : D.card = 2) : CoReach N D := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 h2
  have hx := Finset.mem_Icc.1 (hD (Finset.mem_insert_self x {y}))
  have hy := Finset.mem_Icc.1 (hD (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)))
  rcases Nat.lt_or_gt_of_ne hxy with hlt | hlt
  · exact Live7.coReach_le_64 N hN x y (by omega) hlt (by omega) (by simp [deadB]; omega)
  · rw [Finset.pair_comm]
    exact Live7.coReach_le_64 N hN y x (by omega) hlt (by omega) (by simp [deadB]; omega)

theorem card_dead_pairs_le_64 {N : Nat} (hN : N ≤ 64) :
    ((Finset.powersetCard 2 (Finset.Icc 1 N)).filter (fun D => ¬ CoReach N D)).card ≤
      2 * (N - 1) := by
  have := card_dead_le_of_Ek N 2 ∅ (fun D hD hc hd => absurd (coReach_pair_le_64 hN hD hc) hd)
  simpa using this

end Ek
end Folds
