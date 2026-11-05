import Folds.Counting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

/-!
# The subset recursion for semi-symmetric fold sequences

For a finite set `S` of panels, `g N S` is the number of *semi-symmetric orderings* of
`S`: lists that enumerate `S` without repetition such that every step is semi-symmetric
(for the strip `1..N`) relative to the panels listed before it.  These are exactly the
possible prefixes of a semi-symmetric bisection order whose set of bisected panels is `S`.

Main results (all for every `N`):

* `g_empty`: `g N ∅ = 1`.
* `g_eq_sum`: for nonempty `S`,
  `g N S = ∑ m ∈ S with SetStep N (S.erase m) m, g N (S.erase m)`
  (condition on the last panel `m`; the step condition depends only on the *set*
  `S.erase m`, see `semiStep_congr`).
* `semiCount_eq_g`: `a(N) = semiCount N = g N [1..N]`.
* `semiCount_eq_sum_split` (meet in the middle / reversal identity): for every `k ≤ N`,
  `a(N) = ∑_{S ⊆ [1..N], |S| = k} g N S · g N ([1..N] \ S)`.

The reversal identity comes from the per-step reversal lemma `semiStep_reverse_iff`
(the step at index `j` of a fold sequence `a` is semi-symmetric iff the step at the mirror
index of `a.reverse` is), which gives the splitting lemma `semiSymmetric_split_iff`:
a fold sequence is semi-symmetric iff its first `k` panels are, and its last `N - k`
panels read backwards are.
-/

namespace Folds

/-! ## The step condition depends only on membership -/

/-- `SemiStep N S m` depends on the list `S` only through membership. -/
theorem semiStep_congr {N m : Nat} {S T : List Nat} (h : ∀ x, x ∈ S ↔ x ∈ T) :
    SemiStep N S m ↔ SemiStep N T m := by
  unfold SemiStep leftCount rightCount
  simp only [h]

/-- The semi-symmetric step condition for a *set* `S` of already-bisected panels. -/
def SetStep (N : Nat) (S : Finset Nat) (m : Nat) : Prop := SemiStep N (S.sort) m

instance (N : Nat) (S : Finset Nat) (m : Nat) : Decidable (SetStep N S m) :=
  inferInstanceAs (Decidable (SemiStep _ _ _))

theorem setStep_iff {N m : Nat} {S : Finset Nat} {l : List Nat} (h : ∀ x, x ∈ l ↔ x ∈ S) :
    SetStep N S m ↔ SemiStep N l m :=
  semiStep_congr fun x => by rw [Finset.mem_sort, h]

/-! ## Orderings of a set and the function `g` -/

/-- All orderings (repetition-free enumerations) of the finite set `S`. -/
def orderings (S : Finset Nat) : Finset (List Nat) := (S.sort).permutations.toFinset

theorem mem_orderings {S : Finset Nat} {l : List Nat} :
    l ∈ orderings S ↔ l.Nodup ∧ l.toFinset = S := by
  rw [orderings, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    refine ⟨h.nodup_iff.2 (Finset.sort_nodup _ _), ?_⟩
    ext x; rw [List.mem_toFinset, h.mem_iff, Finset.mem_sort]
  · rintro ⟨hnd, rfl⟩
    rw [List.perm_ext_iff_of_nodup hnd (Finset.sort_nodup _ _)]
    intro x; rw [Finset.mem_sort, List.mem_toFinset]

/-- The semi-symmetric orderings of `S` (for the strip `1..N`). -/
def semiOrders (N : Nat) (S : Finset Nat) : Finset (List Nat) :=
  (orderings S).filter (SemiSymmetric N)

/-- `g N S`: the number of semi-symmetric orderings of the set `S`, i.e. the number of
ways to bisect exactly the panels of `S` (in some order) with every step semi-symmetric. -/
def g (N : Nat) (S : Finset Nat) : Nat := (semiOrders N S).card

theorem mem_semiOrders {N : Nat} {S : Finset Nat} {l : List Nat} :
    l ∈ semiOrders N S ↔ (l.Nodup ∧ l.toFinset = S) ∧ SemiSymmetric N l := by
  rw [semiOrders, Finset.mem_filter, mem_orderings]

/-- Appending one panel. -/
theorem semiSymmetric_concat_iff {N m : Nat} {l : List Nat} :
    SemiSymmetric N (l ++ [m]) ↔ SemiSymmetric N l ∧ SemiStep N l m := by
  rw [semiSymmetric_append_iff]
  apply and_congr Iff.rfl
  constructor
  · intro h; simpa using h 0 (by simp)
  · intro h k hk
    obtain rfl : k = 0 := by simp at hk; omega
    simpa using h

/-! ## (a) The recursion -/

/-- **Base case.** `g N ∅ = 1` (the empty ordering). -/
theorem g_empty (N : Nat) : g N ∅ = 1 := by
  rw [g, Finset.card_eq_one]
  refine ⟨[], ?_⟩
  ext l
  rw [mem_semiOrders, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨-, h⟩, -⟩; simpa using h
  · rintro rfl; exact ⟨⟨List.nodup_nil, rfl⟩, fun k hk => absurd hk (by simp)⟩

theorem semiOrders_eq_biUnion {N : Nat} {S : Finset Nat} (hS : S.Nonempty) :
    semiOrders N S = (S.filter fun m => SetStep N (S.erase m) m).biUnion
      fun m => (semiOrders N (S.erase m)).image (· ++ [m]) := by
  ext l
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, mem_semiOrders]
  constructor
  · rintro ⟨⟨hnd, hS'⟩, hss⟩
    rcases List.eq_nil_or_concat l with rfl | ⟨l', m, rfl⟩
    · exfalso; subst hS'; simp at hS
    simp only [List.concat_eq_append] at *
    have hnd' := hnd
    rw [List.nodup_append] at hnd'
    have hm : m ∉ l' := fun h => hnd'.2.2 m h m (by simp) rfl
    have hset : l'.toFinset = S.erase m := by
      rw [← hS']; ext x; simp only [List.mem_toFinset, Finset.mem_erase, List.mem_append,
        List.mem_singleton]
      constructor
      · intro hx; exact ⟨fun e => hm (e ▸ hx), Or.inl hx⟩
      · rintro ⟨hne, hx | hx⟩
        · exact hx
        · exact absurd hx hne
    rw [semiSymmetric_concat_iff] at hss
    refine ⟨m, ⟨by rw [← hS']; simp, ?_⟩, l', ⟨⟨hnd'.1, hset⟩, hss.1⟩, rfl⟩
    rw [setStep_iff (l := l') (fun x => by rw [← hset, List.mem_toFinset])]
    exact hss.2
  · rintro ⟨m, ⟨hmS, hstep⟩, l', ⟨⟨hnd, hset⟩, hss⟩, rfl⟩
    have hm : m ∉ l' := by
      intro h; have : m ∈ l'.toFinset := List.mem_toFinset.2 h
      rw [hset] at this; simp at this
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro x hx y hy e; simp at hy; subst hy; subst e; exact hm hx
    · rw [List.toFinset_append, hset]; simp [Finset.insert_erase hmS]
    · rw [semiSymmetric_concat_iff]
      refine ⟨hss, ?_⟩
      rwa [setStep_iff (l := l') (fun x => by rw [← hset, List.mem_toFinset])] at hstep

/-- **The subset recursion.**  For a nonempty set `S` of panels,
`g N S = ∑_{m ∈ S, the step (S \ {m}, m) is semi-symmetric} g N (S \ {m})`:
classify the orderings of `S` by their last panel `m`. -/
theorem g_eq_sum {N : Nat} {S : Finset Nat} (hS : S.Nonempty) :
    g N S = ∑ m ∈ S.filter (fun m => SetStep N (S.erase m) m), g N (S.erase m) := by
  rw [g, semiOrders_eq_biUnion hS, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro m _
    rw [Finset.card_image_of_injective _ (List.append_left_injective [m]), g]
  · intro m _ m' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro l h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨u, -, rfl⟩ := h1
    obtain ⟨v, -, e⟩ := h2
    have := congrArg List.getLast? e
    simp at this
    exact hne this.symm

/-! ## (b) `a(N) = g N [1..N]` -/

theorem isFoldSeq_iff {N : Nat} {a : List Nat} :
    IsFoldSeq N a ↔ a.Nodup ∧ a.toFinset = Finset.Icc 1 N := by
  constructor
  · intro hf
    refine ⟨nodup_of_foldSeq hf, ?_⟩
    ext x; rw [List.mem_toFinset, mem_range'_of_perm hf, Finset.mem_Icc]
  · rintro ⟨hnd, h⟩
    unfold IsFoldSeq
    rw [List.perm_ext_iff_of_nodup hnd (List.nodup_range' ..)]
    intro x
    rw [List.mem_range'_1, ← List.mem_toFinset, h, Finset.mem_Icc]; omega

theorem semiSeqs_eq_semiOrders (N : Nat) : semiSeqs N = semiOrders N (Finset.Icc 1 N) := by
  ext a; rw [mem_semiSeqs, mem_semiOrders, isFoldSeq_iff]

/-- **(b)** `a(N) = g N {1, …, N}`. -/
theorem semiCount_eq_g (N : Nat) : semiCount N = g N (Finset.Icc 1 N) := by
  rw [semiCount, semiSeqs_eq_semiOrders, g]

/-! ## Reversal, step by step -/

/-- **Per-step reversal.**  For a fold sequence `a` of length `n`, the step at index `j`
is semi-symmetric iff the step of `a.reverse` at index `n - 1 - j` is. -/
theorem semiStep_reverse_iff {N : Nat} {a : List Nat} (hf : IsFoldSeq N a) {j : Nat}
    (hj : j < a.length) :
    SemiStep N (a.take j) a[j] ↔
      SemiStep N (a.reverse.take (a.length - 1 - j))
        (a.reverse[a.length - 1 - j]'(by simp; omega)) := by
  have hnd := nodup_of_foldSeq hf
  have e1 : a.reverse[a.length - 1 - j]'(by simp; omega) = a[j] := by
    rw [List.getElem_reverse]; congr 1; omega
  have e2 : a.reverse.take (a.length - 1 - j) = (a.drop (j + 1)).reverse := by
    rw [List.take_reverse]; congr 2; omega
  rw [e1, e2]
  apply semiStep_iff_of_compl
  intro d _ hd2
  have hm := List.getElem_mem hj
  obtain ⟨h1, h2⟩ := window_mem hf hm hd2
  have hr : 1 ≤ a[j] := ((mem_range'_of_perm hf).1 hm).1
  simp only [List.mem_reverse]
  constructor
  · exact reversal_compl hnd hj h1 (by unfold reach at hd2; omega)
  · exact reversal_compl hnd hj h2 (by unfold reach at hd2; omega)

theorem semiSymmetric_take_iff {N k : Nat} {a : List Nat} :
    SemiSymmetric N (a.take k) ↔
      ∀ j (hj : j < a.length), j < k → SemiStep N (a.take j) a[j] := by
  constructor
  · intro h j hj hjk
    have := h j (by simp; omega)
    rwa [List.take_take, Nat.min_eq_left hjk.le, List.getElem_take] at this
  · intro h j hj
    simp only [List.length_take] at hj
    rw [List.take_take, Nat.min_eq_left (by omega), List.getElem_take]
    exact h j (by omega) (by omega)

/-- **Splitting at position `k`.**  A fold sequence is semi-symmetric iff its first `k`
panels form a semi-symmetric sequence and so do its remaining panels read backwards. -/
theorem semiSymmetric_split_iff {N : Nat} {a : List Nat} (hf : IsFoldSeq N a) {k : Nat}
    (hk : k ≤ a.length) :
    SemiSymmetric N a ↔ SemiSymmetric N (a.take k) ∧ SemiSymmetric N (a.drop k).reverse := by
  have hr : (a.drop k).reverse = a.reverse.take (a.length - k) := by
    rw [List.take_reverse]; congr 2; omega
  have key : ∀ i j (hi : i < a.reverse.length) (hj : j < a.length), i = a.length - 1 - j →
      (SemiStep N (a.reverse.take i) a.reverse[i] ↔ SemiStep N (a.take j) a[j]) := by
    intro i j hi hj e; subst e; exact (semiStep_reverse_iff hf hj).symm
  rw [hr, semiSymmetric_take_iff, semiSymmetric_take_iff]
  simp only [List.length_reverse]
  constructor
  · intro h
    refine ⟨fun j hj _ => h j hj, fun i hi hik => ?_⟩
    exact (key i (a.length - 1 - i) (by simpa using hi) (by omega) (by omega)).2 (h _ _)
  · rintro ⟨h1, h2⟩ j hj
    by_cases hjk : j < k
    · exact h1 j hj hjk
    · exact (key (a.length - 1 - j) j (by simp; omega) hj rfl).1
        (h2 _ (by omega) (by omega))

/-! ## (c) The reversal (meet-in-the-middle) identity -/

theorem mem_drop_iff_of_nodup {a : List Nat} (hnd : a.Nodup) (k x : Nat) :
    x ∈ a.drop k ↔ x ∈ a ∧ x ∉ a.take k := by
  have h := hnd
  rw [← List.take_append_drop k a] at h
  have hd := (List.nodup_append.1 h).2.2
  constructor
  · intro hx; exact ⟨List.mem_of_mem_drop hx, fun ht => hd x ht x hx rfl⟩
  · rintro ⟨hx, hnt⟩
    rw [← List.take_append_drop k a, List.mem_append] at hx
    exact hx.resolve_left hnt

/-- **(c) Reversal identity.**  For every `k ≤ N`,
`a(N) = ∑_{S ⊆ [1..N], |S| = k} g N S · g N ([1..N] \ S)`.
A semi-symmetric sequence is split after its first `k` panels; the first part is a
semi-symmetric ordering of its set `S`, and the second part, read backwards, is a
semi-symmetric ordering of the complement. -/
theorem semiCount_eq_sum_split {N k : Nat} (hk : k ≤ N) :
    semiCount N = ∑ S ∈ (Finset.Icc 1 N).powersetCard k,
      g N S * g N (Finset.Icc 1 N \ S) := by
  rw [semiCount, Finset.card_eq_sum_card_fiberwise
    (f := fun a => (a.take k).toFinset) (t := (Finset.Icc 1 N).powersetCard k)]
  · apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [g, g, ← Finset.card_product]
    apply Finset.card_nbij' (fun a => (a.take k, (a.drop k).reverse))
      (fun p => p.1 ++ p.2.reverse)
    · intro a ha
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_semiSeqs] at ha
      obtain ⟨⟨hf, hss⟩, hSa⟩ := ha
      have hnd := nodup_of_foldSeq hf
      have hlen : a.length = N := by rw [hf.length_eq]; simp
      rw [semiSymmetric_split_iff hf (k := k) (by omega)] at hss
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_semiOrders]
      refine ⟨⟨⟨take_nodup hnd k, hSa⟩, hss.1⟩, ⟨⟨?_, ?_⟩, hss.2⟩⟩
      · exact List.nodup_reverse.2 (hnd.sublist (List.drop_sublist _ _))
      · ext x
        rw [List.mem_toFinset, List.mem_reverse, mem_drop_iff_of_nodup hnd, Finset.mem_sdiff,
          ← hSa, List.mem_toFinset, ← List.mem_toFinset (l := a), (isFoldSeq_iff.1 hf).2]
    · rintro ⟨u, v⟩ hp
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_semiOrders] at hp
      obtain ⟨⟨⟨hnu, hu⟩, hsu⟩, ⟨⟨hnv, hv⟩, hsv⟩⟩ := hp
      have hulen : u.length = k := by
        rw [← List.toFinset_card_of_nodup hnu, hu, hS.2]
      have hf : IsFoldSeq N (u ++ v.reverse) := by
        rw [isFoldSeq_iff]
        refine ⟨List.nodup_append.2 ⟨hnu, List.nodup_reverse.2 hnv, ?_⟩, ?_⟩
        · intro x hx y hy e
          subst e
          have h1 : x ∈ u.toFinset := List.mem_toFinset.2 hx
          have h2 : x ∈ v.toFinset := List.mem_toFinset.2 (List.mem_reverse.1 hy)
          rw [hu] at h1; rw [hv, Finset.mem_sdiff] at h2
          exact h2.2 h1
        · rw [List.toFinset_append, List.toFinset_reverse, hu, hv,
            Finset.union_sdiff_of_subset hS.1]
      have ht : (u ++ v.reverse).take k = u := List.take_left' hulen
      have hd : (u ++ v.reverse).drop k = v.reverse := List.drop_left' hulen
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_semiSeqs]
      refine ⟨⟨hf, ?_⟩, by rw [ht, hu]⟩
      rw [semiSymmetric_split_iff hf (k := k) (by simp; omega), ht, hd, List.reverse_reverse]
      exact ⟨hsu, hsv⟩
    · intro a _
      simp
    · rintro ⟨u, v⟩ hp
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_semiOrders] at hp
      have hulen : u.length = k := by
        rw [← List.toFinset_card_of_nodup hp.1.1.1, hp.1.1.2, hS.2]
      simp [List.take_left' hulen, List.drop_left' hulen]
  · intro a ha
    simp only [Finset.mem_coe, mem_semiSeqs] at ha
    have hf := ha.1
    have hnd := nodup_of_foldSeq hf
    have hlen : a.length = N := by rw [hf.length_eq]; simp
    simp only [Finset.mem_coe]
    refine Finset.mem_powersetCard.2 ⟨?_, ?_⟩
    · intro x hx
      rw [List.mem_toFinset] at hx
      rw [Finset.mem_Icc, ← mem_range'_of_perm hf]
      exact List.mem_of_mem_take hx
    · rw [List.toFinset_card_of_nodup (take_nodup hnd k), List.length_take]; omega

end Folds
