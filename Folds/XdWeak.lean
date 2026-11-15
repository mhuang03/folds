import Folds.Neutral

/-!
# Valid weak orders (simultaneous folds)

Experiments and paper proofs: `experiments/xd_weak/NOTES.txt`.

A *weak order* on the panels `[1, N]` is an ordered set partition `(B₁, …, B_k)`: the panels of
a block are folded simultaneously.  Writing `S = B₁ ∪ … ∪ B_{i-1}`, a weak order is a chain
`∅ = S₀ ⊂ S₁ ⊂ … ⊂ S_k = [1, N]`, and it is *valid* for a link relation `R` if every link
`(S_{i-1}, B_i)` satisfies `R`.  Four link relations are studied:

* `linkA`: every `m ∈ B` is balanced with respect to `S`;
* `linkB`: every `m ∈ B` is balanced with respect to `S` and to `S ∪ B`;
* `linkC`: every `m ∈ B` is balanced with respect to `S ∪ T` for all `T ⊆ B`
  (equivalently, every ordering of `B` is a valid run of steps from `S`:
  `linkC_iff_forall_orderings`);
* `linkD`: some ordering of `B` is a valid run of steps from `S`.

## Main results
* `mem_chains`, `card_chains_succ`: the chains of length `k` from `S`, and their recursion.
* `W_top`: `W(N, N) = a(N)` for every link relation that is `BalF` on singletons
  (`WA_top`, `WB_top`, `WC_top`, `WD_top`).
* `W_one`: `W(N, 1) = 1` (`WA_one`, `WB_one`, `WD_one`).
* `W_two`; `WA_two`: `W_a(N, 2)` is the number of proper nonempty window copies;
  `WB_two`: `W_b(N, 2)` is the number of proper neutral sets, `= |NFam N|`.
* closure: `validFrom_refine` (splitting a block) for relations with the splitting property,
  in particular `linkC` (`validFrom_split_C`); `validFrom_coarsen` (merging two adjacent
  blocks) for relations with the merging property, in particular `linkD`
  (`validFrom_merge_D`).  `linkC → linkB → linkA` and `linkC → linkD`.
  The small counterexamples `not_refine_A`, `not_coarsen_A`, `not_refine_B`, `not_coarsen_B`,
  `not_coarsen_C`, `not_refine_D` show that nothing else is closed.
* `euler_flip`: if a panel `x` is always admissible, the alternating sums satisfy
  `E(S) = -E(S ∪ {x})`.
* `euler_A_even`: for even `N ≥ 4`, `∑_k (-1)^k W_a(N, k) = 0`
  (and `euler_symA_even` for the symmetric analogue).
* `euler_A_odd`: for odd `N = 2c - 1 ≥ 3`, `∑_k (-1)^k W_a(N, k) = -E({1, c, N})`.
-/

namespace Folds
namespace XdWeak

open Finset Neutral

/-! ## Chains for a general link relation -/

section Chains

variable (N : ℕ) (R : Finset ℕ → Finset ℕ → Prop) [∀ S B, Decidable (R S B)]

/-- The admissible next blocks after the set `S`: nonempty subsets `B` of `[1, N] \ S` with
`R S B`. -/
def blocks (S : Finset ℕ) : Finset (Finset ℕ) :=
  ((Icc 1 N \ S).powerset).filter (fun B => B.Nonempty ∧ R S B)

theorem mem_blocks {S B : Finset ℕ} :
    B ∈ blocks N R S ↔ B ⊆ Icc 1 N \ S ∧ B.Nonempty ∧ R S B := by
  simp [blocks]

/-- `l = [B₁, …, B_k]` is a valid chain of blocks from `S` up to `[1, N]`. -/
def ValidFrom : Finset ℕ → List (Finset ℕ) → Prop
  | S, [] => S = Icc 1 N
  | S, B :: l => B ∈ blocks N R S ∧ ValidFrom (S ∪ B) l

/-- A valid weak order of `[1, N]`: a valid chain of blocks from `∅`. -/
def IsWeakOrder (l : List (Finset ℕ)) : Prop := ValidFrom N R ∅ l

/-- The valid chains of exactly `k` blocks from `S` up to `[1, N]`. -/
def chains : ℕ → Finset ℕ → Finset (List (Finset ℕ))
  | 0, S => if S = Icc 1 N then {[]} else ∅
  | k + 1, S => (blocks N R S).biUnion fun B => (chains k (S ∪ B)).image (List.cons B)

/-- `W(N, k)`: the number of valid weak orders of `[1, N]` with `k` blocks. -/
def W (k : ℕ) : ℕ := (chains N R k ∅).card

theorem mem_chains {k : ℕ} {S : Finset ℕ} {l : List (Finset ℕ)} :
    l ∈ chains N R k S ↔ l.length = k ∧ ValidFrom N R S l := by
  induction k generalizing S l with
  | zero =>
    cases l with
    | nil => by_cases h : S = Icc 1 N <;> simp [chains, ValidFrom, h]
    | cons B l => by_cases h : S = Icc 1 N <;> simp [chains, h]
  | succ k ih =>
    cases l with
    | nil => simp [chains]
    | cons B l =>
      simp only [chains, mem_biUnion, mem_image, List.cons.injEq, List.length_cons, ValidFrom,
        Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨B', hB', l', hl', rfl, rfl⟩
        exact ⟨(ih.1 hl').1, hB', (ih.1 hl').2⟩
      · rintro ⟨hlen, hB, hv⟩
        exact ⟨B, hB, l, ih.2 ⟨hlen, hv⟩, rfl, rfl⟩

/-- `W(N, k)` counts the valid weak orders with `k` blocks. -/
theorem mem_chains_empty {k : ℕ} {l : List (Finset ℕ)} :
    l ∈ chains N R k ∅ ↔ l.length = k ∧ IsWeakOrder N R l := mem_chains N R

/-- Recursion on the first block. -/
theorem card_chains_succ (k : ℕ) (S : Finset ℕ) :
    (chains N R (k + 1) S).card = ∑ B ∈ blocks N R S, (chains N R k (S ∪ B)).card := by
  rw [chains, card_biUnion]
  · exact sum_congr rfl fun B _ => card_image_of_injective _ List.cons_injective
  · intro B _ B' _ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro l h1 h2
    simp only [mem_image] at h1 h2
    obtain ⟨u, -, rfl⟩ := h1
    obtain ⟨v, -, e⟩ := h2
    exact hne (List.cons.inj e).1.symm

theorem card_sdiff_union {S B : Finset ℕ} (hB : B ⊆ Icc 1 N \ S) :
    (Icc 1 N \ (S ∪ B)).card + B.card = (Icc 1 N \ S).card := by
  have e : Icc 1 N \ (S ∪ B) = (Icc 1 N \ S) \ B := by
    ext x; simp only [mem_sdiff, mem_union]; tauto
  rw [e, card_sdiff_of_subset hB]
  have := card_le_card hB
  omega

/-- Blocks are nonempty and disjoint, so a chain from `S` has at most `|[1, N] \ S|` blocks. -/
theorem length_le_of_validFrom {S : Finset ℕ} {l : List (Finset ℕ)} (h : ValidFrom N R S l) :
    l.length ≤ (Icc 1 N \ S).card := by
  induction l generalizing S with
  | nil => simp
  | cons B l ih =>
    obtain ⟨hB, hv⟩ := h
    obtain ⟨hsub, hne, -⟩ := (mem_blocks N R).1 hB
    have h1 := ih hv
    have h2 := card_sdiff_union N hsub
    have h3 := hne.card_pos
    simp only [List.length_cons]
    omega

theorem chains_eq_empty {k : ℕ} {S : Finset ℕ} (h : (Icc 1 N \ S).card < k) :
    chains N R k S = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro l hl
  obtain ⟨hlen, hv⟩ := (mem_chains N R).1 hl
  have := length_le_of_validFrom N R hv
  omega

theorem W_eq_zero {k : ℕ} (h : N < k) : W N R k = 0 := by
  rw [W, chains_eq_empty N R (by simpa using h), card_empty]

end Chains

/-! ## Balance lemmas -/

theorem semiStep_iff_balF {N m : ℕ} {l : List ℕ} (hnd : l.Nodup) :
    SemiStep N l m ↔ BalF N l.toFinset m := by
  unfold SemiStep BalF
  rw [leftCount_eq hnd, rightCount_eq hnd, countP_eq_card hnd, countP_eq_card hnd]

theorem setStep_iff_balF {N m : ℕ} {S : Finset ℕ} : SetStep N S m ↔ BalF N S m := by
  unfold SetStep
  rw [semiStep_iff_balF (Finset.sort_nodup _ _), Finset.sort_toFinset]

/-- A panel does not lie in its own window. -/
theorem balF_insert_self {N m : ℕ} {X : Finset ℕ} : BalF N (insert m X) m ↔ BalF N X m := by
  unfold BalF
  have h1 : ¬(m - reach N m ≤ m ∧ m < m) := by omega
  have h2 : ¬(m < m ∧ m ≤ m + reach N m) := by omega
  simp only [filter_insert, h1, h2, ↓reduceIte]

theorem balF_empty (N m : ℕ) : BalF N ∅ m := by simp [BalF]

/-- The end panels have an empty window. -/
theorem balF_of_reach_zero {N m : ℕ} (h : reach N m = 0) (S : Finset ℕ) : BalF N S m := by
  unfold BalF
  rw [h, filter_false_of_mem (fun x _ => by omega), filter_false_of_mem (fun x _ => by omega)]

theorem balF_one (N : ℕ) (S : Finset ℕ) : BalF N S 1 :=
  balF_of_reach_zero (by simp [reach]) S

theorem balF_last (N : ℕ) (S : Finset ℕ) : BalF N S N :=
  balF_of_reach_zero (by simp [reach]) S

/-! ## The top column: `W(N, N) = a(N)` -/

section Top

variable (N : ℕ) (R : Finset ℕ → Finset ℕ → Prop) [∀ S B, Decidable (R S B)]

theorem card_chains_top (hR : ∀ S m, R S {m} ↔ BalF N S m) :
    ∀ (j : ℕ) (S : Finset ℕ), S ⊆ Icc 1 N → (Icc 1 N \ S).card = j →
      (chains N R j S).card = g N (Icc 1 N \ S) := by
  intro j
  induction j with
  | zero =>
    intro S hS hc
    have h0 : Icc 1 N \ S = ∅ := card_eq_zero.1 hc
    have hSe : S = Icc 1 N := subset_antisymm hS (sdiff_eq_empty_iff_subset.1 h0)
    rw [h0, g_empty]
    simp [chains, hSe]
  | succ j ih =>
    intro S hS hc
    have hX : (Icc 1 N \ S).Nonempty := card_pos.1 (by omega)
    rw [card_chains_succ, g_eq_sum hX]
    -- the right-hand side, rewritten with `BalF` and the induction hypothesis
    have hR1 : ∀ m ∈ Icc 1 N \ S,
        (SetStep N ((Icc 1 N \ S).erase m) m ↔ BalF N S m) ∧
          Icc 1 N \ insert m S = (Icc 1 N \ S).erase m ∧ insert m S ⊆ Icc 1 N := by
      intro m hm
      have hm' := mem_sdiff.1 hm
      have hsub : insert m S ⊆ Icc 1 N := insert_subset hm'.1 hS
      have e : Icc 1 N \ insert m S = (Icc 1 N \ S).erase m := by
        ext x; simp only [mem_sdiff, mem_insert, mem_erase]; tauto
      refine ⟨?_, e, hsub⟩
      rw [setStep_iff_balF, ← e, balF_compl_iff hsub hm'.1, balF_insert_self]
    have e1 : (Icc 1 N \ S).filter (fun m => SetStep N ((Icc 1 N \ S).erase m) m) =
        (Icc 1 N \ S).filter (fun m => BalF N S m) :=
      filter_congr fun m hm => (hR1 m hm).1
    rw [e1]
    have e2 : ∑ m ∈ (Icc 1 N \ S).filter (fun m => BalF N S m), g N ((Icc 1 N \ S).erase m) =
        ∑ m ∈ (Icc 1 N \ S).filter (fun m => BalF N S m), (chains N R j (S ∪ {m})).card := by
      apply sum_congr rfl
      intro m hm
      have hm' := (mem_filter.1 hm).1
      obtain ⟨-, e, hsub⟩ := hR1 m hm'
      have hc' : (Icc 1 N \ insert m S).card = j := by
        rw [e, card_erase_of_mem hm']; omega
      rw [union_singleton, ih (insert m S) hsub hc', e]
    rw [e2]
    -- the left-hand side: only singleton blocks contribute
    have hinj : Function.Injective (fun m : ℕ => ({m} : Finset ℕ)) := singleton_injective
    rw [← sum_image (f := fun B => (chains N R j (S ∪ B)).card) (fun a _ b _ h => hinj h)]
    symm
    apply sum_subset
    · intro B hB
      obtain ⟨m, hm, rfl⟩ := mem_image.1 hB
      obtain ⟨hm1, hm2⟩ := mem_filter.1 hm
      exact (mem_blocks N R).2 ⟨singleton_subset_iff.2 hm1, singleton_nonempty m, (hR S m).2 hm2⟩
    · intro B hB hBn
      obtain ⟨hsub, hne, hRB⟩ := (mem_blocks N R).1 hB
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro l hl
      obtain ⟨hlen, hv⟩ := (mem_chains N R).1 hl
      have h1 := length_le_of_validFrom N R hv
      have h2 := card_sdiff_union N hsub
      have h3 := hne.card_pos
      have h4 : B.card = 1 := by omega
      obtain ⟨m, rfl⟩ := card_eq_one.1 h4
      exact hBn (mem_image.2 ⟨m, mem_filter.2 ⟨singleton_subset_iff.1 hsub, (hR S m).1 hRB⟩, rfl⟩)

/-- **Top column.**  For every link relation that reduces to `BalF` on singleton blocks, the
valid weak orders with `N` blocks are the semi-symmetric fold sequences: `W(N, N) = a(N)`. -/
theorem W_top (hR : ∀ S m, R S {m} ↔ BalF N S m) : W N R N = semiCount N := by
  rw [W, card_chains_top N R hR N ∅ (empty_subset _) (by simp), sdiff_empty, semiCount_eq_g]

/-- **First column.**  `W(N, 1) = 1` as soon as the single block `[1, N]` is admissible. -/
theorem W_one (hN : 1 ≤ N) (h : R ∅ (Icc 1 N)) : W N R 1 = 1 := by
  rw [W, card_eq_one]
  refine ⟨[Icc 1 N], ?_⟩
  ext l
  rw [mem_chains, mem_singleton]
  constructor
  · rintro ⟨hlen, hv⟩
    match l, hlen, hv with
    | [B], _, hv =>
      simp only [ValidFrom, empty_union] at hv
      rw [hv.2]
  · rintro rfl
    refine ⟨rfl, (mem_blocks N R).2 ⟨by simp, ?_, h⟩, by simp [ValidFrom]⟩
    exact ⟨1, mem_Icc.2 ⟨le_rfl, hN⟩⟩

/-- **Second column.**  `W(N, 2)` counts the sets `X` (the first block) such that both links
`(∅, X)` and `(X, [1, N] \ X)` are admissible. -/
theorem W_two : W N R 2 = (((Icc 1 N).powerset).filter fun X =>
    X.Nonempty ∧ X ≠ Icc 1 N ∧ R ∅ X ∧ R X (Icc 1 N \ X)).card := by
  rw [W]
  symm
  apply card_bij (fun X _ => [X, Icc 1 N \ X])
  · intro X hX
    obtain ⟨hsub, hne, hneq, h1, h2⟩ := by simpa using hX
    rw [mem_chains]
    refine ⟨rfl, (mem_blocks N R).2 ⟨by simpa using hsub, hne, h1⟩, ?_, ?_⟩
    · refine (mem_blocks N R).2 ⟨by simp, ?_, by simpa using h2⟩
      rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty_iff_subset]
      exact fun h => hneq (subset_antisymm hsub h)
    · show ∅ ∪ X ∪ (Icc 1 N \ X) = Icc 1 N
      rw [empty_union, union_sdiff_of_subset hsub]
  · intro X _ Y _ h
    exact (List.cons.inj h).1
  · intro l hl
    obtain ⟨hlen, hv⟩ := (mem_chains N R).1 hl
    match l, hlen, hv with
    | [B, C], _, hv =>
      obtain ⟨hB, hC, hfin⟩ := hv
      rw [empty_union] at hC hfin
      obtain ⟨hBs, hBne, hBR⟩ := (mem_blocks N R).1 hB
      obtain ⟨hCs, hCne, hCR⟩ := (mem_blocks N R).1 hC
      rw [sdiff_empty] at hBs
      have hCe : C = Icc 1 N \ B := by
        apply subset_antisymm hCs
        intro x hx
        obtain ⟨hx1, hx2⟩ := mem_sdiff.1 hx
        rw [← hfin, mem_union] at hx1
        exact hx1.resolve_left hx2
      have hBneq : B ≠ Icc 1 N := by
        rintro rfl
        rw [sdiff_self] at hCe
        exact hCne.ne_empty hCe
      refine ⟨B, ?_, by rw [hCe]⟩
      simp only [mem_filter, mem_powerset]
      exact ⟨hBs, hBne, hBneq, hBR, hCe ▸ hCR⟩

end Top

/-! ## Refinement and coarsening -/

section Closure

variable (N : ℕ) (R : Finset ℕ → Finset ℕ → Prop) [∀ S B, Decidable (R S B)]

/-- **Refinement.**  If the link relation splits (`R S (B ∪ C) → R S B ∧ R (S ∪ B) C`), then
splitting a block of a valid weak order into two nonempty parts gives a valid weak order. -/
theorem validFrom_refine
    (hsplit : ∀ S B C, Disjoint B C → R S (B ∪ C) → R S B ∧ R (S ∪ B) C)
    {S B C : Finset ℕ} {l₁ l₂ : List (Finset ℕ)} (hB : B.Nonempty) (hC : C.Nonempty)
    (hd : Disjoint B C) (h : ValidFrom N R S (l₁ ++ (B ∪ C) :: l₂)) :
    ValidFrom N R S (l₁ ++ B :: C :: l₂) := by
  induction l₁ generalizing S with
  | nil =>
    obtain ⟨hBC, hv⟩ := h
    obtain ⟨hsub, -, hR⟩ := (mem_blocks N R).1 hBC
    obtain ⟨h1, h2⟩ := hsplit S B C hd hR
    refine ⟨(mem_blocks N R).2 ⟨union_subset_left hsub, hB, h1⟩,
      (mem_blocks N R).2 ⟨?_, hC, h2⟩, ?_⟩
    · intro x hx
      have hx' := mem_sdiff.1 (hsub (mem_union_right _ hx))
      rw [mem_sdiff, mem_union]
      exact ⟨hx'.1, fun h => h.elim hx'.2 fun hxB => disjoint_left.1 hd hxB hx⟩
    · rwa [union_assoc]
  | cons A l₁ ih => exact ⟨h.1, ih h.2⟩

/-- **Coarsening.**  If the link relation merges (`R S B → R (S ∪ B) C → R S (B ∪ C)`), then
merging two adjacent blocks of a valid weak order gives a valid weak order. -/
theorem validFrom_coarsen
    (hmerge : ∀ S B C, Disjoint B C → R S B → R (S ∪ B) C → R S (B ∪ C))
    {S B C : Finset ℕ} {l₁ l₂ : List (Finset ℕ)}
    (h : ValidFrom N R S (l₁ ++ B :: C :: l₂)) :
    ValidFrom N R S (l₁ ++ (B ∪ C) :: l₂) := by
  induction l₁ generalizing S with
  | nil =>
    obtain ⟨hB, hC, hv⟩ := h
    obtain ⟨hBs, hBne, hBR⟩ := (mem_blocks N R).1 hB
    obtain ⟨hCs, -, hCR⟩ := (mem_blocks N R).1 hC
    have hd : Disjoint B C := by
      rw [disjoint_left]
      intro x hxB hxC
      exact (mem_sdiff.1 (hCs hxC)).2 (mem_union_right _ hxB)
    refine ⟨(mem_blocks N R).2 ⟨?_, hBne.mono subset_union_left, hmerge S B C hd hBR hCR⟩, ?_⟩
    · apply union_subset hBs
      intro x hx
      have hx' := mem_sdiff.1 (hCs hx)
      exact mem_sdiff.2 ⟨hx'.1, fun h => hx'.2 (mem_union_left _ h)⟩
    · rwa [← union_assoc]
  | cons A l₁ ih => exact ⟨h.1, ih h.2⟩

end Closure

/-! ## Alternating sums -/

section Euler

variable (N : ℕ) (R : Finset ℕ → Finset ℕ → Prop) [∀ S B, Decidable (R S B)]

/-- The alternating sum `E(S) = ∑_k (-1)^k #{valid chains of k blocks from S}`. -/
def euler (S : Finset ℕ) : ℤ :=
  ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * ((chains N R k S).card : ℤ)

/-- `E(∅) = ∑_k (-1)^k W(N, k)`, the value at `q = -1` of `A_N(q) = ∑_k W(N, k) C(q, k)`. -/
theorem euler_empty : euler N R ∅ = ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * (W N R k : ℤ) := rfl

theorem euler_step {S : Finset ℕ} (hS : S ≠ Icc 1 N) :
    euler N R S = -∑ B ∈ blocks N R S, euler N R (S ∪ B) := by
  have h0 : chains N R 0 S = ∅ := by simp [chains, hS]
  have hB : ∀ B ∈ blocks N R S, euler N R (S ∪ B) =
      ∑ k ∈ range N, (-1 : ℤ) ^ k * ((chains N R k (S ∪ B)).card : ℤ) := by
    intro B hB
    obtain ⟨hsub, hne, -⟩ := (mem_blocks N R).1 hB
    have h2 := card_sdiff_union N hsub
    have h3 := hne.card_pos
    have h4 : (Icc 1 N \ S).card ≤ N := by
      have := card_le_card (sdiff_subset (s := Icc 1 N) (t := S))
      simpa using this
    rw [euler, sum_range_succ, chains_eq_empty N R (by omega), card_empty]
    simp
  rw [euler, sum_range_succ', h0, sum_congr rfl hB, sum_comm, ← sum_neg_distrib]
  simp only [card_empty, Nat.cast_zero, mul_zero, add_zero]
  apply sum_congr rfl
  intro k _
  rw [card_chains_succ, Nat.cast_sum, mul_sum, ← sum_neg_distrib]
  apply sum_congr rfl
  intro B _
  ring

/-- **Flip lemma.**  If the panel `x` can be added to or removed from any admissible block
(for `linkA`: `x` is balanced with respect to every set), then `E(S) = -E(S ∪ {x})` for every
`S` not containing `x`. -/
theorem euler_flip {x : ℕ} (hx : x ∈ Icc 1 N) (h0 : ∀ S, R S ∅)
    (hR : ∀ S B, R S (insert x B) ↔ R S B) :
    ∀ (j : ℕ) (S : Finset ℕ), (Icc 1 N \ S).card = j → x ∉ S →
      euler N R S = -euler N R (insert x S) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro S hc hxS
    have hSne : S ≠ Icc 1 N := fun h => hxS (h ▸ hx)
    rw [euler_step N R hSne]
    congr 1
    have hxb : {x} ∈ blocks N R S := by
      refine (mem_blocks N R).2 ⟨singleton_subset_iff.2 (mem_sdiff.2 ⟨hx, hxS⟩),
        singleton_nonempty x, ?_⟩
      have := (hR S ∅).2 (h0 S)
      simpa using this
    rw [← add_sum_erase _ _ hxb, union_singleton]
    suffices h : ∑ B ∈ (blocks N R S).erase {x}, euler N R (S ∪ B) = 0 by rw [h, add_zero]
    -- induction hypothesis in the form used below
    have key : ∀ B ∈ blocks N R S, x ∉ B →
        euler N R (S ∪ B) + euler N R (S ∪ insert x B) = 0 := by
      intro B hB hxB
      obtain ⟨hsub, hne, -⟩ := (mem_blocks N R).1 hB
      have h2 := card_sdiff_union N hsub
      have h3 := hne.card_pos
      have := ih (Icc 1 N \ (S ∪ B)).card (by omega) (S ∪ B) rfl
        (by rw [mem_union]; exact fun h => h.elim hxS hxB)
      rw [this, union_insert]; ring
    refine sum_involution (fun B _ => if x ∈ B then B.erase x else insert x B) ?_ ?_ ?_ ?_
    · intro B hB
      obtain ⟨hBx, hBb⟩ := mem_erase.1 hB
      obtain ⟨hsub, hne, hRB⟩ := (mem_blocks N R).1 hBb
      by_cases hxB : x ∈ B
      · simp only [hxB, ↓reduceIte]
        have hne' : (B.erase x).Nonempty := by
          rw [nonempty_iff_ne_empty, Ne, erase_eq_empty_iff]
          exact fun h => h.elim hne.ne_empty hBx
        have hb' : B.erase x ∈ blocks N R S :=
          (mem_blocks N R).2 ⟨(erase_subset _ _).trans hsub, hne',
            (hR S (B.erase x)).1 (by rwa [insert_erase hxB])⟩
        have := key (B.erase x) hb' (notMem_erase x B)
        rw [insert_erase hxB] at this
        rw [add_comm]; exact this
      · simp only [hxB, ↓reduceIte]
        exact key B hBb hxB
    · intro B _ _
      by_cases hxB : x ∈ B
      · simp only [hxB, ↓reduceIte]
        exact fun h => notMem_erase x B (h ▸ hxB)
      · simp only [hxB, ↓reduceIte]
        exact fun h => hxB (h ▸ mem_insert_self x B)
    · intro B hB
      obtain ⟨hBx, hBb⟩ := mem_erase.1 hB
      obtain ⟨hsub, hne, hRB⟩ := (mem_blocks N R).1 hBb
      by_cases hxB : x ∈ B
      · simp only [hxB, ↓reduceIte]
        have hne' : (B.erase x).Nonempty := by
          rw [nonempty_iff_ne_empty, Ne, erase_eq_empty_iff]
          exact fun h => h.elim hne.ne_empty hBx
        refine mem_erase.2 ⟨fun h => ?_, (mem_blocks N R).2 ⟨(erase_subset _ _).trans hsub, hne',
          (hR S (B.erase x)).1 (by rwa [insert_erase hxB])⟩⟩
        exact notMem_erase x B (h ▸ mem_singleton_self x)
      · simp only [hxB, ↓reduceIte]
        refine mem_erase.2 ⟨fun h => ?_, (mem_blocks N R).2 ⟨?_, insert_nonempty x B,
          (hR S B).2 hRB⟩⟩
        · obtain ⟨y, hy⟩ := hne
          have : y ∈ ({x} : Finset ℕ) := h ▸ mem_insert_of_mem hy
          exact hxB (mem_singleton.1 this ▸ hy)
        · exact insert_subset (mem_sdiff.2 ⟨hx, hxS⟩) hsub
    · intro B hB
      by_cases hxB : x ∈ B
      · simp [hxB, insert_erase hxB]
      · simp [hxB, erase_insert hxB]

theorem euler_full : euler N R (Icc 1 N) = 1 := by
  rw [euler, sum_eq_single 0]
  · simp [chains]
  · intro k _ hk
    rw [chains_eq_empty N R (by simp; omega), card_empty]; simp
  · intro h; exact absurd (mem_range.2 (Nat.succ_pos N)) h

end Euler

/-! ## The four conventions -/

/-- Link relation of "one-sided" type: every panel of the block satisfies the step predicate
`P` with respect to the set `S` of earlier panels. -/
def linkOf (P : Finset ℕ → ℕ → Prop) (S B : Finset ℕ) : Prop := ∀ m ∈ B, P S m

instance (P : Finset ℕ → ℕ → Prop) [∀ S m, Decidable (P S m)] (S B : Finset ℕ) :
    Decidable (linkOf P S B) := inferInstanceAs (Decidable (∀ m ∈ B, P S m))

/-- Convention (a): every panel of the block is balanced with respect to the earlier panels. -/
abbrev linkA (N : ℕ) : Finset ℕ → Finset ℕ → Prop := linkOf (BalF N)

/-- Convention (b): every panel of the block is balanced with respect to the earlier panels,
and also with respect to the earlier panels together with its own block. -/
def linkB (N : ℕ) (S B : Finset ℕ) : Prop := ∀ m ∈ B, BalF N S m ∧ BalF N (S ∪ B) m

instance (N : ℕ) (S B : Finset ℕ) : Decidable (linkB N S B) :=
  inferInstanceAs (Decidable (∀ m ∈ B, BalF N S m ∧ BalF N (S ∪ B) m))

/-- Convention (c): every panel of the block is balanced with respect to the earlier panels
together with any part of its own block. -/
def linkC (N : ℕ) (S B : Finset ℕ) : Prop := ∀ m ∈ B, ∀ T ∈ B.powerset, BalF N (S ∪ T) m

instance (N : ℕ) (S B : Finset ℕ) : Decidable (linkC N S B) :=
  inferInstanceAs (Decidable (∀ m ∈ B, ∀ T ∈ B.powerset, BalF N (S ∪ T) m))

/-- The panels of `l` can be folded one after the other, starting from the set `S`. -/
def StepsFrom (N : ℕ) : Finset ℕ → List ℕ → Prop
  | _, [] => True
  | S, m :: l => BalF N S m ∧ StepsFrom N (insert m S) l

instance decStepsFrom (N : ℕ) : ∀ (S : Finset ℕ) (l : List ℕ), Decidable (StepsFrom N S l)
  | _, [] => isTrue trivial
  | S, m :: l =>
    haveI := decStepsFrom N (insert m S) l
    inferInstanceAs (Decidable (BalF N S m ∧ StepsFrom N (insert m S) l))

/-- Convention (d): some ordering of the block is a valid run of steps. -/
def linkD (N : ℕ) (S B : Finset ℕ) : Prop := ∃ l ∈ orderings B, StepsFrom N S l

instance (N : ℕ) (S B : Finset ℕ) : Decidable (linkD N S B) :=
  inferInstanceAs (Decidable (∃ l ∈ orderings B, StepsFrom N S l))

theorem stepsFrom_append {N : ℕ} {S : Finset ℕ} {l₁ l₂ : List ℕ} :
    StepsFrom N S (l₁ ++ l₂) ↔ StepsFrom N S l₁ ∧ StepsFrom N (S ∪ l₁.toFinset) l₂ := by
  induction l₁ generalizing S with
  | nil => simp [StepsFrom]
  | cons m l ih =>
    simp only [List.cons_append, StepsFrom, ih, List.toFinset_cons, and_assoc]
    rw [insert_union, union_insert]

/-! ### Singleton blocks -/

theorem linkA_singleton (N : ℕ) (S : Finset ℕ) (m : ℕ) : linkA N S {m} ↔ BalF N S m := by
  simp [linkOf]

theorem linkB_singleton (N : ℕ) (S : Finset ℕ) (m : ℕ) : linkB N S {m} ↔ BalF N S m := by
  simp [linkB, union_singleton, balF_insert_self]

theorem linkC_singleton (N : ℕ) (S : Finset ℕ) (m : ℕ) : linkC N S {m} ↔ BalF N S m := by
  constructor
  · intro h
    have := h m (mem_singleton_self m) ∅ (by simp)
    simpa using this
  · intro h m' hm' T hT
    rw [mem_singleton] at hm'; subst hm'
    rcases subset_singleton_iff.1 (mem_powerset.1 hT) with rfl | rfl
    · simpa using h
    · rw [union_singleton, balF_insert_self]; exact h

theorem linkD_singleton (N : ℕ) (S : Finset ℕ) (m : ℕ) : linkD N S {m} ↔ BalF N S m := by
  constructor
  · rintro ⟨l, hl, hs⟩
    obtain ⟨hnd, hf⟩ := mem_orderings.1 hl
    have hlen : l.length = 1 := by
      rw [← List.toFinset_card_of_nodup hnd, hf, card_singleton]
    match l, hlen with
    | [a], _ =>
      have : a = m := by
        have : a ∈ ({m} : Finset ℕ) := hf ▸ (by simp)
        exact mem_singleton.1 this
      subst this
      exact hs.1
  · intro h
    exact ⟨[m], mem_orderings.2 ⟨List.nodup_singleton m, by simp⟩, h, trivial⟩

/-! ### Implications between the conventions -/

theorem linkB_imp_linkA {N : ℕ} {S B : Finset ℕ} (h : linkB N S B) : linkA N S B :=
  fun m hm => (h m hm).1

theorem linkC_imp_linkB {N : ℕ} {S B : Finset ℕ} (h : linkC N S B) : linkB N S B := by
  intro m hm
  refine ⟨?_, h m hm B (mem_powerset.2 (Subset.refl B))⟩
  have := h m hm ∅ (by simp)
  simpa using this

/-- (c) splits: this is closure under refinement. -/
theorem linkC_split {N : ℕ} {S B C : Finset ℕ} (h : linkC N S (B ∪ C)) :
    linkC N S B ∧ linkC N (S ∪ B) C := by
  constructor
  · intro m hm T hT
    exact h m (mem_union_left _ hm) T
      (mem_powerset.2 ((mem_powerset.1 hT).trans subset_union_left))
  · intro m hm T hT
    rw [union_assoc]
    exact h m (mem_union_right _ hm) (B ∪ T)
      (mem_powerset.2 (union_subset_union (Subset.refl B) (mem_powerset.1 hT)))

/-- Under (c), every ordering of the block is a valid run of steps. -/
theorem stepsFrom_of_linkC {N : ℕ} : ∀ (l : List ℕ) (S : Finset ℕ), l.Nodup →
    linkC N S l.toFinset → StepsFrom N S l := by
  intro l
  induction l with
  | nil => intro S _ _; trivial
  | cons m l ih =>
    intro S hnd h
    refine ⟨?_, ih (insert m S) (List.nodup_cons.1 hnd).2 ?_⟩
    · have := h m (by simp) ∅ (by simp)
      simpa using this
    · intro m' hm' T hT
      have e : insert m S ∪ T = S ∪ insert m T := by rw [insert_union, union_insert]
      rw [e]
      refine h m' (by rw [List.toFinset_cons]; exact mem_insert_of_mem hm') (insert m T) ?_
      rw [mem_powerset, List.toFinset_cons]
      exact insert_subset_insert m (mem_powerset.1 hT)

/-- **(c) = "every linear refinement is valid".**  The link `(S, B)` satisfies (c) iff every
ordering of `B` is a valid run of steps from `S`. -/
theorem linkC_iff_forall_orderings {N : ℕ} {S B : Finset ℕ} :
    linkC N S B ↔ ∀ l ∈ orderings B, StepsFrom N S l := by
  constructor
  · intro h l hl
    obtain ⟨hnd, hf⟩ := mem_orderings.1 hl
    exact stepsFrom_of_linkC l S hnd (hf ▸ h)
  · intro h m hm T hT
    have hTB := mem_powerset.1 hT
    -- order: first `T \ {m}`, then `m`, then the rest
    have hl : (T.erase m).toList ++ m :: (B \ insert m T).toList ∈ orderings B := by
      rw [mem_orderings]
      constructor
      · rw [List.nodup_append]
        refine ⟨nodup_toList _, ?_, ?_⟩
        · rw [List.nodup_cons]
          exact ⟨by simp, nodup_toList _⟩
        · intro a ha b hb
          rw [mem_toList, mem_erase] at ha
          rw [List.mem_cons, mem_toList, mem_sdiff, mem_insert] at hb
          rintro rfl
          rcases hb with rfl | hb
          · exact ha.1 rfl
          · exact hb.2 (Or.inr ha.2)
      · ext x
        simp only [List.toFinset_append, List.toFinset_cons, toList_toFinset, mem_union,
          mem_erase, mem_insert, mem_sdiff]
        constructor
        · rintro (⟨-, hx⟩ | rfl | ⟨hx, -⟩)
          · exact hTB hx
          · exact hm
          · exact hx
        · intro hx
          by_cases hxm : x = m
          · exact Or.inr (Or.inl hxm)
          · by_cases hxT : x ∈ T
            · exact Or.inl ⟨hxm, hxT⟩
            · exact Or.inr (Or.inr ⟨hx, fun h => h.elim hxm hxT⟩)
    have h1 := (stepsFrom_append.1 (h _ hl)).2.1
    rw [toList_toFinset] at h1
    by_cases hmT : m ∈ T
    · have e : S ∪ T = insert m (S ∪ T.erase m) := by
        rw [← union_insert, insert_erase hmT]
      rw [e, balF_insert_self]; exact h1
    · rwa [erase_eq_of_notMem hmT] at h1

theorem linkC_imp_linkD {N : ℕ} {S B : Finset ℕ} (h : linkC N S B) : linkD N S B :=
  ⟨B.toList, mem_orderings.2 ⟨nodup_toList B, toList_toFinset B⟩,
    linkC_iff_forall_orderings.1 h _ (mem_orderings.2 ⟨nodup_toList B, toList_toFinset B⟩)⟩

/-- (d) merges: this is closure under coarsening (and transitivity of the reachability
order on sets of panels). -/
theorem linkD_merge {N : ℕ} {S B C : Finset ℕ} (hd : Disjoint B C) (h1 : linkD N S B)
    (h2 : linkD N (S ∪ B) C) : linkD N S (B ∪ C) := by
  obtain ⟨l₁, hl₁, hs₁⟩ := h1
  obtain ⟨l₂, hl₂, hs₂⟩ := h2
  obtain ⟨hnd₁, hf₁⟩ := mem_orderings.1 hl₁
  obtain ⟨hnd₂, hf₂⟩ := mem_orderings.1 hl₂
  refine ⟨l₁ ++ l₂, mem_orderings.2 ⟨?_, by rw [List.toFinset_append, hf₁, hf₂]⟩, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hnd₁, hnd₂, ?_⟩
    intro a ha b hb
    rintro rfl
    have ha' : a ∈ B := hf₁ ▸ List.mem_toFinset.2 ha
    have hb' : a ∈ C := hf₂ ▸ List.mem_toFinset.2 hb
    exact disjoint_left.1 hd ha' hb'
  · rw [stepsFrom_append, hf₁]
    exact ⟨hs₁, hs₂⟩

/-- Valid weak orders for (c) are closed under refinement. -/
theorem validFrom_split_C {N : ℕ} {S B C : Finset ℕ} {l₁ l₂ : List (Finset ℕ)}
    (hB : B.Nonempty) (hC : C.Nonempty) (hd : Disjoint B C)
    (h : ValidFrom N (linkC N) S (l₁ ++ (B ∪ C) :: l₂)) :
    ValidFrom N (linkC N) S (l₁ ++ B :: C :: l₂) :=
  validFrom_refine N (linkC N) (fun _ _ _ _ h => linkC_split h) hB hC hd h

/-- Valid weak orders for (d) are closed under coarsening. -/
theorem validFrom_merge_D {N : ℕ} {S B C : Finset ℕ} {l₁ l₂ : List (Finset ℕ)}
    (h : ValidFrom N (linkD N) S (l₁ ++ B :: C :: l₂)) :
    ValidFrom N (linkD N) S (l₁ ++ (B ∪ C) :: l₂) :=
  validFrom_coarsen N (linkD N) (fun _ _ _ hd h1 h2 => linkD_merge hd h1 h2) h

/-! ### Columns -/

theorem WA_top (N : ℕ) : W N (linkA N) N = semiCount N := W_top N _ (linkA_singleton N)
theorem WB_top (N : ℕ) : W N (linkB N) N = semiCount N := W_top N _ (linkB_singleton N)
theorem WC_top (N : ℕ) : W N (linkC N) N = semiCount N := W_top N _ (linkC_singleton N)
theorem WD_top (N : ℕ) : W N (linkD N) N = semiCount N := W_top N _ (linkD_singleton N)

theorem WA_one {N : ℕ} (hN : 1 ≤ N) : W N (linkA N) 1 = 1 :=
  W_one N _ hN fun m _ => balF_empty N m

theorem WB_one {N : ℕ} (hN : 1 ≤ N) : W N (linkB N) 1 = 1 :=
  W_one N _ hN fun m hm => ⟨balF_empty N m, by rw [empty_union]; exact balF_full hm⟩

/-- `W_a(N, 2)` is the number of nonempty proper window copies (the second block). -/
theorem WA_two (N : ℕ) : W N (linkA N) 2 = (((Icc 1 N).powerset).filter fun Y =>
    Y.Nonempty ∧ Y ≠ Icc 1 N ∧ IsCopy N Y).card := by
  rw [W_two]
  apply card_bij (fun X _ => Icc 1 N \ X)
  · intro X hX
    obtain ⟨hsub, hne, hneq, -, h2⟩ := by simpa using hX
    simp only [mem_filter, mem_powerset]
    refine ⟨sdiff_subset, ?_, ?_, ?_⟩
    · rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty_iff_subset]
      exact fun h => hneq (subset_antisymm hsub h)
    · intro h
      obtain ⟨x, hx⟩ := hne
      have : x ∈ Icc 1 N \ X := h ▸ hsub hx
      exact (mem_sdiff.1 this).2 hx
    · intro m hm
      exact (balF_compl_iff hsub (mem_sdiff.1 hm).1).2 (h2 m hm)
  · intro X hX Y hY h
    have hXs : X ⊆ Icc 1 N := (by simpa using hX : _ ∧ _).1
    have hYs : Y ⊆ Icc 1 N := (by simpa using hY : _ ∧ _).1
    rw [← sdiff_sdiff_eq_self hXs, ← sdiff_sdiff_eq_self hYs, h]
  · intro Y hY
    obtain ⟨hsub, hne, hneq, hc⟩ := by simpa using hY
    refine ⟨Icc 1 N \ Y, ?_, sdiff_sdiff_eq_self hsub⟩
    simp only [mem_filter, mem_powerset]
    refine ⟨sdiff_subset, ?_, ?_, fun m _ => balF_empty N m, ?_⟩
    · rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty_iff_subset]
      exact fun h => hneq (subset_antisymm hsub h)
    · intro h
      obtain ⟨x, hx⟩ := hne
      have : x ∈ Icc 1 N \ Y := h ▸ hsub hx
      exact (mem_sdiff.1 this).2 hx
    · intro m hm
      rw [sdiff_sdiff_eq_self hsub] at hm
      exact (balF_compl_iff hsub (hsub hm)).1 (hc m hm)

/-- `W_b(N, 2)` is the number of proper neutral sets, which are classified: the two parity
classes and `E_d`, `E_dᶜ` for the odd divisors `3 ≤ d < N` of `N`. -/
theorem WB_two {N : ℕ} (hN : 2 ≤ N) : W N (linkB N) 2 = (NFam N).card := by
  rw [W_two]
  congr 1
  ext X
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨hsub, hne, hneq, h1, h2⟩
    refine (neutral_classification hN hsub).1 ⟨?_, hne.card_pos, ?_⟩
    · rw [neutral_iff_copy_compl hsub]
      refine ⟨fun m hm => ?_, fun m hm => ?_⟩
      · have := (h1 m hm).2
        rwa [empty_union] at this
      · exact (balF_compl_iff hsub (mem_sdiff.1 hm).1).2 (h2 m hm).1
    · have := card_lt_card (ssubset_iff_subset_ne.2 ⟨hsub, hneq⟩)
      simpa using this
  · intro hX
    have hsub := nfam_sub hX
    obtain ⟨hn, hpos, hlt⟩ := (neutral_classification hN hsub).2 hX
    refine ⟨hsub, card_pos.1 hpos, ?_, ?_, ?_⟩
    · rintro rfl
      simp at hlt
    · intro m hm
      exact ⟨balF_empty N m, by rw [empty_union]; exact hn m (hsub hm)⟩
    · intro m hm
      have hm' := (mem_sdiff.1 hm).1
      exact ⟨hn m hm', by rw [union_sdiff_of_subset hsub]; exact balF_full hm'⟩

/-! ### The Euler characteristic of convention (a) -/

/-- Symmetric step predicate (3-AP-free case): the earlier panels in the window of `m` are
mirror-symmetric about `m`. -/
def SymF (N : ℕ) (S : Finset ℕ) (m : ℕ) : Prop :=
  ∀ d ∈ Icc 1 (reach N m), (m - d ∈ S ↔ m + d ∈ S)

instance (N : ℕ) (S : Finset ℕ) (m : ℕ) : Decidable (SymF N S m) :=
  inferInstanceAs (Decidable (∀ d ∈ Icc 1 (reach N m), (m - d ∈ S ↔ m + d ∈ S)))

/-- Convention (a) in the symmetric case. -/
abbrev linkSymA (N : ℕ) : Finset ℕ → Finset ℕ → Prop := linkOf (SymF N)

theorem linkOf_insert {P : Finset ℕ → ℕ → Prop} {x : ℕ} (hx : ∀ S, P S x) (S B : Finset ℕ) :
    linkOf P S (insert x B) ↔ linkOf P S B := by
  simp [linkOf, hx]

/-- **Vanishing criterion.**  If the panels `1` and `N` are always admissible and no other
panel is admissible after `{1, N}`, then `∑_k (-1)^k W(N, k) = 0` (`N ≥ 3`). -/
theorem euler_linkOf_eq_zero {N : ℕ} (hN : 3 ≤ N) (P : Finset ℕ → ℕ → Prop)
    [∀ S m, Decidable (P S m)] (h1 : ∀ S, P S 1) (hl : ∀ S, P S N)
    (hmid : ∀ m ∈ Icc 2 (N - 1), ¬P {N, 1} m) :
    ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * (W N (linkOf P) k : ℤ) = 0 := by
  rw [← euler_empty]
  have hf1 := euler_flip N (linkOf P) (x := 1) (by simp; omega) (fun S m hm => by simp at hm)
    (linkOf_insert h1) _ ∅ rfl (by simp)
  have hf2 := euler_flip N (linkOf P) (x := N) (by simp; omega) (fun S m hm => by simp at hm)
    (linkOf_insert hl) _ (insert 1 ∅) rfl (by simp; omega)
  rw [hf1, hf2, neg_neg]
  have hne : insert N (insert 1 (∅ : Finset ℕ)) ≠ Icc 1 N := by
    intro h
    have : 2 ∈ insert N (insert 1 (∅ : Finset ℕ)) := h ▸ (by simp; omega)
    simp at this; omega
  rw [euler_step N _ hne]
  have hb : blocks N (linkOf P) (insert N (insert 1 (∅ : Finset ℕ))) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro B hB
    obtain ⟨hsub, ⟨m, hm⟩, hR⟩ := (mem_blocks N _).1 hB
    have hm' := hsub hm
    simp only [mem_sdiff, mem_Icc, mem_insert, notMem_empty, or_false] at hm'
    exact hmid m (by simp; omega) (by simpa using hR m hm)
  rw [hb, sum_empty, neg_zero]

theorem not_balF_ends {N m : ℕ} (he : N % 2 = 0) (hm : m ∈ Icc 2 (N - 1)) :
    ¬BalF N {N, 1} m := by
  rw [mem_Icc] at hm
  unfold BalF
  rcases Nat.lt_or_ge (m - 1) (N - m) with h | h
  · have hr : reach N m = m - 1 := by unfold reach; omega
    have e1 : ({N, 1} : Finset ℕ).filter (fun x => m - reach N m ≤ x ∧ x < m) = {1} := by
      ext x; simp only [mem_filter, mem_insert, mem_singleton, hr]; omega
    have e2 : ({N, 1} : Finset ℕ).filter (fun x => m < x ∧ x ≤ m + reach N m) = ∅ := by
      ext x; simp only [mem_filter, mem_insert, mem_singleton, hr, notMem_empty]; omega
    rw [e1, e2]; simp
  · have hr : reach N m = N - m := by unfold reach; omega
    have e1 : ({N, 1} : Finset ℕ).filter (fun x => m - reach N m ≤ x ∧ x < m) = ∅ := by
      ext x; simp only [mem_filter, mem_insert, mem_singleton, hr, notMem_empty]; omega
    have e2 : ({N, 1} : Finset ℕ).filter (fun x => m < x ∧ x ≤ m + reach N m) = {N} := by
      ext x; simp only [mem_filter, mem_insert, mem_singleton, hr]; omega
    rw [e1, e2]; simp

/-- **Euler characteristic of convention (a).**  For even `N ≥ 4`,
`∑_k (-1)^k W_a(N, k) = 0`; equivalently `(q + 1)` divides `A_N(q) = ∑_k W_a(N, k) C(q, k)`. -/
theorem euler_A_even {N : ℕ} (hN : 4 ≤ N) (he : N % 2 = 0) :
    ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * (W N (linkA N) k : ℤ) = 0 :=
  euler_linkOf_eq_zero (by omega) (BalF N) (balF_one N) (balF_last N)
    fun _ hm => not_balF_ends he hm

theorem symF_of_reach_zero {N m : ℕ} (h : reach N m = 0) (S : Finset ℕ) : SymF N S m := by
  intro d hd
  rw [h] at hd
  simp at hd

theorem not_symF_ends {N m : ℕ} (he : N % 2 = 0) (hm : m ∈ Icc 2 (N - 1)) :
    ¬SymF N {N, 1} m := by
  rw [mem_Icc] at hm
  intro h
  have hr : 1 ≤ reach N m := by unfold reach; omega
  have := h (reach N m) (mem_Icc.2 ⟨hr, le_rfl⟩)
  simp only [mem_insert, mem_singleton] at this
  unfold reach at this hr
  omega

/-- The same vanishing in the symmetric (3-AP-free) case. -/
theorem euler_symA_even {N : ℕ} (hN : 4 ≤ N) (he : N % 2 = 0) :
    ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * (W N (linkSymA N) k : ℤ) = 0 :=
  euler_linkOf_eq_zero (by omega) (SymF N) (fun S => symF_of_reach_zero (by simp [reach]) S)
    (fun S => symF_of_reach_zero (by simp [reach]) S) fun _ hm => not_symF_ends he hm

end XdWeak
end Folds
