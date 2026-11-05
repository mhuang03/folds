import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Folds.Counting

/-!
# Growth of `a(N)`: splits and the branching (tree) bound

## Splits (lower bounds)

A *window embedding* `φ : [1..p] → [1..N]` (`WinEmb`) maps the window arms of every
`j` in the `p`-strip exactly onto the window arms of `φ j` in the `N`-strip, restricted
to the image of `φ`.  A *split* (`Split`) of `[1..N]` is a pair of window embeddings
`φ : [1..p] → [1..N]`, `ψ : [1..q] → [1..N]` with complementary images such that each
image, once complete, is balanced around every point of the other image.

* `Split.semiSymmetric_iff`: `σ.map φ ++ τ.map ψ` is semi-symmetric iff `σ` and `τ` are.
* `Split.card_le`: `2 · a(p) · a(q) ≤ a(N)` (both block orders).

The parity blocks of `Blocks.lean` are the split `p = ⌊N/2⌋`, `q = ⌈N/2⌉`.  New
instances:

* `threeSplit`: `N = 3n`, `φ y = 3y - 1` (panels `≡ 2 mod 3`, an `n`-strip) and
  `ψ y = y + ⌊y/2⌋` (panels `≡ 0, 1 mod 3`, a `2n`-strip).  Hence
  `semiCount_three : 2 · a(n) · a(2n) ≤ a(3n)`.
* `fiveSplit`: `N = 5n`, panels `≡ 2, 4 mod 5` (a `2n`-strip) and `≡ 0, 1, 3 mod 5`
  (a `3n`-strip).  Hence `semiCount_five : 2 · a(2n) · a(3n) ≤ a(5n)`.

(In general the panels with residue in `{2, 4, …, 2j}` mod `2j+1` form a split of
`[1..(2j+1)n]`; see `experiments/growth/PROOFS.txt`.)

## The branching bound (upper bounds)

`prefixes N k` is the `Finset` of valid prefixes of length `k` (built step by step).
`semiCount_le_prod`: if every valid prefix of length `i < N` has at most `B i` valid
next panels, then `a(N) ≤ ∏_{i<N} B i`.
-/

namespace Folds

/-! ## Window embeddings -/

/-- `φ` embeds the strip `[1..p]` into `[1..N]` so that, restricted to the image of `φ`,
the left (right) window arm of `φ j` is the image of the left (right) arm of `j`. -/
structure WinEmb (N p : Nat) (φ : Nat → Nat) : Prop where
  bound : ∀ y, 1 ≤ y → y ≤ p → 1 ≤ φ y ∧ φ y ≤ N
  inj : ∀ x y, 1 ≤ x → x ≤ p → 1 ≤ y → y ≤ p → φ x = φ y → x = y
  left : ∀ j y, 1 ≤ j → j ≤ p → 1 ≤ y → y ≤ p →
    ((φ j - reach N (φ j) ≤ φ y ∧ φ y < φ j) ↔ (j - reach p j ≤ y ∧ y < j))
  right : ∀ j y, 1 ≤ j → j ≤ p → 1 ≤ y → y ≤ p →
    ((φ j < φ y ∧ φ y ≤ φ j + reach N (φ j)) ↔ (j < y ∧ y ≤ j + reach p j))

/-- `U` has as many elements in the left window arm of `m` as in the right one. -/
def Balanced (N : Nat) (U : List Nat) (m : Nat) : Prop :=
  U.countP (fun x => decide (m - reach N m ≤ x ∧ x < m)) =
    U.countP (fun x => decide (m < x ∧ x ≤ m + reach N m))

theorem balanced_nil (N m : Nat) : Balanced N [] m := by simp [Balanced]

theorem Balanced.perm {N m : Nat} {U V : List Nat} (h : Balanced N U m) (e : U.Perm V) :
    Balanced N V m := by
  unfold Balanced at *; rw [← e.countP_eq, ← e.countP_eq]; exact h

/-- Transfer of a single step through a window embedding, with a balanced background. -/
theorem WinEmb.semiStep_iff {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ)
    {U T : List Nat} {j : Nat} (hnd : (U ++ T.map φ).Nodup)
    (hT : ∀ y ∈ T, 1 ≤ y ∧ y ≤ p) (hj1 : 1 ≤ j) (hjp : j ≤ p) (hU : Balanced N U (φ j)) :
    SemiStep N (U ++ T.map φ) (φ j) ↔ SemiStep p T j := by
  have hndT : T.Nodup := (List.nodup_append.1 hnd).2.1.of_map φ
  unfold SemiStep
  rw [leftCount_eq hnd, rightCount_eq hnd, leftCount_eq hndT, rightCount_eq hndT,
    List.countP_append, List.countP_append, List.countP_map, List.countP_map]
  have L : T.countP ((fun x => decide (φ j - reach N (φ j) ≤ x ∧ x < φ j)) ∘ φ) =
      T.countP (fun y => decide (j - reach p j ≤ y ∧ y < j)) := by
    apply List.countP_congr; intro y hy; have := hT y hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    exact hφ.left j y hj1 hjp this.1 this.2
  have R : T.countP ((fun x => decide (φ j < x ∧ x ≤ φ j + reach N (φ j))) ∘ φ) =
      T.countP (fun y => decide (j < y ∧ y ≤ j + reach p j)) := by
    apply List.countP_congr; intro y hy; have := hT y hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    exact hφ.right j y hj1 hjp this.1 this.2
  unfold Balanced at hU
  rw [L, R]; omega

theorem WinEmb.nodup_map {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ) {σ : List Nat}
    (hnd : σ.Nodup) (hσ : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ p) : (σ.map φ).Nodup :=
  nodup_map_of_injOn hnd fun x hx y hy e =>
    hφ.inj x y (hσ x hx).1 (hσ x hx).2 (hσ y hy).1 (hσ y hy).2 e

theorem WinEmb.map_inj {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ) :
    ∀ {σ σ' : List Nat}, (∀ y ∈ σ, 1 ≤ y ∧ y ≤ p) → (∀ y ∈ σ', 1 ≤ y ∧ y ≤ p) →
      σ.map φ = σ'.map φ → σ = σ'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, e => by simp at e
  | _ :: _, [], _, _, e => by simp at e
  | x :: s, x' :: s', h, h', e => by
    simp only [List.map_cons, List.cons.injEq] at e
    have hx := h x (by simp); have hx' := h' x' (by simp)
    rw [hφ.inj x x' hx.1 hx.2 hx'.1 hx'.2 e.1,
      hφ.map_inj (fun y hy => h y (by simp [hy])) (fun y hy => h' y (by simp [hy])) e.2]

/-- A single embedded block on an empty strip. -/
theorem WinEmb.semiSymmetric_iff {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ)
    {σ : List Nat} (hnd : σ.Nodup) (hσ : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ p) :
    SemiSymmetric N (σ.map φ) ↔ SemiSymmetric p σ := by
  have hndm := hφ.nodup_map hnd hσ
  constructor
  · intro h k hk
    have := h k (by simpa using hk)
    rw [List.getElem_map, ← List.map_take, ← List.nil_append (List.map _ _)] at this
    have hm := hσ _ (List.getElem_mem hk)
    refine (hφ.semiStep_iff ?_ (fun y hy => hσ y (List.mem_of_mem_take hy))
      hm.1 hm.2 (balanced_nil _ _)).1 this
    simpa [List.map_take] using take_nodup hndm k
  · intro h k hk
    simp only [List.length_map] at hk
    rw [List.getElem_map, ← List.map_take, ← List.nil_append (List.map _ _)]
    have hm := hσ _ (List.getElem_mem hk)
    refine (hφ.semiStep_iff ?_ (fun y hy => hσ y (List.mem_of_mem_take hy))
      hm.1 hm.2 (balanced_nil _ _)).2 (h k hk)
    simpa [List.map_take] using take_nodup hndm k

/-! ## Splits -/

/-- A split of `[1..N]` into an embedded `p`-strip and an embedded `q`-strip, each
balanced (when complete) around every point of the other. -/
structure Split (N p q : Nat) (φ ψ : Nat → Nat) : Prop where
  emb₁ : WinEmb N p φ
  emb₂ : WinEmb N q ψ
  cover : ((List.range' 1 p).map φ ++ (List.range' 1 q).map ψ).Perm (List.range' 1 N)
  bal₁ : ∀ j, 1 ≤ j → j ≤ q → Balanced N ((List.range' 1 p).map φ) (ψ j)
  bal₂ : ∀ j, 1 ≤ j → j ≤ p → Balanced N ((List.range' 1 q).map ψ) (φ j)

theorem Split.symm {N p q : Nat} {φ ψ : Nat → Nat} (h : Split N p q φ ψ) :
    Split N q p ψ φ :=
  ⟨h.emb₂, h.emb₁, List.perm_append_comm.trans h.cover, h.bal₂, h.bal₁⟩

theorem Split.isFoldSeq {N p q : Nat} {φ ψ : Nat → Nat} (h : Split N p q φ ψ)
    {σ τ : List Nat} (hσ : IsFoldSeq p σ) (hτ : IsFoldSeq q τ) :
    IsFoldSeq N (σ.map φ ++ τ.map ψ) :=
  ((hσ.map φ).append (hτ.map ψ)).trans h.cover

/-- **Split blocks.**  `σ.map φ ++ τ.map ψ` is semi-symmetric iff `σ` and `τ` are. -/
theorem Split.semiSymmetric_iff {N p q : Nat} {φ ψ : Nat → Nat} (h : Split N p q φ ψ)
    {σ τ : List Nat} (hσ : IsFoldSeq p σ) (hτ : IsFoldSeq q τ) :
    SemiSymmetric N (σ.map φ ++ τ.map ψ) ↔ SemiSymmetric p σ ∧ SemiSymmetric q τ := by
  have hall := nodup_of_foldSeq (h.isFoldSeq hσ hτ)
  have bσ : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ p := fun y hy => (mem_range'_of_perm hσ).1 hy
  have bτ : ∀ y ∈ τ, 1 ≤ y ∧ y ≤ q := fun y hy => (mem_range'_of_perm hτ).1 hy
  rw [semiSymmetric_append_iff, h.emb₁.semiSymmetric_iff (nodup_of_foldSeq hσ) bσ]
  apply and_congr Iff.rfl
  have step : ∀ k (hk : k < τ.length),
      SemiStep N (σ.map φ ++ (τ.map ψ).take k) ((τ.map ψ)[k]'(by simpa using hk)) ↔
        SemiStep q (τ.take k) τ[k] := by
    intro k hk
    rw [List.getElem_map, ← List.map_take]
    have hm := bτ _ (List.getElem_mem hk)
    refine h.emb₂.semiStep_iff ?_ (fun y hy => bτ y (List.mem_of_mem_take hy)) hm.1 hm.2 ?_
    · have := take_nodup hall ((σ.map φ).length + k)
      rw [List.take_length_add_append] at this; rwa [List.map_take]
    · exact (h.bal₁ _ hm.1 hm.2).perm (hσ.map φ).symm
  constructor
  · intro h' k hk; exact (step k hk).1 (h' k (by simpa using hk))
  · intro h' k hk
    simp only [List.length_map] at hk
    exact (step k hk).2 (h' k hk)

/-- The block map `(σ, τ) ↦ σ.map φ ++ τ.map ψ`. -/
def splitMap (φ ψ : Nat → Nat) (x : List Nat × List Nat) : List Nat :=
  x.1.map φ ++ x.2.map ψ

theorem Split.splitMap_mem {N p q : Nat} {φ ψ : Nat → Nat} (h : Split N p q φ ψ)
    {x : List Nat × List Nat} (hx : x ∈ semiSeqs p ×ˢ semiSeqs q) :
    splitMap φ ψ x ∈ semiSeqs N := by
  rw [Finset.mem_product, mem_semiSeqs, mem_semiSeqs] at hx
  rw [mem_semiSeqs]
  exact ⟨h.isFoldSeq hx.1.1 hx.2.1, (h.semiSymmetric_iff hx.1.1 hx.2.1).2 ⟨hx.1.2, hx.2.2⟩⟩

theorem Split.injOn {N p q : Nat} {φ ψ : Nat → Nat} (h : Split N p q φ ψ) :
    Set.InjOn (splitMap φ ψ) (semiSeqs p ×ˢ semiSeqs q : Finset _) := by
  rintro ⟨σ, τ⟩ hx ⟨σ', τ'⟩ hx' e
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_semiSeqs] at hx hx'
  have l1 : (σ.map φ).length = (σ'.map φ).length := by
    simp [hx.1.1.length_eq, hx'.1.1.length_eq]
  obtain ⟨e1, e2⟩ := List.append_inj e l1
  simp only at e1 e2
  rw [h.emb₁.map_inj (fun y hy => (mem_range'_of_perm hx.1.1).1 hy)
      (fun y hy => (mem_range'_of_perm hx'.1.1).1 hy) e1,
    h.emb₂.map_inj (fun y hy => (mem_range'_of_perm hx.2.1).1 hy)
      (fun y hy => (mem_range'_of_perm hx'.2.1).1 hy) e2]

theorem Split.disjoint_images {N p q : Nat} {φ ψ : Nat → Nat} (h : Split N p q φ ψ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Disjoint ((semiSeqs p ×ˢ semiSeqs q).image (splitMap φ ψ))
      ((semiSeqs q ×ˢ semiSeqs p).image (splitMap ψ φ)) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  simp only [Finset.mem_image, Finset.mem_product, mem_semiSeqs] at hx hx'
  obtain ⟨⟨σ, τ⟩, ⟨⟨hσ, -⟩, -⟩, rfl⟩ := hx
  obtain ⟨⟨τ', σ'⟩, ⟨⟨hτ', -⟩, -⟩, e⟩ := hx'
  have l : σ.length = p := by rw [hσ.length_eq]; simp
  have l' : τ'.length = q := by rw [hτ'.length_eq]; simp
  obtain ⟨y, s, rfl⟩ : ∃ y s, σ = y :: s := by
    cases σ with
    | nil => simp at l; omega
    | cons y s => exact ⟨y, s, rfl⟩
  obtain ⟨y', s', rfl⟩ : ∃ y s, τ' = y :: s := by
    cases τ' with
    | nil => simp at l'; omega
    | cons y s => exact ⟨y, s, rfl⟩
  have hy := (mem_range'_of_perm hσ).1 (List.mem_cons_self ..)
  have hy' := (mem_range'_of_perm hτ').1 (List.mem_cons_self ..)
  simp only [splitMap, List.map_cons, List.cons_append, List.cons.injEq] at e
  have hnd := (List.nodup_append.1 (h.cover.nodup_iff.2 (List.nodup_range' ..))).2.2
  exact hnd (φ y) (List.mem_map.2 ⟨y, List.mem_range'_1.2 (by omega), rfl⟩)
    (ψ y') (List.mem_map.2 ⟨y', List.mem_range'_1.2 (by omega), rfl⟩) e.1.symm

/-- **Split lower bound.**  `2 · a(p) · a(q) ≤ a(N)` for a split with `p, q ≥ 1`. -/
theorem Split.card_le {N p q : Nat} {φ ψ : Nat → Nat} (h : Split N p q φ ψ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) : 2 * (semiCount p * semiCount q) ≤ semiCount N := by
  have c1 := Finset.card_image_of_injOn h.injOn
  have c2 := Finset.card_image_of_injOn h.symm.injOn
  have hsub : (semiSeqs p ×ˢ semiSeqs q).image (splitMap φ ψ) ∪
      (semiSeqs q ×ˢ semiSeqs p).image (splitMap ψ φ) ⊆ semiSeqs N := by
    apply Finset.union_subset <;> intro x hx <;> rw [Finset.mem_image] at hx <;>
      obtain ⟨y, hy, rfl⟩ := hx
    · exact h.splitMap_mem hy
    · exact h.symm.splitMap_mem hy
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (h.disjoint_images hp hq), c1, c2,
    Finset.card_product, Finset.card_product] at this
  unfold semiCount
  rw [Nat.mul_comm (semiSeqs q).card] at this
  omega

/-! ## Doubling sets

A *doubling set* is the image of a strictly increasing `φ : [1..p] → [1..N]` whose
counting function `c(x) = #{y ≥ 1 : φ y ≤ x}` satisfies

* `c(2x + 1) = c(x) + c(x + 1)` (the doubling identity), and
* `c(x) + c(N - x) = p` (mirror symmetry).

Then `φ` is a window embedding and its image is balanced around *every* panel.  Two
doubling sets with `c + d = id` form a split. -/

structure DoublingSet (N p : Nat) (φ c : Nat → Nat) : Prop where
  gal : ∀ y t, 1 ≤ y → (φ y ≤ t ↔ y ≤ c t)
  mono : ∀ y, 1 ≤ y → φ y < φ (y + 1)
  zero : c 0 = 0
  double : ∀ x, c (2 * x + 1) = c x + c (x + 1)
  mirror : ∀ x, x ≤ N → c x + c (N - x) = p

namespace DoublingSet

variable {N p : Nat} {φ c : Nat → Nat}

theorem c_N (h : DoublingSet N p φ c) : c N = p := by
  have := h.mirror 0 (Nat.zero_le _); rw [h.zero, Nat.sub_zero] at this; omega

theorem c_mono (h : DoublingSet N p φ c) {x x' : Nat} (hx : x ≤ x') : c x ≤ c x' := by
  rcases Nat.eq_zero_or_pos (c x) with h0 | hpos
  · omega
  · have := (h.gal (c x) x hpos).2 le_rfl
    exact (h.gal (c x) x' hpos).1 (by omega)

theorem phi_pos (h : DoublingSet N p φ c) {y : Nat} (hy : 1 ≤ y) : 1 ≤ φ y := by
  refine Decidable.byContradiction fun hc => ?_
  have := (h.gal y 0 hy).1 (by omega)
  rw [h.zero] at this; omega

theorem phi_le (h : DoublingSet N p φ c) {y : Nat} (hy1 : 1 ≤ y) (hyp : y ≤ p) : φ y ≤ N :=
  (h.gal y N hy1).2 (by rw [h.c_N]; exact hyp)

theorem c_phi (h : DoublingSet N p φ c) {j : Nat} (hj : 1 ≤ j) : c (φ j) = j := by
  have a := (h.gal j (φ j) hj).1 le_rfl
  have b := h.gal (j + 1) (φ j) (by omega)
  have := h.mono j hj
  refine Decidable.byContradiction fun hne => ?_
  have := b.2 (by omega); omega

theorem c_phi_pred (h : DoublingSet N p φ c) {j : Nat} (hj : 1 ≤ j) :
    c (φ j - 1) = j - 1 := by
  have p1 := h.phi_pos hj
  have a := h.gal j (φ j - 1) hj
  have lt : c (φ j - 1) < j := by
    refine Decidable.byContradiction fun hh => ?_
    have := a.2 (by omega); omega
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · omega
  · have b := (h.gal (j - 1) (φ j - 1) (by omega)).1
    have := h.mono (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at this
    have := b (by omega); omega

theorem c_double' (h : DoublingSet N p φ c) {m : Nat} (hm : 1 ≤ m) :
    c (2 * m - 1) = c (m - 1) + c m := by
  have := h.double (m - 1)
  rwa [show 2 * (m - 1) + 1 = 2 * m - 1 by omega, show m - 1 + 1 = m by omega] at this

theorem c_right (h : DoublingSet N p φ c) {m : Nat} (hm1 : 1 ≤ m) (hmN : m ≤ N)
    (hr : N ≤ 2 * m - 1) : c (2 * m - N - 1) + p = c (m - 1) + c m := by
  have e1 := h.mirror (2 * m - N - 1) (by omega)
  rw [show N - (2 * m - N - 1) = 2 * (N - m) + 1 by omega, h.double] at e1
  have e2 := h.mirror m hmN
  have e3 := h.mirror (m - 1) (by omega)
  rw [show N - (m - 1) = N - m + 1 by omega] at e3
  omega

/-- A doubling set is a window embedding. -/
theorem winEmb (h : DoublingSet N p φ c) : WinEmb N p φ := by
  refine ⟨fun y h1 h2 => ⟨h.phi_pos h1, h.phi_le h1 h2⟩, fun x y hx1 _ hy1 _ e => ?_, ?_, ?_⟩
  · have a := h.c_phi hx1; have b := h.c_phi hy1; rw [e] at a; omega
  · intro j y hj1 hjp hy1 hyp
    have hm1 := h.phi_pos hj1; have hmN := h.phi_le hj1 hjp
    have cm := h.c_phi hj1; have cm1 := h.c_phi_pred hj1
    have a := h.gal y (φ j - 1) hy1
    have b := h.gal y (φ j - reach N (φ j) - 1) hy1
    rcases Nat.le_total (φ j - 1) (N - φ j) with hle | hle
    · have hr' : reach N (φ j) = φ j - 1 := by unfold reach; omega
      rw [hr'] at b ⊢; rw [show φ j - (φ j - 1) - 1 = 0 by omega, h.zero] at b
      have d := h.c_double' hm1
      have bd := h.c_mono (show 2 * φ j - 1 ≤ N by omega); rw [h.c_N] at bd
      have hrp : reach p j = j - 1 := by unfold reach; omega
      rw [hrp]; omega
    · have hr' : reach N (φ j) = N - φ j := by unfold reach; omega
      rw [hr'] at b ⊢
      rw [show φ j - (N - φ j) - 1 = 2 * φ j - N - 1 by omega] at b
      have d := h.c_right hm1 hmN (by omega)
      have hrp : reach p j = p - j := by unfold reach; omega
      rw [hrp]; omega
  · intro j y hj1 hjp hy1 hyp
    have hm1 := h.phi_pos hj1; have hmN := h.phi_le hj1 hjp
    have cm := h.c_phi hj1; have cm1 := h.c_phi_pred hj1
    have a := h.gal y (φ j) hy1
    have b := h.gal y (φ j + reach N (φ j)) hy1
    rcases Nat.le_total (φ j - 1) (N - φ j) with hle | hle
    · have hr' : reach N (φ j) = φ j - 1 := by unfold reach; omega
      rw [hr'] at b ⊢; rw [show φ j + (φ j - 1) = 2 * φ j - 1 by omega, h.c_double' hm1] at b
      have bd := h.c_mono (show 2 * φ j - 1 ≤ N by omega)
      rw [h.c_N, h.c_double' hm1] at bd
      have hrp : reach p j = j - 1 := by unfold reach; omega
      rw [hrp]; omega
    · have hr' : reach N (φ j) = N - φ j := by unfold reach; omega
      rw [hr'] at b ⊢
      rw [show φ j + (N - φ j) = N by omega, h.c_N] at b
      have d := h.c_right hm1 hmN (by omega)
      have hrp : reach p j = p - j := by unfold reach; omega
      rw [hrp]; omega

/-- A complete doubling set is balanced around every panel. -/
theorem balanced (h : DoublingSet N p φ c) {m : Nat} (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    Balanced N ((List.range' 1 p).map φ) m := by
  unfold Balanced
  rw [List.countP_map, List.countP_map]
  have hr : reach N m ≤ m - 1 := by unfold reach; omega
  have L : (List.range' 1 p).countP ((fun x => decide (m - reach N m ≤ x ∧ x < m)) ∘ φ) =
      (List.range' 1 p).countP
        (fun y => decide (c (m - reach N m - 1) + 1 ≤ y ∧ y ≤ c (m - 1))) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    have a := h.gal y (m - 1) hy.1
    have b := h.gal y (m - reach N m - 1) hy.1
    omega
  have R : (List.range' 1 p).countP
        ((fun x => decide (m < x ∧ x ≤ m + reach N m)) ∘ φ) =
      (List.range' 1 p).countP
        (fun y => decide (c m + 1 ≤ y ∧ y ≤ c (m + reach N m))) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    have a := h.gal y m hy.1
    have b := h.gal y (m + reach N m) hy.1
    omega
  rw [L, R, countP_range'_interval, countP_range'_interval]
  have b0 := h.c_mono (show m - 1 ≤ m by omega)
  have b1 := h.c_mono hmN; rw [h.c_N] at b1
  rcases Nat.le_total (m - 1) (N - m) with hle | hle
  · have hr' : reach N m = m - 1 := by unfold reach; omega
    rw [hr', show m - (m - 1) - 1 = 0 by omega, show m + (m - 1) = 2 * m - 1 by omega,
      h.zero]
    have b2 := h.c_mono (show 2 * m - 1 ≤ N by omega); rw [h.c_N] at b2
    rw [h.c_double' hm1] at b2 ⊢
    omega
  · have hr' : reach N m = N - m := by unfold reach; omega
    rw [hr', show m - (N - m) - 1 = 2 * m - N - 1 by omega, show m + (N - m) = N by omega,
      h.c_N]
    have := h.c_right hm1 hmN (by omega)
    omega

end DoublingSet

/-- Two doubling sets with complementary counting functions form a split. -/
theorem split_of_doubling {N p q : Nat} {φ ψ c d : Nat → Nat}
    (h1 : DoublingSet N p φ c) (h2 : DoublingSet N q ψ d) (hcd : ∀ x, c x + d x = x) :
    Split N p q φ ψ := by
  refine ⟨h1.winEmb, h2.winEmb, ?_, fun j hj1 hj2 => h1.balanced (h2.phi_pos hj1)
    (h2.phi_le hj1 hj2), fun j hj1 hj2 => h2.balanced (h1.phi_pos hj1) (h1.phi_le hj1 hj2)⟩
  rw [List.perm_ext_iff_of_nodup _ (List.nodup_range' ..)]
  · intro x
    simp only [List.mem_append, List.mem_map, List.mem_range'_1]
    constructor
    · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
      · have := h1.phi_pos (y := y) (by omega); have := h1.phi_le (y := y) (by omega) (by omega)
        omega
      · have := h2.phi_pos (y := y) (by omega); have := h2.phi_le (y := y) (by omega) (by omega)
        omega
    · intro hx
      have e1 := hcd x; have e2 := hcd (x - 1)
      have m1 := h1.c_mono (show x - 1 ≤ x by omega)
      have m2 := h2.c_mono (show x - 1 ≤ x by omega)
      have b1 := h1.c_mono (show x ≤ N by omega); rw [h1.c_N] at b1
      have b2 := h2.c_mono (show x ≤ N by omega); rw [h2.c_N] at b2
      by_cases hc : c x = c (x - 1) + 1
      · refine Or.inl ⟨c x, by omega, ?_⟩
        have u := (h1.gal (c x) x (by omega)).2 le_rfl
        have v := h1.gal (c x) (x - 1) (by omega)
        omega
      · refine Or.inr ⟨d x, by omega, ?_⟩
        have u := (h2.gal (d x) x (by omega)).2 le_rfl
        have v := h2.gal (d x) (x - 1) (by omega)
        omega
  · refine List.nodup_append.2 ⟨h1.winEmb.nodup_map (List.nodup_range' ..)
      (fun y hy => by rw [List.mem_range'_1] at hy; omega),
      h2.winEmb.nodup_map (List.nodup_range' ..)
      (fun y hy => by rw [List.mem_range'_1] at hy; omega), ?_⟩
    intro x hx y hy e
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
    rw [List.mem_range'_1] at ha hb
    have c1 := h1.c_phi (j := a) (by omega); have c2 := h1.c_phi_pred (j := a) (by omega)
    have d1 := h2.c_phi (j := b) (by omega); have d2 := h2.c_phi_pred (j := b) (by omega)
    have := h1.phi_pos (y := a) (by omega)
    have f1 := hcd (φ a); have f2 := hcd (φ a - 1)
    rw [e] at c1 c2 f1 f2 this
    omega

/-! ## Instances: residues `{2, 4, …, 2j}` modulo `q = 2j + 1`

For `N = qn` the panels with residue in `{2, 4, …, 2j}` mod `q` form a doubling set of
size `jn`, with counting function `c(x) = j⌊x/q⌋ + ⌊(x mod q)/2⌋`, and the remaining
panels (residues `{0, 1, 3, …, 2j - 1}`) one of size `(j+1)n`.  We instantiate
`q = 3, 5, 7`. -/

/-- Panels `≡ 2 (mod 3)`: `y ↦ 3y - 1`. -/
def third (y : Nat) : Nat := 3 * y - 1

/-- Panels `≡ 0, 1 (mod 3)`: `2i - 1 ↦ 3i - 2`, `2i ↦ 3i`. -/
def twoThirds (y : Nat) : Nat := y + y / 2

theorem doubling_third (n : Nat) : DoublingSet (3 * n) n third (fun x => (x + 1) / 3) :=
  ⟨fun _ _ _ => by unfold third; omega, fun _ _ => by unfold third; omega, rfl,
    fun x => by
      rcases (by omega : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2) with h | h | h <;> omega,
    fun _ _ => by omega⟩

theorem doubling_twoThirds (n : Nat) :
    DoublingSet (3 * n) (2 * n) twoThirds (fun x => (2 * x + 1) / 3) :=
  ⟨fun _ _ _ => by unfold twoThirds; omega, fun _ _ => by unfold twoThirds; omega, rfl,
    fun x => by
      rcases (by omega : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2) with h | h | h <;> omega,
    fun _ _ => by omega⟩

theorem threeSplit (n : Nat) : Split (3 * n) n (2 * n) third twoThirds :=
  split_of_doubling (doubling_third n) (doubling_twoThirds n) fun _ => by omega

/-- **Mod-3 split lower bound.**  `2 · a(n) · a(2n) ≤ a(3n)`. -/
theorem semiCount_three {n : Nat} (hn : 1 ≤ n) :
    2 * (semiCount n * semiCount (2 * n)) ≤ semiCount (3 * n) :=
  (threeSplit n).card_le hn (by omega)

/-- Panels `≡ 2, 4 (mod 5)`. -/
def twoFifths (y : Nat) : Nat := 5 * ((y - 1) / 2) + 2 * ((y - 1) % 2) + 2

/-- Panels `≡ 0, 1, 3 (mod 5)`. -/
def threeFifths (y : Nat) : Nat := 5 * ((y - 1) / 3) + 2 * ((y - 1) % 3) + 1

theorem doubling_twoFifths (n : Nat) :
    DoublingSet (5 * n) (2 * n) twoFifths (fun x => 2 * (x / 5) + x % 5 / 2) :=
  ⟨fun _ _ _ => by unfold twoFifths; omega, fun _ _ => by unfold twoFifths; omega, rfl,
    fun x => by
      rcases (by omega : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨
        x % 5 = 3 ∨ x % 5 = 4) with h | h | h | h | h <;> omega,
    fun _ _ => by omega⟩

theorem doubling_threeFifths (n : Nat) :
    DoublingSet (5 * n) (3 * n) threeFifths (fun x => 3 * (x / 5) + (x % 5 + 1) / 2) :=
  ⟨fun _ _ _ => by unfold threeFifths; omega, fun _ _ => by unfold threeFifths; omega, rfl,
    fun x => by
      rcases (by omega : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨
        x % 5 = 3 ∨ x % 5 = 4) with h | h | h | h | h <;> omega,
    fun _ _ => by omega⟩

/-- **Mod-5 split lower bound.**  `2 · a(2n) · a(3n) ≤ a(5n)`. -/
theorem semiCount_five {n : Nat} (hn : 1 ≤ n) :
    2 * (semiCount (2 * n) * semiCount (3 * n)) ≤ semiCount (5 * n) :=
  (split_of_doubling (doubling_twoFifths n) (doubling_threeFifths n)
    fun _ => by omega).card_le (by omega) (by omega)

/-- Panels `≡ 2, 4, 6 (mod 7)`. -/
def threeSevenths (y : Nat) : Nat := 7 * ((y - 1) / 3) + 2 * ((y - 1) % 3) + 2

/-- Panels `≡ 0, 1, 3, 5 (mod 7)`. -/
def fourSevenths (y : Nat) : Nat := 7 * ((y - 1) / 4) + 2 * ((y - 1) % 4) + 1

theorem doubling_threeSevenths (n : Nat) :
    DoublingSet (7 * n) (3 * n) threeSevenths (fun x => 3 * (x / 7) + x % 7 / 2) :=
  ⟨fun _ _ _ => by unfold threeSevenths; omega, fun _ _ => by unfold threeSevenths; omega,
    rfl, fun x => by
      rcases (by omega : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨
        x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6) with h | h | h | h | h | h | h <;> omega,
    fun _ _ => by omega⟩

theorem doubling_fourSevenths (n : Nat) :
    DoublingSet (7 * n) (4 * n) fourSevenths (fun x => 4 * (x / 7) + (x % 7 + 1) / 2) :=
  ⟨fun _ _ _ => by unfold fourSevenths; omega, fun _ _ => by unfold fourSevenths; omega,
    rfl, fun x => by
      rcases (by omega : x % 7 = 0 ∨ x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨
        x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6) with h | h | h | h | h | h | h <;> omega,
    fun _ _ => by omega⟩

/-- **Mod-7 split lower bound.**  `2 · a(3n) · a(4n) ≤ a(7n)`. -/
theorem semiCount_seven {n : Nat} (hn : 1 ≤ n) :
    2 * (semiCount (3 * n) * semiCount (4 * n)) ≤ semiCount (7 * n) :=
  (split_of_doubling (doubling_threeSevenths n) (doubling_fourSevenths n)
    fun _ => by omega).card_le (by omega) (by omega)

/-! ## The branching bound

`a(N)` is the number of leaves at depth `N` of the tree of valid prefixes, so it is at
most the product over the levels of the maximal number of valid next panels. -/

/-- The valid next panels after the prefix `p`. -/
def moves (N : Nat) (p : List Nat) : Finset Nat :=
  (Finset.Icc 1 N).filter fun m => m ∉ p ∧ SemiStep N p m

/-- The valid prefixes of length `k`, built one step at a time. -/
def prefixes (N : Nat) : Nat → Finset (List Nat)
  | 0 => {[]}
  | k + 1 => (prefixes N k).biUnion fun p => (moves N p).image fun m => p ++ [m]

theorem mem_prefixes {N : Nat} : ∀ {k : Nat} {p : List Nat}, p ∈ prefixes N k →
    p.length = k ∧ p.Nodup ∧ (∀ x ∈ p, 1 ≤ x ∧ x ≤ N) ∧ SemiSymmetric N p
  | 0, p, hp => by
    simp only [prefixes, Finset.mem_singleton] at hp; subst hp
    exact ⟨rfl, List.nodup_nil, by simp, fun k hk => absurd hk (by simp)⟩
  | k + 1, p, hp => by
    simp only [prefixes, Finset.mem_biUnion, Finset.mem_image] at hp
    obtain ⟨q, hq, m, hm, rfl⟩ := hp
    obtain ⟨hl, hnd, hb, hs⟩ := mem_prefixes hq
    simp only [moves, Finset.mem_filter, Finset.mem_Icc] at hm
    refine ⟨by simp [hl], ?_, ?_, ?_⟩
    · exact List.nodup_append.2 ⟨hnd, List.nodup_singleton m,
        fun x hx y hy => by simp at hy; subst hy; exact fun e => hm.2.1 (e ▸ hx)⟩
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hb x hx
      · exact hm.1
    · rw [semiSymmetric_append_iff]
      refine ⟨hs, fun i hi => ?_⟩
      simp only [List.length_singleton] at hi
      obtain rfl : i = 0 := by omega
      simpa using hm.2.2

theorem take_mem_prefixes {N : Nat} {a : List Nat} (ha : a ∈ semiSeqs N) :
    ∀ k, k ≤ N → a.take k ∈ prefixes N k
  | 0, _ => by simp [prefixes]
  | k + 1, hk => by
    have ha' := mem_semiSeqs.1 ha
    have hlen : a.length = N := by rw [ha'.1.length_eq]; simp
    have hka : k < a.length := by omega
    rw [List.take_succ_eq_append_getElem hka]
    simp only [prefixes, Finset.mem_biUnion, Finset.mem_image]
    refine ⟨a.take k, take_mem_prefixes ha k (by omega), a[k], ?_, rfl⟩
    simp only [moves, Finset.mem_filter, Finset.mem_Icc]
    have hb := (mem_range'_of_perm ha'.1).1 (List.getElem_mem hka)
    refine ⟨hb, fun h => ?_, ha'.2 k hka⟩
    have := (getElem_mem_take_iff (nodup_of_foldSeq ha'.1) hka).1 h
    omega

theorem card_prefixes_le {N : Nat} (B : Nat → Nat)
    (hB : ∀ i p, i < N → p ∈ prefixes N i → (moves N p).card ≤ B i) :
    ∀ k, k ≤ N → (prefixes N k).card ≤ ∏ i ∈ Finset.range k, B i
  | 0, _ => by simp [prefixes]
  | k + 1, hk => by
    rw [Finset.prod_range_succ]
    calc (prefixes N (k + 1)).card
        ≤ ∑ p ∈ prefixes N k, ((moves N p).image fun m => p ++ [m]).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ prefixes N k, B k :=
          Finset.sum_le_sum fun p hp => Finset.card_image_le.trans (hB k p (by omega) hp)
      _ = (prefixes N k).card * B k := by rw [Finset.sum_const]; rfl
      _ ≤ (∏ i ∈ Finset.range k, B i) * B k :=
          Nat.mul_le_mul_right _ (card_prefixes_le B hB k (by omega))

/-- **Branching bound.**  If every valid prefix of length `i < N` has at most `B i` valid
next panels, then `a(N) ≤ ∏_{i < N} B i`. -/
theorem semiCount_le_prod (N : Nat) (B : Nat → Nat)
    (hB : ∀ p : List Nat, p.length < N → p.Nodup → (∀ x ∈ p, 1 ≤ x ∧ x ≤ N) →
      SemiSymmetric N p → (moves N p).card ≤ B p.length) :
    semiCount N ≤ ∏ i ∈ Finset.range N, B i := by
  have hsub : semiSeqs N ⊆ prefixes N N := by
    intro a ha
    have := take_mem_prefixes ha N le_rfl
    rw [mem_semiSeqs] at ha
    rwa [List.take_of_length_le (by rw [ha.1.length_eq]; simp)] at this
  refine (Finset.card_le_card hsub).trans (card_prefixes_le B (fun i p hi hp => ?_) N le_rfl)
  obtain ⟨hl, hnd, hb, hs⟩ := mem_prefixes hp
  subst hl
  exact hB p hi hnd hb hs

/-- At most `N - |p|` panels are left. -/
theorem card_moves_le {N : Nat} {p : List Nat} (hnd : p.Nodup)
    (hb : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N) : (moves N p).card ≤ N - p.length := by
  have hsub : moves N p ⊆ Finset.Icc 1 N \ p.toFinset := by
    intro m hm
    simp only [moves, Finset.mem_filter] at hm
    simp only [Finset.mem_sdiff, List.mem_toFinset]
    exact ⟨hm.1, hm.2.1⟩
  have hp : p.toFinset ⊆ Finset.Icc 1 N := by
    intro x hx; rw [List.mem_toFinset] at hx; rw [Finset.mem_Icc]; exact hb x hx
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_sdiff_of_subset hp, Nat.card_Icc, List.toFinset_card_of_nodup hnd]
  omega

/-- After one panel `x` has been bisected, a panel `m` is valid only if `x` lies outside
its window; there are at most `⌈N/2⌉` such panels. -/
theorem card_moves_singleton_le {N x : Nat} (hx : 1 ≤ x ∧ x ≤ N) :
    (moves N [x]).card ≤ (N + 1) / 2 := by
  have hsub : moves N [x] ⊆ Finset.Icc 1 (x / 2) ∪ Finset.Icc ((N + x) / 2 + 1) N := by
    intro m hm
    simp only [moves, Finset.mem_filter, Finset.mem_Icc, List.mem_singleton] at hm
    obtain ⟨⟨hm1, hmN⟩, hne, hs⟩ := hm
    unfold SemiStep at hs
    rw [leftCount_eq (List.nodup_singleton x), rightCount_eq (List.nodup_singleton x)] at hs
    simp only [List.countP_cons, List.countP_nil] at hs
    simp only [Finset.mem_union, Finset.mem_Icc]
    unfold reach at hs
    split at hs <;> split at hs <;> simp_all <;> omega
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  rw [Nat.card_Icc, Nat.card_Icc]
  omega

/-- **Branching bound, first step.**  `a(N) ≤ N · ⌈N/2⌉ · (N-2)!`, written as a product
over the levels of the tree: `N` choices at level 0, at most `⌈N/2⌉` at level 1, and at
most `N - i` at level `i ≥ 2`. -/
theorem semiCount_le_step_one (N : Nat) :
    semiCount N ≤ ∏ i ∈ Finset.range N, (if i = 1 then (N + 1) / 2 else N - i) := by
  apply semiCount_le_prod
  intro p hl hnd hb _
  split
  · next h1 =>
    match p, h1 with
    | [x], _ => exact card_moves_singleton_le (hb x (by simp))
  · exact card_moves_le hnd hb

end Folds
