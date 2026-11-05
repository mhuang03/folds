import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Folds.Counting

/-!
# Growth of `a(N)`: block constructions and branching bounds

## Lower bounds (block constructions)

A *window embedding* `φ : [1..p] → [1..N]` (`WinEmb`) maps the window arms of every
`j` in the `p`-strip exactly onto the window arms of `φ j` in the `N`-strip, restricted
to the image of `φ` (`WinEmb.semiStep_iff`: steps transfer when the rest is balanced).

* **Splits** (`Split`): two window embeddings with complementary images, each image
  (complete) balanced around every point of the other.  `Split.semiSymmetric_iff`,
  `Split.card_le : 2 · a(p) · a(q) ≤ a(N)`.
* **Doubling sets** (`DoublingSet`): the counting function `c` satisfies
  `c(2x+1) = c(x) + c(x+1)` and `c(x) + c(N-x) = p`.  Such a set is window-embedded
  (`DoublingSet.winEmb`) and balanced around every panel (`DoublingSet.balanced`); two
  complementary ones form a split (`split_of_doubling`).  Instances: residues
  `{2, …, 2j}` mod `2j+1`, giving
  `semiCount_three : 2 a(n) a(2n) ≤ a(3n)`, `semiCount_five : 2 a(2n) a(3n) ≤ a(5n)`,
  `semiCount_seven : 2 a(3n) a(4n) ≤ a(7n)`.
* **Composition** `semiCount_comp : a(q) · a(n)^q ≤ a(nq)`.  The residue classes mod `q`
  are copies of the `n`-strip (`winEmb_cls`), and a set `R` of complete classes is
  balanced around every panel of class `s` iff the step `(R, s)` is valid in the
  `q`-strip (`class_identity`, `classUnion_balanced`).  So the classes can be placed as
  blocks in the order of any valid sequence of the `q`-strip (`semiSymmetric_blocks`).
  `q = 2` is the parity-block theorem.

## Upper bounds (branching)

`prefixes N k` is the `Finset` of valid prefixes of length `k` and `moves N p` the
valid next panels.

* `semiCount_le_prod`: if every valid prefix of length `i < N` has at most `B i`
  valid next panels, then `a(N) ≤ ∏_{i<N} B i`.
* `card_moves_singleton_le`, `semiCount_le_step_one`: `a(N) ≤ N · ⌈N/2⌉ · (N-2)!`.
* `card_moves_odd_le` (`N = 2h`, `|S|` odd `⇒` at most `h` valid panels: the windows
  of `m` and `m + h` partition the strip) and
  `semiCount_even_le_prod : a(2h) ≤ ∏_{i<2h} (i odd ? min(2h-i, h) : 2h-i)`,
  i.e. `a(2h) ≤ (2h)! · (√e/2)^{h(1+o(1))}`.

See `experiments/growth/PROOFS.txt` for the paper proofs and the data.
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

/-! ## The parity bound for even `N`

For `N = 2h` and `1 ≤ m ≤ h` the windows of `m` and `m + h` are `[1, 2m-1]` and
`[2m, N]`: they partition the strip.  A valid step at `m ∉ S` needs `|S ∩ W_m|` even, so
if `|S|` is odd at most one panel of each pair `{m, m + h}` is valid: `V(S) ≤ N/2`. -/

/-- A valid step at `m ∉ S` sees an even number of bisected panels in its window. -/
theorem window_count_even {N m : Nat} {S : List Nat} (hnd : S.Nodup) (hmS : m ∉ S)
    (h : SemiStep N S m) :
    S.countP (fun x => decide (m - reach N m ≤ x ∧ x ≤ m + reach N m)) % 2 = 0 := by
  unfold SemiStep at h
  rw [leftCount_eq hnd, rightCount_eq hnd] at h
  have hsplit := countP_split S (fun x => decide (m - reach N m ≤ x ∧ x ≤ m + reach N m))
    (fun x => decide (x < m))
  have e1 : S.countP (fun x => decide (m - reach N m ≤ x ∧ x ≤ m + reach N m) &&
      decide (x < m)) = S.countP (fun x => decide (m - reach N m ≤ x ∧ x < m)) := by
    apply List.countP_congr; intro x _; simp; omega
  have e2 : S.countP (fun x => decide (m - reach N m ≤ x ∧ x ≤ m + reach N m) &&
      !decide (x < m)) = S.countP (fun x => decide (m < x ∧ x ≤ m + reach N m)) := by
    apply List.countP_congr; intro x hx
    have : x ≠ m := fun e => hmS (e ▸ hx)
    simp; omega
  omega

/-- For `N = 2h` and `|S|` odd, `m` and `m + h` are not both valid. -/
theorem not_both_valid {h m : Nat} {S : List Nat} (hnd : S.Nodup)
    (hb : ∀ x ∈ S, 1 ≤ x ∧ x ≤ 2 * h) (hodd : S.length % 2 = 1) (hm1 : 1 ≤ m) (hmh : m ≤ h)
    (h1 : m ∉ S ∧ SemiStep (2 * h) S m) (h2 : m + h ∉ S ∧ SemiStep (2 * h) S (m + h)) :
    False := by
  have c1 := window_count_even hnd h1.1 h1.2
  have c2 := window_count_even hnd h2.1 h2.2
  have r1 : reach (2 * h) m = m - 1 := by unfold reach; omega
  have r2 : reach (2 * h) (m + h) = h - m := by unfold reach; omega
  rw [r1] at c1; rw [r2] at c2
  have hsplit := countP_split S (fun _ => true) (fun x => decide (x ≤ 2 * m - 1))
  rw [List.countP_true] at hsplit
  have e1 : S.countP (fun x => true && decide (x ≤ 2 * m - 1)) =
      S.countP (fun x => decide (m - (m - 1) ≤ x ∧ x ≤ m + (m - 1))) := by
    apply List.countP_congr; intro x hx; have := hb x hx; simp; omega
  have e2 : S.countP (fun x => true && !decide (x ≤ 2 * m - 1)) =
      S.countP (fun x => decide (m + h - (h - m) ≤ x ∧ x ≤ m + h + (h - m))) := by
    apply List.countP_congr; intro x hx; have := hb x hx; simp; omega
  omega

/-- **Parity bound.**  For `N = 2h` and a prefix of odd length, at most `h` panels are
valid. -/
theorem card_moves_odd_le {h : Nat} {S : List Nat} (hnd : S.Nodup)
    (hb : ∀ x ∈ S, 1 ≤ x ∧ x ≤ 2 * h) (hodd : S.length % 2 = 1) :
    (moves (2 * h) S).card ≤ h := by
  have := Finset.card_le_card_of_injOn (s := moves (2 * h) S) (t := Finset.Icc 1 h)
    (fun m => if m ≤ h then m else m - h) ?_ ?_
  · simpa using this
  · intro m hm
    simp only [moves, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hm
    simp only [Finset.coe_Icc, Set.mem_Icc]
    split <;> omega
  · intro m hm m' hm' e
    simp only [moves, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hm hm'
    simp only at e
    split at e <;> split at e
    · exact e
    · exfalso
      obtain rfl : m' = m + h := by omega
      exact not_both_valid hnd hb hodd (by omega) (by omega) hm.2 hm'.2
    · exfalso
      obtain rfl : m = m' + h := by omega
      exact not_both_valid hnd hb hodd (by omega) (by omega) hm'.2 hm.2
    · omega

/-- **Parity upper bound for even `N`.**  At an odd level `i` of the tree at most
`min(2h - i, h)` panels are valid, so
`a(2h) ≤ ∏_{i < 2h} (if i odd then min(2h - i, h) else 2h - i)`, which is
`(2h)! · exp(-(0.0966… + o(1)) · 2h)`. -/
theorem semiCount_even_le_prod (h : Nat) :
    semiCount (2 * h) ≤
      ∏ i ∈ Finset.range (2 * h), (if i % 2 = 1 then min (2 * h - i) h else 2 * h - i) := by
  apply semiCount_le_prod
  intro p hl hnd hb _
  have c1 := card_moves_le hnd hb
  split
  · next hodd => exact le_min c1 (card_moves_odd_le hnd hb hodd)
  · exact c1

/-! ## Composition: residue classes as blocks -/

/-- Panel `y` (`1 ≤ y ≤ n`) of residue class `s` (`1 ≤ s ≤ q`): `(y - 1) q + s`. -/
def cls (q s y : Nat) : Nat := (y - 1) * q + s

/-- `#{y ≥ 1 : cls q t y ≤ z}` (valid while it is at most `n`). -/
def ccount (q t z : Nat) : Nat := (z + q - t) / q

theorem cls_le_iff {q t y z : Nat} (hq : 0 < q) (ht : t ≤ q) (hy : 1 ≤ y) :
    cls q t y ≤ z ↔ y ≤ ccount q t z := by
  unfold cls ccount
  rw [Nat.le_div_iff_mul_le hq]
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  rw [Nat.succ_mul, Nat.add_sub_cancel]
  omega

theorem div_small {b q k : Nat} (lo : k * q ≤ b) (hi : b < k * q + q) :
    b / q = k :=
  Nat.div_eq_of_lt_le lo (by rw [Nat.succ_mul]; exact hi)

/-- The class counts at the points `x - 1`, `x`, `2x - 1` for `x = cls q s j`. -/
theorem ccount_vals {q s t j : Nat} (hq : 0 < q) (hs1 : 1 ≤ s) (hsq : s ≤ q)
    (ht1 : 1 ≤ t) (htq : t ≤ q) :
    ccount q t (cls q s j - 1) = j - 1 + (if t < s then 1 else 0) ∧
    ccount q t (cls q s j) = j - 1 + (if t ≤ s then 1 else 0) ∧
    ccount q t (2 * cls q s j - 1) =
      2 * (j - 1) + (if t ≤ 2 * s - 1 then 1 else 0) + (if t + q ≤ 2 * s - 1 then 1 else 0) := by
  unfold ccount cls
  have m2 : 2 * (j - 1) * q = 2 * ((j - 1) * q) := Nat.mul_assoc ..
  refine ⟨?_, ?_, ?_⟩
  · rw [show (j - 1) * q + s - 1 + q - t = (s - 1 + q - t) + (j - 1) * q by omega,
      Nat.add_mul_div_right _ _ hq]
    split
    · rw [div_small (k := 1) (by omega) (by omega)]; omega
    · rw [div_small (k := 0) (by omega) (by omega)]; omega
  · rw [show (j - 1) * q + s + q - t = (s + q - t) + (j - 1) * q by omega,
      Nat.add_mul_div_right _ _ hq]
    split
    · rw [div_small (k := 1) (by omega) (by omega)]; omega
    · rw [div_small (k := 0) (by omega) (by omega)]; omega
  · rw [show 2 * ((j - 1) * q + s) - 1 + q - t = (2 * s - 1 + q - t) + 2 * (j - 1) * q by omega,
      Nat.add_mul_div_right _ _ hq]
    split <;> split
    · rw [div_small (k := 2) (by omega) (by omega)]; omega
    · rw [div_small (k := 1) (by omega) (by omega)]; omega
    · omega
    · rw [div_small (k := 0) (by omega) (by omega)]; omega

/-- Mirror identity for the class counts. -/
theorem ccount_mirror {q n t z : Nat} (hq : 0 < q) (ht1 : 1 ≤ t) (htq : t ≤ q)
    (hz : z ≤ n * q) : ccount q t z + ccount q (q + 1 - t) (n * q - z) = n := by
  unfold ccount
  set w := z + q - t with hw
  have hdm := Nat.div_add_mod w q
  have hb : w % q < q := Nat.mod_lt _ hq
  set a := w / q
  set b := w % q
  have ha : a ≤ n := by
    refine Decidable.byContradiction fun h => ?_
    have : (n + 1) * q ≤ a * q := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this
    rw [Nat.mul_comm] at hdm
    omega
  have hsub : (n - a) * q + a * q = n * q := by rw [← Nat.add_mul, Nat.sub_add_cancel ha]
  rw [Nat.mul_comm] at hdm
  rw [show n * q - z + q - (q + 1 - t) = (q - 1 - b) + (n - a) * q by omega,
    Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt (by omega)]
  omega

/-- The panels of class `t`, in increasing order. -/
def classPanels (q n t : Nat) : List Nat := (List.range' 1 n).map (cls q t)

theorem ccount_top {q n t : Nat} (hq : 0 < q) (ht1 : 1 ≤ t) (htq : t ≤ q) :
    ccount q t (n * q) = n := by
  unfold ccount
  rw [show n * q + q - t = (q - t) + n * q by omega, Nat.add_mul_div_right _ _ hq,
    Nat.div_eq_of_lt (by omega)]; omega

theorem ccount_zero {q t : Nat} (ht1 : 1 ≤ t) (htq : t ≤ q) : ccount q t 0 = 0 := by
  unfold ccount; exact Nat.div_eq_of_lt (by omega)

theorem countP_le_classPanels {q n t z : Nat} (hq : 0 < q) (ht1 : 1 ≤ t) (htq : t ≤ q)
    (hz : z ≤ n * q) :
    (classPanels q n t).countP (fun u => decide (u ≤ z)) = ccount q t z := by
  unfold classPanels
  rw [List.countP_map]
  have e : (List.range' 1 n).countP ((fun u => decide (u ≤ z)) ∘ cls q t) =
      (List.range' 1 n).countP (fun y => decide (1 ≤ y ∧ y ≤ ccount q t z)) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    rw [cls_le_iff hq htq hy.1]; omega
  rw [e, countP_range'_interval]
  have : ccount q t z ≤ n := by
    unfold ccount
    have := (Nat.div_lt_iff_lt_mul hq).2
      (show z + q - t < (n + 1) * q by rw [Nat.succ_mul]; omega)
    omega
  omega

theorem countP_interval_add (U : List Nat) {lo hi : Nat} (h : lo ≤ hi + 1) :
    U.countP (fun u => decide (lo ≤ u ∧ u ≤ hi)) + U.countP (fun u => decide (u + 1 ≤ lo)) =
      U.countP (fun u => decide (u ≤ hi)) := by
  have hs := countP_split U (fun u => decide (u ≤ hi)) (fun u => decide (u + 1 ≤ lo))
  have e1 : U.countP (fun u => decide (u ≤ hi) && decide (u + 1 ≤ lo)) =
      U.countP (fun u => decide (u + 1 ≤ lo)) := by
    apply List.countP_congr; intro u _; simp; omega
  have e2 : U.countP (fun u => decide (u ≤ hi) && !decide (u + 1 ≤ lo)) =
      U.countP (fun u => decide (lo ≤ u ∧ u ≤ hi)) := by
    apply List.countP_congr; intro u _; simp; omega
  omega

theorem countP_succ_le {U : List Nat} {lo : Nat} (h : 1 ≤ lo) :
    U.countP (fun u => decide (u + 1 ≤ lo)) = U.countP (fun u => decide (u ≤ lo - 1)) := by
  apply List.countP_congr; intro u _; simp; omega

theorem cls_mirror {q n s j : Nat} (_hs1 : 1 ≤ s) (hsq : s ≤ q) (hj1 : 1 ≤ j)
    (hjn : j ≤ n) : cls q (q + 1 - s) (n + 1 - j) + cls q s j = n * q + 1 := by
  unfold cls
  have h := congrArg (· * q) (show n + 1 - j - 1 + (j - 1) + 1 = n by omega)
  simp only [Nat.add_mul, Nat.one_mul] at h
  omega

theorem cls_bounds {q n s j : Nat} (hq : 0 < q) (hs1 : 1 ≤ s) (hsq : s ≤ q) (hj1 : 1 ≤ j)
    (hjn : j ≤ n) : 1 ≤ cls q s j ∧ cls q s j ≤ n * q := by
  refine ⟨by unfold cls; omega, ?_⟩
  rw [cls_le_iff hq hsq hj1, ccount_top hq hs1 hsq]; exact hjn

/-- **Per-class balance identity.**  The imbalance of class `t` in the window of
`x = cls q s j` equals the indicator imbalance of `t` in the window of `s` in the
`q`-strip. -/
theorem class_identity {q n s t j : Nat} (hq : 0 < q) (hs1 : 1 ≤ s) (hsq : s ≤ q)
    (ht1 : 1 ≤ t) (htq : t ≤ q) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    (classPanels q n t).countP (fun u => decide (cls q s j - reach (n * q) (cls q s j) ≤ u ∧
        u < cls q s j)) + (if s < t ∧ t ≤ s + reach q s then 1 else 0) =
    (classPanels q n t).countP (fun u => decide (cls q s j < u ∧
        u ≤ cls q s j + reach (n * q) (cls q s j))) +
      (if s - reach q s ≤ t ∧ t < s then 1 else 0) := by
  obtain ⟨hx1, hxN⟩ := cls_bounds hq hs1 hsq hj1 hjn
  obtain ⟨v1, v2, v3⟩ := ccount_vals (j := j) hq hs1 hsq ht1 htq
  have hmir := cls_mirror (q := q) hs1 hsq hj1 hjn
  obtain ⟨w1, w2, w3⟩ := ccount_vals (j := n + 1 - j) (s := q + 1 - s) (t := q + 1 - t) hq
    (by omega) (by omega) (by omega) (by omega)
  generalize cls q s j = x at *
  generalize cls q (q + 1 - s) (n + 1 - j) = x' at *
  have hr : reach (n * q) x ≤ x - 1 ∧ reach (n * q) x ≤ n * q - x := by
    unfold reach; omega
  have i1 := countP_interval_add (classPanels q n t) (lo := x - reach (n * q) x) (hi := x - 1)
    (by omega)
  rw [countP_succ_le (by omega), countP_le_classPanels hq ht1 htq (by omega),
    countP_le_classPanels hq ht1 htq (by omega)] at i1
  have i2 := countP_interval_add (classPanels q n t) (lo := x + 1) (hi := x + reach (n * q) x)
    (by omega)
  rw [countP_succ_le (by omega), countP_le_classPanels hq ht1 htq (by omega),
    countP_le_classPanels hq ht1 htq (by omega)] at i2
  have e1 : (classPanels q n t).countP (fun u => decide (x - reach (n * q) x ≤ u ∧ u < x)) =
      (classPanels q n t).countP (fun u => decide (x - reach (n * q) x ≤ u ∧ u ≤ x - 1)) := by
    apply List.countP_congr; intro u _; simp; omega
  have e2 : (classPanels q n t).countP (fun u => decide (x < u ∧ u ≤ x + reach (n * q) x)) =
      (classPanels q n t).countP (fun u => decide (x + 1 ≤ u ∧ u ≤ x + reach (n * q) x)) := by
    apply List.countP_congr; intro u _; simp; omega
  rw [e1, e2]
  have rq : reach q s = min (s - 1) (q - s) := rfl
  rcases Nat.le_total (x - 1) (n * q - x) with hle | hle
  · have hr' : reach (n * q) x = x - 1 := by unfold reach; omega
    rw [hr'] at i1 i2 ⊢
    rw [show x - (x - 1) - 1 = 0 by omega, ccount_zero ht1 htq] at i1
    rw [show x + 1 - 1 = x by omega] at i2
    rw [show x + (x - 1) = 2 * x - 1 by omega] at i2 ⊢
    rw [rq]; split_ifs at v1 v2 v3 ⊢ <;> omega
  · have hr' : reach (n * q) x = n * q - x := by unfold reach; omega
    rw [hr'] at i1 i2 ⊢
    rw [show x + 1 - 1 = x by omega] at i2
    rw [show x + (n * q - x) = n * q by omega] at i2 ⊢
    rw [ccount_top hq ht1 htq] at i2
    rw [show x - (n * q - x) - 1 = 2 * x - n * q - 1 by omega] at i1
    have m1 := ccount_mirror (n := n) (z := x - 1) hq ht1 htq (by omega)
    have m2 := ccount_mirror (n := n) (z := 2 * x - n * q - 1) hq ht1 htq (by omega)
    have m3 := ccount_mirror (n := n) (z := x) hq ht1 htq (by omega)
    rw [show n * q - (x - 1) = x' by omega] at m1
    rw [show n * q - (2 * x - n * q - 1) = 2 * x' - 1 by omega] at m2
    rw [show n * q - x = x' - 1 by omega] at m3
    rw [rq]; split_ifs at w1 w2 w3 ⊢ <;> omega

/-- The union of the classes in `R`, class by class. -/
def classUnion (q n : Nat) (R : List Nat) : List Nat := (R.map (classPanels q n)).flatten

theorem classUnion_identity {q n s j : Nat} (hq : 0 < q) (hs1 : 1 ≤ s) (hsq : s ≤ q)
    (hj1 : 1 ≤ j) (hjn : j ≤ n) : ∀ R : List Nat, (∀ t ∈ R, 1 ≤ t ∧ t ≤ q) →
    (classUnion q n R).countP (fun u => decide (cls q s j - reach (n * q) (cls q s j) ≤ u ∧
        u < cls q s j)) + R.countP (fun t => decide (s < t ∧ t ≤ s + reach q s)) =
    (classUnion q n R).countP (fun u => decide (cls q s j < u ∧
        u ≤ cls q s j + reach (n * q) (cls q s j))) +
      R.countP (fun t => decide (s - reach q s ≤ t ∧ t < s))
  | [], _ => by simp [classUnion]
  | t :: R, hR => by
    have ih := classUnion_identity hq hs1 hsq hj1 hjn R (fun t ht => hR t (by simp [ht]))
    have ht := hR t (by simp)
    have ci := class_identity (t := t) hq hs1 hsq ht.1 ht.2 hj1 hjn
    simp only [classUnion, List.map_cons, List.flatten_cons, List.countP_append,
      List.countP_cons] at ih ⊢
    split_ifs at ci ⊢ <;> simp_all <;> omega

/-- **Class balance.**  If the step `(R, s)` is valid in the `q`-strip, the complete
classes `R` are balanced around every panel of class `s`. -/
theorem classUnion_balanced {q n s j : Nat} {R : List Nat} (hq : 0 < q) (hs1 : 1 ≤ s)
    (hsq : s ≤ q) (hj1 : 1 ≤ j) (hjn : j ≤ n) (hR : ∀ t ∈ R, 1 ≤ t ∧ t ≤ q)
    (hnd : R.Nodup) (hstep : SemiStep q R s) :
    Balanced (n * q) (classUnion q n R) (cls q s j) := by
  have := classUnion_identity hq hs1 hsq hj1 hjn R hR
  unfold SemiStep at hstep
  rw [leftCount_eq hnd, rightCount_eq hnd] at hstep
  unfold Balanced
  omega

theorem ccount_mono {q t z z' : Nat} (h : z ≤ z') : ccount q t z ≤ ccount q t z' := by
  unfold ccount; exact Nat.div_le_div_right (by omega)

/-- Each residue class is a window-embedded copy of the `n`-strip. -/
theorem winEmb_cls {q n s : Nat} (hq : 0 < q) (hs1 : 1 ≤ s) (hsq : s ≤ q) :
    WinEmb (n * q) n (cls q s) := by
  have self : ∀ j, 1 ≤ j → ccount q s (cls q s j) = j := fun j _ => by
    have := (ccount_vals (j := j) hq hs1 hsq hs1 hsq).2.1; simp at this; omega
  refine ⟨fun y h1 h2 => cls_bounds hq hs1 hsq h1 h2, fun x y hx1 _ hy1 _ e => ?_, ?_, ?_⟩
  · have a := self x hx1; have b := self y hy1; rw [e] at a; omega
  all_goals
    intro j y hj1 hjn hy1 hyn
    obtain ⟨hx1, hxN⟩ := cls_bounds hq hs1 hsq hj1 hjn
    obtain ⟨v1, v2, v3⟩ := ccount_vals (j := j) hq hs1 hsq hs1 hsq
    have hmir := cls_mirror (q := q) hs1 hsq hj1 hjn
    obtain ⟨w1, w2, w3⟩ := ccount_vals (j := n + 1 - j) (s := q + 1 - s) (t := q + 1 - s) hq
      (by omega) (by omega) (by omega) (by omega)
    simp only [lt_self_iff_false, ite_false, le_refl, ite_true] at v1 v2 w1 w2
    have hv3 : ccount q s (2 * cls q s j - 1) = 2 * j - 1 := by
      rw [v3]; split_ifs <;> omega
    have hw3 : ccount q (q + 1 - s) (2 * cls q (q + 1 - s) (n + 1 - j) - 1) =
        2 * (n + 1 - j) - 1 := by
      rw [w3]; split_ifs <;> omega
    have c1 := cls_le_iff (z := cls q s j - 1) hq hsq hy1
    have c2 := cls_le_iff (z := cls q s j) hq hsq hy1
    have top := ccount_top (n := n) hq hs1 hsq
    have mn : ∀ z, z ≤ n * q → ccount q s z ≤ n := fun z hz => top ▸ ccount_mono hz
    generalize cls q s j = x at *
    generalize cls q (q + 1 - s) (n + 1 - j) = x' at *
    rcases Nat.le_total (x - 1) (n * q - x) with hle | hle
    · have hr : reach (n * q) x = x - 1 := by unfold reach; omega
      have := mn (2 * x - 1) (by omega)
      have hrn : reach n j = j - 1 := by unfold reach; omega
      rw [hr, hrn]
      first
      | (have c3 := cls_le_iff (z := x - (x - 1) - 1) hq hsq hy1
         rw [show x - (x - 1) - 1 = 0 by omega, ccount_zero hs1 hsq] at c3
         omega)
      | (have c3 := cls_le_iff (z := x + (x - 1)) hq hsq hy1
         rw [show x + (x - 1) = 2 * x - 1 by omega, hv3] at c3
         omega)
    · have hr : reach (n * q) x = n * q - x := by unfold reach; omega
      have m2 := ccount_mirror (n := n) (z := 2 * x - n * q - 1) hq hs1 hsq (by omega)
      rw [show n * q - (2 * x - n * q - 1) = 2 * x' - 1 by omega, hw3] at m2
      have hrn : reach n j = n - j := by unfold reach; omega
      rw [hr, hrn]
      first
      | (have c3 := cls_le_iff (z := x - (n * q - x) - 1) hq hsq hy1
         rw [show x - (n * q - x) - 1 = 2 * x - n * q - 1 by omega] at c3
         omega)
      | (have c3 := cls_le_iff (z := x + (n * q - x)) hq hsq hy1
         rw [show x + (n * q - x) = n * q by omega, top] at c3
         omega)

/-- The composed sequence: the classes in the skeleton order `π`, class `s` in the
order `σ s`. -/
def blocks (q : Nat) (π : List Nat) (σ : Nat → List Nat) : List Nat :=
  (π.map fun s => (σ s).map (cls q s)).flatten

theorem blocks_perm {q n : Nat} {σ : Nat → List Nat} : ∀ π : List Nat,
    (∀ s ∈ π, IsFoldSeq n (σ s)) → (blocks q π σ).Perm (classUnion q n π)
  | [], _ => by simp [blocks, classUnion]
  | s :: π, h => by
    simp only [blocks, classUnion, List.map_cons, List.flatten_cons] at *
    exact ((h s (by simp)).map _).append (blocks_perm π fun t ht => h t (by simp [ht]))

theorem length_classUnion {q n : Nat} : ∀ R : List Nat, (classUnion q n R).length = R.length * n
  | [] => by simp [classUnion]
  | t :: R => by
    have := length_classUnion (q := q) (n := n) R
    simp only [classUnion, List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons] at *
    rw [this]; simp [classPanels, Nat.succ_mul]; omega

theorem classUnion_cover {q n : Nat} (hq : 0 < q) :
    (classUnion q n (List.range' 1 q)).Perm (List.range' 1 (n * q)) := by
  have sub : List.range' 1 (n * q) ⊆ classUnion q n (List.range' 1 q) := by
    intro u hu
    rw [List.mem_range'_1] at hu
    simp only [classUnion, List.mem_flatten, List.mem_map]
    refine ⟨classPanels q n ((u - 1) % q + 1), ⟨(u - 1) % q + 1, List.mem_range'_1.2
      ⟨by omega, by have := Nat.mod_lt (u - 1) hq; omega⟩, rfl⟩, ?_⟩
    simp only [classPanels, List.mem_map, List.mem_range'_1]
    have hd := Nat.div_add_mod' (u - 1) q
    have hlt := (Nat.div_lt_iff_lt_mul hq).2 (show u - 1 < n * q by omega)
    generalize (u - 1) / q = d at hd hlt
    generalize (u - 1) % q = r at hd ⊢
    exact ⟨d + 1, by omega, by unfold cls; rw [Nat.add_sub_cancel]; omega⟩
  refine ((List.subperm_of_subset (List.nodup_range' ..) sub).perm_of_length_le ?_).symm
  rw [length_classUnion]; simp [Nat.mul_comm]

theorem isFoldSeq_blocks {q n : Nat} (hq : 0 < q) {π : List Nat} {σ : Nat → List Nat}
    (hπ : IsFoldSeq q π) (hσ : ∀ s, 1 ≤ s → s ≤ q → IsFoldSeq n (σ s)) :
    IsFoldSeq (n * q) (blocks q π σ) :=
  (blocks_perm π fun s hs => hσ s ((mem_range'_of_perm hπ).1 hs).1
    ((mem_range'_of_perm hπ).1 hs).2).trans
    ((List.Perm.flatten (hπ.map _)).trans (classUnion_cover hq))

theorem blocks_append {q : Nat} {σ : Nat → List Nat} (π π' : List Nat) :
    blocks q (π ++ π') σ = blocks q π σ ++ blocks q π' σ := by
  simp [blocks]

/-- **Composition.**  If `π` is valid for `q` and every `σ s` is valid for `n`, the
composed sequence is valid for `n q`. -/
theorem semiSymmetric_blocks {q n : Nat} (hq : 0 < q) {π : List Nat} {σ : Nat → List Nat}
    (hπ : IsFoldSeq q π) (hπs : SemiSymmetric q π)
    (hσ : ∀ s, 1 ≤ s → s ≤ q → IsFoldSeq n (σ s) ∧ SemiSymmetric n (σ s)) :
    SemiSymmetric (n * q) (blocks q π σ) := by
  have hall := nodup_of_foldSeq (isFoldSeq_blocks hq hπ fun s h1 h2 => (hσ s h1 h2).1)
  have bπ : ∀ s ∈ π, 1 ≤ s ∧ s ≤ q := fun s hs => (mem_range'_of_perm hπ).1 hs
  have hndπ := nodup_of_foldSeq hπ
  suffices H : ∀ k, k ≤ π.length → SemiSymmetric (n * q) (blocks q (π.take k) σ) by
    simpa using H π.length le_rfl
  intro k
  induction k with
  | zero => intro _ i hi; simp [blocks] at hi
  | succ k ih =>
    intro hk
    have hkl : k < π.length := by omega
    rw [List.take_succ_eq_append_getElem hkl, blocks_append, semiSymmetric_append_iff]
    refine ⟨ih (by omega), ?_⟩
    have hs := bπ _ (List.getElem_mem hkl)
    obtain ⟨hσf, hσs⟩ := hσ π[k] hs.1 hs.2
    have bσ : ∀ y ∈ σ π[k], 1 ≤ y ∧ y ≤ n := fun y hy => (mem_range'_of_perm hσf).1 hy
    have hpre : (blocks q (π.take (k + 1)) σ).Nodup := by
      have e : blocks q π σ = blocks q (π.take (k + 1)) σ ++ blocks q (π.drop (k + 1)) σ := by
        rw [← blocks_append, List.take_append_drop]
      rw [e] at hall; exact (List.nodup_append.1 hall).1
    rw [List.take_succ_eq_append_getElem hkl, blocks_append] at hpre
    intro i hi
    simp only [blocks, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.length_map] at hi ⊢
    rw [List.getElem_map, ← List.map_take]
    have hj := bσ _ (List.getElem_mem hi)
    refine ((winEmb_cls (n := n) hq hs.1 hs.2).semiStep_iff ?_
      (fun y hy => bσ y (List.mem_of_mem_take hy)) hj.1 hj.2 ?_).2 (hσs i hi)
    · simp only [blocks, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil] at hpre
      exact hpre.sublist (List.Sublist.append_left (List.map_take ▸
        (List.take_sublist _ _)) _)
    · refine (classUnion_balanced (R := π.take k) hq hs.1 hs.2 hj.1 hj.2
        (fun t ht => bπ t (List.mem_of_mem_take ht)) (take_nodup hndπ k) (hπs k hkl)).perm ?_
      exact (blocks_perm _ fun t ht => (hσ t (bπ t (List.mem_of_mem_take ht)).1
        (bπ t (List.mem_of_mem_take ht)).2).1).symm

theorem cls_class {q s y : Nat} (hs1 : 1 ≤ s) (hsq : s ≤ q) :
    (cls q s y - 1) % q = s - 1 := by
  unfold cls
  rw [show (y - 1) * q + s - 1 = (s - 1) + (y - 1) * q by omega, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by omega)]

theorem flatten_inj_of_length {n : Nat} : ∀ {L L' : List (List Nat)},
    (∀ l ∈ L, l.length = n) → (∀ l ∈ L', l.length = n) → L.length = L'.length →
      L.flatten = L'.flatten → L = L'
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | a :: L, a' :: L', h, h', hl, e => by
    simp only [List.flatten_cons] at e
    obtain ⟨e1, e2⟩ := List.append_inj e (by rw [h a (by simp), h' a' (by simp)])
    rw [e1, flatten_inj_of_length (fun l hl => h l (by simp [hl]))
      (fun l hl => h' l (by simp [hl])) (by simpa using hl) e2]

/-- Extend `σ : Fin q → List ℕ` to the class labels `1..q`. -/
def extFam {q : Nat} (σ : Fin q → List Nat) (s : Nat) : List Nat :=
  if h : s - 1 < q then σ ⟨s - 1, h⟩ else []

/-- The composition map. -/
def compMap (q : Nat) (x : List Nat × (Fin q → List Nat)) : List Nat :=
  blocks q x.1 (extFam x.2)

theorem compMap_mem {q n : Nat} (hq : 0 < q) {x : List Nat × (Fin q → List Nat)}
    (hx : x ∈ semiSeqs q ×ˢ Fintype.piFinset (fun _ : Fin q => semiSeqs n)) :
    compMap q x ∈ semiSeqs (n * q) := by
  rw [Finset.mem_product, mem_semiSeqs, Fintype.mem_piFinset] at hx
  have hσ : ∀ s, 1 ≤ s → s ≤ q → IsFoldSeq n (extFam x.2 s) ∧ SemiSymmetric n (extFam x.2 s) :=
    fun s h1 h2 => by
      unfold extFam; rw [dite_eq_left_of_eq_true (eq_true (by omega))]; exact mem_semiSeqs.1 (hx.2 _)
  rw [mem_semiSeqs]
  exact ⟨isFoldSeq_blocks hq hx.1.1 fun s h1 h2 => (hσ s h1 h2).1,
    semiSymmetric_blocks hq hx.1.1 hx.1.2 hσ⟩

theorem compMap_injOn {q n : Nat} (hq : 0 < q) (hn : 1 ≤ n) :
    Set.InjOn (compMap q)
      (semiSeqs q ×ˢ Fintype.piFinset (fun _ : Fin q => semiSeqs n) : Finset _) := by
  rintro ⟨π, σ⟩ hx ⟨π', σ'⟩ hx' e
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_semiSeqs,
    Fintype.mem_piFinset] at hx hx'
  have fam : ∀ (τ : Fin q → List Nat), (∀ i, IsFoldSeq n (τ i) ∧ SemiSymmetric n (τ i)) → ∀ s, 1 ≤ s → s ≤ q →
      IsFoldSeq n (extFam τ s) := fun τ hτ s h1 h2 => by
    unfold extFam; rw [dite_eq_left_of_eq_true (eq_true (by omega))]; exact (hτ _).1
  have lens : ∀ (τ : Fin q → List Nat) (ρ : List Nat), (∀ i, IsFoldSeq n (τ i) ∧ SemiSymmetric n (τ i)) →
      IsFoldSeq q ρ → ∀ l ∈ ρ.map (fun s => (extFam τ s).map (cls q s)), l.length = n := by
    intro τ ρ hτ hρ l hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hl
    have := (mem_range'_of_perm hρ).1 hs
    rw [List.length_map, (fam τ hτ s this.1 this.2).length_eq]; simp
  have lπ : π.length = q := by rw [hx.1.1.length_eq]; simp
  have lπ' : π'.length = q := by rw [hx'.1.1.length_eq]; simp
  have hL := flatten_inj_of_length (lens σ π hx.2 hx.1.1) (lens σ' π' hx'.2 hx'.1.1)
    (by simp [lπ, lπ']) e
  have pt : ∀ k (hk : k < q), π[k]'(by omega) = π'[k]'(by omega) ∧
      extFam σ (π[k]'(by omega)) = extFam σ' (π[k]'(by omega)) := by
    intro k hk
    have ek := congrArg (fun L => L[k]?) hL
    simp only [List.getElem?_map, List.getElem?_eq_getElem (show k < π.length by omega),
      List.getElem?_eq_getElem (show k < π'.length by omega), Option.map_some,
      Option.some.injEq] at ek
    have bs := (mem_range'_of_perm hx.1.1).1 (List.getElem_mem (show k < π.length by omega))
    have bs' := (mem_range'_of_perm hx'.1.1).1 (List.getElem_mem (show k < π'.length by omega))
    have f1 := fam σ hx.2 _ bs.1 bs.2
    have f2 := fam σ' hx'.2 _ bs'.1 bs'.2
    have l1 : (extFam σ (π[k]'(by omega))).length = n := by rw [f1.length_eq]; simp
    have l2 : (extFam σ' (π'[k]'(by omega))).length = n := by rw [f2.length_eq]; simp
    have hss : π[k]'(by omega) = π'[k]'(by omega) := by
      have h0 := List.getElem_of_eq ek (i := 0) (by simp; omega)
      simp only [List.getElem_map] at h0
      have c1 := cls_class (y := (extFam σ (π[k]'(by omega)))[0]'(by omega)) bs.1 bs.2
      have c2 := cls_class (y := (extFam σ' (π'[k]'(by omega)))[0]'(by omega)) bs'.1 bs'.2
      rw [h0] at c1
      omega
    refine ⟨hss, ?_⟩
    rw [← hss] at ek
    exact (winEmb_cls (n := n) hq bs.1 bs.2).map_inj (fun y hy => (mem_range'_of_perm f1).1 hy)
      (fun y hy => (mem_range'_of_perm (hss ▸ f2)).1 hy) ek
  have hππ : π = π' := List.ext_getElem (by omega) fun k h1 h2 => (pt k (by omega)).1
  subst hππ
  refine Prod.ext rfl (funext fun i => ?_)
  obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.1
    ((mem_range'_of_perm hx.1.1).2 (show 1 ≤ i.val + 1 ∧ i.val + 1 ≤ q by omega))
  have := (pt k (by omega)).2
  rw [hki] at this
  unfold extFam at this
  rw [dite_eq_left_of_eq_true (eq_true (by omega)), dite_eq_left_of_eq_true (eq_true (by omega))] at this
  simpa using this

/-- **Composition lower bound.**  `a(q) · a(n)^q ≤ a(n q)`: place the residue classes
mod `q` (each a copy of the `n`-strip) as blocks, in the order of a valid sequence of the
`q`-strip. -/
theorem semiCount_comp {q n : Nat} (hq : 1 ≤ q) (hn : 1 ≤ n) :
    semiCount q * semiCount n ^ q ≤ semiCount (n * q) := by
  have hsub : (semiSeqs q ×ˢ Fintype.piFinset (fun _ : Fin q => semiSeqs n)).image (compMap q)
      ⊆ semiSeqs (n * q) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact compMap_mem (by omega) hy
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (compMap_injOn (by omega) hn), Finset.card_product,
    Fintype.card_piFinset_const] at this
  exact this

end Folds
