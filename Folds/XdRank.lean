import Folds.Congruence
import Folds.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Connection (cut) matrices of the semi-symmetric fold count

See `experiments/xd_rank/NOTES.txt`.  For a set of panels `X` and its complement `Y` in
`[1, N]`, the *cut matrix* has rows indexed by orderings `σ` of `X`, columns by orderings `τ`
of `Y`, and entry

  `cutCount N X σ τ` = number of semi-symmetric sequences `a` of length `N` whose
  restriction to `X` is `σ` and whose restriction to `Y` is `τ`

(the number of valid shuffles of `σ` and `τ`).  The rank of this matrix is a lower bound for
the number of states of any (weighted) transfer scheme that processes the panels of `X`
before those of `Y`.

* `semiCount_eq_sum_cutCount`: `a(N) = ∑_σ ∑_τ M[σ, τ]`.
* `cutCount_compl`: exchanging `X` and `Y` transposes the matrix.
* `cutCount_reverse`: `M[σ.reverse, τ.reverse] = M[σ, τ]`.
* `cutCount_mirror`: `M_{X'}[mirror σ, mirror τ] = M_X[σ, τ]` for the mirrored cut `X'`.
* `cutCount_eq_zero_of_internal`: a row vanishes as soon as `σ` violates the constraint of a
  panel whose window lies inside `X`.
* `cutCount_map_eq` (**interface lemma**): the row of `σ` depends only on its *descriptor*.
  If a relabelling `f` of the panels of `σ` keeps, for every panel `x` of `σ`, (i) the set of
  `Y`-windows containing `x` on either side, (ii) the `Y`-panels in the two arms of `x`, and
  (iii) the imbalance of the earlier `X`-panels around `x`, then `σ.map f` and `σ` have the
  same row.

The trace identity `M[σ, mirror σ] = 0` for the middle cut of even `N`, and all rank
computations, are in the notes (paper proof / data), not formalised here.
-/

namespace Folds
namespace XdRank

open Finset

/-- Entry of the cut matrix: the number of semi-symmetric sequences of length `N` whose
subsequence of panels in `X` is `σ` and whose subsequence of panels outside `X` is `τ`. -/
def cutCount (N : ℕ) (X : Finset ℕ) (σ τ : List ℕ) : ℕ :=
  ((semiSeqs N).filter fun a => a.filter (· ∈ X) = σ ∧ a.filter (· ∉ X) = τ).card

theorem mem_of_mem_semiSeqs {N : ℕ} {a : List ℕ} (ha : a ∈ semiSeqs N) {x : ℕ} (hx : x ∈ a) :
    1 ≤ x ∧ x ≤ N := by
  have := (mem_range'_of_perm (mem_semiSeqs.1 ha).1).1 hx
  omega

/-- `a(N)` is the sum of all entries of the cut matrix. -/
theorem semiCount_eq_sum_cutCount (N : ℕ) (X : Finset ℕ) :
    semiCount N = ∑ σ ∈ orderings (Icc 1 N ∩ X), ∑ τ ∈ orderings (Icc 1 N \ X),
      cutCount N X σ τ := by
  unfold semiCount
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun a : List ℕ => (a.filter (· ∈ X), a.filter (· ∉ X)))
    (t := orderings (Icc 1 N ∩ X) ×ˢ orderings (Icc 1 N \ X)), Finset.sum_product]
  · refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    unfold cutCount
    congr 1
  · intro a ha
    have hf := (isFoldSeq_iff.1 (mem_semiSeqs.1 ha).1)
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_orderings]
    refine ⟨⟨hf.1.filter _, ?_⟩, ⟨hf.1.filter _, ?_⟩⟩
    · rw [List.toFinset_filter, hf.2]; ext x; simp
    · rw [List.toFinset_filter, hf.2]; ext x; simp

/-- Exchanging the two sides of the cut transposes the matrix. -/
theorem cutCount_compl (N : ℕ) (X : Finset ℕ) (σ τ : List ℕ) :
    cutCount N (Icc 1 N \ X) τ σ = cutCount N X σ τ := by
  unfold cutCount
  congr 1
  apply Finset.filter_congr
  intro a ha
  have e1 : a.filter (· ∈ Icc 1 N \ X) = a.filter (· ∉ X) := by
    apply List.filter_congr
    intro x hx
    have := mem_of_mem_semiSeqs ha hx
    simp [Finset.mem_sdiff, Finset.mem_Icc, this.1, this.2]
  have e2 : a.filter (· ∉ Icc 1 N \ X) = a.filter (· ∈ X) := by
    apply List.filter_congr
    intro x hx
    have := mem_of_mem_semiSeqs ha hx
    simp [Finset.mem_sdiff, Finset.mem_Icc, this.1, this.2]
  rw [e1, e2]
  exact and_comm

/-- Reversal: `M[σ.reverse, τ.reverse] = M[σ, τ]`. -/
theorem cutCount_reverse (N : ℕ) (X : Finset ℕ) (σ τ : List ℕ) :
    cutCount N X σ.reverse τ.reverse = cutCount N X σ τ := by
  unfold cutCount
  refine Finset.card_nbij' List.reverse List.reverse ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    refine ⟨reverse_mem_semiSeqs ha.1, ?_, ?_⟩
    · rw [List.filter_reverse, ha.2.1, List.reverse_reverse]
    · rw [List.filter_reverse, ha.2.2, List.reverse_reverse]
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    refine ⟨reverse_mem_semiSeqs ha.1, ?_, ?_⟩
    · rw [List.filter_reverse, ha.2.1]
    · rw [List.filter_reverse, ha.2.2]
  · intro a _; simp
  · intro a _; simp

/-- The mirror image of a set of panels. -/
def mirrorSet (N : ℕ) (X : Finset ℕ) : Finset ℕ := (Icc 1 N).filter fun x => N + 1 - x ∈ X

theorem mem_mirrorSet {N : ℕ} {X : Finset ℕ} {x : ℕ} :
    x ∈ mirrorSet N X ↔ (1 ≤ x ∧ x ≤ N) ∧ N + 1 - x ∈ X := by
  simp [mirrorSet]

theorem filter_mirror {N : ℕ} {a : List ℕ} (ha : a ∈ semiSeqs N) (X : Finset ℕ) :
    (mirror N a).filter (· ∈ mirrorSet N X) = mirror N (a.filter (· ∈ X)) ∧
    (mirror N a).filter (· ∉ mirrorSet N X) = mirror N (a.filter (· ∉ X)) := by
  unfold mirror
  rw [List.filter_map, List.filter_map]
  constructor
  · congr 1
    apply List.filter_congr
    intro x hx
    have := mem_of_mem_semiSeqs ha hx
    have e : N + 1 - (N + 1 - x) = x := by omega
    simp only [Function.comp_apply, mem_mirrorSet, e, decide_eq_decide]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨⟨by omega, by omega⟩, h⟩
  · congr 1
    apply List.filter_congr
    intro x hx
    have := mem_of_mem_semiSeqs ha hx
    have e : N + 1 - (N + 1 - x) = x := by omega
    simp only [Function.comp_apply, mem_mirrorSet, e, decide_eq_decide]
    constructor
    · exact fun h h' => h ⟨⟨by omega, by omega⟩, h'⟩
    · exact fun h h' => h h'.2

theorem mirror_mirror_of_bounds {N : ℕ} {l : List ℕ} (hl : ∀ x ∈ l, 1 ≤ x ∧ x ≤ N) :
    mirror N (mirror N l) = l := by
  unfold mirror
  rw [List.map_map]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx; have := hl x hx; simp; omega

theorem eq_of_mirror_eq {N : ℕ} {σ L : List ℕ} (hL : ∀ x ∈ L, 1 ≤ x ∧ x ≤ N)
    (h : mirror N σ = mirror N L) : L = σ := by
  have hσ : ∀ x ∈ σ, 1 ≤ x ∧ x ≤ N := by
    intro x hx
    have hx' : N + 1 - x ∈ mirror N σ := List.mem_map.2 ⟨x, hx, rfl⟩
    rw [h] at hx'
    obtain ⟨z, hz, e⟩ := List.mem_map.1 hx'
    have := hL z hz
    omega
  have h2 := congrArg (mirror N) h
  rw [mirror_mirror_of_bounds hσ, mirror_mirror_of_bounds hL] at h2
  exact h2.symm

/-- Mirror symmetry: the cut matrix of the mirrored cut, in mirrored coordinates. -/
theorem cutCount_mirror (N : ℕ) (X : Finset ℕ) (σ τ : List ℕ) :
    cutCount N (mirrorSet N X) (mirror N σ) (mirror N τ) = cutCount N X σ τ := by
  unfold cutCount
  symm
  refine Finset.card_nbij' (mirror N) (mirror N) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    refine ⟨mirror_mem_semiSeqs ha.1, ?_, ?_⟩
    · rw [(filter_mirror ha.1 X).1, ha.2.1]
    · rw [(filter_mirror ha.1 X).2, ha.2.2]
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    have hb : ∀ p : ℕ → Bool, ∀ x ∈ (mirror N a).filter p, 1 ≤ x ∧ x ≤ N := fun p x hx =>
      mem_of_mem_semiSeqs (mirror_mem_semiSeqs ha.1) (List.mem_of_mem_filter hx)
    refine ⟨mirror_mem_semiSeqs ha.1, ?_, ?_⟩
    · have h := (filter_mirror (mirror_mem_semiSeqs ha.1) X).1
      rw [mirror_mirror (mem_semiSeqs.1 ha.1).1, ha.2.1] at h
      exact eq_of_mirror_eq (hb _) h
    · have h := (filter_mirror (mirror_mem_semiSeqs ha.1) X).2
      rw [mirror_mirror (mem_semiSeqs.1 ha.1).1, ha.2.2] at h
      exact eq_of_mirror_eq (hb _) h
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha
    exact mirror_mirror (mem_semiSeqs.1 ha.1).1
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha
    exact mirror_mirror (mem_semiSeqs.1 ha.1).1

/-! ## Arms, prefixes, and the zero rows -/

/-- `x` lies in the left arm of the window of `m`. -/
def inL (N m x : ℕ) : Prop := m - reach N m ≤ x ∧ x < m

/-- `x` lies in the right arm of the window of `m`. -/
def inR (N m x : ℕ) : Prop := m < x ∧ x ≤ m + reach N m

instance (N m x : ℕ) : Decidable (inL N m x) := inferInstanceAs (Decidable (_ ∧ _))
instance (N m x : ℕ) : Decidable (inR N m x) := inferInstanceAs (Decidable (_ ∧ _))

theorem semiStep_iff_arms {N m : ℕ} {S : List ℕ} (hnd : S.Nodup) :
    SemiStep N S m ↔ S.countP (fun x => decide (inL N m x)) = S.countP (fun x => decide (inR N m x)) := by
  unfold SemiStep
  rw [leftCount_eq hnd, rightCount_eq hnd]
  rfl

/-- Split a count according to membership in `X`. -/
theorem countP_split (X : Finset ℕ) (S : List ℕ) (q : ℕ → Bool) :
    S.countP q = (S.filter (· ∈ X)).countP q + (S.filter (· ∉ X)).countP q := by
  induction S with
  | nil => simp
  | cons x S ih =>
    by_cases hx : x ∈ X <;> by_cases hq : q x = true <;>
      simp [hx, hq, ih] <;> omega

/-- The `X`-part of a prefix of `a` is a prefix of the `X`-part of `a`; if the next entry is
in `X`, it is the next entry of the `X`-part. -/
theorem prefix_data {a σ : List ℕ} {X : Finset ℕ} (hσ : a.filter (· ∈ X) = σ) {k : ℕ}
    (hk : k < a.length) (hm : a[k] ∈ X) :
    ∃ p, ∃ hp : p < σ.length, σ[p] = a[k] ∧ (a.take k).filter (· ∈ X) = σ.take p := by
  have h1 : (a.take (k + 1)).filter (· ∈ X) <+: σ := hσ ▸ (List.take_prefix _ _).filter _
  have h2 : a.take (k + 1) = a.take k ++ [a[k]] := (List.take_append_getElem hk).symm
  rw [h2, List.filter_append] at h1
  have h3 : [a[k]].filter (· ∈ X) = [a[k]] := by simp [hm]
  rw [h3] at h1
  set SX := (a.take k).filter (· ∈ X) with hSX
  have h4 := List.prefix_iff_eq_take.1 h1
  have hlen : SX.length + 1 ≤ σ.length := by
    have := h1.length_le; simpa using this
  refine ⟨SX.length, by omega, ?_, ?_⟩
  · have := h1.getElem (i := SX.length) (by simp)
    rw [← this]; simp
  · have h5 : SX <+: σ := (List.prefix_append SX [a[k]]).trans h1
    exact List.prefix_iff_eq_take.1 h5

/-- **Zero rows.**  If the window of the panel `σ[p]` contains no panel outside `X`, and the
earlier panels of `σ` are not balanced around it, the row of `σ` vanishes. -/
theorem cutCount_eq_zero_of_internal {N : ℕ} {X : Finset ℕ} {σ : List ℕ} (τ : List ℕ) {p : ℕ}
    (hp : p < σ.length)
    (hwin : ∀ y, 1 ≤ y → y ≤ N → (inL N σ[p] y ∨ inR N σ[p] y) → y ∈ X)
    (hbad : (σ.take p).countP (fun x => decide (inL N σ[p] x)) ≠
      (σ.take p).countP (fun x => decide (inR N σ[p] x))) :
    cutCount N X σ τ = 0 := by
  unfold cutCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro a ha ⟨hσ, -⟩
  subst hσ
  have hf := (mem_semiSeqs.1 ha).1
  have hnd : a.Nodup := nodup_of_foldSeq hf
  have hσnd : (a.filter (· ∈ X)).Nodup := hnd.filter _
  have hmem : (a.filter (· ∈ X))[p] ∈ a := List.mem_of_mem_filter (List.getElem_mem hp)
  obtain ⟨k, hk, hak⟩ := List.getElem_of_mem hmem
  have hmX : a[k] ∈ X := by
    have := (List.mem_filter.1 (List.getElem_mem hp)).2
    rw [hak]; simpa using this
  obtain ⟨p', hp', e1, e2⟩ := prefix_data rfl hk hmX
  have hpp : p' = p := (hσnd.getElem_inj_iff).1 (e1.trans hak)
  subst hpp
  have hstep := (mem_semiSeqs.1 ha).2 k hk
  rw [semiStep_iff_arms (hnd.sublist (List.take_sublist _ _)), hak,
    countP_split X (a.take k), countP_split X (a.take k) (fun x => decide (inR N (a.filter (· ∈ X))[p'] x)), e2] at hstep
  have z : ∀ q : ℕ → Prop, [DecidablePred q] → (∀ y, 1 ≤ y → y ≤ N → q y → y ∈ X) →
      ((a.take k).filter (· ∉ X)).countP (fun x => decide (q x)) = 0 := by
    intro q _ hq
    rw [List.countP_eq_zero]
    intro y hy
    have hy1 := List.mem_filter.1 hy
    have hb := mem_of_mem_semiSeqs ha (List.mem_of_mem_take hy1.1)
    have hyX : y ∉ X := by simpa using hy1.2
    simpa using fun h => hyX (hq y hb.1 hb.2 h)
  rw [z _ (fun y h1 h2 h => hwin y h1 h2 (Or.inl h)), z _ (fun y h1 h2 h => hwin y h1 h2 (Or.inr h))]
    at hstep
  exact hbad (by simpa using hstep)

/-! ## The interface lemma: the row of `σ` depends only on its descriptor -/

/-- Relabel the panels of `X` by `f`, keep the others. -/
def relabel (X : Finset ℕ) (f : ℕ → ℕ) (x : ℕ) : ℕ := if x ∈ X then f x else x

theorem relabel_of_mem {X : Finset ℕ} {x : ℕ} (f : ℕ → ℕ) (h : x ∈ X) : relabel X f x = f x := by
  simp [relabel, h]

theorem relabel_of_not_mem {X : Finset ℕ} {x : ℕ} (f : ℕ → ℕ) (h : x ∉ X) :
    relabel X f x = x := by
  simp [relabel, h]

/-- `f` preserves the *descriptor* of the ordering `σ` of `X`-panels: for every panel `x` of
`σ`, the windows of outside panels that contain `x` (`kL`, `kR`), the outside panels in the two
arms of `x` (`yL`, `yR`), and the imbalance of the earlier panels of `σ` around `x` (`c`). -/
structure Compat (N : ℕ) (X : Finset ℕ) (f : ℕ → ℕ) (σ : List ℕ) : Prop where
  sub : ∀ x ∈ σ, x ∈ X
  perm : (σ.map f).Perm σ
  kL : ∀ x ∈ σ, ∀ y, 1 ≤ y → y ≤ N → y ∉ X → (inL N y (f x) ↔ inL N y x)
  kR : ∀ x ∈ σ, ∀ y, 1 ≤ y → y ≤ N → y ∉ X → (inR N y (f x) ↔ inR N y x)
  yL : ∀ x ∈ σ, ∀ y, 1 ≤ y → y ≤ N → y ∉ X → (inL N (f x) y ↔ inL N x y)
  yR : ∀ x ∈ σ, ∀ y, 1 ≤ y → y ≤ N → y ∉ X → (inR N (f x) y ↔ inR N x y)
  c : ∀ p (hp : p < σ.length),
    ((σ.take p).map f).countP (fun x => decide (inL N (f σ[p]) x)) +
        (σ.take p).countP (fun x => decide (inR N σ[p] x)) =
      (σ.take p).countP (fun x => decide (inL N σ[p] x)) +
        ((σ.take p).map f).countP (fun x => decide (inR N (f σ[p]) x))

theorem filter_relabel {X : Finset ℕ} {f : ℕ → ℕ} {σ : List ℕ} (hsub : ∀ x ∈ σ, x ∈ X)
    (hperm : (σ.map f).Perm σ) :
    ∀ S : List ℕ, (∀ x ∈ S, x ∈ X → x ∈ σ) →
      (S.map (relabel X f)).filter (· ∈ X) = (S.filter (· ∈ X)).map f ∧
      (S.map (relabel X f)).filter (· ∉ X) = S.filter (· ∉ X)
  | [], _ => by simp
  | x :: S, h => by
    have ih := filter_relabel hsub hperm S (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.filter_cons]
    rw [ih.1, ih.2]
    by_cases hx : x ∈ X
    · have hfx : f x ∈ X :=
        hsub _ (hperm.subset (List.mem_map.2 ⟨x, h x List.mem_cons_self hx, rfl⟩))
      have e : relabel X f x = f x := relabel_of_mem f hx
      rw [e]; simp [hx, hfx]
    · have e : relabel X f x = x := relabel_of_not_mem f hx
      rw [e]; simp [hx]

/-- Relabelling by a descriptor-preserving `f` maps the fibre of `(σ, τ)` into that of
`(σ.map f, τ)`. -/
theorem relabel_mem {N : ℕ} {X : Finset ℕ} {f : ℕ → ℕ} {a : List ℕ}
    (h : Compat N X f (a.filter (· ∈ X))) (ha : a ∈ semiSeqs N) :
    a.map (relabel X f) ∈ semiSeqs N ∧
      (a.map (relabel X f)).filter (· ∈ X) = (a.filter (· ∈ X)).map f ∧
      (a.map (relabel X f)).filter (· ∉ X) = a.filter (· ∉ X) := by
  have hf := (mem_semiSeqs.1 ha).1
  have hnd : a.Nodup := nodup_of_foldSeq hf
  have A := filter_relabel h.sub h.perm
  have Aa := A a (fun x hx hxX => List.mem_filter.2 ⟨hx, by simpa using hxX⟩)
  have e : ∀ l : List ℕ, l.filter (fun x => !decide (x ∈ X)) = l.filter (· ∉ X) := fun l => by
    congr 1
  have p1 := List.filter_append_perm (fun x => decide (x ∈ X)) (a.map (relabel X f))
  have p2 := List.filter_append_perm (fun x => decide (x ∈ X)) a
  rw [e] at p1 p2
  rw [Aa.1, Aa.2] at p1
  have hf' : IsFoldSeq N (a.map (relabel X f)) :=
    (p1.symm.trans ((h.perm.append_right _).trans p2)).trans hf
  have hnd' := nodup_of_foldSeq hf'
  refine ⟨mem_semiSeqs.2 ⟨hf', ?_⟩, Aa.1, Aa.2⟩
  intro k hk
  simp only [List.length_map] at hk
  rw [List.getElem_map, semiStep_iff_arms (hnd'.sublist (List.take_sublist _ _)), ← List.map_take]
  have hs := (mem_semiSeqs.1 ha).2 k hk
  rw [semiStep_iff_arms (hnd.sublist (List.take_sublist _ _))] at hs
  have Ak := A (a.take k) (fun x hx hxX =>
    List.mem_filter.2 ⟨List.mem_of_mem_take hx, by simpa using hxX⟩)
  rw [countP_split X ((a.take k).map (relabel X f)),
    countP_split X ((a.take k).map (relabel X f)) (fun x => decide (inR N _ x)), Ak.1, Ak.2]
  rw [countP_split X (a.take k), countP_split X (a.take k) (fun x => decide (inR N _ x))] at hs
  have hm := mem_of_mem_semiSeqs ha (List.getElem_mem hk)
  have hSY : ∀ y ∈ (a.take k).filter (· ∉ X), (1 ≤ y ∧ y ≤ N) ∧ y ∉ X := fun y hy =>
    ⟨mem_of_mem_semiSeqs ha (List.mem_of_mem_take (List.mem_filter.1 hy).1),
      by simpa using (List.mem_filter.1 hy).2⟩
  have hSX : ∀ x ∈ (a.take k).filter (· ∈ X), x ∈ a.filter (· ∈ X) := fun x hx =>
    List.mem_filter.2 ⟨List.mem_of_mem_take (List.mem_filter.1 hx).1, (List.mem_filter.1 hx).2⟩
  by_cases hmX : a[k] ∈ X
  · have e1 : relabel X f a[k] = f a[k] := relabel_of_mem f hmX
    rw [e1]
    obtain ⟨p, hp, ep, eS⟩ := prefix_data (σ := a.filter (· ∈ X)) rfl hk hmX
    have hc := h.c p hp
    rw [ep, ← eS] at hc
    have y1 : ((a.take k).filter (· ∉ X)).countP (fun x => decide (inL N (f a[k]) x)) =
        ((a.take k).filter (· ∉ X)).countP (fun x => decide (inL N a[k] x)) := by
      apply List.countP_congr
      intro y hy
      simp only [decide_eq_true_eq]
      have := h.yL _ (List.getElem_mem hp) y (hSY y hy).1.1 (hSY y hy).1.2 (hSY y hy).2
      rwa [ep] at this
    have y2 : ((a.take k).filter (· ∉ X)).countP (fun x => decide (inR N (f a[k]) x)) =
        ((a.take k).filter (· ∉ X)).countP (fun x => decide (inR N a[k] x)) := by
      apply List.countP_congr
      intro y hy
      simp only [decide_eq_true_eq]
      have := h.yR _ (List.getElem_mem hp) y (hSY y hy).1.1 (hSY y hy).1.2 (hSY y hy).2
      rwa [ep] at this
    rw [y1, y2]
    omega
  · have e1 : relabel X f a[k] = a[k] := relabel_of_not_mem f hmX
    rw [e1]
    have x1 : (((a.take k).filter (· ∈ X)).map f).countP (fun x => decide (inL N a[k] x)) =
        ((a.take k).filter (· ∈ X)).countP (fun x => decide (inL N a[k] x)) := by
      rw [List.countP_map]
      apply List.countP_congr
      intro x hx
      simp only [Function.comp_apply, decide_eq_true_eq]
      exact h.kL x (hSX x hx) _ hm.1 hm.2 hmX
    have x2 : (((a.take k).filter (· ∈ X)).map f).countP (fun x => decide (inR N a[k] x)) =
        ((a.take k).filter (· ∈ X)).countP (fun x => decide (inR N a[k] x)) := by
      rw [List.countP_map]
      apply List.countP_congr
      intro x hx
      simp only [Function.comp_apply, decide_eq_true_eq]
      exact h.kR x (hSX x hx) _ hm.1 hm.2 hmX
    rw [x1, x2]
    exact hs

/-- The inverse relabelling preserves the descriptor of the relabelled ordering. -/
theorem Compat.inv {N : ℕ} {X : Finset ℕ} {f g : ℕ → ℕ} {σ : List ℕ} (h : Compat N X f σ)
    (hg : ∀ x ∈ σ, g (f x) = x) : Compat N X g (σ.map f) := by
  have hmap : ∀ S : List ℕ, (∀ x ∈ S, x ∈ σ) → (S.map f).map g = S := by
    intro S hS
    rw [List.map_map]
    conv => rhs; rw [← List.map_id S]
    apply List.map_congr_left
    intro x hx; simpa using hg x (hS x hx)
  refine ⟨fun x hx => h.sub x (h.perm.subset hx), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmap σ (fun x hx => hx)]; exact h.perm.symm
  · intro x' hx' y h1 h2 h3
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
    rw [hg x hx]; exact (h.kL x hx y h1 h2 h3).symm
  · intro x' hx' y h1 h2 h3
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
    rw [hg x hx]; exact (h.kR x hx y h1 h2 h3).symm
  · intro x' hx' y h1 h2 h3
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
    rw [hg x hx]; exact (h.yL x hx y h1 h2 h3).symm
  · intro x' hx' y h1 h2 h3
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
    rw [hg x hx]; exact (h.yR x hx y h1 h2 h3).symm
  · intro p hp
    have hp' : p < σ.length := by simpa using hp
    have hc := h.c p hp'
    simp only [List.getElem_map, ← List.map_take]
    rw [hmap (σ.take p) (fun x hx => List.mem_of_mem_take hx), hg _ (List.getElem_mem hp')]
    omega

/-- **Interface lemma.**  If `f` preserves the descriptor of `σ` (and `g` undoes `f` on the
panels of `σ`), then `σ.map f` and `σ` have the same row of the cut matrix. -/
theorem cutCount_map_eq {N : ℕ} {X : Finset ℕ} {f g : ℕ → ℕ} {σ : List ℕ}
    (h : Compat N X f σ) (hg : ∀ x ∈ σ, g (f x) = x) (τ : List ℕ) :
    cutCount N X (σ.map f) τ = cutCount N X σ τ := by
  unfold cutCount
  symm
  have h' := h.inv hg
  refine Finset.card_nbij' (List.map (relabel X f)) (List.map (relabel X g)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨ha1, rfl, rfl⟩ := ha
    exact relabel_mem h ha1
  · intro b hb
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hb ⊢
    obtain ⟨hb1, hb2, rfl⟩ := hb
    have r := relabel_mem (hb2 ▸ h') hb1
    refine ⟨r.1, ?_, r.2.2⟩
    rw [r.2.1, hb2, List.map_map]
    conv => rhs; rw [← List.map_id σ]
    apply List.map_congr_left
    intro x hx; simpa using hg x hx
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha
    obtain ⟨ha1, rfl, rfl⟩ := ha
    rw [List.map_map]
    conv => rhs; rw [← List.map_id a]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply, id_eq]
    by_cases hxX : x ∈ X
    · have hxσ : x ∈ a.filter (· ∈ X) := List.mem_filter.2 ⟨hx, by simpa using hxX⟩
      have hfx : f x ∈ X := h.sub _ (h.perm.subset (List.mem_map.2 ⟨x, hxσ, rfl⟩))
      rw [relabel_of_mem f hxX, relabel_of_mem g hfx]
      exact hg x hxσ
    · rw [relabel_of_not_mem f hxX, relabel_of_not_mem g hxX]
  · intro b hb
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hb
    obtain ⟨hb1, hb2, rfl⟩ := hb
    rw [List.map_map]
    conv => rhs; rw [← List.map_id b]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_apply, id_eq]
    by_cases hxX : x ∈ X
    · have hxσ : x ∈ σ.map f := hb2 ▸ List.mem_filter.2 ⟨hx, by simpa using hxX⟩
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hxσ
      have hzX : z ∈ X := h.sub z hz
      rw [relabel_of_mem g hxX, hg z hz, relabel_of_mem f hzX]
    · rw [relabel_of_not_mem g hxX, relabel_of_not_mem f hxX]

end XdRank
end Folds
