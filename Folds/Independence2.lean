import Folds.Independence

/-!
# Independence with one outside element

Case (b) of the pair classification with one element of `W_a` outside `W_b`
(`experiments/independence/PROOFS.txt` §4).  Then `N = 2n+2` is even, `b = n+2` (window
`[2, N]`), the outside element is `e = 1` and `W_a ⊆ M := {1} ∪ L_b = [1, n+1]`
(or the mirror image).

The proof here is a slight reorganisation of the paper proof.  Write `D` for the set of
panels before `b`, `k = |D ∩ M|`, `j = |D ∩ R_b|` and `i` for the rank of `e` in the
restriction `ρ` of the ordering to `M`.  Then `e ∈ D ↔ i < k`, so
`C_b ↔ j + [i < k] = k` (`qb_iff_phi`).  For fixed `i` the right-hand side is invariant
under all relabellings of `M`, so by `card_indep` the fibre of `C_b` over each `ρ` has
`#{j + [i < k] = k} / (n+1)!` elements (`card_fiber_qb`).  Finally `#{j + [i < k] = k}` does
not depend on `i ≤ n` (`card_phi_eq`): the only change from `i` to `i + 1` is at `k = i + 1`,
where it rests on `C(n,i) (2i+1)! (2n-2i)! = C(n,i+1) (2i+2)! (2n-2i-1)!` — the identity
`T2(i+1) = T1(i)` of the paper proof.  So all fibres have the same size and `C_b` is
independent of every event of the relative order on `M` (`card_indep_qb`).

* `card_pair_one_outside`, `card_pair_one_outside'`: the pair `(a, b)` is independent.
* `card_constrSeqs_chain_append`, `card_constrSeqs_chain_one_outside`: a compatible chain
  may end with such a pair.
-/

namespace Folds

open Finset Nat

/-! ## Before-sets are nested -/

theorem mem_before_iff {l : List ℕ} {x y : ℕ} (hx : x ∈ l) :
    x ∈ before l y ↔ l.idxOf x < l.idxOf y := by
  rw [before, List.mem_toFinset, List.mem_take_iff_idxOf_lt hx]

theorem not_mem_before_self (l : List ℕ) (x : ℕ) : x ∉ before l x := by
  intro h
  have hx : x ∈ l := List.mem_of_mem_take (List.mem_toFinset.1 h)
  exact lt_irrefl _ ((mem_before_iff hx).1 h)

theorem before_subset_before {l : List ℕ} {x y : ℕ} (h : l.idxOf x ≤ l.idxOf y) :
    before l x ⊆ before l y := by
  intro z hz
  rw [before, List.mem_toFinset] at hz ⊢
  exact List.take_subset_take_left l h hz

theorem before_subset_toFinset (l : List ℕ) (x : ℕ) : before l x ⊆ l.toFinset := by
  intro z hz
  rw [before, List.mem_toFinset] at hz
  exact List.mem_toFinset.2 (List.mem_of_mem_take hz)

/-! ## An abstract step condition and its shifted form -/

/-- The step placing `b` is balanced between the parts `L` and `R`. -/
def QB (L R : Finset ℕ) (b : ℕ) (l : List ℕ) : Prop :=
  ((before l b).filter (· ∈ L)).card = ((before l b).filter (· ∈ R)).card

instance (L R : Finset ℕ) (b : ℕ) : DecidablePred (QB L R b) := fun _ =>
  inferInstanceAs (Decidable (_ = _))

/-- The step condition written in terms of `k = |D ∩ M|` and `j = |D ∩ R|`, for an outside
element of rank `i` in `M`: `j + [i < k] = k`. -/
def PhiBal (M R : Finset ℕ) (i : ℕ) (D : Finset ℕ) : Prop :=
  (D.filter (· ∈ R)).card + (if i < (D.filter (· ∈ M)).card then 1 else 0) =
    (D.filter (· ∈ M)).card

instance (M R : Finset ℕ) (i : ℕ) : DecidablePred (PhiBal M R i) := fun _ =>
  inferInstanceAs (Decidable (_ = _))

/-- With `M = {e} ∪ L` and `i` the number of `M`-panels before `e`: `e` comes before `b`
iff `i < k`, so the balance condition becomes `j + [i < k] = k`. -/
theorem qb_iff_phi {X L R : Finset ℕ} {b e : ℕ} (heL : e ∉ L) {l : List ℕ}
    (hl : l ∈ orderings X) (he : e ∈ X) :
    QB L R b l ↔
      PhiBal (insert e L) R ((before l e).filter (· ∈ insert e L)).card (before l b) := by
  set D := before l b with hD
  have hel : e ∈ l := by rw [← List.mem_toFinset, (mem_orderings.1 hl).2]; exact he
  have hsplit : (D.filter (· ∈ insert e L)).card =
      (D.filter (· ∈ L)).card + (if e ∈ D then 1 else 0) := by
    have e1 : D.filter (· ∈ insert e L) = D.filter (· ∈ L) ∪ D.filter (· = e) := by
      ext x; simp only [mem_filter, mem_insert, mem_union]; tauto
    have hdisj : Disjoint (D.filter (· ∈ L)) (D.filter (· = e)) := by
      rw [disjoint_filter]; rintro x _ hx rfl; exact heL hx
    rw [e1, card_union_of_disjoint hdisj, filter_eq']
    split_ifs <;> simp
  have hiff : e ∈ D ↔ ((before l e).filter (· ∈ insert e L)).card <
      (D.filter (· ∈ insert e L)).card := by
    constructor
    · intro h
      have hlt : l.idxOf e < l.idxOf b := (mem_before_iff hel).1 h
      apply card_lt_card
      refine ⟨filter_subset_filter _ (before_subset_before hlt.le), ?_⟩
      intro hsub
      have : e ∈ (before l e).filter (· ∈ insert e L) :=
        hsub (mem_filter.2 ⟨h, mem_insert_self _ _⟩)
      exact not_mem_before_self l e (mem_filter.1 this).1
    · intro h
      by_contra h'
      have hle : l.idxOf b ≤ l.idxOf e := by
        rw [hD, mem_before_iff hel] at h'; omega
      have := card_le_card (filter_subset_filter (· ∈ insert e L) (before_subset_before hle))
      rw [← hD] at this
      omega
  unfold QB PhiBal
  rw [← hD]
  by_cases h : e ∈ D
  · have h2 := hiff.1 h
    simp only [h2, ↓reduceIte]; rw [hsplit]; simp only [h, ↓reduceIte]; omega
  · have h2 : ¬ _ := fun h' => h (hiff.2 h')
    simp only [h2, ↓reduceIte]; rw [hsplit]; simp only [h, ↓reduceIte]; omega

/-- The shifted condition is invariant under relabelling `M`. -/
theorem phi_relab {M R : Finset ℕ} {b : ℕ} (hbM : b ∉ M) (hMR : Disjoint M R)
    {u u' : List ℕ} (hu : u ∈ orderings M) (hu' : u' ∈ orderings M) (i : ℕ) (l : List ℕ) :
    PhiBal M R i (before (l.map (relab u u')) b) ↔ PhiBal M R i (before l b) := by
  obtain ⟨hfix, -, hinv, -⟩ := relab_props hu hu'
  have hinj : Function.Injective (relab u u') := Function.LeftInverse.injective hinv
  have hM := relab_mem_of_sub_or_disj hu hu' (Or.inl (subset_refl M))
  have hR := relab_mem_of_sub_or_disj hu hu' (Or.inr hMR)
  unfold PhiBal
  rw [before_map hinj (hfix b hbM)]
  simp only [filter_image, card_image_of_injective _ hinj, hM, hR]

/-! ## Fibres over the relative order on `M = {e} ∪ L` -/

/-- Setting: `X \ {b} = M ∪ R` with `M = {e} ∪ L`. -/
theorem setup_props {X L R : Finset ℕ} {b e : ℕ} (hX : X.erase b = insert e L ∪ R) :
    insert e L ⊆ X ∧ b ∉ insert e L ∧ e ∈ X := by
  have hM : insert e L ⊆ X.erase b := hX ▸ subset_union_left
  refine ⟨hM.trans (erase_subset _ _), fun h => ?_, (hM.trans (erase_subset _ _))
    (mem_insert_self _ _)⟩
  have := hM h
  simp at this

/-- The fibre of the balance condition over an ordering `ρ` of `M`, times `|M|!`, is the
number of orderings satisfying the shifted condition for the rank of `e` in `ρ`. -/
theorem card_fiber_qb {X L R : Finset ℕ} {b e : ℕ} (hX : X.erase b = insert e L ∪ R)
    (heL : e ∉ L) (hMR : Disjoint (insert e L) R) {ρ : List ℕ}
    (hρ : ρ ∈ orderings (insert e L)) :
    ((orderings X).filter (fun l => restrict (insert e L) l = ρ ∧ QB L R b l)).card *
        (insert e L).card ! =
      ((orderings X).filter
        (fun l => PhiBal (insert e L) R (before ρ e).card (before l b))).card := by
  obtain ⟨hMX, hbM, he⟩ := setup_props hX
  have e1 : (orderings X).filter (fun l => restrict (insert e L) l = ρ ∧ QB L R b l) =
      (orderings X).filter (fun l => restrict (insert e L) l = ρ ∧
        PhiBal (insert e L) R (before ρ e).card (before l b)) := by
    apply filter_congr
    intro l hl
    constructor
    · rintro ⟨hr, hq⟩
      refine ⟨hr, ?_⟩
      rw [← hr, before_restrict (mem_insert_self _ _)]
      exact (qb_iff_phi heL hl he).1 hq
    · rintro ⟨hr, hq⟩
      refine ⟨hr, (qb_iff_phi heL hl he).2 ?_⟩
      rw [← hr, before_restrict (mem_insert_self _ _)] at hq
      exact hq
  rw [e1]
  have h := card_indep hMX (· = ρ)
    (fun l => PhiBal (insert e L) R (before ρ e).card (before l b))
    (fun u hu u' hu' l _ => phi_relab hbM hMR hu hu' _ l)
  rw [h, filter_eq']
  simp only [hρ, ↓reduceIte, card_singleton, one_mul]

/-! ## The count of the shifted condition does not depend on the rank -/

/-- Splitting the set before `b` into its parts in `M` and in `R`. -/
theorem sum_phi {X L R : Finset ℕ} {b e : ℕ} (hX : X.erase b = insert e L ∪ R)
    (hMR : Disjoint (insert e L) R) (f : ℕ → ℕ) (i : ℕ) :
    ∑ D ∈ (X.erase b).powerset.filter (PhiBal (insert e L) R i), f D.card =
      ∑ k ∈ range ((insert e L).card + 1), (insert e L).card.choose k *
        ∑ j ∈ range (R.card + 1), R.card.choose j *
          (if j + (if i < k then 1 else 0) = k then f (k + j) else 0) := by
  set M := insert e L with hMdef
  rw [sum_filter, hX, sum_powerset_union hMR]
  have step : ∀ B ∈ M.powerset, ∑ C ∈ R.powerset,
      (if PhiBal M R i (B ∪ C) then f (B ∪ C).card else 0) =
      ∑ C ∈ R.powerset, (if C.card + (if i < B.card then 1 else 0) = B.card
        then f (B.card + C.card) else 0) := by
    intro B hB
    apply sum_congr rfl
    intro C hC
    rw [mem_powerset] at hB hC
    have hBC : Disjoint B C := disjoint_of_subset_left hB (disjoint_of_subset_right hC hMR)
    have fM : (B ∪ C).filter (· ∈ M) = B := by
      rw [filter_union, filter_true_of_mem (fun x hx => hB hx),
        filter_false_of_mem (fun x hx h => disjoint_left.1 hMR h (hC hx)), union_empty]
    have fR : (B ∪ C).filter (· ∈ R) = C := by
      rw [filter_union, filter_false_of_mem (fun x hx h => disjoint_left.1 hMR (hB hx) h),
        filter_true_of_mem (fun x hx => hC hx), empty_union]
    have hp : PhiBal M R i (B ∪ C) ↔ C.card + (if i < B.card then 1 else 0) = B.card := by
      unfold PhiBal; rw [fM, fR]
    simp only [hp, card_union_of_disjoint hBC]
  rw [sum_congr rfl step]
  have h1 : ∀ B ∈ M.powerset, ∑ C ∈ R.powerset,
      (if C.card + (if i < B.card then 1 else 0) = B.card then f (B.card + C.card) else 0) =
      ∑ j ∈ range (R.card + 1), R.card.choose j *
        (if j + (if i < B.card then 1 else 0) = B.card then f (B.card + j) else 0) := by
    intro B _
    have := sum_powerset_apply_card
      (fun j => if j + (if i < B.card then 1 else 0) = B.card then f (B.card + j) else 0)
      (x := R)
    simpa only [nsmul_eq_mul, Nat.cast_id] using this
  rw [sum_congr rfl h1]
  have := sum_powerset_apply_card (fun k => ∑ j ∈ range (R.card + 1), R.card.choose j *
    (if j + (if i < k then 1 else 0) = k then f (k + j) else 0)) (x := M)
  simpa only [nsmul_eq_mul, Nat.cast_id] using this

theorem inner_phi (n i k : ℕ) (f : ℕ → ℕ) (hi : i ≤ n) (hk : k ≤ n + 1) :
    ∑ j ∈ range (n + 1), n.choose j *
        (if j + (if i < k then 1 else 0) = k then f (k + j) else 0) =
      if i < k then n.choose (k - 1) * f (2 * k - 1) else n.choose k * f (2 * k) := by
  by_cases h : i < k
  · simp only [h, ↓reduceIte]
    rw [sum_eq_single (k - 1)]
    · simp only [show k - 1 + 1 = k by omega, ↓reduceIte, show k + (k - 1) = 2 * k - 1 by omega]
    · intro j _ hj
      simp [show j + 1 ≠ k by omega]
    · intro hj; simp at hj; omega
  · simp only [h, ↓reduceIte, add_zero]
    rw [sum_eq_single k]
    · simp only [↓reduceIte, show k + k = 2 * k by omega]
    · intro j _ hj
      simp [hj]
    · intro hj; simp at hj; omega

/-- The factorial identity `T2(k) = T1(k-1)` of the paper proof. -/
theorem choose_factorial_shift {n k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) :
    n.choose k * ((2 * k)! * (2 * n + 1 - 2 * k)!) =
      n.choose (k - 1) * ((2 * k - 1)! * (2 * n + 1 - (2 * k - 1))!) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, n = m + 1 + t := ⟨n - m - 1, by omega⟩
  have hc := Nat.choose_succ_right_eq (m + 1 + t) m
  rw [show m + 1 + t - m = t + 1 by omega] at hc
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
    show 2 * (m + 1 + t) + 1 - (2 * m + 1 + 1) = 2 * t + 1 by omega,
    show m + 1 - 1 = m by omega, show 2 * m + 1 + 1 - 1 = 2 * m + 1 by omega,
    show 2 * (m + 1 + t) + 1 - (2 * m + 1) = 2 * t + 1 + 1 by omega,
    factorial_succ (2 * m + 1), factorial_succ (2 * t + 1)]
  calc (m + 1 + t).choose (m + 1) * ((2 * m + 1 + 1) * (2 * m + 1)! * (2 * t + 1)!)
      = 2 * ((m + 1 + t).choose (m + 1) * (m + 1)) * ((2 * m + 1)! * (2 * t + 1)!) := by ring
    _ = 2 * ((m + 1 + t).choose m * (t + 1)) * ((2 * m + 1)! * (2 * t + 1)!) := by rw [hc]
    _ = _ := by ring

/-- **Step 1.**  The number of orderings satisfying the shifted condition is the same for
every rank `i ≤ n` of the outside element. -/
theorem card_phi_eq {X L R : Finset ℕ} {b e n : ℕ} (hb : b ∈ X)
    (hX : X.erase b = insert e L ∪ R) (heL : e ∉ L) (hMR : Disjoint (insert e L) R)
    (hL : L.card = n) (hR : R.card = n) {i : ℕ} (hi : i ≤ n) :
    ((orderings X).filter (fun l => PhiBal (insert e L) R i (before l b))).card =
      ((orderings X).filter (fun l => PhiBal (insert e L) R 0 (before l b))).card := by
  have hM : (insert e L).card = n + 1 := by rw [card_insert_of_notMem heL, hL]
  have hXc : X.card = 2 * n + 2 := by
    have h := card_erase_of_mem hb
    rw [hX, card_union_of_disjoint hMR, hM, hR] at h
    have : 0 < X.card := card_pos.2 ⟨b, hb⟩
    omega
  have hs := fun i => sum_phi hX hMR (fun s => s ! * (2 * n + 2 - 1 - s)!) i
  rw [card_filter_before hb, card_filter_before hb, hXc, hs, hs, hM, hR]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  have h1 := inner_phi n i k (fun s => s ! * (2 * n + 2 - 1 - s)!) hi (by omega)
  have h2 := inner_phi n 0 k (fun s => s ! * (2 * n + 2 - 1 - s)!) (Nat.zero_le _) (by omega)
  rw [h1, h2]
  congr 1
  by_cases h : i < k
  · simp [h, show 0 < k by omega]
  · by_cases h0 : k = 0
    · subst h0; simp
    · simp only [h, show 0 < k by omega, ↓reduceIte]
      have := choose_factorial_shift (n := n) (k := k) (by omega) (by omega)
      rw [show 2 * n + 2 - 1 - 2 * k = 2 * n + 1 - 2 * k by omega,
        show 2 * n + 2 - 1 - (2 * k - 1) = 2 * n + 1 - (2 * k - 1) by omega]
      exact this

/-! ## Independence from the relative order on `M` -/

/-- Counting by the restriction to `A` when all fibres have the same size `c`. -/
theorem card_indep_of_fiber {X A : Finset ℕ} (hAX : A ⊆ X) (P Q : List ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (c : ℕ)
    (hc : ∀ u ∈ orderings A,
      ((orderings X).filter (fun l => restrict A l = u ∧ Q l)).card = c) :
    ((orderings X).filter (fun l => P (restrict A l) ∧ Q l)).card =
      ((orderings A).filter P).card * c := by
  rw [card_eq_sum_card_fiberwise (f := restrict A) (t := (orderings A).filter P)]
  · apply sum_const_nat
    intro u hu
    rw [mem_filter] at hu
    rw [← hc u hu.1, filter_filter]
    congr 1
    apply filter_congr
    intro l _
    constructor
    · rintro ⟨⟨_, hq⟩, hr⟩; exact ⟨hr, hq⟩
    · rintro ⟨hr, hq⟩; exact ⟨⟨hr ▸ hu.2, hq⟩, hr⟩
  · intro l hl
    simp only [coe_filter, Set.mem_ofPred_eq] at hl ⊢
    exact ⟨restrict_mem_orderings hAX hl.1, hl.2.1⟩

/-- **Independence with one outside element (abstract form).**  Let `X \ {b} = M ∪ R` with
`M = {e} ∪ L`, `e ∉ L`, `M ∩ R = ∅` and `|L| = |R|`.  Then the balance condition at `b`
between `L` and `R` is independent of every event of the relative order on `M`, although
it is not invariant under relabelling `M`. -/
theorem card_indep_qb {X L R : Finset ℕ} {b e : ℕ} (hb : b ∈ X)
    (hX : X.erase b = insert e L ∪ R) (heL : e ∉ L) (hMR : Disjoint (insert e L) R)
    (hLR : L.card = R.card) (P : List ℕ → Prop) [DecidablePred P] :
    ((orderings X).filter (fun l => P (restrict (insert e L) l) ∧ QB L R b l)).card *
        (insert e L).card ! =
      ((orderings (insert e L)).filter P).card * ((orderings X).filter (QB L R b)).card := by
  obtain ⟨hMX, -, -⟩ := setup_props hX
  set M := insert e L with hMdef
  set c := ((orderings X).filter
    (fun l => restrict M l = M.sort (· ≤ ·) ∧ QB L R b l)).card with hcdef
  have hfib : ∀ ρ ∈ orderings M,
      ((orderings X).filter (fun l => restrict M l = ρ ∧ QB L R b l)).card * M.card ! =
        ((orderings X).filter (fun l => PhiBal M R 0 (before l b))).card := by
    intro ρ hρ
    rw [card_fiber_qb hX heL hMR hρ]
    apply card_phi_eq hb hX heL hMR rfl hLR.symm
    have hsub : before ρ e ⊆ M.erase e := by
      intro x hx
      rw [mem_erase]
      refine ⟨fun h => not_mem_before_self ρ e (h ▸ hx), ?_⟩
      have := before_subset_toFinset ρ e hx
      rwa [(mem_orderings.1 hρ).2] at this
    have := card_le_card hsub
    rw [card_erase_of_mem (mem_insert_self _ _), card_insert_of_notMem heL] at this
    simpa using this
  have hc : ∀ ρ ∈ orderings M,
      ((orderings X).filter (fun l => restrict M l = ρ ∧ QB L R b l)).card = c := by
    intro ρ hρ
    apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos M.card)
    rw [hfib ρ hρ, hfib _ (sort_mem_orderings M)]
  have h1 := card_indep_of_fiber hMX P (QB L R b) c hc
  have h2 := card_indep_of_fiber hMX (fun _ => True) (QB L R b) c hc
  simp only [true_and, filter_true, card_orderings] at h2
  rw [h1, h2]; ring

end Folds
