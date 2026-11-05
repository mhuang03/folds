import Folds.Wallis

/-!
# Independence of single-panel constraints
-/

namespace Folds

open Finset Nat

/-! ## Relabelling the entries of one ordering by another -/

/-- `relab u u'` sends the `i`-th entry of `u` to the `i`-th entry of `u'` and fixes every
number that does not occur in `u`. -/
def relab (u u' : List ℕ) (x : ℕ) : ℕ := if x ∈ u then u'.getD (u.idxOf x) x else x

theorem relab_of_not_mem {u u' : List ℕ} {x : ℕ} (h : x ∉ u) : relab u u' x = x := by
  simp [relab, h]

theorem relab_getElem {u u' : List ℕ} (hu : u.Nodup) (hl : u.length = u'.length) (i : ℕ)
    (hi : i < u.length) : relab u u' u[i] = u'[i] := by
  simp [relab, List.getElem_mem, hu.idxOf_getElem i hi, hl ▸ hi]

theorem relab_mem {u u' : List ℕ} (hu : u.Nodup) (hl : u.length = u'.length) {x : ℕ}
    (hx : x ∈ u) : relab u u' x ∈ u' := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  rw [relab_getElem hu hl i hi]; exact List.getElem_mem _

theorem relab_relab {u u' : List ℕ} (hu : u.Nodup) (hu' : u'.Nodup) (hl : u.length = u'.length)
    (hmem : ∀ x, x ∈ u ↔ x ∈ u') (x : ℕ) : relab u' u (relab u u' x) = x := by
  by_cases hx : x ∈ u
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    rw [relab_getElem hu hl i hi, relab_getElem hu' hl.symm i (hl ▸ hi)]
  · rw [relab_of_not_mem hx, relab_of_not_mem (fun h => hx ((hmem x).2 h))]

theorem map_relab {u u' : List ℕ} (hu : u.Nodup) (hl : u.length = u'.length) :
    u.map (relab u u') = u' := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  rw [List.getElem_map, relab_getElem hu hl i (by simpa using h1)]

theorem relab_mem_iff {u u' : List ℕ} (hu : u.Nodup) (hl : u.length = u'.length)
    (hmem : ∀ x, x ∈ u ↔ x ∈ u') (x : ℕ) : relab u u' x ∈ u ↔ x ∈ u := by
  by_cases hx : x ∈ u
  · exact iff_of_true ((hmem _).2 (relab_mem hu hl hx)) hx
  · rw [relab_of_not_mem hx]

/-- Data about two orderings of the same finite set. -/
theorem orderings_data {A : Finset ℕ} {u u' : List ℕ} (hu : u ∈ orderings A)
    (hu' : u' ∈ orderings A) :
    u.Nodup ∧ u'.Nodup ∧ u.length = u'.length ∧ (∀ x, x ∈ u ↔ x ∈ u') ∧ (∀ x, x ∈ u ↔ x ∈ A) := by
  obtain ⟨h1, h2⟩ := mem_orderings.1 hu
  obtain ⟨h1', h2'⟩ := mem_orderings.1 hu'
  refine ⟨h1, h1', ?_, ?_, ?_⟩
  · rw [← List.toFinset_card_of_nodup h1, ← List.toFinset_card_of_nodup h1', h2, h2']
  · intro x; rw [← List.mem_toFinset, ← List.mem_toFinset (l := u'), h2, h2']
  · intro x; rw [← List.mem_toFinset, h2]

/-- The relabelling `relab u u'`, for two orderings of `A`, fixes the complement of `A`,
maps `A` to itself, and is undone by `relab u' u`. -/
theorem relab_props {A : Finset ℕ} {u u' : List ℕ} (hu : u ∈ orderings A)
    (hu' : u' ∈ orderings A) :
    (∀ x, x ∉ A → relab u u' x = x) ∧ (∀ x, relab u u' x ∈ A ↔ x ∈ A) ∧
      (∀ x, relab u' u (relab u u' x) = x) ∧ u.map (relab u u') = u' := by
  obtain ⟨h1, h1', hl, hmem, hA⟩ := orderings_data hu hu'
  refine ⟨fun x hx => relab_of_not_mem (fun h => hx ((hA x).1 h)), fun x => ?_,
    relab_relab h1 h1' hl hmem, map_relab h1 hl⟩
  rw [← hA, ← hA]; exact relab_mem_iff h1 hl hmem x

/-! ## Fibres of the restriction map have equal size -/

/-- The restriction of an ordering to the entries in `A`. -/
def restrict (A : Finset ℕ) (l : List ℕ) : List ℕ := l.filter fun x => decide (x ∈ A)

theorem restrict_mem_orderings {X A : Finset ℕ} (hAX : A ⊆ X) {l : List ℕ}
    (hl : l ∈ orderings X) : restrict A l ∈ orderings A := by
  obtain ⟨h1, h2⟩ := mem_orderings.1 hl
  refine mem_orderings.2 ⟨h1.filter _, ?_⟩
  ext x
  simp only [restrict, List.toFinset_filter, mem_filter, List.mem_toFinset, decide_eq_true_eq]
  rw [← List.mem_toFinset, h2]
  exact ⟨fun h => h.2, fun h => ⟨hAX h, h⟩⟩

theorem restrict_map {A : Finset ℕ} {g : ℕ → ℕ} (hg : ∀ x, g x ∈ A ↔ x ∈ A) (l : List ℕ) :
    restrict A (l.map g) = (restrict A l).map g := by
  unfold restrict
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp [hg]

/-- Relabelling an ordering of `X` along two orderings of `A ⊆ X`. -/
theorem map_relab_mem_orderings {X A : Finset ℕ} (hAX : A ⊆ X) {u u' : List ℕ}
    (hu : u ∈ orderings A) (hu' : u' ∈ orderings A) {l : List ℕ} (hl : l ∈ orderings X) :
    l.map (relab u u') ∈ orderings X := by
  obtain ⟨hfix, hA, hinv, -⟩ := relab_props hu hu'
  obtain ⟨hfix', hA', hinv', -⟩ := relab_props hu' hu
  obtain ⟨h1, h2⟩ := mem_orderings.1 hl
  have hinj : Function.Injective (relab u u') := Function.LeftInverse.injective hinv
  have hX : ∀ x, x ∈ X → relab u u' x ∈ X := by
    intro x hx
    by_cases h : x ∈ A
    · exact hAX ((hA x).2 h)
    · rw [hfix x h]; exact hx
  have hX' : ∀ x, x ∈ X → relab u' u x ∈ X := by
    intro x hx
    by_cases h : x ∈ A
    · exact hAX ((hA' x).2 h)
    · rw [hfix' x h]; exact hx
  refine mem_orderings.2 ⟨h1.map hinj, ?_⟩
  ext y
  simp only [List.mem_toFinset, List.mem_map]
  have hm : ∀ x, x ∈ l ↔ x ∈ X := fun x => by rw [← List.mem_toFinset, h2]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hX x ((hm x).1 hx)
  · intro hy; exact ⟨relab u' u y, (hm _).2 (hX' y hy), hinv' y⟩

/-- **Uniform fibres.**  If `Q` is invariant under relabelling the entries of `A`, then the
number of orderings `l` of `X` with `Q l` and a prescribed restriction to `A` does not depend
on that restriction. -/
theorem card_fiber_eq {X A : Finset ℕ} (hAX : A ⊆ X) (Q : List ℕ → Prop) [DecidablePred Q]
    (hQ : ∀ u ∈ orderings A, ∀ u' ∈ orderings A, ∀ l ∈ orderings X,
      Q (l.map (relab u u')) ↔ Q l)
    {u u' : List ℕ} (hu : u ∈ orderings A) (hu' : u' ∈ orderings A) :
    ((orderings X).filter (fun l => restrict A l = u ∧ Q l)).card =
      ((orderings X).filter (fun l => restrict A l = u' ∧ Q l)).card := by
  obtain ⟨-, hA, hinv, hmap⟩ := relab_props hu hu'
  obtain ⟨-, -, hinv', -⟩ := relab_props hu' hu
  apply card_nbij' (List.map (relab u u')) (List.map (relab u' u))
  · intro l hl
    simp only [coe_filter, Set.mem_ofPred_eq] at hl ⊢
    obtain ⟨hlX, hr, hq⟩ := hl
    refine ⟨map_relab_mem_orderings hAX hu hu' hlX, ?_, (hQ u hu u' hu' l hlX).2 hq⟩
    rw [restrict_map hA, hr, hmap]
  · intro l hl
    obtain ⟨-, hA', -, hmap'⟩ := relab_props hu' hu
    simp only [coe_filter, Set.mem_ofPred_eq] at hl ⊢
    obtain ⟨hlX, hr, hq⟩ := hl
    refine ⟨map_relab_mem_orderings hAX hu' hu hlX, ?_, (hQ u' hu' u hu l hlX).2 hq⟩
    rw [restrict_map hA', hr, hmap']
  · intro l _
    simp only [List.map_map]
    conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left (fun x _ => hinv x)
  · intro l _
    simp only [List.map_map]
    conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left (fun x _ => hinv' x)

theorem sort_mem_orderings (A : Finset ℕ) : A.sort (· ≤ ·) ∈ orderings A :=
  mem_orderings.2 ⟨sort_nodup _ _, sort_toFinset _ _⟩

/-- Counting by the restriction to `A`: every fibre has the size of the fibre over the sorted
ordering. -/
theorem card_filter_restrict {X A : Finset ℕ} (hAX : A ⊆ X) (P Q : List ℕ → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hQ : ∀ u ∈ orderings A, ∀ u' ∈ orderings A, ∀ l ∈ orderings X,
      Q (l.map (relab u u')) ↔ Q l) :
    ((orderings X).filter (fun l => P (restrict A l) ∧ Q l)).card =
      ((orderings A).filter P).card *
        ((orderings X).filter (fun l => restrict A l = A.sort (· ≤ ·) ∧ Q l)).card := by
  rw [card_eq_sum_card_fiberwise (f := restrict A) (t := (orderings A).filter P)]
  · rw [← Nat.cast_id (((orderings A).filter P).card), ← nsmul_eq_mul, ← sum_const]
    apply sum_congr rfl
    intro u hu
    rw [mem_filter] at hu
    rw [← card_fiber_eq hAX Q hQ hu.1 (sort_mem_orderings A), filter_filter]
    congr 1
    apply filter_congr
    intro l _
    constructor
    · rintro ⟨⟨_, hq⟩, hr⟩; exact ⟨hr, hq⟩
    · rintro ⟨hr, hq⟩; exact ⟨⟨hr ▸ hu.2, hq⟩, hr⟩
  · intro l hl
    simp only [coe_filter, Set.mem_ofPred_eq] at hl ⊢
    exact ⟨restrict_mem_orderings hAX hl.1, hl.2.1⟩

/-- **Independence lemma.**  Let `A ⊆ X` and let `Q` be a property of orderings of `X` that
is invariant under every relabelling of the entries of `A` among themselves.  Then for every
property `P` of orderings of `A`, the events "the restriction to `A` satisfies `P`" and `Q`
are independent under a uniformly random ordering of `X`. -/
theorem card_indep {X A : Finset ℕ} (hAX : A ⊆ X) (P Q : List ℕ → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hQ : ∀ u ∈ orderings A, ∀ u' ∈ orderings A, ∀ l ∈ orderings X,
      Q (l.map (relab u u')) ↔ Q l) :
    ((orderings X).filter (fun l => P (restrict A l) ∧ Q l)).card * A.card ! =
      ((orderings A).filter P).card * ((orderings X).filter Q).card := by
  have h1 := card_filter_restrict hAX P Q hQ
  have h2 := card_filter_restrict hAX (fun _ => True) Q hQ
  simp only [true_and, filter_true] at h2
  rw [card_orderings] at h2
  rw [h1, h2]; ring

/-- **Disjoint supports.**  For disjoint `A, B ⊆ X`, events determined by the relative orders
of the entries in `A` and in `B` are independent. -/
theorem card_indep_disjoint {X A B : Finset ℕ} (hAX : A ⊆ X) (hBX : B ⊆ X)
    (hAB : Disjoint A B) (P Q : List ℕ → Prop) [DecidablePred P] [DecidablePred Q] :
    ((orderings X).filter (fun l => P (restrict A l) ∧ Q (restrict B l))).card *
        A.card ! * B.card ! =
      X.card ! * ((orderings A).filter P).card * ((orderings B).filter Q).card := by
  have hQ : ∀ u ∈ orderings A, ∀ u' ∈ orderings A, ∀ l ∈ orderings X,
      Q (restrict B (l.map (relab u u'))) ↔ Q (restrict B l) := by
    intro u hu u' hu' l _
    obtain ⟨hfix, -, -, -⟩ := relab_props hu hu'
    have hB : ∀ x, relab u u' x ∈ B ↔ x ∈ B := by
      intro x
      by_cases hx : x ∈ A
      · have h1 : x ∉ B := disjoint_left.1 hAB hx
        have h2 : relab u u' x ∉ B := disjoint_left.1 hAB (((relab_props hu hu').2.1 x).2 hx)
        exact iff_of_false h2 h1
      · rw [hfix x hx]
    have e : (restrict B l).map (relab u u') = restrict B l := by
      conv_rhs => rw [← List.map_id (restrict B l)]
      apply List.map_congr_left
      intro x hx
      simp only [restrict, List.mem_filter, decide_eq_true_eq] at hx
      exact hfix x (disjoint_right.1 hAB hx.2)
    rw [restrict_map hB, e]
  have h1 := card_indep hAX P (fun l => Q (restrict B l)) hQ
  have h2 := card_indep hBX Q (fun _ => True) (fun _ _ _ _ _ _ => Iff.rfl)
  simp only [and_true, filter_true, card_orderings] at h2
  calc _ = ((orderings X).filter (fun l => P (restrict A l) ∧ Q (restrict B l))).card *
        A.card ! * B.card ! := rfl
    _ = ((orderings A).filter P).card *
        (((orderings X).filter fun l => Q (restrict B l)).card * B.card !) := by rw [← mul_assoc, ← h1]
    _ = _ := by rw [h2]; ring

/-! ## Windows and the step condition as a property of orderings -/

/-- The window `[m - r, m + r]` of panel `m`, with `r = reach N m`. -/
def window (N m : ℕ) : Finset ℕ := Icc (m - reach N m) (m + reach N m)

/-- The left arm `[m - r, m)` of the window of `m`. -/
def leftArm (N m : ℕ) : Finset ℕ := Ico (m - reach N m) m

/-- The right arm `(m, m + r]` of the window of `m`. -/
def rightArm (N m : ℕ) : Finset ℕ := Ioc m (m + reach N m)

/-- The step placing `m` in the ordering `l` is semi-symmetric. -/
def Cstep (N m : ℕ) (l : List ℕ) : Prop := BalancedBefore N m (before l m)

instance (N m : ℕ) : DecidablePred (Cstep N m) := fun l =>
  inferInstanceAs (Decidable (BalancedBefore N m (before l m)))

theorem before_cons (a m : ℕ) (l : List ℕ) :
    before (a :: l) m = if a = m then ∅ else insert a (before l m) := by
  by_cases h : a = m <;> simp [before, h]

theorem before_restrict {S : Finset ℕ} {m : ℕ} (hm : m ∈ S) (l : List ℕ) :
    before (restrict S l) m = (before l m).filter (· ∈ S) := by
  induction l with
  | nil => simp [restrict, before]
  | cons a l ih =>
    by_cases ha : a ∈ S
    · have e : restrict S (a :: l) = a :: restrict S l := by simp [restrict, ha]
      rw [e, before_cons, before_cons, ih]
      by_cases h : a = m
      · simp [h]
      · simp [h, filter_insert, ha]
    · have e : restrict S (a :: l) = restrict S l := by simp [restrict, ha]
      have h : a ≠ m := fun h => ha (h ▸ hm)
      rw [e, before_cons, ih]
      simp [h, filter_insert, ha]

theorem before_map {g : ℕ → ℕ} (hg : Function.Injective g) {m : ℕ} (hm : g m = m)
    (l : List ℕ) : before (l.map g) m = (before l m).image g := by
  induction l with
  | nil => simp [before]
  | cons a l ih =>
    rw [List.map_cons, before_cons, before_cons, ih]
    by_cases h : a = m
    · simp [h, hm]
    · have h' : g a ≠ m := fun e => h (hg (e.trans hm.symm))
      simp [h, h', image_insert]

theorem cstep_restrict {N m : ℕ} {S : Finset ℕ} (hS : window N m ⊆ S) (l : List ℕ) :
    Cstep N m (restrict S l) ↔ Cstep N m l := by
  have hm : m ∈ S := hS (by simp [window])
  unfold Cstep BalancedBefore
  rw [before_restrict hm, filter_filter, filter_filter]
  have hw : ∀ x, m - reach N m ≤ x → x ≤ m + reach N m → x ∈ S :=
    fun x h1 h2 => hS (by simp [window]; omega)
  have e1 : (before l m).filter (fun x => x ∈ S ∧ (m - reach N m ≤ x ∧ x < m)) =
      (before l m).filter (fun x => m - reach N m ≤ x ∧ x < m) :=
    filter_congr (fun x _ => ⟨fun h => h.2, fun h => ⟨hw x h.1 (by omega), h⟩⟩)
  have e2 : (before l m).filter (fun x => x ∈ S ∧ (m < x ∧ x ≤ m + reach N m)) =
      (before l m).filter (fun x => m < x ∧ x ≤ m + reach N m) :=
    filter_congr (fun x _ => ⟨fun h => h.2, fun h => ⟨hw x (by omega) h.2, h⟩⟩)
  rw [e1, e2]

/-- The relabelling of `A` preserves membership in `T` when `A ⊆ T` or `A` misses `T`. -/
theorem relab_mem_of_sub_or_disj {A T : Finset ℕ} {u u' : List ℕ} (hu : u ∈ orderings A)
    (hu' : u' ∈ orderings A) (hT : A ⊆ T ∨ Disjoint A T) (x : ℕ) :
    relab u u' x ∈ T ↔ x ∈ T := by
  obtain ⟨hfix, hA, -, -⟩ := relab_props hu hu'
  by_cases hx : x ∈ A
  · have hx' := (hA x).2 hx
    rcases hT with hT | hT
    · exact iff_of_true (hT hx') (hT hx)
    · exact iff_of_false (disjoint_left.1 hT hx') (disjoint_left.1 hT hx)
  · rw [hfix x hx]

/-- `A` is *compatible* with panel `b`: `b ∉ A`, and `A` lies inside or misses each arm of `b`.
Then the constraint at `b` cannot tell the entries of `A` apart. -/
def Compat (N : ℕ) (A : Finset ℕ) (b : ℕ) : Prop :=
  b ∉ A ∧ (A ⊆ leftArm N b ∨ Disjoint A (leftArm N b)) ∧
    (A ⊆ rightArm N b ∨ Disjoint A (rightArm N b))

theorem cstep_relab {N b : ℕ} {A : Finset ℕ} (hc : Compat N A b) {u u' : List ℕ}
    (hu : u ∈ orderings A) (hu' : u' ∈ orderings A) (l : List ℕ) :
    Cstep N b (l.map (relab u u')) ↔ Cstep N b l := by
  obtain ⟨hfix, -, hinv, -⟩ := relab_props hu hu'
  have hinj : Function.Injective (relab u u') := Function.LeftInverse.injective hinv
  unfold Cstep BalancedBefore
  rw [before_map hinj (hfix b hc.1), filter_image, filter_image,
    card_image_of_injective _ hinj, card_image_of_injective _ hinj]
  have hL := relab_mem_of_sub_or_disj hu hu' hc.2.1
  have hR := relab_mem_of_sub_or_disj hu hu' hc.2.2
  simp only [leftArm, rightArm, mem_Ico, mem_Ioc] at hL hR
  simp only [hL, hR]

/-! ## Counting sequences satisfying a set of constraints -/

/-- Fold sequences of length `N` in which the step placing each panel of `F` is
semi-symmetric. -/
def constrSeqs (N : ℕ) (F : Finset ℕ) : Finset (List ℕ) :=
  (List.range' 1 N).permutations.toFinset.filter fun a =>
    ∀ m ∈ F, SemiStep N (a.take (a.idxOf m)) m

theorem constrSeqs_eq {N : ℕ} {F : Finset ℕ} :
    constrSeqs N F = (orderings (Icc 1 N)).filter fun l => ∀ m ∈ F, Cstep N m l := by
  ext a
  rw [constrSeqs, mem_filter, mem_filter, List.mem_toFinset, List.mem_permutations]
  have e : a.Perm (List.range' 1 N) ↔ a ∈ orderings (Icc 1 N) := by
    rw [mem_orderings, ← isFoldSeq_iff]; rfl
  rw [e]
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨h, fun m hm =>
      (semiStep_iff_balanced (take_nodup (mem_orderings.1 h).1 _)).1 (hs m hm)⟩
  · rintro ⟨h, hs⟩
    exact ⟨h, fun m hm =>
      (semiStep_iff_balanced (take_nodup (mem_orderings.1 h).1 _)).2 (hs m hm)⟩

theorem window_subset {N m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ N) : window N m ⊆ Icc 1 N := by
  intro x hx
  simp only [window, mem_Icc] at hx ⊢
  unfold reach at hx; omega

theorem card_window (N m : ℕ) : (window N m).card = 2 * reach N m + 1 := by
  rw [window, Nat.card_Icc]
  have : reach N m ≤ m := by unfold reach; omega
  omega

/-- The single constraint, counted on the orderings of its own window. -/
theorem card_window_orderings {N m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ N) :
    ((orderings (window N m)).filter (Cstep N m)).card = 4 ^ reach N m * (reach N m)! ^ 2 := by
  have h := card_indep (window_subset h1 h2) (Cstep N m) (fun _ => True)
    (fun _ _ _ _ _ _ => Iff.rfl)
  simp only [and_true, filter_true, card_orderings, Nat.card_Icc, card_window] at h
  simp only [cstep_restrict (subset_refl _)] at h
  have hw := card_wallisSeqs h1 h2
  rw [wallisSeqs_eq] at hw
  change ((orderings (Icc 1 N)).filter (Cstep N m)).card * _ = _ at hw
  rw [hw, Nat.add_sub_cancel] at h
  have hpos : 0 < N ! := Nat.factorial_pos N
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← h]; ring

end Folds
