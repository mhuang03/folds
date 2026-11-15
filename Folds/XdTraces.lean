import Folds.Congruence

/-!
# Partial commutation: swap classes (traces) of semi-symmetric sequences

Cross-domain angle "Cartier–Foata traces / heaps of pieces / weak order"
(`experiments/xd_traces/NOTES.txt`).

`InWindow N m x`: panel `x` lies in the window of `m` (`x ≠ m`, `|x - m| ≤ reach N m`).
`Indep N x y`: each of `x`, `y` lies outside the other's window.  This is a **fixed**
(context-free) independence relation on panels.

Main results.

* `swap_step_iff` (**exact swap criterion**, step level): if `(S, m)` and `(S ∪ {m}, m')` are
  valid steps, then `(S, m')` and `(S ∪ {m'}, m)` are both valid iff `m'` is outside the
  window of `m` and `m` is outside the window of `m'`.  There is no "compensation" case:
  `not_semiStep_cons_of_inWindow` (a panel entering the window breaks a valid step) and
  `semiStep_cons_of_not_inWindow` (a panel outside the window is irrelevant).
* `semiSymmetric_swap_iff` (sequence level): exchanging two adjacent entries `m, m'` of a
  semi-symmetric sequence gives a semi-symmetric sequence iff `m, m'` are independent; no
  later step is affected.
* `indep_iff`: for `1 ≤ x < y ≤ N`, `Indep N x y ↔ 2x ≤ y ∧ x + N + 1 ≤ 2y`.  Hence
  independent panels lie in opposite halves (`Indep.left_right`), and independence is an
  upper set for interval inclusion (`Indep.widen`) – the condition under which the trace
  equivalence is a lattice congruence of the weak order.
* `SwapStep`, `SwapEquiv`: one valid swap, and the equivalence relation generated.
  `SwapEquiv.mem_semiSeqs_iff` (classes stay inside the semi-symmetric sequences),
  `SwapEquiv.reverse`, `SwapEquiv.mirror` (compatibility with reversal and mirror),
  `SwapEquiv.filter_left`, `SwapEquiv.filter_right` (the order of the left-half panels and
  the order of the right-half panels are constant on a class: every class is a set of
  shuffles of two fixed words).
* `semiCount_eq_sum_swapClasses`: `a(N) = ∑_{classes c} |c|`.
* **Order-convexity in the weak order.**  `WeakLE a b`: every inversion of `a` is an inversion
  of `b`.  `before_iff_of_weakLE`: two semi-symmetric fold sequences with `WeakLE a b` order
  every pair `(x, m)`, `x` in the window of `m`, in the same way.
  `semiSymmetric_of_weak_between`: a fold sequence weakly between two semi-symmetric fold
  sequences is semi-symmetric.
* `Rigid`, `hasSwap`: sequences without a valid swap; `not_rigid_small`: there is none for
  `2 ≤ N ≤ 8` (kernel-checked search `allExt`; numerically none for `N ≤ 22`).
-/

namespace Folds

/-! ## Counting lemmas -/

theorem countP_lt_countP_of {α : Type*} {p q : α → Bool} {l : List α}
    (h : ∀ x ∈ l, p x = true → q x = true) (hx : ∃ x ∈ l, q x = true ∧ p x = false) :
    l.countP p < l.countP q := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    obtain ⟨x, hxm, hq, hp⟩ := hx
    have hmono : t.countP p ≤ t.countP q :=
      List.countP_mono_left fun y hy => h y (List.mem_cons_of_mem _ hy)
    have ha := h a (by simp)
    have key : t.countP p < t.countP q ∨ (p a = false ∧ q a = true) := by
      rcases List.mem_cons.1 hxm with rfl | hxt
      · exact Or.inr ⟨hp, hq⟩
      · exact Or.inl (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) ⟨x, hxt, hq, hp⟩)
    by_cases hpa : p a = true
    · rw [List.countP_cons_of_pos hpa, List.countP_cons_of_pos (ha hpa)]
      have : t.countP p < t.countP q :=
        key.resolve_right fun ⟨h', _⟩ => by rw [hpa] at h'; cases h'
      omega
    · by_cases hqa : q a = true
      · rw [List.countP_cons_of_neg hpa, List.countP_cons_of_pos hqa]; omega
      · rw [List.countP_cons_of_neg hpa, List.countP_cons_of_neg hqa]
        exact key.resolve_right fun ⟨_, h'⟩ => hqa h'

theorem countP_eq_imp {α : Type*} {p q : α → Bool} {l : List α}
    (h : ∀ x ∈ l, p x = true → q x = true) (he : l.countP p = l.countP q) :
    ∀ x ∈ l, q x = true → p x = true := by
  intro x hx hq
  by_contra hp
  have := countP_lt_countP_of h ⟨x, hx, hq, by simpa using hp⟩
  omega

/-! ## Windows and independence -/

/-- `x` lies in the window of `m`: `x ≠ m` and `|x - m| ≤ reach N m`. -/
def InWindow (N m x : ℕ) : Prop := x ≠ m ∧ m ≤ x + reach N m ∧ x ≤ m + reach N m

instance (N m x : ℕ) : Decidable (InWindow N m x) := by unfold InWindow; infer_instance

/-- Two panels are *independent* if each lies outside the window of the other. -/
def Indep (N x y : ℕ) : Prop := x ≠ y ∧ ¬ InWindow N x y ∧ ¬ InWindow N y x

instance (N x y : ℕ) : Decidable (Indep N x y) := by unfold Indep; infer_instance

theorem Indep.symm {N x y : ℕ} (h : Indep N x y) : Indep N y x :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

theorem indep_comm {N x y : ℕ} : Indep N x y ↔ Indep N y x := ⟨Indep.symm, Indep.symm⟩

theorem inWindow_iff_exists {N m x : ℕ} :
    InWindow N m x ↔ ∃ d, 1 ≤ d ∧ d ≤ reach N m ∧ (x = m - d ∨ x = m + d) := by
  unfold InWindow
  constructor
  · rintro ⟨hne, h1, h2⟩
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨m - x, by omega, by omega, Or.inl (by omega)⟩
    · exact ⟨x - m, by omega, by omega, Or.inr (by omega)⟩
  · rintro ⟨d, hd1, hd2, rfl | rfl⟩
    · refine ⟨?_, by omega, by omega⟩
      unfold reach at hd2; omega
    · exact ⟨by omega, by omega, by omega⟩

/-- **Independence, explicitly.**  For `1 ≤ x < y ≤ N`: `x, y` are independent iff
`2x ≤ y` and `x + N + 1 ≤ 2y`. -/
theorem indep_iff {N x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hy : y ≤ N) :
    Indep N x y ↔ 2 * x ≤ y ∧ x + N + 1 ≤ 2 * y := by
  unfold Indep InWindow reach
  omega

/-- Independent panels lie in opposite halves of the strip. -/
theorem Indep.left_right {N x y : ℕ} (h : Indep N x y) (hx : 1 ≤ x) (hxy : x < y) (hy : y ≤ N) :
    2 * x ≤ N ∧ N < 2 * y := by
  have := (indep_iff hx hxy hy).1 h
  omega

/-- Independence is an upper set for inclusion of the interval `[x, y]`. -/
theorem Indep.widen {N x y x' y' : ℕ} (h : Indep N x y) (hx' : 1 ≤ x') (h1 : x' ≤ x)
    (hxy : x < y) (h2 : y ≤ y') (hy' : y' ≤ N) : Indep N x' y' := by
  have := (indep_iff (by omega) hxy (by omega)).1 h
  exact (indep_iff hx' (by omega) hy').2 (by omega)

theorem inWindow_mirror {N m x : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ N) (hx1 : 1 ≤ x) (hx : x ≤ N) :
    InWindow N (N + 1 - m) (N + 1 - x) ↔ InWindow N m x := by
  unfold InWindow reach
  omega

theorem indep_mirror {N x y : ℕ} (hx1 : 1 ≤ x) (hx : x ≤ N) (hy1 : 1 ≤ y) (hy : y ≤ N) :
    Indep N (N + 1 - x) (N + 1 - y) ↔ Indep N x y := by
  unfold Indep
  rw [inWindow_mirror hx1 hx hy1 hy, inWindow_mirror hy1 hy hx1 hx]
  constructor
  · rintro ⟨h, h'⟩; exact ⟨fun e => h (by rw [e]), h'⟩
  · rintro ⟨h, h'⟩; exact ⟨by omega, h'⟩

/-! ## The step condition and the window -/

/-- The step condition at `m` depends only on which panels of the window of `m` are placed. -/
theorem semiStep_congr_window {N m : ℕ} {S T : List ℕ}
    (h : ∀ x, InWindow N m x → (x ∈ S ↔ x ∈ T)) : SemiStep N S m ↔ SemiStep N T m := by
  have hl : leftCount N S m = leftCount N T m := by
    unfold leftCount; apply List.countP_congr; intro d hd; rw [List.mem_range'_1] at hd
    simpa using h (m - d) (inWindow_iff_exists.2 ⟨d, by omega, by omega, Or.inl rfl⟩)
  have hr : rightCount N S m = rightCount N T m := by
    unfold rightCount; apply List.countP_congr; intro d hd; rw [List.mem_range'_1] at hd
    simpa using h (m + d) (inWindow_iff_exists.2 ⟨d, by omega, by omega, Or.inr rfl⟩)
  unfold SemiStep; rw [hl, hr]

/-- A panel outside the window of `m` is irrelevant for the step at `m`. -/
theorem semiStep_cons_of_not_inWindow {N m x : ℕ} {S : List ℕ} (hx : ¬ InWindow N m x) :
    SemiStep N (x :: S) m ↔ SemiStep N S m := by
  apply semiStep_congr_window
  intro y hy
  have : y ≠ x := fun e => hx (e ▸ hy)
  simp [this]

/-- A new panel inside the window of `m` destroys a valid step at `m`. -/
theorem not_semiStep_cons_of_inWindow {N m x : ℕ} {S : List ℕ} (hx : InWindow N m x)
    (hxS : x ∉ S) (h : SemiStep N S m) : ¬ SemiStep N (x :: S) m := by
  obtain ⟨hne, h1, h2⟩ := hx
  unfold SemiStep at h ⊢
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- `x` is on the left: the left count grows, the right count does not change
    have hr : rightCount N (x :: S) m = rightCount N S m := by
      unfold rightCount; apply List.countP_congr; intro d hd
      have : m + d ≠ x := by omega
      simp [this]
    have hl : leftCount N S m < leftCount N (x :: S) m := by
      unfold leftCount
      apply countP_lt_countP_of
      · intro d _ hd; simp only [decide_eq_true_eq] at hd ⊢; exact List.mem_cons_of_mem _ hd
      · refine ⟨m - x, by rw [List.mem_range'_1]; omega, ?_, ?_⟩
        · have : m - (m - x) = x := by omega
          simp [this]
        · have : m - (m - x) = x := by omega
          simp [this, hxS]
    omega
  · have hl : leftCount N (x :: S) m = leftCount N S m := by
      unfold leftCount; apply List.countP_congr; intro d hd; rw [List.mem_range'_1] at hd
      have : m - d ≠ x := by omega
      simp [this]
    have hr : rightCount N S m < rightCount N (x :: S) m := by
      unfold rightCount
      apply countP_lt_countP_of
      · intro d _ hd; simp only [decide_eq_true_eq] at hd ⊢; exact List.mem_cons_of_mem _ hd
      · refine ⟨x - m, by rw [List.mem_range'_1]; omega, ?_, ?_⟩
        · have : m + (x - m) = x := by omega
          simp [this]
        · have : m + (x - m) = x := by omega
          simp [this, hxS]
    omega

/-- **Exact swap criterion (step level).**  Let `(S, m)` and `(S ∪ {m}, m')` be valid steps.
The two steps can be exchanged (both `(S, m')` and `(S ∪ {m'}, m)` are valid) iff `m'` lies
outside the window of `m` and `m` lies outside the window of `m'`. -/
theorem swap_step_iff {N m m' : ℕ} {S : List ℕ} (hm : m ∉ S) (hm' : m' ∉ S)
    (h1 : SemiStep N S m) (h2 : SemiStep N (m :: S) m') :
    (SemiStep N S m' ∧ SemiStep N (m' :: S) m) ↔ (¬ InWindow N m m' ∧ ¬ InWindow N m' m) := by
  constructor
  · rintro ⟨g1, g2⟩
    exact ⟨fun hw => not_semiStep_cons_of_inWindow hw hm' h1 g2,
      fun hw => not_semiStep_cons_of_inWindow hw hm g1 h2⟩
  · rintro ⟨g1, g2⟩
    exact ⟨(semiStep_cons_of_not_inWindow g2).1 h2, (semiStep_cons_of_not_inWindow g1).2 h1⟩

/-- The same without assuming that the first order is valid: both orders of `m, m'` after `S`
are valid iff both panels are valid after `S` and each lies outside the other's window. -/
theorem both_orders_iff {N m m' : ℕ} {S : List ℕ} (hm : m ∉ S) (hm' : m' ∉ S) :
    (SemiStep N S m ∧ SemiStep N (m :: S) m' ∧ SemiStep N S m' ∧ SemiStep N (m' :: S) m) ↔
      (SemiStep N S m ∧ SemiStep N S m' ∧ ¬ InWindow N m m' ∧ ¬ InWindow N m' m) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h3, (swap_step_iff hm hm' h1 h2).1 ⟨h3, h4⟩⟩
  · rintro ⟨h1, h3, g1, g2⟩
    exact ⟨h1, (semiStep_cons_of_not_inWindow g2).2 h3, h3,
      (semiStep_cons_of_not_inWindow g1).2 h1⟩

/-! ## Swapping two adjacent entries of a sequence -/

theorem semiSymmetric_two_iff {N m m' : ℕ} {u v : List ℕ} :
    SemiSymmetric N (u ++ m :: m' :: v) ↔
      SemiSymmetric N u ∧ SemiStep N u m ∧ SemiStep N (m :: u) m' ∧
        ∀ k (hk : k < v.length), SemiStep N (m :: m' :: (u ++ v.take k)) v[k] := by
  have e1 : ∀ x, x ∈ u ++ [m] ↔ x ∈ m :: u := by intro x; simp [or_comm]
  have e2 : ∀ k x, x ∈ u ++ m :: m' :: v.take k ↔ x ∈ m :: m' :: (u ++ v.take k) := by
    intro k x; simp only [List.mem_append, List.mem_cons]; tauto
  have e0 : ∀ x, x ∈ u ++ List.take 0 (m :: m' :: v) ↔ x ∈ u := by intro x; simp
  rw [semiSymmetric_append_iff]
  constructor
  · rintro ⟨hu, hB⟩
    refine ⟨hu, ?_, ?_, fun k hk => ?_⟩
    · exact (semiStep_congr e0).1 (hB 0 (by simp))
    · exact (semiStep_congr e1).1 (hB 1 (by simp))
    · exact (semiStep_congr (e2 k)).1 (hB (k + 2) (by simp; omega))
  · rintro ⟨hu, h0, h1, hv⟩
    refine ⟨hu, fun k hk => ?_⟩
    match k, hk with
    | 0, _ => exact (semiStep_congr e0).2 h0
    | 1, _ => exact (semiStep_congr e1).2 h1
    | k + 2, hk => exact (semiStep_congr (e2 k)).2 (hv k (by simpa using hk))

/-- **Exact swap criterion (sequence level).**  Exchanging two adjacent entries `m, m'` of a
semi-symmetric sequence gives a semi-symmetric sequence iff each of the two panels lies
outside the window of the other.  (All later steps are unaffected, because validity of a
step depends only on the *set* of earlier panels.) -/
theorem semiSymmetric_swap_iff {N m m' : ℕ} {u v : List ℕ} (hm : m ∉ u) (hm' : m' ∉ u)
    (h : SemiSymmetric N (u ++ m :: m' :: v)) :
    SemiSymmetric N (u ++ m' :: m :: v) ↔ (¬ InWindow N m m' ∧ ¬ InWindow N m' m) := by
  rw [semiSymmetric_two_iff] at h ⊢
  obtain ⟨hu, h1, h2, hv⟩ := h
  have e : ∀ k x, x ∈ m' :: m :: (u ++ v.take k) ↔ x ∈ m :: m' :: (u ++ v.take k) := by
    intro k x; simp only [List.mem_cons]; tauto
  constructor
  · rintro ⟨-, g1, g2, -⟩
    exact (swap_step_iff hm hm' h1 h2).1 ⟨g1, g2⟩
  · intro hI
    obtain ⟨g1, g2⟩ := (swap_step_iff hm hm' h1 h2).2 hI
    exact ⟨hu, g1, g2, fun k hk => (semiStep_congr (e k)).2 (hv k hk)⟩

/-! ## The swap relation and its classes -/

/-- One valid swap: exchange two adjacent independent entries. -/
inductive SwapStep (N : ℕ) : List ℕ → List ℕ → Prop
  | mk (u v : List ℕ) (m m' : ℕ) (h : Indep N m m') :
      SwapStep N (u ++ m :: m' :: v) (u ++ m' :: m :: v)

theorem SwapStep.symm {N : ℕ} {a b : List ℕ} (h : SwapStep N a b) : SwapStep N b a := by
  obtain ⟨u, v, m, m', hI⟩ := h
  exact SwapStep.mk u v m' m hI.symm

theorem SwapStep.perm {N : ℕ} {a b : List ℕ} (h : SwapStep N a b) : a.Perm b := by
  obtain ⟨u, v, m, m', hI⟩ := h
  exact List.Perm.append_left u (List.Perm.swap m' m v)

theorem SwapStep.isFoldSeq {N : ℕ} {a b : List ℕ} (h : SwapStep N a b) (ha : IsFoldSeq N a) :
    IsFoldSeq N b :=
  h.perm.symm.trans ha

/-- A valid swap preserves semi-symmetry of the whole sequence. -/
theorem SwapStep.semiSymmetric {N : ℕ} {a b : List ℕ} (h : SwapStep N a b) (hnd : a.Nodup)
    (ha : SemiSymmetric N a) : SemiSymmetric N b := by
  obtain ⟨u, v, m, m', hI⟩ := h
  have hd := (List.nodup_append.1 hnd).2.2
  have hm : m ∉ u := fun hmu => hd m hmu m (by simp) rfl
  have hm' : m' ∉ u := fun hmu => hd m' hmu m' (by simp) rfl
  exact (semiSymmetric_swap_iff hm hm' ha).2 hI.2

theorem SwapStep.mem_semiSeqs {N : ℕ} {a b : List ℕ} (h : SwapStep N a b)
    (ha : a ∈ semiSeqs N) : b ∈ semiSeqs N := by
  rw [Folds.mem_semiSeqs] at ha ⊢
  exact ⟨h.isFoldSeq ha.1, h.semiSymmetric (nodup_of_foldSeq ha.1) ha.2⟩

/-- Converse: an exchange of adjacent entries that stays semi-symmetric is a valid swap. -/
theorem swapStep_of_semiSymmetric {N m m' : ℕ} {u v : List ℕ}
    (hnd : (u ++ m :: m' :: v).Nodup) (h : SemiSymmetric N (u ++ m :: m' :: v))
    (h' : SemiSymmetric N (u ++ m' :: m :: v)) :
    SwapStep N (u ++ m :: m' :: v) (u ++ m' :: m :: v) := by
  have hd := (List.nodup_append.1 hnd).2.2
  have hm : m ∉ u := fun hmu => hd m hmu m (by simp) rfl
  have hm' : m' ∉ u := fun hmu => hd m' hmu m' (by simp) rfl
  have hne : m ≠ m' := by
    have := (List.nodup_append.1 hnd).2.1
    rw [List.nodup_cons] at this
    intro e; exact this.1 (by simp [e])
  exact SwapStep.mk u v m m' ⟨hne, (semiSymmetric_swap_iff hm hm' h).1 h'⟩

theorem SwapStep.reverse {N : ℕ} {a b : List ℕ} (h : SwapStep N a b) :
    SwapStep N a.reverse b.reverse := by
  obtain ⟨u, v, m, m', hI⟩ := h
  have e1 : (u ++ m :: m' :: v).reverse = v.reverse ++ m' :: m :: u.reverse := by simp
  have e2 : (u ++ m' :: m :: v).reverse = v.reverse ++ m :: m' :: u.reverse := by simp
  rw [e1, e2]
  exact SwapStep.mk _ _ m' m hI.symm

theorem SwapStep.mirror {N : ℕ} {a b : List ℕ} (h : SwapStep N a b) (ha : IsFoldSeq N a) :
    SwapStep N (mirror N a) (mirror N b) := by
  obtain ⟨u, v, m, m', hI⟩ := h
  have bm := (mem_range'_of_perm ha (x := m)).1 (by simp)
  have bm' := (mem_range'_of_perm ha (x := m')).1 (by simp)
  have e1 : Folds.mirror N (u ++ m :: m' :: v) =
      Folds.mirror N u ++ (N + 1 - m) :: (N + 1 - m') :: Folds.mirror N v := by
    simp [Folds.mirror]
  have e2 : Folds.mirror N (u ++ m' :: m :: v) =
      Folds.mirror N u ++ (N + 1 - m') :: (N + 1 - m) :: Folds.mirror N v := by
    simp [Folds.mirror]
  rw [e1, e2]
  exact SwapStep.mk _ _ _ _ ((indep_mirror bm.1 bm.2 bm'.1 bm'.2).2 hI)

theorem filter_swap {p : ℕ → Bool} {m m' : ℕ} (u v : List ℕ)
    (h : ¬ (p m = true ∧ p m' = true)) :
    (u ++ m :: m' :: v).filter p = (u ++ m' :: m :: v).filter p := by
  simp only [List.filter_append, List.filter_cons]
  by_cases h1 : p m = true <;> by_cases h2 : p m' = true <;> simp_all

/-- A valid swap does not change the order of the left-half panels … -/
theorem SwapStep.filter_left {N : ℕ} {a b : List ℕ} (h : SwapStep N a b) (ha : IsFoldSeq N a) :
    a.filter (fun x => decide (2 * x ≤ N)) = b.filter (fun x => decide (2 * x ≤ N)) := by
  obtain ⟨u, v, m, m', hI⟩ := h
  have bm := (mem_range'_of_perm ha (x := m)).1 (by simp)
  have bm' := (mem_range'_of_perm ha (x := m')).1 (by simp)
  apply filter_swap
  simp only [decide_eq_true_eq]
  rcases Nat.lt_or_gt_of_ne hI.1 with hlt | hgt
  · have := hI.left_right bm.1 hlt bm'.2; omega
  · have := hI.symm.left_right bm'.1 hgt bm.2; omega

/-- … nor the order of the right-half panels. -/
theorem SwapStep.filter_right {N : ℕ} {a b : List ℕ} (h : SwapStep N a b) (ha : IsFoldSeq N a) :
    a.filter (fun x => decide (N < 2 * x)) = b.filter (fun x => decide (N < 2 * x)) := by
  obtain ⟨u, v, m, m', hI⟩ := h
  have bm := (mem_range'_of_perm ha (x := m)).1 (by simp)
  have bm' := (mem_range'_of_perm ha (x := m')).1 (by simp)
  apply filter_swap
  simp only [decide_eq_true_eq]
  rcases Nat.lt_or_gt_of_ne hI.1 with hlt | hgt
  · have := hI.left_right bm.1 hlt bm'.2; omega
  · have := hI.symm.left_right bm'.1 hgt bm.2; omega

/-- The equivalence relation generated by valid swaps ("same trace"). -/
def SwapEquiv (N : ℕ) : List ℕ → List ℕ → Prop := Relation.EqvGen (SwapStep N)

theorem swapEquiv_equivalence (N : ℕ) : Equivalence (SwapEquiv N) :=
  Relation.EqvGen.is_equivalence _

theorem SwapEquiv.refl {N : ℕ} (a : List ℕ) : SwapEquiv N a a := Relation.EqvGen.refl a

theorem SwapEquiv.symm {N : ℕ} {a b : List ℕ} (h : SwapEquiv N a b) : SwapEquiv N b a :=
  Relation.EqvGen.symm _ _ h

theorem SwapEquiv.trans {N : ℕ} {a b c : List ℕ} (h : SwapEquiv N a b) (h' : SwapEquiv N b c) :
    SwapEquiv N a c :=
  Relation.EqvGen.trans _ _ _ h h'

/-- Induction principle for swap-equivalent *fold sequences*. -/
theorem SwapEquiv.induction_foldSeq {N : ℕ} {P : List ℕ → List ℕ → Prop}
    (hrel : ∀ a b, IsFoldSeq N a → SwapStep N a b → P a b) (hrefl : ∀ a, P a a)
    (hsymm : ∀ a b, P a b → P b a) (htrans : ∀ a b c, P a b → P b c → P a c)
    {a b : List ℕ} (h : SwapEquiv N a b) :
    (IsFoldSeq N a ↔ IsFoldSeq N b) ∧ (IsFoldSeq N a → P a b) := by
  induction h with
  | rel x y h => exact ⟨⟨h.isFoldSeq, h.symm.isFoldSeq⟩, fun hx => hrel x y hx h⟩
  | refl x => exact ⟨Iff.rfl, fun _ => hrefl x⟩
  | symm x y _ ih => exact ⟨ih.1.symm, fun hy => hsymm _ _ (ih.2 (ih.1.2 hy))⟩
  | trans x y z _ _ ih1 ih2 =>
    exact ⟨ih1.1.trans ih2.1, fun hx => htrans _ _ _ (ih1.2 hx) (ih2.2 (ih1.1.1 hx))⟩

theorem SwapEquiv.isFoldSeq_iff {N : ℕ} {a b : List ℕ} (h : SwapEquiv N a b) :
    IsFoldSeq N a ↔ IsFoldSeq N b :=
  (SwapEquiv.induction_foldSeq (P := fun _ _ => True) (fun _ _ _ _ => trivial)
    (fun _ => trivial) (fun _ _ _ => trivial) (fun _ _ _ _ _ => trivial) h).1

/-- **Swap classes stay inside the semi-symmetric sequences.** -/
theorem SwapEquiv.mem_semiSeqs_iff {N : ℕ} {a b : List ℕ} (h : SwapEquiv N a b) :
    a ∈ semiSeqs N ↔ b ∈ semiSeqs N := by
  induction h with
  | rel x y h => exact ⟨h.mem_semiSeqs, h.symm.mem_semiSeqs⟩
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Compatibility with reversal.** -/
theorem SwapEquiv.reverse {N : ℕ} {a b : List ℕ} (h : SwapEquiv N a b) :
    SwapEquiv N a.reverse b.reverse := by
  induction h with
  | rel x y h => exact Relation.EqvGen.rel _ _ h.reverse
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- **Compatibility with the mirror `m ↦ N + 1 - m`.** -/
theorem SwapEquiv.mirror {N : ℕ} {a b : List ℕ} (h : SwapEquiv N a b) (ha : IsFoldSeq N a) :
    SwapEquiv N (mirror N a) (mirror N b) :=
  (SwapEquiv.induction_foldSeq (P := fun a b => SwapEquiv N (Folds.mirror N a) (Folds.mirror N b))
    (fun _ _ hx hs => Relation.EqvGen.rel _ _ (hs.mirror hx)) (fun _ => Relation.EqvGen.refl _)
    (fun _ _ h => Relation.EqvGen.symm _ _ h) (fun _ _ _ h h' => Relation.EqvGen.trans _ _ _ h h')
    h).2 ha

/-- **The left-half word is a class invariant.** -/
theorem SwapEquiv.filter_left {N : ℕ} {a b : List ℕ} (h : SwapEquiv N a b) (ha : IsFoldSeq N a) :
    a.filter (fun x => decide (2 * x ≤ N)) = b.filter (fun x => decide (2 * x ≤ N)) :=
  (SwapEquiv.induction_foldSeq
    (P := fun a b => a.filter (fun x => decide (2 * x ≤ N)) = b.filter (fun x => decide (2 * x ≤ N)))
    (fun _ _ hx hs => hs.filter_left hx) (fun _ => rfl) (fun _ _ h => h.symm)
    (fun _ _ _ h h' => h.trans h') h).2 ha

/-- **The right-half word is a class invariant.** -/
theorem SwapEquiv.filter_right {N : ℕ} {a b : List ℕ} (h : SwapEquiv N a b) (ha : IsFoldSeq N a) :
    a.filter (fun x => decide (N < 2 * x)) = b.filter (fun x => decide (N < 2 * x)) :=
  (SwapEquiv.induction_foldSeq
    (P := fun a b => a.filter (fun x => decide (N < 2 * x)) = b.filter (fun x => decide (N < 2 * x)))
    (fun _ _ hx hs => hs.filter_right hx) (fun _ => rfl) (fun _ _ h => h.symm)
    (fun _ _ _ h h' => h.trans h') h).2 ha

/-! ## `a(N)` as a sum over swap classes -/

open Classical in
/-- The swap class of `a` inside the set of semi-symmetric sequences. -/
noncomputable def swapClass (N : ℕ) (a : List ℕ) : Finset (List ℕ) :=
  (semiSeqs N).filter (SwapEquiv N a)

open Classical in
/-- The set of swap classes of semi-symmetric sequences of length `N`. -/
noncomputable def swapClasses (N : ℕ) : Finset (Finset (List ℕ)) :=
  (semiSeqs N).image (swapClass N)

/-- `K(N)`: the number of swap classes (valid traces). -/
noncomputable def classCount (N : ℕ) : ℕ := (swapClasses N).card

theorem mem_swapClass {N : ℕ} {a b : List ℕ} :
    b ∈ swapClass N a ↔ b ∈ semiSeqs N ∧ SwapEquiv N a b := by
  classical
  simp [swapClass]

theorem swapClass_eq_iff {N : ℕ} {a b : List ℕ} (hb : b ∈ semiSeqs N) :
    swapClass N b = swapClass N a ↔ SwapEquiv N a b := by
  constructor
  · intro e
    have : b ∈ swapClass N b := mem_swapClass.2 ⟨hb, SwapEquiv.refl b⟩
    rw [e] at this
    exact (mem_swapClass.1 this).2
  · intro h
    ext c
    rw [mem_swapClass, mem_swapClass]
    exact ⟨fun ⟨hc, hbc⟩ => ⟨hc, h.trans hbc⟩, fun ⟨hc, hac⟩ => ⟨hc, h.symm.trans hac⟩⟩

/-- **`a(N)` is the sum of the sizes of the swap classes.** -/
theorem semiCount_eq_sum_swapClasses (N : ℕ) : semiCount N = ∑ c ∈ swapClasses N, c.card := by
  classical
  rw [semiCount, swapClasses, Finset.card_eq_sum_card_image (swapClass N) (semiSeqs N)]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
  congr 1
  ext b
  rw [Finset.mem_filter, mem_swapClass]
  constructor
  · rintro ⟨hb, e⟩; exact ⟨hb, (swapClass_eq_iff hb).1 e⟩
  · rintro ⟨hb, e⟩; exact ⟨hb, (swapClass_eq_iff hb).2 e⟩

theorem classCount_le_semiCount (N : ℕ) : classCount N ≤ semiCount N :=
  Finset.card_image_le

/-- Every class is non-empty, hence `classCount N` is positive as soon as `a(N)` is. -/
theorem card_pos_of_mem_swapClasses {N : ℕ} {c : Finset (List ℕ)} (hc : c ∈ swapClasses N) :
    0 < c.card := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
  exact Finset.card_pos.2 ⟨a, mem_swapClass.2 ⟨ha, SwapEquiv.refl a⟩⟩

/-! ## Order-convexity in the weak order -/

/-- `x` is placed strictly before `y` in `a`. -/
def Before (a : List ℕ) (x y : ℕ) : Prop := a.idxOf x < a.idxOf y

theorem mem_take_iff_idxOf_lt {x : ℕ} : ∀ {a : List ℕ} {k : ℕ}, k ≤ a.length →
    (x ∈ a.take k ↔ a.idxOf x < k)
  | [], k, hk => by simp at hk; simp [hk]
  | b :: t, 0, _ => by simp
  | b :: t, k + 1, hk => by
    have ih := mem_take_iff_idxOf_lt (x := x) (a := t) (k := k) (by simpa using hk)
    by_cases hb : b = x
    · subst hb; simp
    · rw [List.take_succ_cons, List.mem_cons, ih, List.idxOf_cons_ne _ hb]
      constructor
      · rintro (h | h)
        · exact absurd h.symm hb
        · omega
      · intro h; right; omega

theorem mem_take_idxOf {a : List ℕ} {x y : ℕ} : x ∈ a.take (a.idxOf y) ↔ Before a x y :=
  mem_take_iff_idxOf_lt List.idxOf_le_length

theorem before_or {a : List ℕ} {x y : ℕ} (hx : x ∈ a) (hne : x ≠ y) :
    Before a x y ∨ Before a y x := by
  unfold Before
  have : a.idxOf x ≠ a.idxOf y := fun e => hne ((List.idxOf_inj hx).1 e)
  omega

theorem Before.asymm {a : List ℕ} {x y : ℕ} (h : Before a x y) : ¬ Before a y x := by
  unfold Before at *; omega

/-- Semi-symmetry in terms of "the panels placed before `m`". -/
theorem semiSymmetric_iff_before {N : ℕ} {a : List ℕ} (hnd : a.Nodup) :
    SemiSymmetric N a ↔ ∀ m ∈ a, SemiStep N (a.take (a.idxOf m)) m := by
  constructor
  · intro h m hm
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hm
    rw [hnd.idxOf_getElem k hk]
    exact h k hk
  · intro h k hk
    have := h a[k] (List.getElem_mem hk)
    rwa [hnd.idxOf_getElem k hk] at this

/-- The (right) weak order on sequences: every inversion of `a` (a pair `x < y` with `y`
placed before `x`) is an inversion of `b`. -/
def WeakLE (a b : List ℕ) : Prop := ∀ x y, x < y → Before a y x → Before b y x

theorem WeakLE.refl (a : List ℕ) : WeakLE a a := fun _ _ _ h => h

theorem WeakLE.trans {a b c : List ℕ} (h : WeakLE a b) (h' : WeakLE b c) : WeakLE a c :=
  fun x y hxy hb => h' x y hxy (h x y hxy hb)

/-- **Comparable semi-symmetric sequences orient every window pair in the same way.**  If
`a ≤ b` in the weak order and both are semi-symmetric fold sequences, then for every panel
`m` and every `x` in the window of `m`: `x` precedes `m` in `a` iff it does in `b`.
(Going up in the weak order can only remove left neighbours and add right neighbours from
the set of earlier panels in the window of `m`; the two counts must stay equal.) -/
theorem before_iff_of_weakLE {N : ℕ} {a b : List ℕ} (ha : IsFoldSeq N a) (hb : IsFoldSeq N b)
    (hsa : SemiSymmetric N a) (hsb : SemiSymmetric N b) (hle : WeakLE a b) {m x : ℕ}
    (hx : InWindow N m x) : Before a x m ↔ Before b x m := by
  obtain ⟨d0, hd1, hd2, hxd⟩ := inWindow_iff_exists.1 hx
  have hmN : 1 ≤ m ∧ m ≤ N := by unfold reach at hd2; omega
  have hma : m ∈ a := (mem_range'_of_perm ha).2 hmN
  have hmb : m ∈ b := (mem_range'_of_perm hb).2 hmN
  have sa := (semiSymmetric_iff_before (nodup_of_foldSeq ha)).1 hsa m hma
  have sb := (semiSymmetric_iff_before (nodup_of_foldSeq hb)).1 hsb m hmb
  -- left side: placed-before in `b` implies placed-before in `a`
  have hL : ∀ d ∈ List.range' 1 (reach N m),
      decide (m - d ∈ b.take (b.idxOf m)) = true → decide (m - d ∈ a.take (a.idxOf m)) = true := by
    intro d hd h
    rw [List.mem_range'_1] at hd
    simp only [decide_eq_true_eq, mem_take_idxOf] at h ⊢
    have hmem : m - d ∈ a := (mem_range'_of_perm ha).2 (by unfold reach at hd; omega)
    rcases before_or hmem (show m - d ≠ m by omega) with h' | h'
    · exact h'
    · exact absurd (hle (m - d) m (by omega) h') h.asymm
  have hR : ∀ d ∈ List.range' 1 (reach N m),
      decide (m + d ∈ a.take (a.idxOf m)) = true → decide (m + d ∈ b.take (b.idxOf m)) = true := by
    intro d hd h
    simp only [decide_eq_true_eq, mem_take_idxOf] at h ⊢
    exact hle m (m + d) (by rw [List.mem_range'_1] at hd; omega) h
  have h1 := List.countP_mono_left hL
  have h2 := List.countP_mono_left hR
  unfold SemiStep leftCount rightCount at sa sb
  have eL := countP_eq_imp hL (by omega)
  have eR := countP_eq_imp hR (by omega)
  have hd : d0 ∈ List.range' 1 (reach N m) := by rw [List.mem_range'_1]; omega
  rcases hxd with rfl | rfl
  · constructor
    · intro h
      have := eL d0 hd (by simpa [mem_take_idxOf] using h)
      simpa [mem_take_idxOf] using this
    · intro h
      have := hL d0 hd (by simpa [mem_take_idxOf] using h)
      simpa [mem_take_idxOf] using this
  · constructor
    · intro h
      have := hR d0 hd (by simpa [mem_take_idxOf] using h)
      simpa [mem_take_idxOf] using this
    · intro h
      have := eR d0 hd (by simpa [mem_take_idxOf] using h)
      simpa [mem_take_idxOf] using this

/-- **The semi-symmetric sequences are order-convex in the weak order.**  A fold sequence
`c` with `a ≤ c ≤ b` (weak order), `a` and `b` semi-symmetric, is semi-symmetric. -/
theorem semiSymmetric_of_weak_between {N : ℕ} {a b c : List ℕ} (ha : IsFoldSeq N a)
    (hb : IsFoldSeq N b) (hc : IsFoldSeq N c) (hsa : SemiSymmetric N a)
    (hsb : SemiSymmetric N b) (hac : WeakLE a c) (hcb : WeakLE c b) : SemiSymmetric N c := by
  rw [semiSymmetric_iff_before (nodup_of_foldSeq hc)]
  intro m hm
  have hmN := (mem_range'_of_perm hc).1 hm
  have hma : m ∈ a := (mem_range'_of_perm ha).2 hmN
  have sa := (semiSymmetric_iff_before (nodup_of_foldSeq ha)).1 hsa m hma
  refine (semiStep_congr_window ?_).1 sa
  intro x hx
  rw [mem_take_idxOf, mem_take_idxOf]
  have hab := before_iff_of_weakLE ha hb hsa hsb (hac.trans hcb) hx
  obtain ⟨d, hd1, hd2, hxd⟩ := inWindow_iff_exists.1 hx
  have hxN : 1 ≤ x ∧ x ≤ N := by unfold reach at hd2; omega
  have hxa : x ∈ a := (mem_range'_of_perm ha).2 hxN
  have hxc : x ∈ c := (mem_range'_of_perm hc).2 hxN
  have hne : x ≠ m := hx.1
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- `x < m`
    constructor
    · intro h
      rcases before_or hxc hne with h' | h'
      · exact h'
      · exact absurd (hcb x m hlt h') (hab.1 h).asymm
    · intro h
      rcases before_or hxa hne with h' | h'
      · exact h'
      · exact absurd (hac x m hlt h') h.asymm
  · -- `m < x`
    constructor
    · intro h; exact hac m x hgt h
    · intro h; exact hab.2 (hcb m x hgt h)

/-! ## Rigid sequences -/

/-- A sequence is *rigid* if it admits no valid swap. -/
def Rigid (N : ℕ) (a : List ℕ) : Prop := ∀ b, ¬ SwapStep N a b

/-- Boolean test: some pair of adjacent entries is independent. -/
def hasSwap (N : ℕ) : List ℕ → Bool
  | m :: m' :: v => decide (Indep N m m') || hasSwap N (m' :: v)
  | _ => false

theorem hasSwap_iff {N : ℕ} : ∀ {a : List ℕ}, hasSwap N a = true ↔ ∃ b, SwapStep N a b
  | [] => by
    simp only [hasSwap, Bool.false_eq_true, false_iff]
    rintro ⟨b, hb⟩
    generalize hE : ([] : List ℕ) = e at hb
    obtain ⟨u, v, m, m', hI⟩ := hb
    simp at hE
  | [x] => by
    simp only [hasSwap, Bool.false_eq_true, false_iff]
    rintro ⟨b, hb⟩
    generalize hE : [x] = e at hb
    obtain ⟨u, v, m, m', hI⟩ := hb
    have := congrArg List.length hE
    simp at this
    omega
  | x :: y :: w => by
    have ih := hasSwap_iff (N := N) (a := y :: w)
    simp only [hasSwap, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · exact ⟨_, SwapStep.mk [] w x y h⟩
      · obtain ⟨b, hb⟩ := ih.1 h
        generalize hE : y :: w = e at hb
        obtain ⟨u, v, m, m', hI⟩ := hb
        exact ⟨x :: (u ++ m' :: m :: v), SwapStep.mk (x :: u) v m m' hI⟩
    · rintro ⟨b, hb⟩
      generalize hE : x :: y :: w = e at hb
      obtain ⟨u, v, m, m', hI⟩ := hb
      match u, hE with
      | [], hE =>
        simp only [List.nil_append, List.cons.injEq] at hE
        obtain ⟨rfl, rfl, rfl⟩ := hE
        exact Or.inl hI
      | z :: u', hE =>
        simp only [List.cons_append, List.cons.injEq] at hE
        obtain ⟨rfl, hE⟩ := hE
        right
        exact ih.2 ⟨u' ++ m' :: m :: v, by rw [hE]; exact SwapStep.mk u' v m m' hI⟩

theorem rigid_iff {N : ℕ} {a : List ℕ} : Rigid N a ↔ hasSwap N a = false := by
  rw [Rigid, ← Bool.not_eq_true, hasSwap_iff]
  simp

/-- Reversal preserves rigidity. -/
theorem Rigid.reverse {N : ℕ} {a : List ℕ} (h : Rigid N a) : Rigid N a.reverse := by
  intro b hb
  have := hb.reverse
  rw [List.reverse_reverse] at this
  exact h _ this

/-- Depth-first search over all semi-symmetric extensions of the prefix `S` by `f` more
panels, checking `Q` on every complete extension (kernel-friendly: structural recursion). -/
def allExt (N : ℕ) (Q : List ℕ → Bool) : ℕ → List ℕ → Bool
  | 0, S => Q S
  | f + 1, S => (List.range' 1 N).all fun m =>
      decide (m ∈ S) || !decide (SemiStep N S m) || allExt N Q f (S ++ [m])

theorem allExt_sound {N : ℕ} {Q : List ℕ → Bool} : ∀ (f : ℕ) (S t : List ℕ),
    allExt N Q f S = true → t.length = f → (∀ x ∈ t, 1 ≤ x ∧ x ≤ N) → (S ++ t).Nodup →
    SemiSymmetric N (S ++ t) → Q (S ++ t) = true
  | 0, S, t, h, ht, _, _, _ => by
    obtain rfl := List.length_eq_zero_iff.1 ht
    simpa [allExt] using h
  | f + 1, S, t, h, ht, hb, hnd, hs => by
    match t, ht with
    | m :: t', ht =>
      simp only [allExt, List.all_eq_true] at h
      have hm := h m (by rw [List.mem_range'_1]; have := hb m (by simp); omega)
      have hmS : m ∉ S := fun hmS => (List.nodup_append.1 hnd).2.2 m hmS m (by simp) rfl
      have hstep : SemiStep N S m := by
        have := (semiSymmetric_append_iff.1 hs).2 0 (by simp)
        exact (semiStep_congr (by intro x; simp)).1 this
      simp only [hmS, hstep, decide_false, decide_true, Bool.not_true, Bool.false_or] at hm
      have := allExt_sound f (S ++ [m]) t' hm (by simpa using ht)
        (fun x hx => hb x (by simp [hx])) (by simpa using hnd) (by simpa using hs)
      simpa using this

theorem forall_semiSeqs_of_allExt {N : ℕ} {Q : List ℕ → Bool} (h : allExt N Q N [] = true)
    {a : List ℕ} (ha : a ∈ semiSeqs N) : Q a = true := by
  rw [mem_semiSeqs] at ha
  have hlen : a.length = N := by rw [ha.1.length_eq]; simp
  simpa using allExt_sound N [] a h hlen (fun x hx => (mem_range'_of_perm ha.1).1 hx)
    (by simpa using nodup_of_foldSeq ha.1) (by simpa using ha.2)

theorem allExt_hasSwap_small :
    ∀ N ∈ [2, 3, 4, 5, 6, 7, 8], allExt N (hasSwap N) N [] = true := by
  decide +kernel

/-- **No rigid semi-symmetric sequence for `2 ≤ N ≤ 8`**: every semi-symmetric sequence
admits a valid swap.  (Numerically true for all `2 ≤ N ≤ 22`, `experiments/xd_traces`.) -/
theorem hasSwap_of_mem_semiSeqs_small {N : ℕ} (hN : N ∈ [2, 3, 4, 5, 6, 7, 8]) {a : List ℕ}
    (ha : a ∈ semiSeqs N) : hasSwap N a = true :=
  forall_semiSeqs_of_allExt (allExt_hasSwap_small N hN) ha

theorem not_rigid_small {N : ℕ} (hN : N ∈ [2, 3, 4, 5, 6, 7, 8]) {a : List ℕ}
    (ha : a ∈ semiSeqs N) : ¬ Rigid N a := by
  rw [rigid_iff, hasSwap_of_mem_semiSeqs_small hN ha]; simp

end Folds
