import Folds.RecCount

namespace Folds
namespace Neutral

/-! ## Balance, neutral sets, copies (Finset form) -/

/-- `X` has as many elements in the left window arm of `m` as in the right one. -/
def BalF (N : Nat) (X : Finset Nat) (m : Nat) : Prop :=
  (X.filter (fun x => m - reach N m ≤ x ∧ x < m)).card =
    (X.filter (fun x => m < x ∧ x ≤ m + reach N m)).card

instance (N : Nat) (X : Finset Nat) (m : Nat) : Decidable (BalF N X m) :=
  inferInstanceAs (Decidable (_ = _))

/-- `X` is neutral: balanced around every panel of `[1, N]`. -/
def IsNeutral (N : Nat) (X : Finset Nat) : Prop := ∀ m ∈ Finset.Icc 1 N, BalF N X m

/-- `X` is a (window) copy: balanced around each of its own elements. -/
def IsCopy (N : Nat) (X : Finset Nat) : Prop := ∀ m ∈ X, BalF N X m

instance (N : Nat) (X : Finset Nat) : Decidable (IsNeutral N X) :=
  inferInstanceAs (Decidable (∀ m ∈ Finset.Icc 1 N, BalF N X m))

instance (N : Nat) (X : Finset Nat) : Decidable (IsCopy N X) :=
  inferInstanceAs (Decidable (∀ m ∈ X, BalF N X m))

theorem countP_eq_card {l : List Nat} (hnd : l.Nodup) (p : Nat → Prop) [DecidablePred p] :
    l.countP (fun x => decide (p x)) = (l.toFinset.filter p).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _),
    List.toFinset_filter]
  simp

theorem balanced_iff_balF {N m : Nat} {l : List Nat} (hnd : l.Nodup) :
    Balanced N l m ↔ BalF N l.toFinset m := by
  unfold Balanced BalF
  rw [countP_eq_card hnd, countP_eq_card hnd]

theorem card_filter_sdiff {X Y : Finset Nat} (h : X ⊆ Y) (p : Nat → Prop) [DecidablePred p] :
    ((Y \ X).filter p).card = (Y.filter p).card - (X.filter p).card := by
  have e : (Y \ X).filter p = Y.filter p \ X.filter p := by
    ext x; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [e, Finset.card_sdiff_of_subset (Finset.monotone_filter_left p h)]

theorem balF_sdiff {N m : Nat} {X Y : Finset Nat} (h : X ⊆ Y) (hX : BalF N X m)
    (hY : BalF N Y m) : BalF N (Y \ X) m := by
  unfold BalF at *
  rw [card_filter_sdiff h, card_filter_sdiff h, hX, hY]

theorem balF_full {N m : Nat} (hm : m ∈ Finset.Icc 1 N) : BalF N (Finset.Icc 1 N) m := by
  rw [Finset.mem_Icc] at hm
  unfold BalF
  have hr : reach N m ≤ m - 1 ∧ m + reach N m ≤ N := by unfold reach; omega
  have e1 : (Finset.Icc 1 N).filter (fun x => m - reach N m ≤ x ∧ x < m) =
      Finset.Icc (m - reach N m) (m - 1) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have e2 : (Finset.Icc 1 N).filter (fun x => m < x ∧ x ≤ m + reach N m) =
      Finset.Icc (m + 1) (m + reach N m) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [e1, e2, Nat.card_Icc, Nat.card_Icc]
  omega

theorem balF_compl_iff {N m : Nat} {X : Finset Nat} (hX : X ⊆ Finset.Icc 1 N)
    (hm : m ∈ Finset.Icc 1 N) : BalF N (Finset.Icc 1 N \ X) m ↔ BalF N X m := by
  have hf := balF_full hm
  unfold BalF at *
  rw [card_filter_sdiff hX, card_filter_sdiff hX]
  have a1 := Finset.card_le_card (Finset.monotone_filter_left
    (fun x => m - reach N m ≤ x ∧ x < m) hX)
  have a2 := Finset.card_le_card (Finset.monotone_filter_left
    (fun x => m < x ∧ x ≤ m + reach N m) hX)
  omega

/-- Neutral iff the set and its complement are both copies. -/
theorem neutral_iff_copy_compl {N : Nat} {X : Finset Nat} (hX : X ⊆ Finset.Icc 1 N) :
    IsNeutral N X ↔ IsCopy N X ∧ IsCopy N (Finset.Icc 1 N \ X) := by
  constructor
  · intro h
    refine ⟨fun m hm => h m (hX hm), fun m hm => ?_⟩
    have hm' := (Finset.mem_sdiff.1 hm).1
    exact (balF_compl_iff hX hm').2 (h m hm')
  · rintro ⟨h1, h2⟩ m hm
    by_cases hmX : m ∈ X
    · exact h1 m hmX
    · exact (balF_compl_iff hX hm).1 (h2 m (Finset.mem_sdiff.2 ⟨hm, hmX⟩))

theorem neutral_sdiff {N : Nat} {X Y : Finset Nat} (h : X ⊆ Y) (hX : IsNeutral N X)
    (hY : IsNeutral N Y) : IsNeutral N (Y \ X) := fun m hm => balF_sdiff h (hX m hm) (hY m hm)

theorem neutral_full (N : Nat) : IsNeutral N (Finset.Icc 1 N) := fun _ hm => balF_full hm

/-! ## The periodic counting function and the doubling form -/

/-- The `N`-periodic indicator of `X ⊆ [1, N]`: `xi k = [k mod N ∈ X]` (residue `0` read as `N`). -/
def xi (N : Nat) (X : Finset Nat) (k : Nat) : Nat := if (k + N - 1) % N + 1 ∈ X then 1 else 0

/-- `P t = xi 1 + ⋯ + xi t`, the periodic counting function. -/
def P (N : Nat) (X : Finset Nat) (t : Nat) : Nat := ∑ i ∈ Finset.range t, xi N X (i + 1)

/-- `y k = xi k + xi (k + 1)`. -/
def y (N : Nat) (X : Finset Nat) (k : Nat) : Nat := xi N X k + xi N X (k + 1)

variable {N : Nat} {X : Finset Nat}

theorem xi_le_one (k : Nat) : xi N X k ≤ 1 := by unfold xi; split <;> omega

theorem xi_of_le (hN : 0 < N) {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ N) :
    xi N X k = if k ∈ X then 1 else 0 := by
  unfold xi
  rw [show k + N - 1 = (k - 1) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
    Nat.sub_add_cancel h1]

theorem xi_add (hN : 0 < N) (k : Nat) : xi N X (k + N) = xi N X k := by
  unfold xi
  rw [show k + N + N - 1 = (k + N - 1) + N by omega, Nat.add_mod_right]

theorem P_zero : P N X 0 = 0 := by simp [P]

theorem P_succ (t : Nat) : P N X (t + 1) = P N X t + xi N X (t + 1) := by
  simp [P, Finset.sum_range_succ]

theorem P_mono {a b : Nat} (h : a ≤ b) : P N X a ≤ P N X b := by
  induction b with
  | zero => rw [Nat.le_zero.1 h]
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with e | lt
    · rw [e]
    · rw [P_succ]; have := ih (by omega); omega

theorem P_le (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) :
    ∀ t, t ≤ N → P N X t = (X.filter (· ≤ t)).card
  | 0, _ => by
    rw [P_zero]; symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx; have := Finset.mem_Icc.1 (hX hx); omega
  | t + 1, ht => by
    rw [P_succ, P_le hN hX t (by omega), xi_of_le hN (by omega) ht]
    by_cases hm : t + 1 ∈ X
    · have e : X.filter (· ≤ t + 1) = insert (t + 1) (X.filter (· ≤ t)) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hx, h⟩; by_cases e : x = t + 1
          · exact Or.inl e
          · exact Or.inr ⟨hx, by omega⟩
        · rintro (rfl | ⟨hx, h⟩)
          · exact ⟨hm, le_rfl⟩
          · exact ⟨hx, by omega⟩
      rw [e, Finset.card_insert_of_notMem (by simp), if_pos hm]
      
    · have e : X.filter (· ≤ t + 1) = X.filter (· ≤ t) := by
        ext x; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hx, h⟩
          refine ⟨hx, ?_⟩
          rcases Nat.eq_or_lt_of_le h with e | lt
          · subst e; exact absurd hx hm
          · omega
        · rintro ⟨hx, h⟩; exact ⟨hx, by omega⟩
      rw [e, if_neg hm, Nat.add_zero]

theorem P_N (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) : P N X N = X.card := by
  rw [P_le hN hX N le_rfl]
  congr 1
  ext x; simp only [Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro hx; exact ⟨hx, (Finset.mem_Icc.1 (hX hx)).2⟩

theorem P_add (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) :
    ∀ t, P N X (t + N) = P N X t + X.card
  | 0 => by rw [Nat.zero_add, P_N hN hX, P_zero, Nat.zero_add]
  | t + 1 => by
    rw [show t + 1 + N = (t + N) + 1 by omega, P_succ, P_add hN hX t, P_succ,
      show t + N + 1 = (t + 1) + N by omega, xi_add hN]
    omega

/-- Interval counts: `#(X ∩ (a, b]) = P b - P a` for `a ≤ b ≤ N`. -/
theorem P_interval (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) {a b : Nat} (hab : a ≤ b)
    (hb : b ≤ N) : P N X b = P N X a + (X.filter (fun x => a < x ∧ x ≤ b)).card := by
  rw [P_le hN hX b hb, P_le hN hX a (by omega)]
  rw [← Finset.card_filter_add_card_filter_not (s := X.filter (· ≤ b)) (· ≤ a),
    Finset.filter_filter, Finset.filter_filter]
  congr 2
  · ext x; simp only [Finset.mem_filter]; constructor
    · rintro ⟨hx, h⟩; exact ⟨hx, h.2⟩
    · rintro ⟨hx, h⟩; exact ⟨hx, by omega, h⟩
  · ext x; simp only [Finset.mem_filter]; constructor
    · rintro ⟨hx, h⟩; exact ⟨hx, by omega⟩
    · rintro ⟨hx, h⟩; exact ⟨hx, by omega⟩

/-- Balance at one panel, in counting form: `P(2m - 1) = P(m - 1) + P(m)`. -/
theorem balF_iff_P (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) {m : Nat} (hm1 : 1 ≤ m)
    (hmN : m ≤ N) :
    BalF N X m ↔ P N X (2 * m - 1) = P N X (m - 1) + P N X m := by
  unfold BalF
  set r := reach N m with hr
  have hr1 : r ≤ m - 1 ∧ m + r ≤ N := by rw [hr]; unfold reach; omega
  have eL : X.filter (fun x => m - r ≤ x ∧ x < m) =
      X.filter (fun x => m - r - 1 < x ∧ x ≤ m - 1) := by
    apply Finset.filter_congr; intro x hx; have := Finset.mem_Icc.1 (hX hx); omega
  rw [eL]
  have i1 := P_interval hN hX (a := m - r - 1) (b := m - 1) (by omega) (by omega)
  have i2 := P_interval hN hX (a := m) (b := m + r) (by omega) (by omega)
  have hmono := P_mono (N := N) (X := X) (show m - 1 ≤ m by omega)
  rcases Nat.le_total (2 * m - 1) N with h | h
  · have hr' : r = m - 1 := by rw [hr]; unfold reach; omega
    have e1 : P N X (m - r - 1) = 0 := by rw [show m - r - 1 = 0 by omega, P_zero]
    have e2 : P N X (m + r) = P N X (2 * m - 1) := by rw [show m + r = 2 * m - 1 by omega]
    omega
  · have hr' : r = N - m := by rw [hr]; unfold reach; omega
    have e2 : P N X (m + r) = X.card := by rw [show m + r = N by omega, P_N hN hX]
    have := P_add hN hX (2 * m - 1 - N)
    rw [show 2 * m - 1 - N + N = 2 * m - 1 by omega] at this
    have e1 : P N X (m - r - 1) = P N X (2 * m - 1 - N) := by
      rw [show m - r - 1 = 2 * m - 1 - N by omega]
    omega

/-- The doubling relation `P(2k + 1) = P(k) + P(k + 1)`. -/
def Dbl (N : Nat) (X : Finset Nat) (k : Nat) : Prop := P N X (2 * k + 1) = P N X k + P N X (k + 1)

theorem dbl_add_iff (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (k : Nat) :
    Dbl N X (k + N) ↔ Dbl N X k := by
  unfold Dbl
  have a := P_add hN hX (2 * k + 1 + N)
  have b := P_add hN hX (2 * k + 1)
  have c := P_add hN hX k
  have d := P_add hN hX (k + 1)
  rw [show 2 * k + 1 + N + N = 2 * (k + N) + 1 by ring] at a
  rw [show k + 1 + N = k + N + 1 by ring] at d
  rw [a, b, c, d]
  omega

/-- **Doubling form of neutrality.**  `X` is neutral iff `P(2k+1) = P(k) + P(k+1)` for all `k`. -/
theorem neutral_iff_dbl (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) :
    IsNeutral N X ↔ ∀ k, Dbl N X k := by
  have key : ∀ k, k < N → (Dbl N X k ↔ BalF N X (k + 1)) := by
    intro k hk
    rw [balF_iff_P hN hX (by omega) (by omega)]
    unfold Dbl
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, Nat.add_sub_cancel]
  constructor
  · intro h k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.lt_or_ge k N with hk | hk
      · exact (key k hk).2 (h (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
      · have := ih (k - N) (by omega)
        rw [← dbl_add_iff hN hX, Nat.sub_add_cancel hk] at this
        exact this
  · intro h m hm
    rw [Finset.mem_Icc] at hm
    have := (key (m - 1) (by omega)).1 (h (m - 1))
    rwa [Nat.sub_add_cancel hm.1] at this

/-- **`y`-form of neutrality.**  With `y k = xi k + xi (k + 1)`, `X` is neutral iff
`y (2k) = y k` for all `k`: `y` is constant on the orbits of the doubling map. -/
theorem neutral_iff_y (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) :
    IsNeutral N X ↔ ∀ k, y N X (2 * k) = y N X k := by
  rw [neutral_iff_dbl hN hX]
  have s1 : ∀ k, P N X (2 * k + 3) = P N X (2 * k + 1) + xi N X (2 * k + 2) +
      xi N X (2 * k + 3) := fun k => by
    rw [show 2 * k + 3 = (2 * k + 2) + 1 by omega, P_succ, show 2 * k + 2 = (2 * k + 1) + 1 by
      omega, P_succ]
  have s2 : ∀ k, P N X (k + 2) = P N X (k + 1) + xi N X (k + 2) := fun k => P_succ (k + 1)
  have s3 : ∀ k, P N X (k + 1) = P N X k + xi N X (k + 1) := fun k => P_succ k
  unfold Dbl y
  constructor
  · intro h k
    rcases k with _ | k
    · rfl
    · have a := h k; have b := h (k + 1)
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, show k + 1 + 1 = k + 2 by ring] at b
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * k + 2 + 1 = 2 * k + 3 by ring]
      have := s1 k; have := s2 k; have := s3 k; have := s3 (k + 1)
      simp only [show k + 1 + 1 = k + 2 from rfl] at *
      omega
  · intro h k
    induction k with
    | zero => simp [P_zero]
    | succ k ih =>
      have hy := h (k + 1)
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * k + 2 + 1 = 2 * k + 3 by ring] at hy
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, show k + 1 + 1 = k + 2 by ring]
      have := s1 k; have := s2 k; have := s3 k; have := s3 (k + 1)
      simp only [show k + 1 + 1 = k + 2 from rfl] at *
      omega

/-! ## The discrepancy bound -/

/-- The discrepancy `h t = N · P t - |X| · t`. -/
def hd (N : Nat) (X : Finset Nat) (t : Nat) : Int := (N : Int) * (P N X t : Int) - (X.card : Int) * t

theorem hd_zero : hd N X 0 = 0 := by simp [hd, P_zero]

theorem hd_succ (t : Nat) :
    hd N X (t + 1) = hd N X t + (N : Int) * (xi N X (t + 1) : Int) - X.card := by
  unfold hd; rw [P_succ]; push_cast; ring

theorem hd_add (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (t : Nat) : hd N X (t + N) = hd N X t := by
  unfold hd; rw [P_add hN hX]; push_cast; ring

theorem hd_add_mul (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (t : Nat) :
    ∀ q, hd N X (t + N * q) = hd N X t
  | 0 => by simp
  | q + 1 => by rw [Nat.mul_succ, ← Nat.add_assoc, hd_add hN hX, hd_add_mul hN hX t q]

theorem hd_mod (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (t : Nat) : hd N X t = hd N X (t % N) := by
  conv_lhs => rw [← Nat.mod_add_div t N]
  exact hd_add_mul hN hX _ _

theorem hd_dbl {k : Nat} (h : Dbl N X k) : hd N X (2 * k + 1) = hd N X k + hd N X (k + 1) := by
  unfold hd; unfold Dbl at h; rw [h]; push_cast; ring

/-- **Discrepancy bound.**  For a neutral `X`, `|N · P t - |X| · t| ≤ min(|X|, N - |X|)`. -/
theorem hd_bounds (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hn : IsNeutral N X) (t : Nat) :
    hd N X t ≤ X.card ∧ hd N X t ≤ (N : Int) - X.card ∧
      -(X.card : Int) ≤ hd N X t ∧ -((N : Int) - X.card) ≤ hd N X t := by
  have hd' := (neutral_iff_dbl hN hX).1 hn
  have hne : (Finset.range N).Nonempty := ⟨0, Finset.mem_range.2 hN⟩
  have x01 : ∀ k, (0 : Int) ≤ (N : Int) * (xi N X k : Int) ∧
      (N : Int) * (xi N X k : Int) ≤ N := by
    intro k
    have := xi_le_one (N := N) (X := X) k
    constructor
    · positivity
    · have : (xi N X k : Int) ≤ 1 := by exact_mod_cast this
      nlinarith
  obtain ⟨t0, -, hmax⟩ := Finset.exists_max_image (Finset.range N) (hd N X) hne
  obtain ⟨t1, -, hmin⟩ := Finset.exists_min_image (Finset.range N) (hd N X) hne
  have hall : ∀ t, hd N X t ≤ hd N X t0 := fun t => by
    rw [hd_mod hN hX t]; exact hmax _ (Finset.mem_range.2 (Nat.mod_lt _ hN))
  have hall' : ∀ t, hd N X t1 ≤ hd N X t := fun t => by
    rw [hd_mod hN hX t]; exact hmin _ (Finset.mem_range.2 (Nat.mod_lt _ hN))
  -- the maximum
  have u1 : hd N X t0 ≤ X.card := by
    have a := hall (2 * t0 + 1); rw [hd_dbl (hd' t0)] at a
    have b := hd_succ (N := N) (X := X) t0
    have := x01 (t0 + 1); linarith
  have u2 : hd N X t0 ≤ (N : Int) - X.card := by
    have e := hd_add hN hX t0
    have a := hall (2 * (t0 + N - 1) + 1); rw [hd_dbl (hd' _)] at a
    rw [show t0 + N - 1 + 1 = t0 + N by omega, e] at a
    have b := hd_succ (N := N) (X := X) (t0 + N - 1)
    rw [show t0 + N - 1 + 1 = t0 + N by omega, e] at b
    have := x01 (t0 + N); linarith
  -- the minimum
  have l1 : -((N : Int) - X.card) ≤ hd N X t1 := by
    have a := hall' (2 * t1 + 1); rw [hd_dbl (hd' t1)] at a
    have b := hd_succ (N := N) (X := X) t1
    have := x01 (t1 + 1); linarith
  have l2 : -(X.card : Int) ≤ hd N X t1 := by
    have e := hd_add hN hX t1
    have a := hall' (2 * (t1 + N - 1) + 1); rw [hd_dbl (hd' _)] at a
    rw [show t1 + N - 1 + 1 = t1 + N by omega, e] at a
    have b := hd_succ (N := N) (X := X) (t1 + N - 1)
    rw [show t1 + N - 1 + 1 = t1 + N by omega, e] at b
    have := x01 (t1 + N); linarith
  have := hall t; have := hall' t
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem mem_iff_xi (hN : 0 < N) {x : Nat} (hx : x ∈ Finset.Icc 1 N) :
    x ∈ X ↔ xi N X x = 1 := by
  rw [Finset.mem_Icc] at hx
  rw [xi_of_le hN hx.1 hx.2]; split <;> simp_all

theorem eq_of_P_eq {X' : Finset Nat} (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N)
    (hX' : X' ⊆ Finset.Icc 1 N) (h : ∀ t, P N X t = P N X' t) : X = X' := by
  have hxi : ∀ k, xi N X (k + 1) = xi N X' (k + 1) := fun k => by
    have a := P_succ (N := N) (X := X) k; have b := P_succ (N := N) (X := X') k
    rw [h, h] at a; omega
  ext x
  constructor
  · intro hx
    have hm := hX hx
    have e := hxi (x - 1)
    rw [Nat.sub_add_cancel (Finset.mem_Icc.1 hm).1] at e
    rw [mem_iff_xi hN hm] at hx; rw [mem_iff_xi hN hm]; omega
  · intro hx
    have hm := hX' hx
    have e := hxi (x - 1)
    rw [Nat.sub_add_cancel (Finset.mem_Icc.1 hm).1] at e
    rw [mem_iff_xi hN hm] at hx; rw [mem_iff_xi hN hm]; omega

/-- **Uniqueness by size.**  Two neutral sets of the same size `s` with `2s ≠ N` coincide. -/
theorem neutral_unique {X' : Finset Nat} (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N)
    (hX' : X' ⊆ Finset.Icc 1 N) (n1 : IsNeutral N X) (n2 : IsNeutral N X')
    (hc : X.card = X'.card) (h2 : 2 * X.card ≠ N) : X = X' := by
  apply eq_of_P_eq hN hX hX'
  intro t
  have b1 := hd_bounds hN hX n1 t
  have b2 := hd_bounds hN hX' n2 t
  rw [← hc] at b2
  have hND : (N : Int) * ((P N X t : Int) - P N X' t) = hd N X t - hd N X' t := by
    unfold hd; rw [← hc]; ring
  have hNpos : (0 : Int) < N := by exact_mod_cast hN
  have h2' : 2 * (X.card : Int) ≠ N := by exact_mod_cast h2
  have lt1 : (N : Int) * ((P N X t : Int) - P N X' t) < N * 1 := by
    rcases lt_or_gt_of_ne h2' with h | h <;> linarith
  have lt2 : (N : Int) * (-1) < N * ((P N X t : Int) - P N X' t) := by
    rcases lt_or_gt_of_ne h2' with h | h <;> linarith
  have := lt_of_mul_lt_mul_left lt1 hNpos.le
  have := lt_of_mul_lt_mul_left lt2 hNpos.le
  omega

/-- **Size bound.**  For neutral `X` with `g = gcd(|X|, N)`:
`g ⌊N/(2g)⌋ ≤ min(|X|, N - |X|)`. -/
theorem size_bound (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hn : IsNeutral N X) :
    Nat.gcd X.card N * (N / Nat.gcd X.card N / 2) ≤ X.card ∧
      Nat.gcd X.card N * (N / Nat.gcd X.card N / 2) ≤ N - X.card := by
  have hsN : X.card ≤ N := by
    have := Finset.card_le_card hX; rw [Nat.card_Icc] at this; omega
  have hgN : Nat.gcd X.card N * (N / Nat.gcd X.card N) = N :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ N)
  generalize hq : N / Nat.gcd X.card N / 2 = q
  have h2q : 2 * (Nat.gcd X.card N * q) ≤ N := by
    have : q * 2 ≤ N / Nat.gcd X.card N := by rw [← hq]; exact Nat.div_mul_le_self _ _
    calc 2 * (Nat.gcd X.card N * q) = Nat.gcd X.card N * (q * 2) := by ring
      _ ≤ Nat.gcd X.card N * (N / Nat.gcd X.card N) := Nat.mul_le_mul_left _ this
      _ = N := hgN
  have bez : (Nat.gcd X.card N : Int) =
      X.card * Nat.gcdA X.card N + N * Nat.gcdB X.card N := Nat.gcd_eq_gcd_ab _ _
  have hNpos : (0 : Int) < N := by exact_mod_cast hN
  have htz : (((-Nat.gcdA X.card N * q) % N).toNat : Int) =
      -Nat.gcdA X.card N * q - N * ((-Nat.gcdA X.card N * q) / N) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hNpos.ne'), Int.emod_def]
  generalize ((-Nat.gcdA X.card N * q) % N).toNat = t at htz
  have key : hd N X t - Nat.gcd X.card N * q = N * ((P N X t : Int) +
      X.card * ((-Nat.gcdA X.card N * q) / N) - Nat.gcdB X.card N * q) := by
    unfold hd; rw [htz, bez]; ring
  generalize ((P N X t : Int) + X.card * ((-Nat.gcdA X.card N * q) / N) -
      Nat.gcdB X.card N * q) = w at key
  have b := hd_bounds hN hX hn t
  have h2q' : 2 * ((Nat.gcd X.card N : Int) * q) ≤ N := by exact_mod_cast h2q
  have neg : ∀ μ : Int, hd N X t ≤ μ → -μ ≤ hd N X t →
      ((Nat.gcd X.card N : Int) * q : Int) ≤ μ := by
    intro μ hu hl
    by_contra hc
    push_neg at hc
    have h1 : (N : Int) * w < 0 := by linarith
    have hw0 : w < 0 := by
      by_contra hw0; push_neg at hw0; nlinarith
    have : (N : Int) * w ≤ N * (-1) := mul_le_mul_of_nonneg_left (by omega) hNpos.le
    linarith
  have c1 := neg X.card b.1 b.2.2.1
  have c2 := neg ((N : Int) - X.card) b.2.1 b.2.2.2
  constructor
  · exact_mod_cast c1
  · have : ((Nat.gcd X.card N * q : Nat) : Int) ≤ ((N - X.card : Nat) : Int) := by
      push_cast [hsN]; linarith
    exact_mod_cast this

/-- The size bound in the form `|X| = g a`, `N = g d`, `⌊d/2⌋ ≤ a`, `⌊d/2⌋ ≤ d - a`. -/
theorem size_ad (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hn : IsNeutral N X) :
    ∃ g a d, 0 < g ∧ X.card = g * a ∧ N = g * d ∧ d / 2 ≤ a ∧ d / 2 ≤ d - a := by
  obtain ⟨b1, b2⟩ := size_bound hN hX hn
  have hg : 0 < Nat.gcd X.card N := Nat.gcd_pos_of_pos_right _ hN
  have hs := (Nat.mul_div_cancel' (Nat.gcd_dvd_left X.card N)).symm
  have hNd := (Nat.mul_div_cancel' (Nat.gcd_dvd_right X.card N)).symm
  refine ⟨Nat.gcd X.card N, X.card / Nat.gcd X.card N, N / Nat.gcd X.card N, hg, hs, hNd,
    Nat.le_of_mul_le_mul_left (by rw [← hs]; exact b1) hg,
    Nat.le_of_mul_le_mul_left ?_ hg⟩
  rw [Nat.mul_sub, ← hs, ← hNd]; exact b2

/-- **Proper neutral sets are large:** `N ≤ 3 |X|`. -/
theorem three_mul_card (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hn : IsNeutral N X)
    (h0 : 0 < X.card) (h1 : X.card < N) : N ≤ 3 * X.card := by
  obtain ⟨g, a, d, hg, hs, hNd, l1, l2⟩ := size_ad hN hX hn
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, Nat.mul_zero] at hNd; omega
    · exact h
  have hd2 : 2 ≤ d := by
    by_contra hc
    have hd : d = 1 := by omega
    rw [hd, Nat.mul_one] at hNd
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, Nat.mul_zero] at hs; omega
    · have := Nat.le_mul_of_pos_right g ha; omega
  have : d ≤ 3 * a := by omega
  rw [hNd, hs]
  calc g * d ≤ g * (3 * a) := Nat.mul_le_mul_left _ this
    _ = 3 * (g * a) := by ring

/-- **Sizes of proper neutral sets.**  If `2|X| ≠ N` there is an odd `d ∣ N`, `d ≥ 3`, with
`|X| = (d ∓ 1) N / (2d)`. -/
theorem size_odd (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hn : IsNeutral N X)
    (h0 : 0 < X.card) (h1 : X.card < N) (h2 : 2 * X.card ≠ N) :
    ∃ d, d ∣ N ∧ d % 2 = 1 ∧ 3 ≤ d ∧
      (2 * X.card * d = (d - 1) * N ∨ 2 * X.card * d = (d + 1) * N) := by
  obtain ⟨g, a, d, hg, hs, hNd, l1, l2⟩ := size_ad hN hX hn
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, Nat.mul_zero] at hNd; omega
    · exact h
  have hodd : d % 2 = 1 := by
    by_contra hc
    have : 2 * a = d := by omega
    apply h2; rw [hs, hNd, ← this]; ring
  have hd3 : 3 ≤ d := by
    by_contra hc
    have hd : d = 1 := by omega
    rw [hd, Nat.mul_one] at hNd
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, Nat.mul_zero] at hs; omega
    · have := Nat.le_mul_of_pos_right g ha; omega
  refine ⟨d, ⟨g, by rw [hNd]; ring⟩, hodd, hd3, ?_⟩
  rcases Nat.lt_or_ge a (d / 2 + 1) with h | h
  · left
    have e : 2 * a = d - 1 := by omega
    rw [hs, hNd, ← e]; ring
  · right
    have e : 2 * a = d + 1 := by omega
    rw [hs, hNd, ← e]; ring

/-! ## The half case: parity classes -/

/-- **Half case.**  A neutral set of size `N/2` is the set of odd or of even panels. -/
theorem neutral_half (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hn : IsNeutral N X)
    (h2 : 2 * X.card = N) : X = parCls N 1 ∨ X = parCls N 2 := by
  have hdb := (neutral_iff_dbl hN hX).1 hn
  have hs : (0 : Int) < X.card := by
    have : 0 < X.card := by omega
    exact_mod_cast this
  have h2' : (N : Int) = 2 * X.card := by exact_mod_cast h2.symm
  -- `P (2u) = u`
  have heven : ∀ u, P N X (2 * u) = u := by
    intro u
    have b := hd_bounds hN hX hn (2 * u)
    unfold hd at b
    rw [h2'] at b
    have e : (2 * (X.card : Int)) * (P N X (2 * u) : Int) - X.card * ((2 * u : Nat) : Int) =
        X.card * (2 * ((P N X (2 * u) : Int) - u)) := by push_cast; ring
    rw [e] at b
    have c1 : (P N X (2 * u) : Int) - u ≤ 0 := by
      by_contra hc
      have : (1 : Int) ≤ (P N X (2 * u) : Int) - u := by omega
      nlinarith
    have c2 : 0 ≤ (P N X (2 * u) : Int) - u := by
      by_contra hc
      have : (P N X (2 * u) : Int) - u ≤ -1 := by omega
      nlinarith
    omega
  -- `P (2k + 1) = k + P 1`
  have hodd : ∀ k, P N X (2 * k + 1) = k + P N X 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.even_or_odd' k with ⟨u, rfl | rfl⟩
      · rcases Nat.eq_zero_or_pos u with rfl | hu
        · simp
        · have := hdb (2 * u)
          unfold Dbl at this
          rw [heven u, ih u (by omega)] at this
          rw [this]; omega
      · have := hdb (2 * u + 1)
        unfold Dbl at this
        rw [show 2 * u + 1 + 1 = 2 * (u + 1) by ring, heven, ih u (by omega)] at this
        rw [this]; omega
  have hP1 : P N X 1 ≤ 1 := by
    rw [show (1 : Nat) = 0 + 1 from rfl, P_succ, P_zero]; exact Nat.zero_add _ ▸ xi_le_one _
  have xodd : ∀ u, xi N X (2 * u + 1) = P N X 1 := by
    intro u; have := P_succ (N := N) (X := X) (2 * u); rw [hodd, heven] at this; omega
  have xeven : ∀ u, xi N X (2 * u + 2) + P N X 1 = 1 := by
    intro u; have := P_succ (N := N) (X := X) (2 * u + 1)
    rw [show 2 * u + 1 + 1 = 2 * (u + 1) by ring, hodd, heven] at this
    rw [show 2 * u + 2 = 2 * (u + 1) by ring]; omega
  have hxi : ∀ x, 1 ≤ x → (xi N X x = 1 ↔ (x % 2 = 1 ↔ P N X 1 = 1)) := by
    intro x hx
    rcases Nat.even_or_odd' x with ⟨u, rfl | rfl⟩
    · obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
      have := xeven v
      rw [show 2 * (v + 1) = 2 * v + 2 by ring]; omega
    · rw [xodd]; omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hP1 with h | h
  · right
    ext x
    rw [mem_parCls (by omega) le_rfl]
    constructor
    · intro hx
      have hm := hX hx
      rw [mem_iff_xi hN hm, hxi x (Finset.mem_Icc.1 hm).1] at hx
      rw [Finset.mem_Icc] at hm; omega
    · rintro ⟨a1, a2, a3⟩
      rw [mem_iff_xi hN (Finset.mem_Icc.2 ⟨a1, a2⟩), hxi x a1]; omega
  · left
    ext x
    rw [mem_parCls le_rfl (by omega)]
    constructor
    · intro hx
      have hm := hX hx
      rw [mem_iff_xi hN hm, hxi x (Finset.mem_Icc.1 hm).1] at hx
      rw [Finset.mem_Icc] at hm; omega
    · rintro ⟨a1, a2, a3⟩
      rw [mem_iff_xi hN (Finset.mem_Icc.2 ⟨a1, a2⟩), hxi x a1]; omega

/-! ## The antichain property -/

/-- **Proper neutral sets never contain one another.** -/
theorem neutral_antichain {Y : Finset Nat} (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N)
    (hY : Y ⊆ Finset.Icc 1 N) (nX : IsNeutral N X) (nY : IsNeutral N Y) (pX : 0 < X.card)
    (pY : Y.card < N) (hXY : X ⊆ Y) : X = Y := by
  by_contra hne
  have hZ : Y \ X ⊆ Finset.Icc 1 N := fun x hx => hY (Finset.mem_sdiff.1 hx).1
  have hW : Finset.Icc 1 N \ Y ⊆ Finset.Icc 1 N := Finset.sdiff_subset
  have nZ := neutral_sdiff hXY nX nY
  have nW := neutral_sdiff hY nY (neutral_full N)
  have cZ : (Y \ X).card = Y.card - X.card := Finset.card_sdiff_of_subset hXY
  have cW : (Finset.Icc 1 N \ Y).card = N - Y.card := by
    rw [Finset.card_sdiff_of_subset hY, Nat.card_Icc]; omega
  have lt : X.card < Y.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hXY, hne⟩)
  have t1 := three_mul_card hN hX nX pX (by omega)
  have t2 := three_mul_card hN hZ nZ (by omega) (by omega)
  have t3 := three_mul_card hN hW nW (by omega) (by omega)
  have e := neutral_unique hN hX hZ nX nZ (by omega) (by omega)
  have : X = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    have := e ▸ hx
    exact (Finset.mem_sdiff.1 this).2 hx
  rw [this] at pX; simp at pX

end Neutral
end Folds
