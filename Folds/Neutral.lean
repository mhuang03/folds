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

end Neutral
end Folds
