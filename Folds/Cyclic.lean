import Folds.Basic
import Folds.Decide

/-!
# The cyclic ("doubling") reformulation of a semi-symmetric step

Write `P(j) = below S j = #{x ∈ S | x ≤ j}` and `s = |S|`.  For a nodup `S ⊆ [1, N]`
and a panel `1 ≤ m ≤ N` with `m ∉ S`:

1. **Interval-count form** (`leftCount_eq`, `rightCount_eq`, only needs `S.Nodup`):
   `leftCount N S m = #{x ∈ S | m - r ≤ x < m}` and
   `rightCount N S m = #{x ∈ S | m < x ≤ m + r}` where `r = reach N m`.
2. **Prefix form**: on the left half (`2m - 1 ≤ N`) the step is semi-symmetric iff
   `P(2m-1) = 2·P(m-1)` (`semiStep_iff_left`); on the right half (`N ≤ 2m - 1`) iff
   `s + P(2m-1-N) = 2·P(m-1)` (`semiStep_iff_right`).
3. **Cyclic form** (`semiStep_iff_cyclicStep`): with `P̃(j) = P(j mod N) + ⌊j/N⌋·s`,
   both halves read `P̃(2m-1) = 2·P(m-1)`.  (When `2m - 1 = N` both halves apply;
   the right-half formula is used, `P(0) = 0` is not even needed.)
-/

namespace Folds

theorem countP_split {α} (l : List α) (p q : α → Bool) :
    l.countP p = l.countP (fun x => p x && q x) + l.countP (fun x => p x && !q x) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

theorem countP_eq_nodup {S : List Nat} (hnd : S.Nodup) (c : Nat) :
    S.countP (fun x => x = c) = if c ∈ S then 1 else 0 := by
  induction S with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.countP_cons, ih hnd.2, List.mem_cons]
    by_cases h : a = c
    · subst h; simp [hnd.1]
    · by_cases hc : c ∈ t <;> simp [h, hc, Ne.symm h]

theorem countP_left {S : List Nat} (hnd : S.Nodup) (m : Nat) :
    ∀ r, r < m → (List.range' 1 r).countP (fun d => m - d ∈ S) =
      S.countP (fun x => m - r ≤ x ∧ x < m)
  | 0, _ => by
    simp only [List.range'_zero, List.countP_nil]
    symm; rw [List.countP_eq_zero]; intro x _; simp
  | r + 1, hr => by
    rw [List.range'_concat, List.countP_append, countP_left hnd m r (by omega),
      countP_split S (fun x => decide (m - (r+1) ≤ x ∧ x < m)) (fun x => decide (x = m - (r + 1)))]
    have h1 : S.countP (fun x => decide (m - (r+1) ≤ x ∧ x < m) && decide (x = m - (r + 1)))
        = S.countP (fun x => x = m - (r+1)) := by
      apply List.countP_congr; intro x _; simp; omega
    have h2 : S.countP (fun x => decide (m - (r+1) ≤ x ∧ x < m) && !decide (x = m - (r + 1)))
        = S.countP (fun x => m - r ≤ x ∧ x < m) := by
      apply List.countP_congr; intro x _; simp; omega
    rw [h1, h2, countP_eq_nodup hnd]
    simp [Nat.add_comm 1 r]
    omega

theorem countP_right {S : List Nat} (hnd : S.Nodup) (m : Nat) :
    ∀ r, (List.range' 1 r).countP (fun d => m + d ∈ S) =
      S.countP (fun x => m < x ∧ x ≤ m + r)
  | 0 => by
    simp only [List.range'_zero, List.countP_nil]
    symm; rw [List.countP_eq_zero]; intro x _; simp
  | r + 1 => by
    rw [List.range'_concat, List.countP_append, countP_right hnd m r,
      countP_split S (fun x => decide (m < x ∧ x ≤ m + (r + 1))) (fun x => decide (x = m + (r + 1)))]
    have h1 : S.countP (fun x => decide (m < x ∧ x ≤ m + (r + 1)) && decide (x = m + (r + 1)))
        = S.countP (fun x => x = m + (r+1)) := by
      apply List.countP_congr; intro x _; simp; omega
    have h2 : S.countP (fun x => decide (m < x ∧ x ≤ m + (r + 1)) && !decide (x = m + (r + 1)))
        = S.countP (fun x => m < x ∧ x ≤ m + r) := by
      apply List.countP_congr; intro x _; simp; omega
    rw [h1, h2, countP_eq_nodup hnd]
    simp [Nat.add_comm 1 r]
    omega

/-! ## Interval-count form -/

theorem leftCount_eq {N m : Nat} {S : List Nat} (hnd : S.Nodup) :
    leftCount N S m = S.countP (fun x => m - reach N m ≤ x ∧ x < m) := by
  unfold leftCount
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    have : reach N 0 = 0 := by simp [reach]
    rw [this]; simp only [List.range'_zero, List.countP_nil]
    symm; rw [List.countP_eq_zero]; intro x _; simp
  · exact countP_left hnd m _ (by unfold reach; omega)

theorem rightCount_eq {N m : Nat} {S : List Nat} (hnd : S.Nodup) :
    rightCount N S m = S.countP (fun x => m < x ∧ x ≤ m + reach N m) :=
  countP_right hnd m _

/-! ## Prefix form -/

/-- `below S j = #{x ∈ S | x ≤ j}`, the prefix count `P(j)`. -/
def below (S : List Nat) (j : Nat) : Nat := S.countP (· ≤ j)

theorem below_split (S : List Nat) {j k : Nat} (h : j ≤ k) :
    below S k = below S j + S.countP (fun x => j < x ∧ x ≤ k) := by
  unfold below
  rw [countP_split S (fun x => decide (x ≤ k)) (fun x => decide (x ≤ j))]
  congr 1 <;> apply List.countP_congr <;> intro x _ <;> simp <;> omega

theorem below_of_not_mem {S : List Nat} {m : Nat} (hm1 : 1 ≤ m) (hmS : m ∉ S) :
    below S m = below S (m - 1) := by
  rw [below_split S (show m - 1 ≤ m by omega)]
  have : S.countP (fun x => m - 1 < x ∧ x ≤ m) = 0 := by
    rw [List.countP_eq_zero]; intro x hx hc; simp at hc
    have : x = m := by omega
    subst this; exact hmS hx
  omega

theorem below_zero {S : List Nat} (hpos : ∀ x ∈ S, 1 ≤ x) : below S 0 = 0 := by
  unfold below; rw [List.countP_eq_zero]; intro x hx; have := hpos x hx; simp; omega

theorem below_eq_length {S : List Nat} {N : Nat} (hle : ∀ x ∈ S, x ≤ N) :
    below S N = S.length := by
  unfold below; rw [List.countP_eq_length]; intro x hx; simpa using hle x hx

/-- Left half: the reference crease is `2m - 1`. -/
theorem semiStep_iff_left {N m : Nat} {S : List Nat} (hnd : S.Nodup)
    (hpos : ∀ x ∈ S, 1 ≤ x) (hm1 : 1 ≤ m) (h : 2 * m - 1 ≤ N) (hmS : m ∉ S) :
    SemiStep N S m ↔ below S (2 * m - 1) = 2 * below S (m - 1) := by
  have hr : reach N m = m - 1 := by unfold reach; omega
  have hl : leftCount N S m = below S (m - 1) := by
    rw [leftCount_eq hnd, hr]; unfold below
    apply List.countP_congr; intro x hx; have := hpos x hx; simp; omega
  have hrc : rightCount N S m = S.countP (fun x => m < x ∧ x ≤ 2 * m - 1) := by
    rw [rightCount_eq hnd, hr]
    apply List.countP_congr; intro x _; simp; omega
  have h1 := below_split S (show m ≤ 2 * m - 1 by omega)
  have h2 := below_of_not_mem hm1 hmS
  unfold SemiStep; omega

/-- Right half: the reference crease wraps around to `2m - 1 - N`. -/
theorem semiStep_iff_right {N m : Nat} {S : List Nat} (hnd : S.Nodup)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (hm1 : 1 ≤ m) (hmN : m ≤ N) (h : N ≤ 2 * m - 1)
    (hmS : m ∉ S) :
    SemiStep N S m ↔ S.length + below S (2 * m - 1 - N) = 2 * below S (m - 1) := by
  have hr : reach N m = N - m := by unfold reach; omega
  have hl : leftCount N S m = S.countP (fun x => 2 * m - 1 - N < x ∧ x ≤ m - 1) := by
    rw [leftCount_eq hnd, hr]
    apply List.countP_congr; intro x _; simp; omega
  have hrc : rightCount N S m = S.countP (fun x => m < x ∧ x ≤ N) := by
    rw [rightCount_eq hnd, hr]
    apply List.countP_congr; intro x _; simp; omega
  have h1 := below_split S (show 2 * m - 1 - N ≤ m - 1 by omega)
  have h2 := below_split S hmN
  have h3 := below_of_not_mem hm1 hmS
  have h4 := below_eq_length (fun x hx => (hS x hx).2)
  unfold SemiStep; omega

/-! ## The cyclic ("doubling") form -/

/-- Quasi-periodic extension of `below`: `P̃(j) = P(j mod N) + ⌊j / N⌋ · s`. -/
def cycBelow (N : Nat) (S : List Nat) (j : Nat) : Nat :=
  below S (j % N) + (j / N) * S.length

/-- The cyclic reformulation of a semi-symmetric step: `P̃(2m - 1) = 2 · P(m - 1)`. -/
def CyclicStep (N : Nat) (S : List Nat) (m : Nat) : Prop :=
  cycBelow N S (2 * m - 1) = 2 * below S (m - 1)

instance (N : Nat) (S : List Nat) (m : Nat) : Decidable (CyclicStep N S m) :=
  inferInstanceAs (Decidable (_ = _))

theorem semiStep_iff_cyclicStep {N m : Nat} {S : List Nat} (hnd : S.Nodup)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (hm1 : 1 ≤ m) (hmN : m ≤ N) (hmS : m ∉ S) :
    SemiStep N S m ↔ CyclicStep N S m := by
  have hpos : ∀ x ∈ S, 1 ≤ x := fun x hx => (hS x hx).1
  unfold CyclicStep cycBelow
  rcases Nat.lt_or_ge (2 * m - 1) N with h | h
  · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, Nat.zero_mul, Nat.add_zero]
    exact semiStep_iff_left hnd hpos hm1 (by omega) hmS
  · have hN : 0 < N := by omega
    have hlt : 2 * m - 1 - N < N := by omega
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt hlt, Nat.div_eq_sub_div hN h,
      Nat.div_eq_of_lt hlt, Nat.zero_add, Nat.one_mul, Nat.add_comm]
    exact semiStep_iff_right hnd hS hm1 hmN h hmS

/-! ## Corollaries -/

/-- Complement within the window, in cyclic form: replacing `S` by a set `T` that agrees
with the complement of `S` on the window around `m` does not change `CyclicStep`. -/
theorem cyclicStep_iff_of_compl {N m : Nat} {S T : List Nat}
    (hndS : S.Nodup) (hndT : T.Nodup)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (hT : ∀ x ∈ T, 1 ≤ x ∧ x ≤ N)
    (hm1 : 1 ≤ m) (hmN : m ≤ N) (hmS : m ∉ S) (hmT : m ∉ T)
    (hST : ∀ d, 1 ≤ d → d ≤ reach N m →
      ((m - d ∈ T ↔ m - d ∉ S) ∧ (m + d ∈ T ↔ m + d ∉ S))) :
    CyclicStep N S m ↔ CyclicStep N T m := by
  rw [← semiStep_iff_cyclicStep hndS hS hm1 hmN hmS,
    ← semiStep_iff_cyclicStep hndT hT hm1 hmN hmT]
  exact semiStep_iff_of_compl hST

/-- Complement within the window, in prefix form (left half). -/
theorem prefix_left_iff_of_compl {N m : Nat} {S T : List Nat}
    (hndS : S.Nodup) (hndT : T.Nodup)
    (hS : ∀ x ∈ S, 1 ≤ x) (hT : ∀ x ∈ T, 1 ≤ x)
    (hm1 : 1 ≤ m) (h : 2 * m - 1 ≤ N) (hmS : m ∉ S) (hmT : m ∉ T)
    (hST : ∀ d, 1 ≤ d → d ≤ reach N m →
      ((m - d ∈ T ↔ m - d ∉ S) ∧ (m + d ∈ T ↔ m + d ∉ S))) :
    below S (2 * m - 1) = 2 * below S (m - 1) ↔
      below T (2 * m - 1) = 2 * below T (m - 1) := by
  rw [← semiStep_iff_left hndS hS hm1 h hmS, ← semiStep_iff_left hndT hT hm1 h hmT]
  exact semiStep_iff_of_compl hST

/-- Complement within the window, in prefix form (right half). -/
theorem prefix_right_iff_of_compl {N m : Nat} {S T : List Nat}
    (hndS : S.Nodup) (hndT : T.Nodup)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (hT : ∀ x ∈ T, 1 ≤ x ∧ x ≤ N)
    (hm1 : 1 ≤ m) (hmN : m ≤ N) (h : N ≤ 2 * m - 1) (hmS : m ∉ S) (hmT : m ∉ T)
    (hST : ∀ d, 1 ≤ d → d ≤ reach N m →
      ((m - d ∈ T ↔ m - d ∉ S) ∧ (m + d ∈ T ↔ m + d ∉ S))) :
    S.length + below S (2 * m - 1 - N) = 2 * below S (m - 1) ↔
      T.length + below T (2 * m - 1 - N) = 2 * below T (m - 1) := by
  rw [← semiStep_iff_right hndS hS hm1 hmN h hmS, ← semiStep_iff_right hndT hT hm1 hmN h hmT]
  exact semiStep_iff_of_compl hST

/-- A dead end: for `N = 4`, `[1, 4]` is a valid start, but neither remaining panel
can be bisected next. -/
theorem deadEnd_four :
    SemiSymmetric 4 [1, 4] ∧ ∀ m ∈ [2, 3], ¬ SemiStep 4 [1, 4] m := by
  decide

end Folds
