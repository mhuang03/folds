import Mathlib.Order.Interval.Finset.Nat
import Folds.Cyclic

/-!
# The imbalance field and its dipole update

For a list `S` of already-bisected panels and a panel `m`, the *imbalance*
`imb N S m = rightCount N S m - leftCount N S m` (an integer) vanishes exactly when the
step `(S, m)` is semi-symmetric (`semiStep_iff_imb`).  This is the field `J` used in the
asymptotic analysis (`experiments/asymptotics/NOTES.txt`): the valid next panels are
the free zeros of `J`.

Main result (`imb_cons`, the *dipole lemma*): adding a new panel `x` (not in `S`, with
`S` duplicate-free) changes the imbalance at every panel `m ≠ x` of the strip by
  `+1` if `m < x ≤ 2m - 1`        (`x` lies in the right arm of `m`),
  `-1` if `2m - N ≤ x < m`        (`x` lies in the left arm of `m`),
   `0` otherwise.
So `x` acts on the field as a dipole: `+1` on the panels `⌈(x+1)/2⌉ … x-1`, `-1` on the
panels `x+1 … ⌊(N+x)/2⌋`.  The supports have `⌊(x-1)/2⌋` and `⌊(N-x)/2⌋` panels
(`card_plus_support`, `card_minus_support`), so every panel touches about half of the strip.
A panel `m` whose window does not contain `x` keeps its imbalance (`imb_cons_of_not_mem_window`).
-/

namespace Folds

/-- The imbalance of panel `m`: right-arm count minus left-arm count. -/
def imb (N : Nat) (S : List Nat) (m : Nat) : Int :=
  (rightCount N S m : Int) - (leftCount N S m : Int)

theorem semiStep_iff_imb (N : Nat) (S : List Nat) (m : Nat) :
    SemiStep N S m ↔ imb N S m = 0 := by
  unfold SemiStep imb; omega

/-- `x` lies in the right arm of `m`. -/
theorem inRight_iff {N m x : Nat} (hx : x ≤ N) :
    (m < x ∧ x ≤ m + reach N m) ↔ (m < x ∧ x + 1 ≤ 2 * m) := by
  unfold reach
  constructor
  · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rcases Nat.le_total (m - 1) (N - m) with h | h
    · rw [Nat.min_eq_left h] at h2; omega
    · rw [Nat.min_eq_right h] at h2; omega
  · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rcases Nat.le_total (m - 1) (N - m) with h | h
    · rw [Nat.min_eq_left h]; omega
    · rw [Nat.min_eq_right h]; omega

/-- `x` lies in the left arm of `m`. -/
theorem inLeft_iff {N m x : Nat} (hx : 1 ≤ x) (hm : 1 ≤ m) (hmN : m ≤ N) :
    (m - reach N m ≤ x ∧ x < m) ↔ (x < m ∧ 2 * m ≤ N + x) := by
  unfold reach
  constructor
  · rintro ⟨h1, h2⟩; refine ⟨h2, ?_⟩; rcases Nat.le_total (m - 1) (N - m) with h | h
    · rw [Nat.min_eq_left h] at h1; omega
    · rw [Nat.min_eq_right h] at h1; omega
  · rintro ⟨h1, h2⟩; refine ⟨?_, h1⟩; rcases Nat.le_total (m - 1) (N - m) with h | h
    · rw [Nat.min_eq_left h]; omega
    · rw [Nat.min_eq_right h]; omega

theorem leftCount_cons {N m x : Nat} {S : List Nat} (hnd : S.Nodup) (hx : x ∉ S) :
    leftCount N (x :: S) m =
      leftCount N S m + (if m - reach N m ≤ x ∧ x < m then 1 else 0) := by
  have hnd' : (x :: S).Nodup := List.nodup_cons.2 ⟨hx, hnd⟩
  rw [leftCount_eq hnd', leftCount_eq hnd, List.countP_cons]
  by_cases h : m - reach N m ≤ x ∧ x < m <;> simp [h]

theorem rightCount_cons {N m x : Nat} {S : List Nat} (hnd : S.Nodup) (hx : x ∉ S) :
    rightCount N (x :: S) m =
      rightCount N S m + (if m < x ∧ x ≤ m + reach N m then 1 else 0) := by
  have hnd' : (x :: S).Nodup := List.nodup_cons.2 ⟨hx, hnd⟩
  rw [rightCount_eq hnd', rightCount_eq hnd, List.countP_cons]
  by_cases h : m < x ∧ x ≤ m + reach N m <;> simp [h]

/-- **Dipole lemma.** Adding panel `x` changes the imbalance of panel `m` by `+1` if `x`
is in the right arm of `m` (`m < x ≤ 2m - 1`), by `-1` if `x` is in the left arm
(`2m - N ≤ x < m`), and leaves it unchanged otherwise. -/
theorem imb_cons {N m x : Nat} {S : List Nat} (hnd : S.Nodup) (hx : x ∉ S)
    (hx1 : 1 ≤ x) (hm : 1 ≤ m) (hmN : m ≤ N) (hxN : x ≤ N) :
    imb N (x :: S) m = imb N S m
      + (if m < x ∧ x + 1 ≤ 2 * m then 1 else 0)
      - (if x < m ∧ 2 * m ≤ N + x then 1 else 0) := by
  unfold imb
  rw [leftCount_cons hnd hx, rightCount_cons hnd hx]
  simp only [inRight_iff (N := N) (m := m) hxN, inLeft_iff (N := N) (x := x) hx1 hm hmN]
  split_ifs <;> push_cast <;> omega

/-- A panel whose window does not contain `x` is unaffected by adding `x`. -/
theorem imb_cons_of_not_mem_window {N m x : Nat} {S : List Nat} (hnd : S.Nodup)
    (hx : x ∉ S) (hx1 : 1 ≤ x) (hm : 1 ≤ m) (hmN : m ≤ N) (hxN : x ≤ N)
    (hw : ¬ (m < x ∧ x + 1 ≤ 2 * m)) (hw' : ¬ (x < m ∧ 2 * m ≤ N + x)) :
    imb N (x :: S) m = imb N S m := by
  rw [imb_cons hnd hx hx1 hm hmN hxN]; simp [hw, hw']

/-- Validity of `m` is unaffected by adding `x` outside its window. -/
theorem semiStep_cons_iff {N m x : Nat} {S : List Nat} (hnd : S.Nodup)
    (hx : x ∉ S) (hx1 : 1 ≤ x) (hm : 1 ≤ m) (hmN : m ≤ N) (hxN : x ≤ N)
    (hw : ¬ (m < x ∧ x + 1 ≤ 2 * m)) (hw' : ¬ (x < m ∧ 2 * m ≤ N + x)) :
    SemiStep N (x :: S) m ↔ SemiStep N S m := by
  rw [semiStep_iff_imb, semiStep_iff_imb, imb_cons_of_not_mem_window hnd hx hx1 hm hmN hxN hw hw']

/-- The `+1` support of the dipole of `x`: panels `m` with `m < x ≤ 2m - 1`.  It is the
interval `[x/2 + 1, x - 1]` and has `(x - 1) / 2` elements. -/
theorem plus_support_eq (x : Nat) :
    (Finset.Icc 1 x).filter (fun m => m < x ∧ x + 1 ≤ 2 * m) = Finset.Icc (x / 2 + 1) (x - 1) := by
  ext m; simp only [Finset.mem_filter, Finset.mem_Icc]; omega

theorem card_plus_support (x : Nat) :
    ((Finset.Icc 1 x).filter (fun m => m < x ∧ x + 1 ≤ 2 * m)).card = (x - 1) / 2 := by
  rw [plus_support_eq, Nat.card_Icc]; omega

/-- The `-1` support of the dipole of `x`: panels `m` with `x < m`, `2m ≤ N + x`.  It is the
interval `[x + 1, (N + x)/2]` and has `(N - x) / 2` elements (for `x ≤ N`). -/
theorem minus_support_eq (N x : Nat) :
    (Finset.Icc 1 N).filter (fun m => x < m ∧ 2 * m ≤ N + x) = Finset.Icc (x + 1) ((N + x) / 2) := by
  ext m; simp only [Finset.mem_filter, Finset.mem_Icc]; omega

theorem card_minus_support {N x : Nat} (hx : x ≤ N) :
    ((Finset.Icc 1 N).filter (fun m => x < m ∧ 2 * m ≤ N + x)).card = (N - x) / 2 := by
  rw [minus_support_eq, Nat.card_Icc]; omega

end Folds
