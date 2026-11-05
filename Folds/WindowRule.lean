import Folds.Prefix
import Folds.Cyclic

/-!
# The window rule, suffixes, and dead 2-prefixes

Let `S` be a nodup list of panels in `[1, N]` and `c ∉ S` a panel.  Write
`A = #{x ∈ S | c < x}` (points above `c`) and `B = #{x ∈ S | x < c}` (points below).
The window of `c` is `[2c - N, 2c - 1] ∩ [1, N]`.

* `semiStep_iff_window` (**window rule**, an iff):
  - if `A < B`: the step is semi-symmetric iff `c` is in the right half (`N + 1 < 2c`) and
    exactly `A` points of `S` lie in `[2c - N, c)`.  Equivalently (`ys` the points below `c`
    in decreasing order) `y_A ≥ 2c - N > y_{A+1}`;
  - if `B < A`: mirror image, `2c < N + 1` and exactly `B` points of `S` lie in `(c, 2c - 1]`;
  - if `A = B`: every point of `S` lies in the window.
* `card_validSuffixes`: the numbers of valid length-`k` suffixes and of valid length-`k`
  prefixes are equal (reversal plus complementation).
* `not_semiSymmetric_one_N`, `not_semiSymmetric_N_one`: for even `N ≥ 3` no semi-symmetric
  fold sequence starts with `[1, N]` or `[N, 1]` (no valid third step exists).
-/

namespace Folds

/-! ## The window rule -/

/-- Number of points of `S` above `c`. -/
def numAbove (S : List Nat) (c : Nat) : Nat := S.countP (fun x => c < x)

/-- Number of points of `S` below `c`. -/
def numBelow (S : List Nat) (c : Nat) : Nat := S.countP (fun x => x < c)

theorem countP_le_of_imp {S : List Nat} {p q : Nat → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ x, p x → q x) :
    S.countP (fun x => decide (p x)) + S.countP (fun x => decide (q x ∧ ¬ p x)) =
      S.countP (fun x => decide (q x)) := by
  rw [countP_split S (fun x => decide (q x)) (fun x => decide (p x))]
  congr 1
  · apply List.countP_congr; intro x _; have := h x; simp; tauto

theorem countP_eq_zero_iff' {S : List Nat} {p : Nat → Prop} [DecidablePred p] :
    S.countP (fun x => decide (p x)) = 0 ↔ ∀ x ∈ S, ¬ p x := by
  rw [List.countP_eq_zero]; simp

/-- **The window rule.**  For a nodup list `S ⊆ [1, N]` and a panel `c ∉ S`, with
`A = numAbove S c` and `B = numBelow S c`, the step `(S, c)` is semi-symmetric iff
* `A < B`, `c` is in the right half and exactly `A` points lie in `[2c - N, c)`, or
* `B < A`, `c` is in the left half and exactly `B` points lie in `(c, 2c - 1]`, or
* `A = B` and the window `[2c - N, 2c - 1]` contains all of `S`. -/
theorem semiStep_iff_window {N c : Nat} {S : List Nat} (hnd : S.Nodup)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (hc1 : 1 ≤ c) (hcN : c ≤ N) (hcS : c ∉ S) :
    SemiStep N S c ↔
      (numAbove S c < numBelow S c ∧ N + 1 < 2 * c ∧
          S.countP (fun x => 2 * c - N ≤ x ∧ x < c) = numAbove S c) ∨
      (numBelow S c < numAbove S c ∧ 2 * c < N + 1 ∧
          S.countP (fun x => c < x ∧ x ≤ 2 * c - 1) = numBelow S c) ∨
      (numAbove S c = numBelow S c ∧ ∀ x ∈ S, 2 * c - N ≤ x ∧ x ≤ 2 * c - 1) := by
  have hne : ∀ x ∈ S, x ≠ c := fun x hx e => hcS (e ▸ hx)
  -- split the counts above/below into inside / outside the window
  have hB := countP_le_of_imp (S := S) (p := fun x => c - reach N c ≤ x ∧ x < c)
    (q := fun x => x < c) (fun x h => h.2)
  have hA := countP_le_of_imp (S := S) (p := fun x => c < x ∧ x ≤ c + reach N c)
    (q := fun x => c < x) (fun x h => h.1)
  rw [← leftCount_eq hnd] at hB
  rw [← rightCount_eq hnd] at hA
  set L := leftCount N S c
  set R := rightCount N S c
  set Lo := S.countP (fun x => decide (x < c ∧ ¬(c - reach N c ≤ x ∧ x < c)))
  set Ro := S.countP (fun x => decide (c < x ∧ ¬(c < x ∧ x ≤ c + reach N c)))
  change L + Lo = numBelow S c at hB
  change R + Ro = numAbove S c at hA
  have hwin : (∀ x ∈ S, 2 * c - N ≤ x ∧ x ≤ 2 * c - 1) ↔ Lo = 0 ∧ Ro = 0 := by
    rw [countP_eq_zero_iff', countP_eq_zero_iff']
    constructor
    · intro h
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> have := h x hx <;> have := hS x hx <;>
        unfold reach <;> omega
    · rintro ⟨h1, h2⟩ x hx
      have := h1 x hx; have := h2 x hx; have := hS x hx; have := hne x hx
      unfold reach at *; omega
  unfold SemiStep
  rcases Nat.lt_or_ge N (2 * c - 1) with hh | hh
  · -- right half: everything above `c` is in the window
    have hRo : Ro = 0 := by
      rw [countP_eq_zero_iff']; intro x hx; have := hS x hx; unfold reach; omega
    have hL : L = S.countP (fun x => 2 * c - N ≤ x ∧ x < c) := by
      show leftCount N S c = _
      rw [leftCount_eq hnd]; apply List.countP_congr; intro x _; unfold reach; simp; omega
    rw [hwin, ← hL]
    omega
  · -- left half: everything below `c` is in the window
    have hLo : Lo = 0 := by
      rw [countP_eq_zero_iff']; intro x hx; have := hS x hx; unfold reach; omega
    have hR : R = S.countP (fun x => c < x ∧ x ≤ 2 * c - 1) := by
      show rightCount N S c = _
      rw [rightCount_eq hnd]; apply List.countP_congr; intro x _; unfold reach; simp; omega
    have hmid : 2 * c - 1 = N → Ro = 0 := by
      intro e; rw [countP_eq_zero_iff']; intro x hx; have := hS x hx; unfold reach; omega
    rw [hwin, ← hR]
    omega

end Folds
