import Mathlib

/-!
# Period law III: arithmetic lemmas behind the bound `rest2(s,a) < 2`

See `experiments/periods5/PROOFS.txt`.  The analytic part (products of cosecants, the fold
decomposition, the ball-arithmetic evaluation) is not formalised.  This file checks the
arithmetic and combinatorial facts the argument uses:

* `weights_total`, `weights_lt`: `Σ_{i ≤ n} C(i+a, a) 2^(n-i) + Σ_{j ≤ a} C(n+a+1, j) = 2^(n+a+1)`;
  in particular the equality-row weights satisfy `Σ_{e ≤ s} C(e+a, a) 2^(s-e) < 2^(s+a+1)`
  (Lemma 2.2 of PROOFS.txt).
-/

namespace PeriodLaw3

open Finset

/-- Pascal summed over `j ≤ a`: `Σ_{j≤a} C(N+1, j) + C(N, a) = 2 Σ_{j≤a} C(N, j)`. -/
theorem pascal_partial (N a : ℕ) :
    (∑ j ∈ range (a + 1), N.succ.choose j) + N.choose a = 2 * ∑ j ∈ range (a + 1), N.choose j := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ, sum_range_succ (fun j => N.choose j), Nat.choose_succ_succ]
    linarith

/-- The weight identity. -/
theorem weights_total (a n : ℕ) :
    (∑ i ∈ range (n + 1), (i + a).choose a * 2 ^ (n - i)) +
      (∑ j ∈ range (a + 1), (n + a + 1).choose j) = 2 ^ (n + a + 1) := by
  induction n with
  | zero =>
    simp only [zero_add, sum_range_one, Nat.choose_self, Nat.sub_self, pow_zero, mul_one]
    have h := Nat.sum_range_choose (a + 1)
    rw [sum_range_succ, Nat.choose_self] at h
    omega
  | succ n ih =>
    have hS : (∑ i ∈ range (n + 1 + 1), (i + a).choose a * 2 ^ (n + 1 - i)) =
        2 * (∑ i ∈ range (n + 1), (i + a).choose a * 2 ^ (n - i)) + (n + 1 + a).choose a := by
      rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_sum]
      congr 1
      apply sum_congr rfl
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
      rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
      ring
    have hT := pascal_partial (n + a + 1) a
    rw [Nat.succ_eq_add_one] at hT
    rw [hS, show n + 1 + a + 1 = (n + a + 1) + 1 by omega, show n + 1 + a = n + a + 1 by omega,
      pow_succ]
    omega

/-- The equality-row weights are below `2^(n+a+1)`. -/
theorem weights_lt (a n : ℕ) :
    (∑ i ∈ range (n + 1), (i + a).choose a * 2 ^ (n - i)) < 2 ^ (n + a + 1) := by
  have h := weights_total a n
  have hpos : 0 < ∑ j ∈ range (a + 1), (n + a + 1).choose j := by
    apply Nat.lt_of_lt_of_le (Nat.one_pos)
    calc 1 = (n + a + 1).choose 0 := by simp
      _ ≤ ∑ j ∈ range (a + 1), (n + a + 1).choose j :=
        single_le_sum (f := fun j => (n + a + 1).choose j) (fun _ _ => Nat.zero_le _)
          (mem_range.mpr (Nat.succ_pos a))
  omega

end PeriodLaw3
