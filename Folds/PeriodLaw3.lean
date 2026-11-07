import Mathlib

/-!
# Period law III: arithmetic lemmas behind the bound `rest2(s,a) < 2`

See `experiments/periods5/PROOFS.txt`.  The analytic part (products of cosecants, the fold
decomposition, the ball-arithmetic evaluation) is not formalised.  This file checks the
arithmetic and combinatorial facts the argument uses:

* `weights_total`, `weights_lt`: `Σ_{i ≤ n} C(i+a, a) 2^(n-i) + Σ_{j ≤ a} C(n+a+1, j) = 2^(n+a+1)`;
  in particular the equality-row weights satisfy `Σ_{e ≤ s} C(e+a, a) 2^(s-e) < 2^(s+a+1)`
  (Lemma 2.2 of PROOFS.txt).
* `exp_closed_last`, `exp_closed_last_eq`, `exp_closed_last_cl`: the exponent identities of
  Proposition 4.5 (the closed runs and the last run together cost exactly `2^(-as)`).
* `classI_exp`, `class0_exp`, `class0_exp2`, `casec_exp`, `casea_exp`: the endpoint (convexity)
  inequalities of Lemmas 4.1, 4.2 and Proposition 4.5.
* `top_cycle`, `top_chain`: the residues of the top family `u = q/2 + 1` (Lemma 3.1).
* `fold_monotone`: `P_e` does not decrease at a fold (Lemma 2.1).
* `sin_two_pow_le`: `sin(2^j x) ≤ 2^j sin x`, i.e. `κ_j ≤ 2^j` (Lemma 2.2).
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

/-! ### Exponent bookkeeping of Proposition 4.5 (with `m = s + a`) -/

/-- Closed runs times the last run, case `p > a`: the exponent is `-a s` exactly. -/
theorem exp_closed_last (s a g : ℤ) :
    (g + 1) * (g + 1 - (s + a)) + (g + 1 - a) * (s - g - 1) = -(a * s) := by ring

/-- Same with the extra equality row in the last run (term `A_> S_(n+1)`). -/
theorem exp_closed_last_eq (s a g : ℤ) :
    (g + 1) * (g + 1 - (s + a)) + (g + 1 - a) * (s - g) + (s - g) = 1 - a - a * s + s := by ring

/-- Same with the extra equality row in a closed run (term `c A_≤ S_n`), times `2^(m+1)`. -/
theorem exp_closed_last_cl (s a g : ℤ) :
    (g + 2) * (g + 1 - (s + a)) + (g + 1 - a) * (s - g - 1) + (s + a) + 1 = g + 2 - a * s := by
  ring

/-! ### Endpoint (convexity) inequalities used in Lemmas 4.1, 4.2 and 4.5 -/

/-- Class I: `b - 2 - (b-1)(k-b) ≤ 7 - 2k` for `3 ≤ b ≤ k - 6`. -/
theorem classI_exp (b k : ℤ) (h1 : 3 ≤ b) (h2 : b ≤ k - 6) :
    b - 2 - (b - 1) * (k - b) ≤ 7 - 2 * k := by nlinarith

/-- Class 0: `b^2 - b(m-1) + m - 3 ≤ 9 - 2m` for `3 ≤ b ≤ m - 6`. -/
theorem class0_exp (b m : ℤ) (h1 : 3 ≤ b) (h2 : b ≤ m - 6) :
    b ^ 2 - b * (m - 1) + m - 3 ≤ 9 - 2 * m := by nlinarith

/-- Class 0, large `t`: `a^2 - (m+1) a + 2m - 3 ≤ 9 - 2m` for `4 ≤ a ≤ m - 4`. -/
theorem class0_exp2 (a m : ℤ) (h1 : 4 ≤ a) (h2 : a ≤ m - 4) :
    a ^ 2 - (m + 1) * a + 2 * m - 3 ≤ 9 - 2 * m := by nlinarith

/-- Case (c), `a ≥ 4`: `(2-a)s + a + 1 ≤ 13 - 2m` and `a + (3-a)s ≤ 8 - m`, `s = m - a ≥ 4`. -/
theorem casec_exp (a s : ℤ) (h1 : 4 ≤ a) (h2 : 4 ≤ s) :
    (2 - a) * s + a + 1 ≤ 13 - 2 * (a + s) ∧ a + (3 - a) * s ≤ 8 - (a + s) := by
  constructor <;> nlinarith

/-- Case (a): `x (m - x - c) ≥ 2 (m - 2 - c)` for `2 ≤ x ≤ m - 4`, `0 ≤ c ≤ 1`, `m ≥ 6`. -/
theorem casea_exp (x m c : ℚ) (h1 : 2 ≤ x) (h2 : x ≤ m - 4) (_hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    2 * (m - 2 - c) ≤ x * (m - x - c) := by nlinarith

/-! ### The top family `u = q/2 + 1` (Lemma 3.1, `e* = 0`) -/

/-- `(q/2 + 1) 2^(e+1) ≡ 2^(e+1) (mod q)` for `q = 2^(a+1) D`. -/
theorem top_cycle (a D e : ℕ) :
    (2 ^ a * D + 1) * 2 ^ (e + 1) % (2 ^ (a + 1) * D) = 2 ^ (e + 1) % (2 ^ (a + 1) * D) := by
  have : (2 ^ a * D + 1) * 2 ^ (e + 1) = 2 ^ (e + 1) + (2 ^ (a + 1) * D) * 2 ^ e := by ring
  rw [this, Nat.add_mul_mod_self_left]

/-- `(q/2 + 1) ≡ 2^a + 1 (mod 2^(a+1))` for `q = 2^(a+1) D`, `D` odd: the chain deviates only in
its last row. -/
theorem top_chain (a D : ℕ) (hD : D % 2 = 1) :
    (2 ^ a * D + 1) % 2 ^ (a + 1) = (2 ^ a + 1) % 2 ^ (a + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, D = 2 * d + 1 := ⟨D / 2, by omega⟩
  have : 2 ^ a * (2 * d + 1) + 1 = (2 ^ a + 1) + 2 ^ (a + 1) * d := by ring
  rw [this, Nat.add_mul_mod_self_left]

/-- The fold rule: `P` does not decrease at a fold (`q < 4d`, `2d ≤ q`):
`2^e (q - 2d) ≤ 2^(e+1) d`. -/
theorem fold_monotone (q d e : ℕ) (h : q < 4 * d) :
    2 ^ e * (q - 2 * d) ≤ 2 ^ (e + 1) * d := by
  rw [pow_succ]
  have : q - 2 * d ≤ 2 * d := by omega
  calc 2 ^ e * (q - 2 * d) ≤ 2 ^ e * (2 * d) := Nat.mul_le_mul_left _ this
    _ = 2 ^ e * 2 * d := by ring

/-- `κ_j ≤ 2^j`: `sin (2^j x) ≤ 2^j sin x` for `0 ≤ x`, `2^j x ≤ π`. -/
theorem sin_two_pow_le (j : ℕ) (x : ℝ) (hx : 0 ≤ x) (hj : 2 ^ j * x ≤ Real.pi) :
    Real.sin (2 ^ j * x) ≤ 2 ^ j * Real.sin x := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    have h2 : 2 ^ j * (2 * x) ≤ Real.pi := by rw [pow_succ] at hj; linarith
    have hx2 : 0 ≤ 2 * x := by linarith
    have hxpi : x ≤ Real.pi := by
      have : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
      nlinarith [Real.pi_pos]
    have hs : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx hxpi
    have key := ih (2 * x) hx2 h2
    rw [Real.sin_two_mul] at key
    have hc : Real.cos x ≤ 1 := Real.cos_le_one x
    calc Real.sin (2 ^ (j + 1) * x) = Real.sin (2 ^ j * (2 * x)) := by ring_nf
      _ ≤ 2 ^ j * (2 * Real.sin x * Real.cos x) := key
      _ ≤ 2 ^ j * (2 * Real.sin x * 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hc (by linarith)
      _ = 2 ^ (j + 1) * Real.sin x := by ring

end PeriodLaw3
