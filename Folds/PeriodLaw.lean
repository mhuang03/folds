import Mathlib

/-!
# Period law: the arithmetic of the one-free-point weights

See `experiments/periods3/PROOFS.txt`.  The polytope part (the local face formula, the column
rule and the case analysis of the valid intervals of the free point) is not formalised; this
file checks the bookkeeping that turns the interval lists of Lemmas 2.1, 2.3, 2.4 into the
closed forms, and the nonvanishing facts used in Theorems D1 and D2.

Notation: `m` = number of structured points, `n = m - 1`, `X = 2^(n-1)`, `D = 2^n - 1 = 2X - 1`.
-/

namespace PeriodLaw

open Finset

/-- The geometric sum `∑_{p=2}^{m-1} 2^(m-p-1) = 2^(m-2) - 1`. -/
theorem geom_tail (m : ℕ) (hm : 2 ≤ m) :
    ∑ p ∈ Ico 2 m, (2 : ℚ) ^ (m - p - 1) = 2 ^ (m - 2) - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  induction j with
  | zero => simp
  | succ j ih =>
    have hsplit : Ico 2 (j + 1 + 2) = insert 2 (Ico 3 (j + 1 + 2)) := by
      ext x; simp [Finset.mem_Ico]; omega
    rw [hsplit, sum_insert (by simp)]
    have hshift : ∑ p ∈ Ico 3 (j + 1 + 2), (2 : ℚ) ^ (j + 1 + 2 - p - 1)
        = ∑ p ∈ Ico 2 (j + 2), (2 : ℚ) ^ (j + 2 - p - 1) := by
      apply Finset.sum_nbij' (fun p => p - 1) (fun p => p + 1)
      · intro a ha; simp [Finset.mem_Ico] at ha ⊢; omega
      · intro a ha; simp [Finset.mem_Ico] at ha ⊢; omega
      · intro a ha; simp [Finset.mem_Ico] at ha; omega
      · intro a ha; simp
      · intro a ha
        simp [Finset.mem_Ico] at ha
        congr 1; omega
    rw [hshift, ih (by omega)]
    have : j + 1 + 2 - 2 - 1 = j := by omega
    rw [this]
    have : j + 1 + 2 - 2 = j + 1 := by omega
    rw [this, pow_succ]
    have : j + 2 - 2 = j := by omega
    rw [this]
    ring

/-- Lemma 2.1 bookkeeping (orbit vertex `1/D`, one free point).  With `X = 2^(n-1)`, the signed
measure `(-1)^m · D · A_above` is
`2 (X-1)` (gaps 0, 1) `+ (X - 1)` (the intervals `(v_{p+1}, v_p)`, gaps `2..m-1`)
`- n (X-1)/2` (the interval `((1+v_2)/2, 1)`, gaps `2..m`) `- 1/2` (`z < θ/2`, gap `m`),
and this equals `-((m-7) D - (m-9))/4`. -/
theorem orbit_total (n : ℕ) (X : ℚ) :
    2 * (X - 1) + (X - 1) - n * (X - 1) / 2 - 1 / 2
      = -(((n : ℚ) + 1 - 7) * (2 * X - 1) - ((n : ℚ) + 1 - 9)) / 4 := by
  ring

/-- Lemma 2.3 bookkeeping (chain `1 0^(n-1)`): `(-1)^n A1 = -1 + (m-1)/4 - (1/2 - 2^(1-m)) + 2^(-m)`
equals `(m-7)/4 + 3/2^m`; here `Y = 2^(-m)`. -/
theorem chain1_total (m : ℕ) (Y : ℚ) :
    -1 + ((m : ℚ) - 1) / 4 - (1 / 2 - 2 * Y) + Y = ((m : ℚ) - 7) / 4 + 3 * Y := by
  ring

/-- The alternating sum `∑_{i=1}^{k} (-1)^i` is `-1` for odd `k` and `0` for even `k`. -/
theorem alt_sum (k : ℕ) :
    ∑ i ∈ Icc 1 k, ((-1 : ℚ)) ^ i = if k % 2 = 1 then -1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
    · subst hr
      have h1 : (r + r) % 2 = 0 := by omega
      have h2 : (r + r + 1) % 2 = 1 := by omega
      simp only [h1, h2]
      rw [pow_succ, ← two_mul, pow_mul]; norm_num
    · subst hr
      have h1 : (2 * r + 1) % 2 = 1 := by omega
      have h2 : (2 * r + 1 + 1) % 2 = 0 := by omega
      simp only [h1, h2]
      rw [show 2 * r + 1 + 1 = 2 * (r + 1) by ring, pow_mul]; norm_num

/-- Lemma 2.4 bookkeeping (chain `1^n`), with `Y = 2^(-m)` (so `2^(-n) = 2Y`):
`(-1)^n A3 = (1/2 - 2Y) + 1/4 + (m-2)/8 + 2Y (2 (-1)^(m-1) + alt) + Y`, which is
`(m+4)/8 - 5Y` for even `m` and `(m+4)/8 + Y` for odd `m`. -/
theorem chain3_total (m : ℕ) (hm : 2 ≤ m) (Y : ℚ) :
    (1 / 2 - 2 * Y) + 1 / 4 + ((m : ℚ) - 2) / 8
      + 2 * Y * (2 * (-1 : ℚ) ^ (m - 1) + ∑ i ∈ Icc 1 (m - 2), ((-1 : ℚ)) ^ i) + Y
      = ((m : ℚ) + 4) / 8 + (if m % 2 = 0 then -5 else 1) * Y := by
  rw [alt_sum]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have e1 : j + 2 - 1 = j + 1 := by omega
  have e2 : j + 2 - 2 = j := by omega
  rw [e1, e2]
  push_cast
  rcases Nat.even_or_odd j with ⟨r, hr⟩ | ⟨r, hr⟩
  · subst hr
    have h1 : (r + r) % 2 = 0 := by omega
    have h2 : (r + r + 2) % 2 = 0 := by omega
    simp only [h1, h2, ite_true, ite_false, zero_ne_one]
    rw [pow_succ, ← two_mul, pow_mul]; norm_num; ring
  · subst hr
    have h1 : (2 * r + 1) % 2 = 1 := by omega
    have h2 : (2 * r + 1 + 2) % 2 = 1 := by omega
    simp only [h1, h2, ite_true, one_ne_zero, ite_false]
    rw [show 2 * r + 1 + 1 = 2 * (r + 1) by ring, pow_mul]; norm_num; ring

/-! ## Nonvanishing -/

/-- `4 D Δ_0 = ±((m-7) D - (m-11))` never vanishes (Theorem D1, odd part): `D = 2^(m-1) - 1`. -/
theorem orbit_delta_ne_zero (m : ℕ) (hm : 4 ≤ m) :
    ((m : ℤ) - 7) * (2 ^ (m - 1) - 1) - ((m : ℤ) - 11) ≠ 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 4 := ⟨m - 4, by omega⟩
  have e : j + 4 - 1 = j + 3 := by omega
  rw [e]
  have hp : (8 : ℤ) ≤ 2 ^ (j + 3) := by
    have := Nat.one_le_two_pow (n := j)
    have h : (2 : ℤ) ^ (j + 3) = 2 ^ j * 8 := by ring
    rw [h]; have : (1 : ℤ) ≤ 2 ^ j := by exact_mod_cast this
    linarith
  push_cast
  rcases (show j < 3 ∨ j = 3 ∨ 3 < j by omega) with h | h | h
  · -- m ≤ 6: (m - 7) D < 0 and -(m - 11) ≤ 7 < |(m-7) D|
    have : ((j : ℤ) + 4 - 7) ≤ -1 := by
      have : (j : ℤ) ≤ 2 := by exact_mod_cast (show j ≤ 2 by omega)
      linarith
    nlinarith
  · subst h; norm_num
  · have : (1 : ℤ) ≤ (j : ℤ) + 4 - 7 := by
      have : (4 : ℤ) ≤ j := by exact_mod_cast (show 4 ≤ j by omega)
      linarith
    have hj : (j : ℤ) + 4 - 11 < 2 ^ (j + 3) - 1 := by
      have : (j : ℤ) + 4 - 11 < (j : ℤ) := by linarith
      have : (j : ℤ) < 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
      have h8 : (2 : ℤ) ^ (j + 3) = 2 ^ j * 8 := by ring
      nlinarith
    nlinarith

/-- `8·2^m (A1 + A3) = ±((3m - 10) 2^m - 16)` (m even) never vanishes for `m ≥ 4`. -/
theorem chain_sum_ne_zero (m : ℕ) (hm : 4 ≤ m) :
    ((3 * (m : ℤ) - 10) * 2 ^ m - 16) ≠ 0 := by
  have hp : (16 : ℤ) ≤ 2 ^ m := by
    have : (2 : ℤ) ^ 4 ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
    simpa using this
  have : (2 : ℤ) ≤ 3 * (m : ℤ) - 10 := by
    have : (4 : ℤ) ≤ m := by exact_mod_cast hm
    linarith
  nlinarith

/-- `8·2^m (A1 - A3) = ±((m - 18) 2^m + 16)` never vanishes for odd `m ≥ 5`. -/
theorem chain_diff_ne_zero (m : ℕ) (hm : 5 ≤ m) (hodd : m % 2 = 1) :
    (((m : ℤ) - 18) * 2 ^ m + 16) ≠ 0 := by
  have hp : (32 : ℤ) ≤ 2 ^ m := by
    have : (2 : ℤ) ^ 5 ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
    simpa using this
  rcases (show m ≤ 17 ∨ 19 ≤ m by omega) with h | h
  · have : ((m : ℤ) - 18) ≤ -1 := by
      have : (m : ℤ) ≤ 17 := by exact_mod_cast h
      linarith
    nlinarith
  · have : (1 : ℤ) ≤ (m : ℤ) - 18 := by
      have : (19 : ℤ) ≤ m := by exact_mod_cast h
      linarith
    nlinarith

/-- The leading part `9 m^2 - 135 m + 22` of the two-free-point weight never vanishes
(it is `≡ 22 ≡ 4 (mod 9)`). -/
theorem lead2_ne_zero (m : ℤ) : 9 * m ^ 2 - 135 * m + 22 ≠ 0 := by
  intro h
  have h9 : (9 : ℤ) ∣ 22 := ⟨15 * m - m ^ 2, by linarith⟩
  norm_num at h9

end PeriodLaw
