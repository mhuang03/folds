import Mathlib

/-!
# Period law II: the mixed components and the reduction of `B(k)` to its carriers

See `experiments/periods4/PROOFS.txt`.  The polytope part (vertex formula, column rule, the
classification of the cycle + pendant chain vertices, the dominance computations) is not
formalised.  This file checks the arithmetic that the argument uses:

* `B_eq_L`: for `k ≥ 9`, `B(k) = lcm(2^(k-1), 2^a (2^s - 1) : a + s = k - 1, s ≥ 1)` equals the
  lcm of the orders that are certified nonzero: `2^(k-1)` and `2^(k-1) - 1` (Theorem C, in
  `c_0`), `2^(k-2) - 1` (Theorem D1, in `c_1`) and the mixed orders `2^a (2^s - 1)` with
  `s ≥ 4`, `a ≥ 2` (Theorem F of PROOFS.txt, in `c_0`).  So these carriers alone force the
  period of `T(N,k)` to be all of `B(k)`.
* `B_eq_L0`: the same with `2 (2^(k-2) - 1)` (the mixed order with `a = 1`, in `c_0`) in place of
  `2^(k-2) - 1`: the carriers inside the constant term alone give `B(k)`.
* `hg_sum`, `main_family`, `main_family_a1`: the identities behind Lemma 2.3 (the valid time
  orders of the main structure add up to the first one when `a ≥ 2`).
* `closing_column`: the closing-column count of Lemma 2.3 (at most two chain points before the
  closing point, and the sides are then forced).
* `weights_sum`: the number of time orders of a structure, summed over the attachment index.
-/

namespace PeriodLaw2

open Finset

/-- The term `2^a (2^s - 1)` of `B(k)`, `a = k - 1 - s`. -/
def term (k s : ℕ) : ℕ := 2 ^ (k - 1 - s) * (2 ^ s - 1)

/-- `B(k) = lcm(2^(k-1), 2^a (2^s - 1) : a + s = k - 1, s ≥ 1)`. -/
def B (k : ℕ) : ℕ := Nat.lcm (2 ^ (k - 1)) ((Icc 1 (k - 1)).lcm (term k))

/-- The certified carriers (Theorems C, D1 and F). -/
def L (k : ℕ) : ℕ :=
  Nat.lcm (2 ^ (k - 1)) (Nat.lcm (2 ^ (k - 1) - 1) (Nat.lcm (2 ^ (k - 2) - 1)
    ((Icc 4 (k - 3)).lcm (term k))))

/-- The carriers inside the constant term `c_0` (Theorems C and F, including `a = 1`). -/
def L0 (k : ℕ) : ℕ :=
  Nat.lcm (2 ^ (k - 1)) (Nat.lcm (2 ^ (k - 1) - 1) (Nat.lcm (term k (k - 2))
    ((Icc 4 (k - 3)).lcm (term k))))

theorem coprime_two_pow_sub_one (s : ℕ) (hs : 1 ≤ s) : Nat.Coprime 2 (2 ^ s - 1) := by
  have h1 : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hodd : (2 ^ s - 1) % 2 = 1 := by
    have : 2 ^ s % 2 = 0 := by
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      simp [pow_succ]
    omega
  exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd)

/-- `2^b (2^s - 1)` divides `n` as soon as `2^b` and `2^s - 1` do. -/
theorem term_dvd {n b s : ℕ} (hs : 1 ≤ s) (h1 : 2 ^ b ∣ n) (h2 : 2 ^ s - 1 ∣ n) :
    2 ^ b * (2 ^ s - 1) ∣ n :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd ((coprime_two_pow_sub_one s hs).pow_left b) h1 h2

/-- `2^s - 1 ∣ 2^6 - 1` for `s = 1, 2, 3`. -/
theorem small_dvd_63 (s : ℕ) (h1 : 1 ≤ s) (h3 : s ≤ 3) : 2 ^ s - 1 ∣ 2 ^ 6 - 1 := by
  interval_cases s <;> norm_num

theorem pow_dvd_pow_k {k b : ℕ} (hb : b ≤ k - 1) : 2 ^ b ∣ 2 ^ (k - 1) :=
  Nat.pow_dvd_pow 2 hb

/-- Every term of `B(k)` divides the lcm `R` of the carriers, given that `2^(k-1)`,
`2^(k-1) - 1`, `2^(k-2) - 1` and the terms with `4 ≤ s ≤ k - 3` divide `R`. -/
theorem terms_dvd {k R : ℕ} (hk : 9 ≤ k) (hA : 2 ^ (k - 1) ∣ R) (hB : 2 ^ (k - 1) - 1 ∣ R)
    (hC : 2 ^ (k - 2) - 1 ∣ R) (hM : ∀ s ∈ Icc 4 (k - 3), term k s ∣ R) :
    ∀ s ∈ Icc 1 (k - 1), term k s ∣ R := by
  intro s hs
  rw [mem_Icc] at hs
  unfold term
  by_cases h3 : s ≤ 3
  · -- 2^s - 1 divides 63, which divides the term with s = 6
    have h6 : term k 6 ∣ R := hM 6 (by rw [mem_Icc]; omega)
    have h63 : 2 ^ 6 - 1 ∣ R := Dvd.dvd.trans (Dvd.intro_left _ rfl) h6
    exact term_dvd hs.1 ((pow_dvd_pow_k (by omega)).trans hA)
      ((small_dvd_63 s hs.1 h3).trans h63)
  · by_cases hm : s ≤ k - 3
    · exact hM s (by rw [mem_Icc]; omega)
    · by_cases h2 : s = k - 2
      · subst h2
        exact term_dvd (by omega) ((pow_dvd_pow_k (by omega)).trans hA) hC
      · have : s = k - 1 := by omega
        subst this
        have : k - 1 - (k - 1) = 0 := by omega
        rw [this, pow_zero, one_mul]
        exact hB

theorem B_eq_L (k : ℕ) (hk : 9 ≤ k) : B k = L k := by
  apply Nat.dvd_antisymm
  · -- every term of B divides L
    unfold B
    apply Nat.lcm_dvd (Nat.dvd_lcm_left _ _)
    rw [Finset.lcm_dvd_iff]
    refine terms_dvd hk (Nat.dvd_lcm_left _ _) ?_ ?_ ?_
    · exact (Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)
    · exact ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)).trans (Nat.dvd_lcm_right _ _)
    · intro s hs
      exact (((Finset.dvd_lcm hs).trans (Nat.dvd_lcm_right _ _)).trans
        (Nat.dvd_lcm_right _ _)).trans (Nat.dvd_lcm_right _ _)
  · -- every carrier divides B
    have hT : ∀ s ∈ Icc 1 (k - 1), term k s ∣ B k := fun s hs =>
      (Finset.dvd_lcm hs).trans (Nat.dvd_lcm_right _ _)
    unfold L
    apply Nat.lcm_dvd (Nat.dvd_lcm_left _ _)
    apply Nat.lcm_dvd
    · have h := hT (k - 1) (by rw [mem_Icc]; omega)
      unfold term at h
      rwa [show k - 1 - (k - 1) = 0 by omega, pow_zero, one_mul] at h
    apply Nat.lcm_dvd
    · have h := hT (k - 2) (by rw [mem_Icc]; omega)
      unfold term at h
      exact (Dvd.intro_left _ rfl).trans h
    · rw [Finset.lcm_dvd_iff]
      intro s hs
      rw [mem_Icc] at hs
      exact hT s (by rw [mem_Icc]; omega)

theorem B_eq_L0 (k : ℕ) (hk : 9 ≤ k) : B k = L0 k := by
  apply Nat.dvd_antisymm
  · unfold B
    apply Nat.lcm_dvd (Nat.dvd_lcm_left _ _)
    rw [Finset.lcm_dvd_iff]
    refine terms_dvd hk (Nat.dvd_lcm_left _ _) ?_ ?_ ?_
    · exact (Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)
    · have h : term k (k - 2) ∣ L0 k :=
        ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)).trans (Nat.dvd_lcm_right _ _)
      unfold term at h
      exact (Dvd.intro_left _ rfl).trans h
    · intro s hs
      exact (((Finset.dvd_lcm hs).trans (Nat.dvd_lcm_right _ _)).trans
        (Nat.dvd_lcm_right _ _)).trans (Nat.dvd_lcm_right _ _)
  · have hT : ∀ s ∈ Icc 1 (k - 1), term k s ∣ B k := fun s hs =>
      (Finset.dvd_lcm hs).trans (Nat.dvd_lcm_right _ _)
    unfold L0
    apply Nat.lcm_dvd (Nat.dvd_lcm_left _ _)
    apply Nat.lcm_dvd
    · have h := hT (k - 1) (by rw [mem_Icc]; omega)
      unfold term at h
      rwa [show k - 1 - (k - 1) = 0 by omega, pow_zero, one_mul] at h
    apply Nat.lcm_dvd
    · exact hT (k - 2) (by rw [mem_Icc]; omega)
    · rw [Finset.lcm_dvd_iff]
      intro s hs
      rw [mem_Icc] at hs
      exact hT s (by rw [mem_Icc]; omega)

/-! ### The main family (Lemma 2.3) -/

/-- `h(x) + g(x) = 1` with `h = 1/(1 - e(-x))`, `g = 1/(1 - e(x))`, written for `z = e(x)`. -/
theorem hg_sum {K : Type*} [Field K] (z : K) (hz : z ≠ 1) (hz0 : z ≠ 0) :
    1 / (1 - z⁻¹) + 1 / (1 - z) = 1 := by
  have h1 : (1 : K) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h2 : (1 : K) - z⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h; apply hz
    have := congrArg (·⁻¹) h; simpa using this.symm
  field_simp
  ring

/-- The three valid time orders of the main structure (closing point after `p = 0, 1, 2` chain
points) contribute `X (-h_c)(-h_e)`, `X h_c (-g_e)`, `X (-h_c)(-g_e)`; their sum is the first. -/
theorem main_family {R : Type*} [CommRing R] (X hc he ge : R) :
    X * ((-hc) * (-he)) + X * (hc * (-ge)) + X * ((-hc) * (-ge)) = X * ((-hc) * (-he)) := by
  ring

/-- For `a = 1` only `p = 0, 1` occur, and the sum is `X h_c (h_e - g_e)`. -/
theorem main_family_a1 {R : Type*} [CommRing R] (X hc he ge : R) :
    X * ((-hc) * (-he)) + X * (hc * (-ge)) = X * hc * (he - ge) := by
  ring

/-- The closing column of the main structure: fixed sum `p` (the chain points before the
closing point), halving contribution `hc ∈ {0, -1}` (bit 0), equality contribution
`ec ∈ {1, -1}`.  A zero column sum forces `p ≤ 2`, and the sides are unique. -/
theorem closing_column (p hc ec : ℤ) (hp : 0 ≤ p) (h1 : hc = 0 ∨ hc = -1)
    (h2 : ec = 1 ∨ ec = -1) (h : p + hc + ec = 0) :
    (p = 0 ∧ hc = -1 ∧ ec = 1) ∨ (p = 1 ∧ hc = 0 ∧ ec = -1) ∨ (p = 2 ∧ hc = -1 ∧ ec = -1) := by
  omega

/-- The weights: a structure with attachment index `j` has at most `C(s - j + a, a)` time
orders (the first `j + 1` cycle points come first; the chain and the remaining `s - j` cycle
points interleave).  Summed over `j < s` this is `C(s + a + 1, a + 1) - 1`. -/
theorem weights_sum (s a : ℕ) :
    ∑ j ∈ range s, Nat.choose (s - j + a) a + 1 = Nat.choose (s + a + 1) (a + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ', show s + 1 - 0 + a = s + a + 1 by omega]
    have hs : ∑ j ∈ range s, Nat.choose (s + 1 - (j + 1) + a) a
        = ∑ j ∈ range s, Nat.choose (s - j + a) a := by
      apply Finset.sum_congr rfl; intro j _; congr 2; omega
    have hp : Nat.choose (s + 1 + a + 1) (a + 1)
        = Nat.choose (s + a + 1) a + Nat.choose (s + a + 1) (a + 1) := by
      rw [show s + 1 + a + 1 = (s + a + 1) + 1 by omega]
      exact Nat.choose_succ_succ (s + a + 1) a
    rw [hs, hp, ← ih]
    ring

end PeriodLaw2
