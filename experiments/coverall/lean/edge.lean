theorem famCons_nonneg {K L R α β smax amin : ℕ} (hL : 0 < L) (hR : 0 < R) {a c : ℚ}
    (h11 : ((K : ℚ) * a - α + 1) / (L + 1) + 1 ≤ ((K : ℚ) * a - α) / L)
    (h12 : ((K : ℚ) * c - β + 1) / (R + 1) + 1 ≤ ((K : ℚ) * a - α) / L)
    (h13 : (R : ℚ) + 1 ≤ ((K : ℚ) * a - α) / L)
    (h14 : (3 : ℚ) ≤ ((K : ℚ) * a - α) / L)
    (h21 : ((K : ℚ) * a - α + 1) / (L + 1) + 1 ≤ ((K : ℚ) * c - β) / R)
    (h22 : ((K : ℚ) * c - β + 1) / (R + 1) + 1 ≤ ((K : ℚ) * c - β) / R)
    (h23 : (R : ℚ) + 1 ≤ ((K : ℚ) * c - β) / R)
    (h24 : (3 : ℚ) ≤ ((K : ℚ) * c - β) / R)
    (h31 : ((K : ℚ) * a - α + 1) / (L + 1) + 1 ≤ smax)
    (h32 : ((K : ℚ) * c - β + 1) / (R + 1) + 1 ≤ smax)
    (h33 : (R : ℚ) + 1 ≤ smax) (h34 : (3 : ℚ) ≤ smax) (h5 : (amin : ℚ) ≤ a) :
    ∀ f ∈ famCons K L R α β smax amin, 0 ≤ f.eval a c := by
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have hRq : (0 : ℚ) < R := by exact_mod_cast hR
  have eU1 : (affU1 K L α).eval a c = (K * a - α) / L := by
    unfold affU1 Aff.eval; field_simp; ring
  have eU2 : (affU2 K R β).eval a c = (K * c - β) / R := by
    unfold affU2 Aff.eval; field_simp; ring
  have eL1 : (affL1 K L α).eval a c = (K * a - α + 1) / (L + 1) := by
    unfold affL1 Aff.eval; field_simp; ring
  have eL2 : (affL2 K R β).eval a c = (K * c - β + 1) / (R + 1) := by
    unfold affL2 Aff.eval; field_simp; ring
  have eC : ∀ k : ℚ, (affC k).eval a c = k := fun k => by unfold affC Aff.eval; ring
  simp only [famCons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Aff.eval_gap, eU1, eU2, eL1, eL2, eC]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | linarith | (simp only [Aff.eval]; linarith)

set_option maxHeartbeats 2000000 in
/-- A point of the edge `U2 - L1 = 1` (parameter `σ = L1`), shifted by `e (p, q)`: all of
`famCons` holds there under the "key" conditions. -/
theorem edge4_corner {K L R α β smax amin : ℕ} (hK : 0 < K) (hL : 0 < L) (hR : 0 < R)
    {p q : ℤ} (hp : 0 ≤ p) (hpq : (p : ℚ) * R ≤ q * (L + 1)) (hreg : (p : ℚ) * (R + 1) ≤ q * L)
    {s0 σ e : ℚ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs0 : s0 ≤ smax) (hs0R : (R : ℚ) + 1 ≤ s0) (hs03 : 3 ≤ s0)
    (ht8 : σ ≤ s0 - 1 - K * p / (L + 1)) (ht9 : σ ≤ ((s0 - 1) * (R + 1) - K * q - 1) / R - 1)
    (hch : 0 ≤ (σ * (L + 1) - 1 + K * p) * (R + 1) - ((σ + 1) * R + 1 + K * q) * L - L * (R + 1))
    (hbot : (L : ℚ) + 1 ≤ σ) (hbotR : (R : ℚ) + 1 ≤ σ) (hamin : (amin : ℚ) * K ≤ σ * (L + 1) + α - 1) :
    ∀ f ∈ famCons K L R α β smax amin, 0 ≤ f.eval ((σ * (L + 1) + α - 1) / K + e * p)
      (((σ + 1) * R + β) / K + e * q) := by
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have hRq : (0 : ℚ) < R := by exact_mod_cast hR
  have hL1 : (0 : ℚ) < L + 1 := by linarith
  have hR1 : (0 : ℚ) < R + 1 := by linarith
  have hpq0 : (0 : ℚ) ≤ p := by exact_mod_cast hp
  have hq0 : (0 : ℚ) ≤ q := by
    by_contra h; push Not at h
    have : (p : ℚ) * (R + 1) ≥ 0 := by positivity
    nlinarith
  set a := (σ * (L + 1) + α - 1) / K + e * p with ha
  set c := ((σ + 1) * R + β) / K + e * q with hc
  have eA : (K : ℚ) * a - α = σ * (L + 1) - 1 + e * K * p := by rw [ha]; field_simp; ring
  have eC : (K : ℚ) * c - β = (σ + 1) * R + e * K * q := by rw [hc]; field_simp; ring
  have u1 : ((K : ℚ) * a - α) / L = (σ * (L + 1) - 1 + e * K * p) / L := by rw [eA]
  have u2 : ((K : ℚ) * c - β) / R = σ + 1 + e * K * q / R := by rw [eC]; field_simp
  have l1 : ((K : ℚ) * a - α + 1) / (L + 1) = σ + e * K * p / (L + 1) := by
    rw [eA]; field_simp; ring
  have l2 : ((K : ℚ) * c - β + 1) / (R + 1) = ((σ + 1) * R + 1 + e * K * q) / (R + 1) := by
    rw [eC]; ring
  have ePK : 0 ≤ e * K * p := by positivity
  have eQK : 0 ≤ e * K * q := by positivity
  have hL1' : (1 : ℚ) ≤ L := by exact_mod_cast hL
  apply famCons_nonneg hL hR
  · -- 11
    rw [u1, l1, le_div_iff₀ hLq]
    have : e * K * p / (L + 1) * L ≤ e * K * p := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hL1]; nlinarith
    linarith
  · -- 12 chord
    rw [u1, l2, div_add_one (ne_of_gt hR1), div_le_div_iff₀ hR1 hLq]
    have h1 : (σ * (L + 1) - 1 + e * K * p) * (R + 1) - ((σ + 1) * R + 1 + e * K * q) * L
        - L * (R + 1) = (σ * (L + 1) - 1 + K * p) * (R + 1) - ((σ + 1) * R + 1 + K * q) * L
        - L * (R + 1) + (1 - e) * K * (q * L - p * (R + 1)) := by ring
    have : 0 ≤ (1 - e) * K * (q * L - p * (R + 1)) := by
      apply mul_nonneg (mul_nonneg (by linarith) hKq.le); linarith
    linarith
  · rw [u1, le_div_iff₀ hLq]
    have := mul_le_mul_of_nonneg_right hbotR hL1.le
    linarith
  · rw [u1, le_div_iff₀ hLq]
    have := mul_le_mul_of_nonneg_right hbot hL1.le
    have : (L : ℚ) ≤ L * L := by nlinarith
    linarith
  · -- 21
    rw [u2, l1]
    have : e * K * p / (L + 1) ≤ e * K * q / R := by
      rw [div_le_div_iff₀ hL1 hRq]
      have : 0 ≤ e * K := by positivity
      have := mul_le_mul_of_nonneg_left hpq this
      linarith
    linarith
  · -- 22
    rw [u2, l2, div_add_one (ne_of_gt hR1), div_le_iff₀ hR1]
    have h3 : e * K * q ≤ e * K * q / R * (R + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hRq]
      have := mul_nonneg eQK hRq.le
      linarith
    linarith
  · rw [u2]; have : 0 ≤ e * K * q / R := by positivity
    linarith
  · rw [u2]; have : 0 ≤ e * K * q / R := by positivity
    linarith
  · -- 31
    rw [l1]
    have : e * K * p / (L + 1) ≤ K * p / (L + 1) := by
      have h0 : 0 ≤ (K : ℚ) * p := by positivity
      have h1 : e * K * p ≤ K * p := by nlinarith
      exact div_le_div_of_nonneg_right h1 hL1.le
    linarith
  · -- 32
    rw [l2, div_add_one (ne_of_gt hR1), div_le_iff₀ hR1]
    have h9 : (σ + 1) * R ≤ (s0 - 1) * (R + 1) - K * q - 1 := by
      have := ht9
      rw [le_sub_iff_add_le, le_div_iff₀ hRq] at this
      linarith
    have : e * K * q ≤ K * q := by
      have : 0 ≤ (K : ℚ) * q := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_right hs0 hR1.le
    linarith
  · linarith
  · linarith
  · -- amin
    rw [ha]
    have : (amin : ℚ) ≤ (σ * (L + 1) + α - 1) / K := by rw [le_div_iff₀ hKq]; linarith
    have : 0 ≤ e * p := by positivity
    linarith

/-- **Edge certificate (f4-edge).**  The parallelogram with corners on the edge `U2 - L1 = 1` at
`σ₁` (outer line; its `w₁`-neighbour under both tops) and `σ₃ = σ₁ - K/Δ` (inner line), sides
`w₁ = (p, q)`, `w₂ + δ w₁`. -/
theorem parOK_edge4 {K L R α β smax amin : ℕ} (hK : 0 < K) (hL : 0 < L) (hR : 0 < R)
    {p q p2 q2 : ℤ} (hdet : p * q2 - p2 * q = 1) (hp : 0 ≤ p) (hq : 0 < q)
    {Δ : ℚ} (hΔ : Δ = q * (L + 1) - p * R) (hΔpos : 0 < Δ) (hreg : (p : ℚ) * (R + 1) ≤ q * L)
    {s0 σ1 σ3 : ℚ} (hs0 : s0 ≤ smax) (hs0R : (R : ℚ) + 1 ≤ s0) (hs03 : 3 ≤ s0)
    (ht8 : σ1 ≤ s0 - 1 - K * p / (L + 1)) (ht9 : σ1 ≤ ((s0 - 1) * (R + 1) - K * q - 1) / R - 1)
    (hσ3 : σ3 = σ1 - K / Δ)
    (hch : 0 ≤ (σ3 * (L + 1) - 1 + K * p) * (R + 1) - ((σ3 + 1) * R + 1 + K * q) * L - L * (R + 1))
    (hbot : (L : ℚ) + 1 ≤ σ3) (hbotR : (R : ℚ) + 1 ≤ σ3)
    (hamin : (amin : ℚ) * K ≤ σ3 * (L + 1) + α - 1) :
    ParOK (famCons K L R α β smax amin) := by
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have hRq : (0 : ℚ) < R := by exact_mod_cast hR
  have hqq : (0 : ℚ) < q := by exact_mod_cast hq
  have hpq : (p : ℚ) * R ≤ q * (L + 1) := by linarith
  have hKD : 0 < (K : ℚ) / Δ := div_pos hKq hΔpos
  have h31 : σ3 ≤ σ1 := by linarith
  have hch1 : 0 ≤ (σ1 * (L + 1) - 1 + K * p) * (R + 1) - ((σ1 + 1) * R + 1 + K * q) * L
      - L * (R + 1) := by
    have : (σ1 * (L + 1) - 1 + K * p) * (R + 1) - ((σ1 + 1) * R + 1 + K * q) * L - L * (R + 1)
        = (σ3 * (L + 1) - 1 + K * p) * (R + 1) - ((σ3 + 1) * R + 1 + K * q) * L - L * (R + 1)
          + (σ1 - σ3) * (L + R + 1) := by ring
    rw [this]
    have : 0 ≤ (σ1 - σ3) * (L + R + 1) := mul_nonneg (by linarith) (by positivity)
    linarith
  have ham1 : (amin : ℚ) * K ≤ σ1 * (L + 1) + α - 1 := by
    have := mul_le_mul_of_nonneg_right h31 (by positivity : (0 : ℚ) ≤ L + 1); linarith
  have c1 := fun e (he0 : (0 : ℚ) ≤ e) (he1 : e ≤ 1) => edge4_corner (smax := smax) (amin := amin)
    (β := β) hK hL hR hp hpq hreg he0 he1 hs0 hs0R hs03 ht8 ht9 hch1 (by linarith) (by linarith) ham1
  have c3 := fun e (he0 : (0 : ℚ) ≤ e) (he1 : e ≤ 1) => edge4_corner (smax := smax) (amin := amin)
    (β := β) hK hL hR hp hpq hreg he0 he1 hs0 hs0R hs03 (by linarith) (by linarith) hch hbot hbotR
    hamin
  have hdq : ((p : ℚ) * q2 - p2 * q) = 1 := by exact_mod_cast hdet
  refine ⟨(σ1 * (L + 1) + α - 1) / K, ((σ1 + 1) * R + β) / K, ((σ3 - σ1) * R / K - q2) / q,
    p, q, p2, q2, hdet, fun f hf => ⟨?_, ?_, ?_, ?_⟩⟩
  · have := c1 0 le_rfl zero_le_one f hf; simpa using this
  · simpa using c1 1 zero_le_one le_rfl f hf
  · have e1 : (σ1 * (L + 1) + α - 1) / K + (p2 + ((σ3 - σ1) * R / K - q2) / q * p)
        = (σ3 * (L + 1) + α - 1) / K + 0 * p := by
      rw [hσ3]; field_simp; rw [hΔ]; linear_combination (K : ℚ) * (-L * q + R * p - q) * hdq
    have e2 : ((σ1 + 1) * R + β) / K + (q2 + ((σ3 - σ1) * R / K - q2) / q * q)
        = ((σ3 + 1) * R + β) / K + 0 * q := by field_simp; ring
    rw [e1, e2]; exact c3 0 le_rfl zero_le_one f hf
  · have e1 : (σ1 * (L + 1) + α - 1) / K + p + (p2 + ((σ3 - σ1) * R / K - q2) / q * p)
        = (σ3 * (L + 1) + α - 1) / K + 1 * p := by
      rw [hσ3]; field_simp; rw [hΔ]; linear_combination (K : ℚ) * (-L * q + R * p - q) * hdq
    have e2 : ((σ1 + 1) * R + β) / K + q + (q2 + ((σ3 - σ1) * R / K - q2) / q * q)
        = ((σ3 + 1) * R + β) / K + 1 * q := by field_simp; ring
    rw [e1, e2]; exact c3 1 zero_le_one le_rfl f hf

set_option maxHeartbeats 2000000 in
/-- A point of the edge `U1 - L2 = 1` (parameter `τ = L2`), shifted by `e (p, q)`. -/
theorem edge1_corner {K L R α β smax amin : ℕ} (hK : 0 < K) (hL : 0 < L) (hR : 0 < R)
    {p q : ℤ} (hq : 0 ≤ q) (hp : 0 ≤ p) (hpq : (q : ℚ) * (L + 1) ≤ p * R) (hreg : (q : ℚ) * L ≤ p * (R + 1))
    {s0 τ e : ℚ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs0 : s0 ≤ smax) (hs0R : (R : ℚ) + 1 ≤ s0) (hs03 : 3 ≤ s0)
    (ht8 : τ ≤ ((s0 - 1) * (L + 1) - K * p - 1) / L - 1) (ht9 : τ ≤ s0 - 1 - K * q / (R + 1))
    (hch : 0 ≤ (τ * (R + 1) - 1 + K * q) * (L + 1) - ((τ + 1) * L + 1 + K * p) * R - R * (L + 1))
    (hbot : (L : ℚ) + 1 ≤ τ) (hbotR : (R : ℚ) + 1 ≤ τ) (hamin : (amin : ℚ) * K ≤ (τ + 1) * L + α) :
    ∀ f ∈ famCons K L R α β smax amin, 0 ≤ f.eval (((τ + 1) * L + α) / K + e * p)
      ((τ * (R + 1) + β - 1) / K + e * q) := by
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have hRq : (0 : ℚ) < R := by exact_mod_cast hR
  have hL1 : (0 : ℚ) < L + 1 := by linarith
  have hR1 : (0 : ℚ) < R + 1 := by linarith
  have hpq0 : (0 : ℚ) ≤ p := by exact_mod_cast hp
  have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast hq
  set a := ((τ + 1) * L + α) / K + e * p with ha
  set c := (τ * (R + 1) + β - 1) / K + e * q with hc
  have eA : (K : ℚ) * a - α = (τ + 1) * L + e * K * p := by rw [ha]; field_simp; ring
  have eC : (K : ℚ) * c - β = τ * (R + 1) - 1 + e * K * q := by rw [hc]; field_simp; ring
  have u1 : ((K : ℚ) * a - α) / L = τ + 1 + e * K * p / L := by rw [eA]; field_simp
  have u2 : ((K : ℚ) * c - β) / R = (τ * (R + 1) - 1 + e * K * q) / R := by rw [eC]
  have l1 : ((K : ℚ) * a - α + 1) / (L + 1) = ((τ + 1) * L + 1 + e * K * p) / (L + 1) := by
    rw [eA]; ring
  have l2 : ((K : ℚ) * c - β + 1) / (R + 1) = τ + e * K * q / (R + 1) := by
    rw [eC]; field_simp; ring
  have ePK : 0 ≤ e * K * p := by positivity
  have eQK : 0 ≤ e * K * q := by positivity
  have hR1' : (1 : ℚ) ≤ R := by exact_mod_cast hR
  apply famCons_nonneg hL hR
  · -- 11
    rw [u1, l1, div_add_one (ne_of_gt hL1), div_le_iff₀ hL1]
    have h3 : e * K * p ≤ e * K * p / L * (L + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hLq]
      have := mul_nonneg ePK hLq.le
      linarith
    linarith
  · -- 12
    rw [u1, l2]
    have : e * K * q / (R + 1) ≤ e * K * p / L := by
      rw [div_le_div_iff₀ hR1 hLq]
      have : 0 ≤ e * K := by positivity
      have := mul_le_mul_of_nonneg_left hreg this
      linarith
    linarith
  · rw [u1]; have : 0 ≤ e * K * p / L := by positivity
    linarith
  · rw [u1]; have : 0 ≤ e * K * p / L := by positivity
    linarith
  · -- 21 chord
    rw [u2, l1, div_add_one (ne_of_gt hL1), div_le_div_iff₀ hL1 hRq]
    have h1 : (τ * (R + 1) - 1 + e * K * q) * (L + 1) - ((τ + 1) * L + 1 + e * K * p) * R
        - R * (L + 1) = (τ * (R + 1) - 1 + K * q) * (L + 1) - ((τ + 1) * L + 1 + K * p) * R
        - R * (L + 1) + (1 - e) * K * (p * R - q * (L + 1)) := by ring
    have : 0 ≤ (1 - e) * K * (p * R - q * (L + 1)) := by
      apply mul_nonneg (mul_nonneg (by linarith) hKq.le); linarith
    linarith
  · -- 22
    rw [u2, l2, le_div_iff₀ hRq]
    have h3 : e * K * q / (R + 1) * R ≤ e * K * q := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hR1]
      have := mul_nonneg eQK hRq.le
      linarith
    have := mul_le_mul_of_nonneg_right hbotR hR1.le
    linarith
  · rw [u2, le_div_iff₀ hRq]
    have := mul_le_mul_of_nonneg_right hbotR hR1.le
    linarith
  · rw [u2, le_div_iff₀ hRq]
    have := mul_le_mul_of_nonneg_right hbotR hR1.le
    have : (R : ℚ) ≤ R * R := by nlinarith
    linarith
  · -- 31
    rw [l1, div_add_one (ne_of_gt hL1), div_le_iff₀ hL1]
    have h8 : (τ + 1) * L ≤ (s0 - 1) * (L + 1) - K * p - 1 := by
      have := ht8
      rw [le_sub_iff_add_le, le_div_iff₀ hLq] at this
      linarith
    have : e * K * p ≤ K * p := by
      have : 0 ≤ (K : ℚ) * p := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_right hs0 hL1.le
    linarith
  · -- 32
    rw [l2]
    have : e * K * q / (R + 1) ≤ K * q / (R + 1) := by
      have h0 : 0 ≤ (K : ℚ) * q := by positivity
      have h1 : e * K * q ≤ K * q := by nlinarith
      exact div_le_div_of_nonneg_right h1 hR1.le
    linarith
  · linarith
  · linarith
  · -- amin
    rw [ha]
    have : (amin : ℚ) ≤ ((τ + 1) * L + α) / K := by rw [le_div_iff₀ hKq]; linarith
    have : 0 ≤ e * p := by positivity
    linarith

/-- **Edge certificate (f1-edge).**  Corners on the edge `U1 - L2 = 1` at `τ₁` (inner line)
and `τ₃ = τ₁ + K/Δ` (outer line, its `w₁`-neighbour under both tops). -/
theorem parOK_edge1 {K L R α β smax amin : ℕ} (hK : 0 < K) (hL : 0 < L) (hR : 0 < R)
    {p q p2 q2 : ℤ} (hdet : p * q2 - p2 * q = 1) (hp : 0 ≤ p) (hq : 0 < q)
    {Δ : ℚ} (hΔ : Δ = p * (R + 1) - q * L) (hΔpos : 0 < Δ) (hreg : (q : ℚ) * (L + 1) ≤ p * R)
    {s0 τ1 τ3 : ℚ} (hs0 : s0 ≤ smax) (hs0R : (R : ℚ) + 1 ≤ s0) (hs03 : 3 ≤ s0)
    (ht8 : τ3 ≤ ((s0 - 1) * (L + 1) - K * p - 1) / L - 1) (ht9 : τ3 ≤ s0 - 1 - K * q / (R + 1))
    (hτ1 : τ1 = τ3 - K / Δ)
    (hch : 0 ≤ (τ1 * (R + 1) - 1 + K * q) * (L + 1) - ((τ1 + 1) * L + 1 + K * p) * R - R * (L + 1))
    (hbot : (L : ℚ) + 1 ≤ τ1) (hbotR : (R : ℚ) + 1 ≤ τ1)
    (hamin : (amin : ℚ) * K ≤ (τ1 + 1) * L + α) :
    ParOK (famCons K L R α β smax amin) := by
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have hRq : (0 : ℚ) < R := by exact_mod_cast hR
  have hqq : (0 : ℚ) < q := by exact_mod_cast hq
  have hpq : (q : ℚ) * L ≤ p * (R + 1) := by linarith
  have hKD : 0 < (K : ℚ) / Δ := div_pos hKq hΔpos
  have h13 : τ1 ≤ τ3 := by linarith
  have hch3 : 0 ≤ (τ3 * (R + 1) - 1 + K * q) * (L + 1) - ((τ3 + 1) * L + 1 + K * p) * R
      - R * (L + 1) := by
    have : (τ3 * (R + 1) - 1 + K * q) * (L + 1) - ((τ3 + 1) * L + 1 + K * p) * R - R * (L + 1)
        = (τ1 * (R + 1) - 1 + K * q) * (L + 1) - ((τ1 + 1) * L + 1 + K * p) * R - R * (L + 1)
          + (τ3 - τ1) * (L + R + 1) := by ring
    rw [this]
    have : 0 ≤ (τ3 - τ1) * (L + R + 1) := mul_nonneg (by linarith) (by positivity)
    linarith
  have ham3 : (amin : ℚ) * K ≤ (τ3 + 1) * L + α := by
    have := mul_le_mul_of_nonneg_right h13 hLq.le; linarith
  have c3 := fun e (he0 : (0 : ℚ) ≤ e) (he1 : e ≤ 1) => edge1_corner (smax := smax) (amin := amin)
    (β := β) hK hL hR hq.le hp hreg hpq he0 he1 hs0 hs0R hs03 ht8 ht9 hch3 (by linarith)
    (by linarith) ham3
  have c1 := fun e (he0 : (0 : ℚ) ≤ e) (he1 : e ≤ 1) => edge1_corner (smax := smax) (amin := amin)
    (β := β) hK hL hR hq.le hp hreg hpq he0 he1 hs0 hs0R hs03 (by linarith) (by linarith) hch hbot
    hbotR hamin
  have hdq : ((p : ℚ) * q2 - p2 * q) = 1 := by exact_mod_cast hdet
  refine ⟨((τ1 + 1) * L + α) / K, (τ1 * (R + 1) + β - 1) / K, ((τ3 - τ1) * (R + 1) / K - q2) / q,
    p, q, p2, q2, hdet, fun f hf => ⟨?_, ?_, ?_, ?_⟩⟩
  · have := c1 0 le_rfl zero_le_one f hf; simpa using this
  · simpa using c1 1 zero_le_one le_rfl f hf
  · have e1 : ((τ1 + 1) * L + α) / K + (p2 + ((τ3 - τ1) * (R + 1) / K - q2) / q * p)
        = ((τ3 + 1) * L + α) / K + 0 * p := by
      rw [hτ1]; field_simp; rw [hΔ]; linear_combination -(K : ℚ) * (R * p + p - L * q) * hdq
    have e2 : (τ1 * (R + 1) + β - 1) / K + (q2 + ((τ3 - τ1) * (R + 1) / K - q2) / q * q)
        = (τ3 * (R + 1) + β - 1) / K + 0 * q := by field_simp; ring
    rw [e1, e2]; exact c3 0 le_rfl zero_le_one f hf
  · have e1 : ((τ1 + 1) * L + α) / K + p + (p2 + ((τ3 - τ1) * (R + 1) / K - q2) / q * p)
        = ((τ3 + 1) * L + α) / K + 1 * p := by
      rw [hτ1]; field_simp; rw [hΔ]; linear_combination -(K : ℚ) * (R * p + p - L * q) * hdq
    have e2 : (τ1 * (R + 1) + β - 1) / K + q + (q2 + ((τ3 - τ1) * (R + 1) / K - q2) / q * q)
        = (τ3 * (R + 1) + β - 1) / K + 1 * q := by field_simp; ring
    rw [e1, e2]; exact c3 1 zero_le_one le_rfl f hf
