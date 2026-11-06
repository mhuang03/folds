import Folds.Residual

/-!
# The covering statement `CoverAll`: explicit certificates on a cell decomposition

`experiments/coverall/PROOFS.txt`.

`Residual.CoverAll N` says that every mixed-parity wide non-special pair `(u, u')` lies in
`Proven2` (old regions, `RegionPF`, `RegionSL`, `RegionS`).  Here:

* `parOK_edge4`, `parOK_edge1`: **edge certificates**.  For a family and a lattice direction
  `w₁ = (p, q)`, the witness polygon contains the fundamental parallelogram whose two corners on the
  inner and outer lattice lines lie on one edge of the strip (`U2 - L1 = 1`, resp. `U1 - L2 = 1`),
  the outer one as high as both tops allow; this reduces `ParOK` to four "key" inequalities in the
  edge parameter.
* `KeyA`, `KeyB4`, `KeyB1`: the cells `Z` in orientation `(u', u)` with `w₁ = (1,1)`, `(2,1)`;
  their key conditions are explicit polynomials in `(N, u, u')` (`parOK_of_keyA` ...).
* `leaf_*`: on eleven polyhedra ("leaves") in `(N, u, u')` the key polynomials (or the polynomial
  conditions of the old regions `D`, `B`: `regionD_of_polys`, `regionB_of_polys`) are nonnegative;
  each proof is `linarith` with explicit products of the leaf's linear constraints (a
  Handelman-type certificate found by LP, `experiments/coverall/leaves.py`).
* `bulk`: outside the thin sets `Thin` (the diagonal strip `u' ≤ u + 9`, the strip
  `|u' - 2u| ≲ 15` above `u ≈ N/8`, a bounded cluster at `(N/4, 3N/8)` on the edge, `u ≤ 3`),
  every pair of the triangle is in `Proven` or `ParOK (consZ N u' u)`.
* `d1_line`: the line `u' = u + 1` (`5 ≤ u ≤ (N - 21)/3`) by an explicit slice certificate
  (`RegionSL`: `X(N, s, 0)`, orientation `(u', u)`, slice `a = c + 1`, sides `(1, 0)`, `(δ, 1)`).
* `coverAll_of_thinCover`, `conjectureC_of_thinCover`: `CoverAll N` (hence Conjecture C) for all
  `N > 300` follows from the statement `ThinCover` about the remaining thin sets `ThinRest`
  (**not proven**: the diagonal strip `u' ≤ u + 9` except the bulk of the line `d = 1`, the strip
  `u' - 2u ∈ [-12, 15]` above `u ≈ N/8`, the cluster at `(N/4, 3N/8)`, `u ≤ 3`; numerically only
  `d ∈ {0, 1, 2, 3}`, `u' - 2u ∈ [-9, 7]` and a few cluster points there need slices, see
  `experiments/coverall/PROOFS.txt`).
-/

namespace Folds
namespace CoverAll

open Residual Live2 Live8 ArithCover

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

theorem nonneg_of_cleared {E P D : ℚ} (hD : 0 < D) (hP : 0 ≤ P) (hE : E * D = P) : 0 ≤ E := by
  by_contra h
  push Not at h
  have : E * D < 0 := mul_neg_of_neg_of_pos h hD
  linarith

theorem s0_le_Z (N : ℕ) : ((N : ℚ) + 1) / 2 ≤ (((N + 2) / 2 : ℕ) : ℚ) := by
  have h : N + 1 ≤ 2 * ((N + 2) / 2) := by omega
  have : ((N : ℚ) + 1) ≤ 2 * (((N + 2) / 2 : ℕ) : ℚ) := by exact_mod_cast h
  linarith

/-- Key polynomial `chord8` of cell A. -/
def kAc8 (N u v : ℚ) : ℚ :=
  -3 * N * u ^ 2 * v - N * u ^ 2 + 4 * N * u * v ^ 2 + 2 * N * u * v - 2 * N * u - N * v ^ 3 - 3 * N * v ^ 2 - 3 * N * v - N + 4 * u ^ 2 * v ^ 2 + 3 * u ^ 2 * v + 3 * u ^ 2 - 4 * u * v ^ 3 + 2 * u * v ^ 2 + 2 * u * v - 4 * u - 9 * v ^ 3 - 25 * v ^ 2 - 23 * v - 7

/-- Key polynomial `bot8` of cell A. -/
def kAb8 (N u v : ℚ) : ℚ :=
  -N * u * v + N * u + N * v ^ 2 - 2 * N * v - 3 * N + 2 * u * v ^ 2 + 5 * u * v + 7 * u - 2 * v ^ 3 - 7 * v ^ 2 - 16 * v - 11

/-- Key polynomial `botR8` of cell A. -/
def kAr8 (N u v : ℚ) : ℚ :=
  -N * u * v + N * u + N * v ^ 2 - 2 * N * v - 3 * N + 2 * u ^ 2 * v + 2 * u ^ 2 - 2 * u * v ^ 2 - u * v + 5 * u - 3 * v ^ 2 - 14 * v - 11

/-- Key polynomial `amin8` of cell A. -/
def kAa8 (N u v : ℚ) : ℚ :=
  -N * u * v ^ 2 + 4 * N * u * v + 5 * N * u + N * v ^ 3 - 5 * N * v ^ 2 - 13 * N * v - 7 * N + u * v ^ 2 + 16 * u * v + 15 * u - v ^ 3 - 21 * v ^ 2 - 39 * v - 19

/-- Key polynomial `chord9` of cell A. -/
def kAc9 (N u v : ℚ) : ℚ :=
  -3 * N * u ^ 3 + 4 * N * u ^ 2 * v - N * u ^ 2 - N * u * v ^ 2 + N * u - N * v ^ 2 - 2 * N * v - N + 4 * u ^ 3 * v + u ^ 3 - 4 * u ^ 2 * v ^ 2 + 6 * u ^ 2 * v + 3 * u ^ 2 - 11 * u * v ^ 2 - 16 * u * v - 5 * u - 7 * v ^ 2 - 14 * v - 7

/-- Key polynomial `bot9` of cell A. -/
def kAb9 (N u v : ℚ) : ℚ :=
  -N * u ^ 2 + N * u * v - N * v - N + 2 * u ^ 2 * v + 5 * u ^ 2 - 2 * u * v ^ 2 - 7 * u * v - 2 * u - 7 * v - 7

/-- Key polynomial `botR9` of cell A. -/
def kAr9 (N u v : ℚ) : ℚ :=
  -N * u ^ 2 + N * u * v - N * v - N + 2 * u ^ 3 - 2 * u ^ 2 * v + 3 * u ^ 2 - 5 * u * v - 2 * u - 7 * v - 7

/-- Key polynomial `amin9` of cell A. -/
def kAa9 (N u v : ℚ) : ℚ :=
  -N * u ^ 2 * v + 3 * N * u ^ 2 + N * u * v ^ 2 - 3 * N * u * v - 4 * N * u - N * v ^ 2 - 2 * N * v - N + 3 * u ^ 2 * v + 13 * u ^ 2 - 3 * u * v ^ 2 - 13 * u * v - 10 * u - 7 * v ^ 2 - 14 * v - 7

/-- Cell A: family `Z`, orientation `(u', u)`, `w₁ = (1, 1)`, f4-edge. -/
def KeyA (N u v : ℕ) : Prop :=
  2 ≤ u ∧ u ≤ v ∧ 1 * (u + 1) ≤ 1 * v ∧ 2 * u + 5 ≤ N ∧
  0 ≤ kAc8 N u v ∧
  0 ≤ kAb8 N u v ∧
  0 ≤ kAr8 N u v ∧
  0 ≤ kAa8 N u v ∧
  0 ≤ kAc9 N u v ∧
  0 ≤ kAb9 N u v ∧
  0 ≤ kAr9 N u v ∧
  0 ≤ kAa9 N u v

theorem parOK_of_keyA {N u v : ℕ} (h : KeyA N u v) : ParOK (consZ N v u) := by
  obtain ⟨hu, huv, hv, hN, c8, b8, r8, a8, c9, b9, r9, a9⟩ := h
  have huq : (2 : ℚ) ≤ u := by exact_mod_cast hu
  have huvq : (u : ℚ) ≤ v := by exact_mod_cast huv
  have hvq : (1 * ((u : ℚ) + 1) : ℚ) ≤ 1 * (v : ℚ) := by exact_mod_cast hv
  have hNq : 2 * (u : ℚ) + 5 ≤ N := by exact_mod_cast hN
  have hD : (0 : ℚ) < (((v : ℚ) + 1) - u) := by linarith
  have hv1 : (0 : ℚ) < v + 1 := by linarith
  have hu1 : (0 : ℚ) < u + 1 := by linarith
  have hv0 : (0 : ℚ) < v := by linarith
  have hu0 : (0 : ℚ) < u := by linarith
  have hD8 : (0 : ℚ) < -2*(v + 1)*(u - v - 1) := by nlinarith
  have hD9 : (0 : ℚ) < -2*u*(u - v - 1) := by nlinarith
  set s8 : ℚ := ((N : ℚ) + 1) / 2 - 1 - ((N : ℚ) + 2) * 1 / (v + 1) with hs8
  set s9 : ℚ := ((((N : ℚ) + 1) / 2 - 1) * (u + 1) - ((N : ℚ) + 2) * 1 - 1) / u - 1 with hs9
  have key : ∀ σ1 : ℚ, σ1 ≤ s8 → σ1 ≤ s9 → 0 ≤ ((σ1 - ((N : ℚ) + 2) / (((v : ℚ) + 1) - u)) * (v + 1) - 1 + ((N : ℚ) + 2) * 1) * (u + 1) - (((σ1 - ((N : ℚ) + 2) / (((v : ℚ) + 1) - u)) + 1) * u + 1 + ((N : ℚ) + 2) * 1) * v - v * (u + 1) →
      (v : ℚ) + 1 ≤ (σ1 - ((N : ℚ) + 2) / (((v : ℚ) + 1) - u)) → (u : ℚ) + 1 ≤ (σ1 - ((N : ℚ) + 2) / (((v : ℚ) + 1) - u)) → (2 : ℚ) * ((N : ℚ) + 2) ≤ (σ1 - ((N : ℚ) + 2) / (((v : ℚ) + 1) - u)) * (v + 1) + 0 - 1 → ParOK (consZ N v u) := by
    intro σ1 h8 h9 hc hb hr ha
    unfold consZ
    refine parOK_edge4 (K := N + 2) (L := v) (R := u) (p := 1) (q := 1) (p2 := 0) (q2 := 1)
      (Δ := (((v : ℚ) + 1) - u)) (s0 := ((N : ℚ) + 1) / 2) (σ1 := σ1)
      (σ3 := σ1 - ((N : ℚ) + 2) / (((v : ℚ) + 1) - u)) (by omega) (by omega) (by omega) (by norm_num)
      (by norm_num) (by norm_num) (by push_cast; ring) hD (by push_cast; linarith) (s0_le_Z N)
      (by push_cast; linarith) (by linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; ring) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith)
  rcases le_total s8 s9 with hle | hle
  · apply key s8 le_rfl hle
    · exact nonneg_of_cleared hD8 c8 (by rw [hs8]; unfold kAc8; field_simp; ring)
    · exact sub_nonneg.mp (nonneg_of_cleared hD8 b8 (by rw [hs8]; unfold kAb8; field_simp; ring))
    · exact sub_nonneg.mp (nonneg_of_cleared hD8 r8 (by rw [hs8]; unfold kAr8; field_simp; ring))
    · exact sub_nonneg.mp (nonneg_of_cleared hD8 a8 (by rw [hs8]; unfold kAa8; field_simp; ring))
  · apply key s9 hle le_rfl
    · exact nonneg_of_cleared hD9 c9 (by rw [hs9]; unfold kAc9; field_simp; ring)
    · exact sub_nonneg.mp (nonneg_of_cleared hD9 b9 (by rw [hs9]; unfold kAb9; field_simp; ring))
    · exact sub_nonneg.mp (nonneg_of_cleared hD9 r9 (by rw [hs9]; unfold kAr9; field_simp; ring))
    · exact sub_nonneg.mp (nonneg_of_cleared hD9 a9 (by rw [hs9]; unfold kAa9; field_simp; ring))

/-- Key polynomial `chord8` of cell B4. -/
def kB4c8 (N u v : ℚ) : ℚ :=
  -10 * N * u ^ 2 * v - 2 * N * u ^ 2 + 7 * N * u * v ^ 2 + 4 * N * u * v - 3 * N * u - N * v ^ 3 - 3 * N * v ^ 2 - 3 * N * v - N + 8 * u ^ 2 * v ^ 2 - 2 * u ^ 2 * v + 6 * u ^ 2 - 4 * u * v ^ 3 + 15 * u * v ^ 2 + 18 * u * v - u - 9 * v ^ 3 - 25 * v ^ 2 - 23 * v - 7

/-- Key polynomial `bot8` of cell B4. -/
def kB4b8 (N u v : ℚ) : ℚ :=
  -2 * N * u * v + 6 * N * u + N * v ^ 2 - 4 * N * v - 5 * N + 4 * u * v ^ 2 + 10 * u * v + 22 * u - 2 * v ^ 3 - 7 * v ^ 2 - 20 * v - 15

/-- Key polynomial `botR8` of cell B4. -/
def kB4r8 (N u v : ℚ) : ℚ :=
  -2 * N * u * v + 6 * N * u + N * v ^ 2 - 4 * N * v - 5 * N + 4 * u ^ 2 * v + 4 * u ^ 2 - 2 * u * v ^ 2 + 2 * u * v + 20 * u - 3 * v ^ 2 - 18 * v - 15

/-- Key polynomial `amin8` of cell B4. -/
def kB4a8 (N u v : ℚ) : ℚ :=
  -2 * N * u * v ^ 2 + 12 * N * u * v + 14 * N * u + N * v ^ 3 - 7 * N * v ^ 2 - 17 * N * v - 9 * N + 2 * u * v ^ 2 + 40 * u * v + 38 * u - v ^ 3 - 25 * v ^ 2 - 47 * v - 23

/-- Key polynomial `chord9` of cell B4. -/
def kB4c9 (N u v : ℚ) : ℚ :=
  -10 * N * u ^ 3 + 7 * N * u ^ 2 * v - 5 * N * u ^ 2 - N * u * v ^ 2 + 3 * N * u * v + 4 * N * u - N * v ^ 2 - 2 * N * v - N + 8 * u ^ 3 * v - 6 * u ^ 3 - 4 * u ^ 2 * v ^ 2 + 21 * u ^ 2 * v + 7 * u ^ 2 - 11 * u * v ^ 2 - 5 * u * v + 6 * u - 7 * v ^ 2 - 14 * v - 7

/-- Key polynomial `bot9` of cell B4. -/
def kB4b9 (N u v : ℚ) : ℚ :=
  -2 * N * u ^ 2 + N * u * v + N * u - N * v - N + 4 * u ^ 2 * v + 10 * u ^ 2 - 2 * u * v ^ 2 - 7 * u * v + 5 * u - 7 * v - 7

/-- Key polynomial `botR9` of cell B4. -/
def kB4r9 (N u v : ℚ) : ℚ :=
  -2 * N * u ^ 2 + N * u * v + N * u - N * v - N + 4 * u ^ 3 - 2 * u ^ 2 * v + 8 * u ^ 2 - 5 * u * v + 5 * u - 7 * v - 7

/-- Key polynomial `amin9` of cell B4. -/
def kB4a9 (N u v : ℚ) : ℚ :=
  -2 * N * u ^ 2 * v + 6 * N * u ^ 2 + N * u * v ^ 2 - 2 * N * u * v - 3 * N * u - N * v ^ 2 - 2 * N * v - N + 6 * u ^ 2 * v + 26 * u ^ 2 - 3 * u * v ^ 2 - 6 * u * v - 3 * u - 7 * v ^ 2 - 14 * v - 7

/-- Cell B4: family `Z`, orientation `(u', u)`, `w₁ = (2, 1)`, f4-edge. -/
def KeyB4 (N u v : ℕ) : Prop :=
  2 ≤ u ∧ u ≤ v ∧ 2 * (u + 1) ≤ 1 * v ∧ 2 * u + 5 ≤ N ∧
  0 ≤ kB4c8 N u v ∧
  0 ≤ kB4b8 N u v ∧
  0 ≤ kB4r8 N u v ∧
  0 ≤ kB4a8 N u v ∧
  0 ≤ kB4c9 N u v ∧
  0 ≤ kB4b9 N u v ∧
  0 ≤ kB4r9 N u v ∧
  0 ≤ kB4a9 N u v

theorem parOK_of_keyB4 {N u v : ℕ} (h : KeyB4 N u v) : ParOK (consZ N v u) := by
  obtain ⟨hu, huv, hv, hN, c8, b8, r8, a8, c9, b9, r9, a9⟩ := h
  have huq : (2 : ℚ) ≤ u := by exact_mod_cast hu
  have huvq : (u : ℚ) ≤ v := by exact_mod_cast huv
  have hvq : (2 * ((u : ℚ) + 1) : ℚ) ≤ 1 * (v : ℚ) := by exact_mod_cast hv
  have hNq : 2 * (u : ℚ) + 5 ≤ N := by exact_mod_cast hN
  have hD : (0 : ℚ) < (((v : ℚ) + 1) - 2 * u) := by linarith
  have hv1 : (0 : ℚ) < v + 1 := by linarith
  have hu1 : (0 : ℚ) < u + 1 := by linarith
  have hv0 : (0 : ℚ) < v := by linarith
  have hu0 : (0 : ℚ) < u := by linarith
  have hD8 : (0 : ℚ) < -2*(v + 1)*(2*u - v - 1) := by nlinarith
  have hD9 : (0 : ℚ) < -2*u*(2*u - v - 1) := by nlinarith
  set s8 : ℚ := ((N : ℚ) + 1) / 2 - 1 - ((N : ℚ) + 2) * 2 / (v + 1) with hs8
  set s9 : ℚ := ((((N : ℚ) + 1) / 2 - 1) * (u + 1) - ((N : ℚ) + 2) * 1 - 1) / u - 1 with hs9
  have key : ∀ σ1 : ℚ, σ1 ≤ s8 → σ1 ≤ s9 → 0 ≤ ((σ1 - ((N : ℚ) + 2) / (((v : ℚ) + 1) - 2 * u)) * (v + 1) - 1 + ((N : ℚ) + 2) * 2) * (u + 1) - (((σ1 - ((N : ℚ) + 2) / (((v : ℚ) + 1) - 2 * u)) + 1) * u + 1 + ((N : ℚ) + 2) * 1) * v - v * (u + 1) →
      (v : ℚ) + 1 ≤ (σ1 - ((N : ℚ) + 2) / (((v : ℚ) + 1) - 2 * u)) → (u : ℚ) + 1 ≤ (σ1 - ((N : ℚ) + 2) / (((v : ℚ) + 1) - 2 * u)) → (2 : ℚ) * ((N : ℚ) + 2) ≤ (σ1 - ((N : ℚ) + 2) / (((v : ℚ) + 1) - 2 * u)) * (v + 1) + 0 - 1 → ParOK (consZ N v u) := by
    intro σ1 h8 h9 hc hb hr ha
    unfold consZ
    refine parOK_edge4 (K := N + 2) (L := v) (R := u) (p := 2) (q := 1) (p2 := 1) (q2 := 1)
      (Δ := (((v : ℚ) + 1) - 2 * u)) (s0 := ((N : ℚ) + 1) / 2) (σ1 := σ1)
      (σ3 := σ1 - ((N : ℚ) + 2) / (((v : ℚ) + 1) - 2 * u)) (by omega) (by omega) (by omega) (by norm_num)
      (by norm_num) (by norm_num) (by push_cast; ring) hD (by push_cast; linarith) (s0_le_Z N)
      (by push_cast; linarith) (by linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; ring) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith)
  rcases le_total s8 s9 with hle | hle
  · apply key s8 le_rfl hle
    · exact nonneg_of_cleared hD8 c8 (by rw [hs8]; unfold kB4c8; field_simp; ring)
    · exact sub_nonneg.mp (nonneg_of_cleared hD8 b8 (by rw [hs8]; unfold kB4b8; field_simp; ring))
    · exact sub_nonneg.mp (nonneg_of_cleared hD8 r8 (by rw [hs8]; unfold kB4r8; field_simp; ring))
    · exact sub_nonneg.mp (nonneg_of_cleared hD8 a8 (by rw [hs8]; unfold kB4a8; field_simp; ring))
  · apply key s9 hle le_rfl
    · exact nonneg_of_cleared hD9 c9 (by rw [hs9]; unfold kB4c9; field_simp; ring)
    · exact sub_nonneg.mp (nonneg_of_cleared hD9 b9 (by rw [hs9]; unfold kB4b9; field_simp; ring))
    · exact sub_nonneg.mp (nonneg_of_cleared hD9 r9 (by rw [hs9]; unfold kB4r9; field_simp; ring))
    · exact sub_nonneg.mp (nonneg_of_cleared hD9 a9 (by rw [hs9]; unfold kB4a9; field_simp; ring))

/-- Key polynomial `chord8` of cell B1. -/
def kB1c8 (N u v : ℚ) : ℚ :=
  -6 * N * u ^ 2 * v - 6 * N * u ^ 2 + 9 * N * u * v ^ 2 - 5 * N * u * v - 12 * N * u - 3 * N * v ^ 3 + 4 * N * v ^ 2 + N * v - 6 * N - 8 * u ^ 2 * v ^ 2 - 30 * u ^ 2 * v - 22 * u ^ 2 + 4 * u * v ^ 3 + 5 * u * v ^ 2 - 47 * u * v - 44 * u + v ^ 3 + 6 * v ^ 2 - 17 * v - 22

/-- Key polynomial `bot8` of cell B1. -/
def kB1b8 (N u v : ℚ) : ℚ :=
  2 * N * u * v - 6 * N * u - N * v ^ 2 + 3 * N * v - 6 * N - 4 * u * v ^ 2 - 10 * u * v - 22 * u + 2 * v ^ 3 + v ^ 2 - 3 * v - 22

/-- Key polynomial `botR8` of cell B1. -/
def kB1r8 (N u v : ℚ) : ℚ :=
  2 * N * u * v - 6 * N * u - N * v ^ 2 + 3 * N * v - 6 * N - 4 * u ^ 2 * v + 2 * u * v ^ 2 - 14 * u * v - 22 * u + 5 * v ^ 2 - 3 * v - 22

/-- Key polynomial `amin8` of cell B1. -/
def kB1a8 (N u v : ℚ) : ℚ :=
  2 * N * u * v ^ 2 - 14 * N * u * v - N * v ^ 3 + 7 * N * v ^ 2 - 14 * N * v - 2 * u * v ^ 2 - 38 * u * v + v ^ 3 + 13 * v ^ 2 - 38 * v

/-- Key polynomial `chord9` of cell B1. -/
def kB1c9 (N u v : ℚ) : ℚ :=
  -6 * N * u ^ 3 + 9 * N * u ^ 2 * v - 12 * N * u ^ 2 - 3 * N * u * v ^ 2 + 8 * N * u * v - 6 * N * u - N * v ^ 2 - N * v - 8 * u ^ 3 * v - 26 * u ^ 3 + 4 * u ^ 2 * v ^ 2 - u ^ 2 * v - 62 * u ^ 2 + 3 * u * v ^ 2 - 46 * u + 3 * v ^ 2 - 7 * v - 10

/-- Key polynomial `bot9` of cell B1. -/
def kB1b9 (N u v : ℚ) : ℚ :=
  2 * N * u ^ 2 - N * u * v - 2 * N * u + N * v - 4 * N - 4 * u ^ 2 * v - 6 * u ^ 2 + 2 * u * v ^ 2 - 5 * u * v - 24 * u + 2 * v ^ 2 + 3 * v - 18

/-- Key polynomial `botR9` of cell B1. -/
def kB1r9 (N u v : ℚ) : ℚ :=
  2 * N * u ^ 2 - N * u * v - 2 * N * u + N * v - 4 * N - 4 * u ^ 3 + 2 * u ^ 2 * v - 14 * u ^ 2 + 5 * u * v - 28 * u + 7 * v - 18

/-- Key polynomial `amin9` of cell B1. -/
def kB1a9 (N u v : ℚ) : ℚ :=
  2 * N * u ^ 2 * v - 8 * N * u ^ 2 - N * u * v ^ 2 + 2 * N * u * v - 16 * N * u + N * v ^ 2 - 8 * N + 2 * u ^ 2 * v - 16 * u ^ 2 - u * v ^ 2 - 32 * u + 3 * v ^ 2 - 2 * v - 16

/-- Cell B1: family `Z`, orientation `(u', u)`, `w₁ = (2, 1)`, f1-edge. -/
def KeyB1 (N u v : ℕ) : Prop :=
  2 ≤ u ∧ u ≤ v ∧ 1 * (v + 1) ≤ 2 * u ∧ 2 * u + 5 ≤ N ∧
  0 ≤ kB1c8 N u v ∧
  0 ≤ kB1b8 N u v ∧
  0 ≤ kB1r8 N u v ∧
  0 ≤ kB1a8 N u v ∧
  0 ≤ kB1c9 N u v ∧
  0 ≤ kB1b9 N u v ∧
  0 ≤ kB1r9 N u v ∧
  0 ≤ kB1a9 N u v

theorem parOK_of_keyB1 {N u v : ℕ} (h : KeyB1 N u v) : ParOK (consZ N v u) := by
  obtain ⟨hu, huv, hv, hN, c8, b8, r8, a8, c9, b9, r9, a9⟩ := h
  have huq : (2 : ℚ) ≤ u := by exact_mod_cast hu
  have huvq : (u : ℚ) ≤ v := by exact_mod_cast huv
  have hvq : (1 * ((v : ℚ) + 1) : ℚ) ≤ 2 * (u : ℚ) := by exact_mod_cast hv
  have hNq : 2 * (u : ℚ) + 5 ≤ N := by exact_mod_cast hN
  have hD : (0 : ℚ) < (2 * ((u : ℚ) + 1) - v) := by linarith
  have hv1 : (0 : ℚ) < v + 1 := by linarith
  have hu1 : (0 : ℚ) < u + 1 := by linarith
  have hv0 : (0 : ℚ) < v := by linarith
  have hu0 : (0 : ℚ) < u := by linarith
  have hD8 : (0 : ℚ) < 2*v*(2*u - v + 2) := by nlinarith
  have hD9 : (0 : ℚ) < 2*(u + 1)*(2*u - v + 2) := by nlinarith
  set s8 : ℚ := ((((N : ℚ) + 1) / 2 - 1) * (v + 1) - ((N : ℚ) + 2) * 2 - 1) / v - 1 with hs8
  set s9 : ℚ := ((N : ℚ) + 1) / 2 - 1 - ((N : ℚ) + 2) * 1 / (u + 1) with hs9
  have key : ∀ σ1 : ℚ, σ1 ≤ s8 → σ1 ≤ s9 → 0 ≤ ((σ1 - ((N : ℚ) + 2) / (2 * ((u : ℚ) + 1) - v)) * (u + 1) - 1 + ((N : ℚ) + 2) * 1) * (v + 1) - (((σ1 - ((N : ℚ) + 2) / (2 * ((u : ℚ) + 1) - v)) + 1) * v + 1 + ((N : ℚ) + 2) * 2) * u - u * (v + 1) →
      (v : ℚ) + 1 ≤ (σ1 - ((N : ℚ) + 2) / (2 * ((u : ℚ) + 1) - v)) → (u : ℚ) + 1 ≤ (σ1 - ((N : ℚ) + 2) / (2 * ((u : ℚ) + 1) - v)) → (2 : ℚ) * ((N : ℚ) + 2) ≤ ((σ1 - ((N : ℚ) + 2) / (2 * ((u : ℚ) + 1) - v)) + 1) * v + 0 → ParOK (consZ N v u) := by
    intro σ1 h8 h9 hc hb hr ha
    unfold consZ
    refine parOK_edge1 (K := N + 2) (L := v) (R := u) (p := 2) (q := 1) (p2 := 1) (q2 := 1)
      (Δ := (2 * ((u : ℚ) + 1) - v)) (s0 := ((N : ℚ) + 1) / 2) (τ3 := σ1)
      (τ1 := σ1 - ((N : ℚ) + 2) / (2 * ((u : ℚ) + 1) - v)) (by omega) (by omega) (by omega) (by norm_num)
      (by norm_num) (by norm_num) (by push_cast; ring) hD (by push_cast; linarith) (s0_le_Z N)
      (by push_cast; linarith) (by linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; ring) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith)
  rcases le_total s8 s9 with hle | hle
  · apply key s8 le_rfl hle
    · exact nonneg_of_cleared hD8 c8 (by rw [hs8]; unfold kB1c8; field_simp; ring)
    · exact sub_nonneg.mp (nonneg_of_cleared hD8 b8 (by rw [hs8]; unfold kB1b8; field_simp; ring))
    · exact sub_nonneg.mp (nonneg_of_cleared hD8 r8 (by rw [hs8]; unfold kB1r8; field_simp; ring))
    · exact sub_nonneg.mp (nonneg_of_cleared hD8 a8 (by rw [hs8]; unfold kB1a8; field_simp; ring))
  · apply key s9 hle le_rfl
    · exact nonneg_of_cleared hD9 c9 (by rw [hs9]; unfold kB1c9; field_simp; ring)
    · exact sub_nonneg.mp (nonneg_of_cleared hD9 b9 (by rw [hs9]; unfold kB1b9; field_simp; ring))
    · exact sub_nonneg.mp (nonneg_of_cleared hD9 r9 (by rw [hs9]; unfold kB1r9; field_simp; ring))
    · exact sub_nonneg.mp (nonneg_of_cleared hD9 a9 (by rw [hs9]; unfold kB1a9; field_simp; ring))

/-! ## The old regions `D` and `B` from polynomial inequalities over `ℚ` -/

/-- `RegionD`, first inequality, with `u - u % 2` replaced by `u - 1`. -/
def dP1 (N u v : ℚ) : ℚ := (u - 1) * (N + 2) * (u + v + 1) - 2 * (u + 1) * ((N + 2) * u + 2 * u * v + u)
/-- `RegionD`, second inequality, with `u % 2` replaced by `1`. -/
def dP2 (N u v : ℚ) : ℚ := ((u - 1) * (N + 2) - 2 * u + 2) * (v + 1) - 2 * u * (v ^ 2 + N + 2)
def dP3 (N u v : ℚ) : ℚ := N - u - v

def DPolys (N u v : ℕ) : Prop := 0 ≤ dP1 N u v ∧ 0 ≤ dP2 N u v ∧ 0 ≤ dP3 N u v

theorem regionD_of_polys {N u v : ℕ} (hu : 4 ≤ u) (huv : u ≤ v) (h : DPolys N u v) :
    ArithCover.RegionD N u v := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold dP1 at h1; unfold dP2 at h2; unfold dP3 at h3
  have hr : u % 2 ≤ 1 := by omega
  have hrq : ((u % 2 : ℕ) : ℚ) ≤ 1 := by exact_mod_cast hr
  have hr0 : (0 : ℚ) ≤ ((u % 2 : ℕ) : ℚ) := by positivity
  have huq : (4 : ℚ) ≤ u := by exact_mod_cast hu
  have hvq : (u : ℚ) ≤ v := by exact_mod_cast huv
  have hN0 : (0 : ℚ) ≤ N := by positivity
  refine ⟨hu, huv, ?_, ?_, ?_⟩
  · have : (u : ℚ) + v ≤ N := by linarith
    exact_mod_cast this
  · have e : ((u - u % 2 : ℕ) : ℚ) = (u : ℚ) - ((u % 2 : ℕ) : ℚ) := by
      rw [Nat.cast_sub (Nat.mod_le u 2)]
    have key : (2 * ((u : ℚ) + 1) * (((N : ℚ) + 2) * u + 2 * u * v + u)) ≤
        ((u - u % 2 : ℕ) : ℚ) * ((N : ℚ) + 2) * ((u : ℚ) + v + 1) := by
      rw [e]
      have : 0 ≤ (1 - ((u % 2 : ℕ) : ℚ)) * (((N : ℚ) + 2) * ((u : ℚ) + v + 1)) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith
    exact_mod_cast key
  · have hNn : 8 ≤ N := by
      have : (8 : ℚ) ≤ N := by linarith
      exact_mod_cast this
    have hle : u % 2 * (N + 2) + 2 * u ≤ u * (N + 2) := by
      have : u % 2 * (N + 2) ≤ 1 * (N + 2) := Nat.mul_le_mul_right _ hr
      nlinarith
    have e : ((u * (N + 2) - u % 2 * (N + 2) - 2 * u + 2 : ℕ) : ℚ) =
        (u : ℚ) * (N + 2) - ((u % 2 : ℕ) : ℚ) * (N + 2) - 2 * u + 2 := by
      rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
    have key : 2 * (u : ℚ) * ((v : ℚ) * v + ((N : ℚ) + 2)) ≤
        ((u * (N + 2) - u % 2 * (N + 2) - 2 * u + 2 : ℕ) : ℚ) * ((v : ℚ) + 1) := by
      rw [e]
      have : 0 ≤ (1 - ((u % 2 : ℕ) : ℚ)) * (((N : ℚ) + 2) * ((v : ℚ) + 1)) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith
    exact_mod_cast key

/-- `RegionB` with `n = N + 2 - 2v` and `u / 2` replaced by `(u - 1)/2` (all times 2). -/
def bP1 (N u v : ℚ) : ℚ := (u - 1) * (N + 2) - 2 * (u + 1) * (N + 2 - 2 * v - 1)
def bP2 (N u v : ℚ) : ℚ := (u - 1) * (N + 2) - 2 * u * (u + 1)
def bP3 (N u v : ℚ) : ℚ := (u - 1) * (N + 2) * (N + 2 - 2 * v + 2 * u) -
  2 * u * ((2 * u + 1) * (N + 2 - 2 * v) - 2 * u) - 2 * u * (u + 1) * (2 * (N + 2 - 2 * v) + (N + 2) - 1)
def bP4 (N u v : ℚ) : ℚ := (u - 1) * v - 4 * (u + 1)
def bP5 (N u v : ℚ) : ℚ := N + 2 - 2 * v - 3

def BPolys (N u v : ℕ) : Prop :=
  0 ≤ bP1 N u v ∧ 0 ≤ bP2 N u v ∧ 0 ≤ bP3 N u v ∧ 0 ≤ bP4 N u v ∧ 0 ≤ bP5 N u v

theorem regionB_of_polys {N u v : ℕ} (hu : 4 ≤ u) (h : BPolys N u v) :
    ArithCover.RegionB N u v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold bP1 at h1; unfold bP2 at h2; unfold bP3 at h3; unfold bP4 at h4; unfold bP5 at h5
  have huq : (4 : ℚ) ≤ u := by exact_mod_cast hu
  have hc : ((u : ℚ) - 1) ≤ 2 * ((u / 2 : ℕ) : ℚ) := by
    have : u ≤ 2 * (u / 2) + 1 := by omega
    have : (u : ℚ) ≤ 2 * ((u / 2 : ℕ) : ℚ) + 1 := by exact_mod_cast this
    linarith
  have hn : 2 * v + 3 ≤ N + 2 := by
    have : (2 : ℚ) * v + 3 ≤ N + 2 := by linarith
    exact_mod_cast this
  obtain ⟨n, hnN⟩ : ∃ n, N + 2 = n + 2 * v := ⟨N + 2 - 2 * v, by omega⟩
  have hnq : (N : ℚ) + 2 = n + 2 * v := by exact_mod_cast hnN
  have e1 : N + 2 - 2 * v = n := by omega
  have e2 : N + 2 - 2 * v - 1 = n - 1 := by omega
  have hn3 : 3 ≤ n := by omega
  rw [hnq] at h1 h2 h3 h5
  have hcn : (0 : ℚ) ≤ ((u / 2 : ℕ) : ℚ) := by positivity
  have hnq' : (3 : ℚ) ≤ n := by exact_mod_cast hn3
  refine ⟨by omega, hn, ?_, ?_, ?_, ?_⟩
  · rw [e2]
    have key : ((u : ℚ) + 1) * ((n : ℚ) - 1) ≤ ((u / 2 : ℕ) : ℚ) * (n + 2 * v) := by
      have := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℚ) ≤ n + 2 * v)
      nlinarith
    have e : (((n - 1 : ℕ)) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hnN]
    have : ((u + 1) * (n - 1) : ℕ) ≤ ((u / 2 * (n + 2 * v)) : ℕ) := by
      have : (((u + 1) * (n - 1) : ℕ) : ℚ) ≤ ((u / 2 * (n + 2 * v) : ℕ) : ℚ) := by
        push_cast; rw [e]; linarith
      exact_mod_cast this
    exact this
  · rw [hnN]
    have : (((u * (u + 1)) : ℕ) : ℚ) ≤ ((u / 2 * (n + 2 * v) : ℕ) : ℚ) := by
      push_cast
      have := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℚ) ≤ n + 2 * v)
      nlinarith
    exact_mod_cast this
  · rw [e1, hnN]
    have hs : 2 * u ≤ (2 * u + 1) * n := by nlinarith
    have e3 : (((2 * u + 1) * n - 2 * u : ℕ) : ℚ) = (2 * (u : ℚ) + 1) * n - 2 * u := by
      rw [Nat.cast_sub hs]; push_cast; ring
    have e4 : ((2 * n + (n + 2 * v) - 1 : ℕ) : ℚ) = 2 * (n : ℚ) + (n + 2 * v) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have : ((u * ((2 * u + 1) * n - 2 * u) + u * (u + 1) * (2 * n + (n + 2 * v) - 1) : ℕ) : ℚ) ≤
        ((u / 2 * (n + 2 * v) * (n + 2 * u) : ℕ) : ℚ) := by
      push_cast
      rw [e3, e4]
      have := mul_le_mul_of_nonneg_right hc
        (by positivity : (0 : ℚ) ≤ ((n : ℚ) + 2 * v) * (n + 2 * u))
      nlinarith
    exact_mod_cast this
  · have hv : (0 : ℚ) ≤ v := by positivity
    have : (((2 * (u + 1)) : ℕ) : ℚ) ≤ ((u / 2 * v : ℕ) : ℚ) := by
      push_cast
      have := mul_le_mul_of_nonneg_right hc hv
      nlinarith
    exact_mod_cast this

theorem leaf_L1a {N u v : ℕ} (g0 : 4 ≤ u) (g1 : u + 10 ≤ v) (g2 : u + 2 * v + 1 ≤ N) (g3 : 301 ≤ N) (g4 : 0 ≤ u) (g5 : 0 ≤ v) (g6 : 2 * v ≤ 3 * u) (g7 : 4 * u + 81 ≤ N) :
    KeyA N u v := by
  have h0 : (0 : ℚ) ≤ u - 4 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g0; push_cast at h; linarith
  have h1 : (0 : ℚ) ≤ -u + v - 10 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g1; push_cast at h; linarith
  have h2 : (0 : ℚ) ≤ N - u - 2 * v - 1 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g2; push_cast at h; linarith
  have h3 : (0 : ℚ) ≤ N - 301 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g3; push_cast at h; linarith
  have h4 : (0 : ℚ) ≤ u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g4; push_cast at h; linarith
  have h5 : (0 : ℚ) ≤ v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g5; push_cast at h; linarith
  have h6 : (0 : ℚ) ≤ 3 * u - 2 * v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g6; push_cast at h; linarith
  have h7 : (0 : ℚ) ≤ N - 4 * u - 81 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g7; push_cast at h; linarith
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold kAc8; linarith [mul_nonneg (h0) h2, mul_nonneg (h2) h4, mul_nonneg (h3) h4, mul_nonneg (h4) h6, mul_nonneg (h5) h6, mul_nonneg (mul_nonneg (h0) h5) h7, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h1) h5) h6, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h4) h4) h7, mul_nonneg (mul_nonneg (h4) h5) h7, mul_nonneg (mul_nonneg (h5) h5) h6, mul_nonneg (mul_nonneg (h5) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h0) h1) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h1) h2) h4) h5, mul_nonneg (mul_nonneg (mul_nonneg (h1) h4) h5) h6, mul_nonneg (mul_nonneg (mul_nonneg (h1) h5) h6) h7]
  · unfold kAb8; linarith [mul_nonneg (h0) h2, mul_nonneg (h0) h5, mul_nonneg (h2) h5, mul_nonneg (h3) h4, mul_nonneg (h3) h5, mul_nonneg (h4) h4, mul_nonneg (mul_nonneg (h0) h1) h5, mul_nonneg (mul_nonneg (h1) h2) h5, mul_nonneg (mul_nonneg (h1) h3) h5, mul_nonneg (mul_nonneg (h1) h5) h6]
  · unfold kAr8; linarith [mul_nonneg (h0) h2, mul_nonneg (h1) h1, mul_nonneg (h1) h5, mul_nonneg (h2) h5, mul_nonneg (h3) h4, mul_nonneg (h3) h5, mul_nonneg (mul_nonneg (h1) h1) h5, mul_nonneg (mul_nonneg (h1) h2) h5, mul_nonneg (mul_nonneg (h1) h3) h5]
  · unfold kAa8; linarith [mul_nonneg (h0) h3, mul_nonneg (h1) h5, mul_nonneg (h3) h4, mul_nonneg (h5) h5, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h1) h1) h5, mul_nonneg (mul_nonneg (h1) h5) h5, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h3) h5) h5, mul_nonneg (mul_nonneg (h5) h5) h5, mul_nonneg (mul_nonneg (mul_nonneg (h1) h3) h5) h5]
  · unfold kAc9; linarith [mul_nonneg (h0) h3, mul_nonneg (h1) h2, mul_nonneg (h3) h4, mul_nonneg (h3) h6, mul_nonneg (h4) h6, mul_nonneg (h5) h6, mul_nonneg (mul_nonneg (h0) h0) h2, mul_nonneg (mul_nonneg (h0) h0) h7, mul_nonneg (mul_nonneg (h0) h4) h7, mul_nonneg (mul_nonneg (h4) h5) h6, mul_nonneg (mul_nonneg (h5) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h0) h0) h1) h2, mul_nonneg (mul_nonneg (mul_nonneg (h0) h0) h1) h7, mul_nonneg (mul_nonneg (mul_nonneg (h1) h2) h4) h4, mul_nonneg (mul_nonneg (mul_nonneg (h1) h2) h4) h6, mul_nonneg (mul_nonneg (mul_nonneg (h1) h3) h4) h6, mul_nonneg (mul_nonneg (mul_nonneg (h1) h4) h4) h6, mul_nonneg (mul_nonneg (mul_nonneg (h1) h4) h5) h6]
  · unfold kAb9; linarith [mul_nonneg (h0) h0, mul_nonneg (h0) h2, mul_nonneg (h0) h3, mul_nonneg (h2) h4, mul_nonneg (h3) h4, mul_nonneg (h4) h6, mul_nonneg (h5) h6, mul_nonneg (mul_nonneg (h0) h0) h1, mul_nonneg (mul_nonneg (h0) h1) h2, mul_nonneg (mul_nonneg (h1) h2) h4]
  · unfold kAr9; linarith [mul_nonneg (h0) h1, mul_nonneg (h0) h2, mul_nonneg (h1) h3, mul_nonneg (h2) h5, mul_nonneg (h3) h5, mul_nonneg (mul_nonneg (h0) h1) h1, mul_nonneg (mul_nonneg (h0) h1) h2, mul_nonneg (mul_nonneg (h0) h1) h5, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h1) h4) h5]
  · unfold kAa9; linarith [mul_nonneg (h0) h3, mul_nonneg (h3) h4, mul_nonneg (mul_nonneg (h0) h1) h5, mul_nonneg (mul_nonneg (h0) h2) h4, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h0) h3) h5, mul_nonneg (mul_nonneg (h0) h5) h5, mul_nonneg (mul_nonneg (h1) h1) h4, mul_nonneg (mul_nonneg (h1) h4) h5, mul_nonneg (mul_nonneg (h2) h4) h4, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h3) h4) h4, mul_nonneg (mul_nonneg (h4) h5) h5, mul_nonneg (mul_nonneg (mul_nonneg (h0) h1) h3) h5, mul_nonneg (mul_nonneg (mul_nonneg (h1) h3) h4) h5]

theorem leaf_L1b {N u v : ℕ} (g0 : 4 ≤ u) (g1 : u + 10 ≤ v) (g2 : u + 2 * v + 1 ≤ N) (g3 : 301 ≤ N) (g4 : 0 ≤ u) (g5 : 0 ≤ v) (g6 : 2 * v ≤ 3 * u) (g7 : N + 41 ≤ 4 * u) :
    KeyA N u v := by
  have h0 : (0 : ℚ) ≤ u - 4 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g0; push_cast at h; linarith
  have h1 : (0 : ℚ) ≤ -u + v - 10 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g1; push_cast at h; linarith
  have h2 : (0 : ℚ) ≤ N - u - 2 * v - 1 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g2; push_cast at h; linarith
  have h3 : (0 : ℚ) ≤ N - 301 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g3; push_cast at h; linarith
  have h4 : (0 : ℚ) ≤ u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g4; push_cast at h; linarith
  have h5 : (0 : ℚ) ≤ v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g5; push_cast at h; linarith
  have h6 : (0 : ℚ) ≤ 3 * u - 2 * v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g6; push_cast at h; linarith
  have h7 : (0 : ℚ) ≤ -N + 4 * u - 41 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g7; push_cast at h; linarith
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold kAc8; linarith [mul_nonneg (h0) h2, mul_nonneg (h2) h4, mul_nonneg (h3) h6, mul_nonneg (h3) h7, mul_nonneg (h5) h6, mul_nonneg (h5) h7, mul_nonneg (mul_nonneg (h0) h1) h3, mul_nonneg (mul_nonneg (h0) h3) h5, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h1) h4) h6, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h2) h5) h7, mul_nonneg (mul_nonneg (h3) h3) h5, mul_nonneg (mul_nonneg (h4) h5) h6, mul_nonneg (mul_nonneg (h4) h5) h7, mul_nonneg (mul_nonneg (h5) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h0) h1) h2) h5, mul_nonneg (mul_nonneg (mul_nonneg (h0) h1) h5) h6, mul_nonneg (mul_nonneg (mul_nonneg (h0) h2) h2) h6, mul_nonneg (mul_nonneg (mul_nonneg (h1) h3) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h1) h4) h4) h6, mul_nonneg (mul_nonneg (mul_nonneg (h1) h5) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h2) h2) h7) h7, mul_nonneg (mul_nonneg (mul_nonneg (h2) h3) h3) h7, mul_nonneg (mul_nonneg (mul_nonneg (h5) h5) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h7) h7) h7) h7]
  · unfold kAb8; linarith [mul_nonneg (h0) h5, mul_nonneg (h2) h4, mul_nonneg (h2) h5, mul_nonneg (h2) h7, mul_nonneg (h3) h3, mul_nonneg (h3) h4, mul_nonneg (h4) h4, mul_nonneg (mul_nonneg (h0) h1) h5, mul_nonneg (mul_nonneg (h1) h2) h5, mul_nonneg (mul_nonneg (h1) h3) h5, mul_nonneg (mul_nonneg (h1) h5) h6]
  · unfold kAr8; linarith [mul_nonneg (h0) h2, mul_nonneg (h1) h1, mul_nonneg (h1) h5, mul_nonneg (h2) h5, mul_nonneg (h3) h4, mul_nonneg (h3) h5, mul_nonneg (mul_nonneg (h1) h1) h5, mul_nonneg (mul_nonneg (h1) h2) h5, mul_nonneg (mul_nonneg (h1) h3) h5]
  · unfold kAa8; linarith [mul_nonneg (h0) h3, mul_nonneg (h1) h5, mul_nonneg (h3) h4, mul_nonneg (h5) h5, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h1) h1) h5, mul_nonneg (mul_nonneg (h1) h5) h5, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h3) h5) h5, mul_nonneg (mul_nonneg (h5) h5) h5, mul_nonneg (mul_nonneg (mul_nonneg (h1) h3) h5) h5]
  · unfold kAc9; linarith [mul_nonneg (h2) h7, mul_nonneg (h3) h3, mul_nonneg (h4) h7, mul_nonneg (h5) h7, mul_nonneg (h6) h6, mul_nonneg (mul_nonneg (h0) h0) h3, mul_nonneg (mul_nonneg (h0) h3) h4, mul_nonneg (mul_nonneg (h2) h4) h4, mul_nonneg (mul_nonneg (h3) h5) h6, mul_nonneg (mul_nonneg (h4) h4) h6, mul_nonneg (mul_nonneg (h4) h5) h7, mul_nonneg (mul_nonneg (h5) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h0) h0) h1) h6, mul_nonneg (mul_nonneg (mul_nonneg (h0) h1) h2) h4, mul_nonneg (mul_nonneg (mul_nonneg (h0) h1) h4) h6, mul_nonneg (mul_nonneg (mul_nonneg (h1) h2) h4) h4, mul_nonneg (mul_nonneg (mul_nonneg (h1) h4) h5) h7]
  · unfold kAb9; linarith [mul_nonneg (h0) h0, mul_nonneg (h0) h2, mul_nonneg (h0) h3, mul_nonneg (h2) h4, mul_nonneg (h3) h6, mul_nonneg (h4) h6, mul_nonneg (h5) h7, mul_nonneg (mul_nonneg (h0) h0) h1, mul_nonneg (mul_nonneg (h1) h2) h4]
  · unfold kAr9; linarith [mul_nonneg (h0) h1, mul_nonneg (h0) h2, mul_nonneg (h1) h3, mul_nonneg (h2) h5, mul_nonneg (h3) h5, mul_nonneg (mul_nonneg (h0) h1) h1, mul_nonneg (mul_nonneg (h0) h1) h2, mul_nonneg (mul_nonneg (h0) h1) h5, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h1) h4) h5]
  · unfold kAa9; linarith [mul_nonneg (h0) h3, mul_nonneg (h3) h4, mul_nonneg (mul_nonneg (h0) h1) h5, mul_nonneg (mul_nonneg (h0) h2) h4, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h0) h3) h5, mul_nonneg (mul_nonneg (h0) h5) h5, mul_nonneg (mul_nonneg (h1) h1) h4, mul_nonneg (mul_nonneg (h1) h4) h5, mul_nonneg (mul_nonneg (h2) h4) h4, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h3) h4) h4, mul_nonneg (mul_nonneg (h4) h5) h5, mul_nonneg (mul_nonneg (mul_nonneg (h0) h1) h3) h5, mul_nonneg (mul_nonneg (mul_nonneg (h1) h3) h4) h5]

theorem leaf_L1c {N u v : ℕ} (g0 : 4 ≤ u) (g1 : u + 10 ≤ v) (g2 : u + 2 * v + 1 ≤ N) (g3 : 301 ≤ N) (g4 : 0 ≤ u) (g5 : 0 ≤ v) (g6 : 2 * v ≤ 3 * u) (g7 : u + 2 * v + 82 ≤ N) :
    KeyA N u v := by
  have h0 : (0 : ℚ) ≤ u - 4 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g0; push_cast at h; linarith
  have h1 : (0 : ℚ) ≤ -u + v - 10 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g1; push_cast at h; linarith
  have h2 : (0 : ℚ) ≤ N - u - 2 * v - 1 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g2; push_cast at h; linarith
  have h3 : (0 : ℚ) ≤ N - 301 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g3; push_cast at h; linarith
  have h4 : (0 : ℚ) ≤ u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g4; push_cast at h; linarith
  have h5 : (0 : ℚ) ≤ v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g5; push_cast at h; linarith
  have h6 : (0 : ℚ) ≤ 3 * u - 2 * v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g6; push_cast at h; linarith
  have h7 : (0 : ℚ) ≤ N - u - 2 * v - 82 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g7; push_cast at h; linarith
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold kAc8; linarith [mul_nonneg (h0) h3, mul_nonneg (h1) h6, mul_nonneg (h3) h4, mul_nonneg (h3) h6, mul_nonneg (h5) h6, mul_nonneg (mul_nonneg (h0) h0) h2, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h0) h5) h7, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h1) h3) h6, mul_nonneg (mul_nonneg (h1) h5) h6, mul_nonneg (mul_nonneg (h3) h5) h6, mul_nonneg (mul_nonneg (h5) h5) h6, mul_nonneg (mul_nonneg (mul_nonneg (h0) h1) h2) h5, mul_nonneg (mul_nonneg (mul_nonneg (h0) h1) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h1) h3) h5) h6, mul_nonneg (mul_nonneg (mul_nonneg (h1) h4) h5) h6]
  · unfold kAb8; linarith [mul_nonneg (h0) h2, mul_nonneg (h2) h4, mul_nonneg (h2) h5, mul_nonneg (h3) h5, mul_nonneg (h4) h4, mul_nonneg (h4) h5, mul_nonneg (mul_nonneg (h0) h1) h5, mul_nonneg (mul_nonneg (h1) h2) h5, mul_nonneg (mul_nonneg (h1) h5) h7]
  · unfold kAr8; linarith [mul_nonneg (h0) h2, mul_nonneg (h1) h1, mul_nonneg (h1) h5, mul_nonneg (h2) h5, mul_nonneg (h3) h4, mul_nonneg (h3) h5, mul_nonneg (mul_nonneg (h1) h1) h5, mul_nonneg (mul_nonneg (h1) h2) h5, mul_nonneg (mul_nonneg (h1) h3) h5]
  · unfold kAa8; linarith [mul_nonneg (h0) h3, mul_nonneg (h1) h5, mul_nonneg (h3) h4, mul_nonneg (h5) h5, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h1) h1) h5, mul_nonneg (mul_nonneg (h1) h5) h5, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h3) h5) h5, mul_nonneg (mul_nonneg (h5) h5) h5, mul_nonneg (mul_nonneg (mul_nonneg (h1) h3) h5) h5]
  · unfold kAc9; linarith [mul_nonneg (h0) h3, mul_nonneg (h1) h2, mul_nonneg (h3) h4, mul_nonneg (h3) h6, mul_nonneg (h4) h6, mul_nonneg (h5) h6, mul_nonneg (mul_nonneg (h0) h0) h2, mul_nonneg (mul_nonneg (h0) h0) h7, mul_nonneg (mul_nonneg (h0) h4) h7, mul_nonneg (mul_nonneg (h1) h3) h6, mul_nonneg (mul_nonneg (h1) h4) h6, mul_nonneg (mul_nonneg (h2) h4) h6, mul_nonneg (mul_nonneg (h4) h5) h6, mul_nonneg (mul_nonneg (mul_nonneg (h0) h0) h1) h2, mul_nonneg (mul_nonneg (mul_nonneg (h0) h0) h1) h7, mul_nonneg (mul_nonneg (mul_nonneg (h1) h2) h4) h6, mul_nonneg (mul_nonneg (mul_nonneg (h1) h4) h4) h6, mul_nonneg (mul_nonneg (mul_nonneg (h1) h4) h5) h6]
  · unfold kAb9; linarith [mul_nonneg (h0) h2, mul_nonneg (h0) h5, mul_nonneg (h1) h6, mul_nonneg (h2) h4, mul_nonneg (h3) h4, mul_nonneg (mul_nonneg (h0) h1) h2, mul_nonneg (mul_nonneg (h0) h1) h3, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h1) h3) h4, mul_nonneg (mul_nonneg (h1) h4) h4, mul_nonneg (mul_nonneg (h1) h4) h6]
  · unfold kAr9; linarith [mul_nonneg (h0) h1, mul_nonneg (h0) h2, mul_nonneg (h1) h3, mul_nonneg (h2) h5, mul_nonneg (h3) h5, mul_nonneg (mul_nonneg (h0) h1) h1, mul_nonneg (mul_nonneg (h0) h1) h2, mul_nonneg (mul_nonneg (h0) h1) h5, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h1) h4) h5]
  · unfold kAa9; linarith [mul_nonneg (h0) h3, mul_nonneg (h3) h4, mul_nonneg (mul_nonneg (h0) h1) h5, mul_nonneg (mul_nonneg (h0) h2) h4, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h0) h3) h5, mul_nonneg (mul_nonneg (h0) h5) h5, mul_nonneg (mul_nonneg (h1) h1) h4, mul_nonneg (mul_nonneg (h1) h4) h5, mul_nonneg (mul_nonneg (h2) h4) h4, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h3) h4) h4, mul_nonneg (mul_nonneg (h4) h5) h5, mul_nonneg (mul_nonneg (mul_nonneg (h0) h1) h3) h5, mul_nonneg (mul_nonneg (mul_nonneg (h1) h3) h4) h5]

theorem leaf_L2a {N u v : ℕ} (g0 : 4 ≤ u) (g1 : u + 10 ≤ v) (g2 : u + 2 * v + 1 ≤ N) (g3 : 301 ≤ N) (g4 : 0 ≤ u) (g5 : 0 ≤ v) (g6 : 3 * u ≤ 2 * v) (g7 : v + 13 ≤ 2 * u) (g8 : 4 * u + 81 ≤ N) :
    KeyB1 N u v := by
  have h0 : (0 : ℚ) ≤ u - 4 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g0; push_cast at h; linarith
  have h1 : (0 : ℚ) ≤ -u + v - 10 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g1; push_cast at h; linarith
  have h2 : (0 : ℚ) ≤ N - u - 2 * v - 1 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g2; push_cast at h; linarith
  have h3 : (0 : ℚ) ≤ N - 301 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g3; push_cast at h; linarith
  have h4 : (0 : ℚ) ≤ u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g4; push_cast at h; linarith
  have h5 : (0 : ℚ) ≤ v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g5; push_cast at h; linarith
  have h6 : (0 : ℚ) ≤ -3 * u + 2 * v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g6; push_cast at h; linarith
  have h7 : (0 : ℚ) ≤ 2 * u - v - 13 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g7; push_cast at h; linarith
  have h8 : (0 : ℚ) ≤ N - 4 * u - 81 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g8; push_cast at h; linarith
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold kB1c8; linarith [mul_nonneg (h1) h8, mul_nonneg (h4) h6, mul_nonneg (h5) h8, mul_nonneg (mul_nonneg (h0) h3) h5, mul_nonneg (mul_nonneg (h1) h2) h5, mul_nonneg (mul_nonneg (h1) h4) h5, mul_nonneg (mul_nonneg (h2) h4) h6, mul_nonneg (mul_nonneg (h2) h5) h5, mul_nonneg (mul_nonneg (h4) h4) h6, mul_nonneg (mul_nonneg (h4) h5) h6, mul_nonneg (mul_nonneg (h5) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h1) h5) h7) h8, mul_nonneg (mul_nonneg (mul_nonneg (h4) h5) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h5) h5) h7) h8, mul_nonneg (mul_nonneg (mul_nonneg (h5) h6) h7) h8]
  · unfold kB1b8; linarith [mul_nonneg (h1) h2, mul_nonneg (h2) h5, mul_nonneg (h2) h6, mul_nonneg (h4) h5, mul_nonneg (h5) h8, mul_nonneg (mul_nonneg (h0) h3) h7, mul_nonneg (mul_nonneg (h0) h7) h8, mul_nonneg (mul_nonneg (h1) h2) h7, mul_nonneg (mul_nonneg (h2) h5) h7, mul_nonneg (mul_nonneg (h4) h5) h7]
  · unfold kB1r8; linarith [mul_nonneg (h0) h5, mul_nonneg (h1) h2, mul_nonneg (h1) h7, mul_nonneg (h2) h5, mul_nonneg (h2) h6, mul_nonneg (h3) h4, mul_nonneg (h3) h5, mul_nonneg (h5) h7, mul_nonneg (mul_nonneg (h4) h5) h7, mul_nonneg (mul_nonneg (h5) h7) h8]
  · unfold kB1a8; linarith [mul_nonneg (h3) h5, mul_nonneg (mul_nonneg (h0) h5) h5, mul_nonneg (mul_nonneg (h1) h2) h5, mul_nonneg (mul_nonneg (h2) h5) h5, mul_nonneg (mul_nonneg (h2) h5) h6, mul_nonneg (mul_nonneg (h3) h4) h5, mul_nonneg (mul_nonneg (h3) h5) h5, mul_nonneg (mul_nonneg (h5) h5) h7, mul_nonneg (mul_nonneg (h5) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h4) h5) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h5) h5) h7) h8]
  · unfold kB1c9; linarith [mul_nonneg (h1) h2, mul_nonneg (h2) h5, mul_nonneg (h2) h6, mul_nonneg (h3) h4, mul_nonneg (h3) h5, mul_nonneg (h5) h7, mul_nonneg (mul_nonneg (h0) h1) h4, mul_nonneg (mul_nonneg (h0) h4) h6, mul_nonneg (mul_nonneg (h1) h4) h4, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h2) h4) h6, mul_nonneg (mul_nonneg (h3) h4) h5, mul_nonneg (mul_nonneg (h4) h4) h6, mul_nonneg (mul_nonneg (h5) h7) h8, mul_nonneg (mul_nonneg (mul_nonneg (h2) h4) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h4) h4) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h4) h5) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h4) h5) h7) h8]
  · unfold kB1b9; linarith [mul_nonneg (h0) h2, mul_nonneg (h2) h4, mul_nonneg (h3) h4, mul_nonneg (h4) h4, mul_nonneg (h5) h8, mul_nonneg (h6) h6, mul_nonneg (h7) h7, mul_nonneg (mul_nonneg (h2) h4) h7, mul_nonneg (mul_nonneg (h4) h4) h7]
  · unfold kB1r9; linarith [mul_nonneg (h0) h2, mul_nonneg (h2) h4, mul_nonneg (h3) h4, mul_nonneg (h4) h4, mul_nonneg (h4) h5, mul_nonneg (mul_nonneg (h0) h7) h8, mul_nonneg (mul_nonneg (h2) h4) h7, mul_nonneg (mul_nonneg (h4) h5) h7, mul_nonneg (mul_nonneg (h4) h7) h8]
  · unfold kB1a9; linarith [mul_nonneg (h0) h3, mul_nonneg (h1) h8, mul_nonneg (mul_nonneg (h0) h0) h1, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h1) h4) h4, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h2) h4) h6, mul_nonneg (mul_nonneg (h3) h4) h5, mul_nonneg (mul_nonneg (h4) h4) h5, mul_nonneg (mul_nonneg (h5) h5) h8, mul_nonneg (mul_nonneg (mul_nonneg (h0) h2) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h0) h5) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h2) h4) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h3) h4) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h4) h4) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h4) h5) h5) h7]

theorem leaf_L2c {N u v : ℕ} (g0 : 4 ≤ u) (g1 : u + 10 ≤ v) (g2 : u + 2 * v + 1 ≤ N) (g3 : 301 ≤ N) (g4 : 0 ≤ u) (g5 : 0 ≤ v) (g6 : 3 * u ≤ 2 * v) (g7 : v + 13 ≤ 2 * u) (g8 : u + 2 * v + 82 ≤ N) :
    KeyB1 N u v := by
  have h0 : (0 : ℚ) ≤ u - 4 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g0; push_cast at h; linarith
  have h1 : (0 : ℚ) ≤ -u + v - 10 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g1; push_cast at h; linarith
  have h2 : (0 : ℚ) ≤ N - u - 2 * v - 1 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g2; push_cast at h; linarith
  have h3 : (0 : ℚ) ≤ N - 301 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g3; push_cast at h; linarith
  have h4 : (0 : ℚ) ≤ u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g4; push_cast at h; linarith
  have h5 : (0 : ℚ) ≤ v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g5; push_cast at h; linarith
  have h6 : (0 : ℚ) ≤ -3 * u + 2 * v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g6; push_cast at h; linarith
  have h7 : (0 : ℚ) ≤ 2 * u - v - 13 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g7; push_cast at h; linarith
  have h8 : (0 : ℚ) ≤ N - u - 2 * v - 82 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g8; push_cast at h; linarith
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold kB1c8; linarith [mul_nonneg (h7) h8, mul_nonneg (mul_nonneg (h0) h3) h5, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h1) h2) h5, mul_nonneg (mul_nonneg (h1) h3) h4, mul_nonneg (mul_nonneg (h1) h4) h4, mul_nonneg (mul_nonneg (h1) h4) h5, mul_nonneg (mul_nonneg (h2) h4) h6, mul_nonneg (mul_nonneg (h2) h5) h5, mul_nonneg (mul_nonneg (h2) h5) h6, mul_nonneg (mul_nonneg (h4) h5) h6, mul_nonneg (mul_nonneg (h5) h5) h8, mul_nonneg (mul_nonneg (h5) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h0) h5) h7) h8, mul_nonneg (mul_nonneg (mul_nonneg (h2) h5) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h3) h5) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h5) h6) h6) h7]
  · unfold kB1b8; linarith [mul_nonneg (h1) h2, mul_nonneg (h1) h4, mul_nonneg (h2) h5, mul_nonneg (h2) h6, mul_nonneg (h3) h5, mul_nonneg (h3) h6, mul_nonneg (mul_nonneg (h2) h5) h7, mul_nonneg (mul_nonneg (h4) h5) h7, mul_nonneg (mul_nonneg (h5) h7) h8]
  · unfold kB1r8; linarith [mul_nonneg (h0) h5, mul_nonneg (h1) h2, mul_nonneg (h1) h7, mul_nonneg (h2) h5, mul_nonneg (h2) h6, mul_nonneg (h3) h4, mul_nonneg (h5) h7, mul_nonneg (h5) h8, mul_nonneg (mul_nonneg (h2) h5) h7, mul_nonneg (mul_nonneg (h3) h5) h7, mul_nonneg (mul_nonneg (h5) h6) h7]
  · unfold kB1a8; linarith [mul_nonneg (h3) h5, mul_nonneg (mul_nonneg (h1) h2) h5, mul_nonneg (mul_nonneg (h1) h5) h7, mul_nonneg (mul_nonneg (h2) h5) h5, mul_nonneg (mul_nonneg (h2) h5) h6, mul_nonneg (mul_nonneg (h3) h4) h5, mul_nonneg (mul_nonneg (h4) h5) h5, mul_nonneg (mul_nonneg (h5) h5) h7, mul_nonneg (mul_nonneg (h5) h5) h8, mul_nonneg (mul_nonneg (mul_nonneg (h3) h5) h5) h7]
  · unfold kB1c9; linarith [mul_nonneg (h1) h7, mul_nonneg (h5) h7, mul_nonneg (h6) h8, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h0) h5) h8, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h3) h6) h7, mul_nonneg (mul_nonneg (h4) h4) h6, mul_nonneg (mul_nonneg (mul_nonneg (h1) h2) h4) h7, mul_nonneg (mul_nonneg (mul_nonneg (h1) h4) h7) h8, mul_nonneg (mul_nonneg (mul_nonneg (h2) h4) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h3) h4) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h4) h4) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h4) h5) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h4) h5) h7) h8]
  · unfold kB1b9; linarith [mul_nonneg (h0) h2, mul_nonneg (h0) h8, mul_nonneg (h2) h4, mul_nonneg (h3) h5, mul_nonneg (h6) h6, mul_nonneg (mul_nonneg (h0) h2) h7, mul_nonneg (mul_nonneg (h2) h4) h7, mul_nonneg (mul_nonneg (h3) h4) h7, mul_nonneg (mul_nonneg (h4) h4) h7, mul_nonneg (mul_nonneg (h4) h7) h7]
  · unfold kB1r9; linarith [mul_nonneg (h0) h2, mul_nonneg (h2) h4, mul_nonneg (h3) h4, mul_nonneg (h3) h5, mul_nonneg (h4) h5, mul_nonneg (mul_nonneg (h0) h1) h7, mul_nonneg (mul_nonneg (h0) h2) h7, mul_nonneg (mul_nonneg (h1) h4) h7, mul_nonneg (mul_nonneg (h2) h4) h7, mul_nonneg (mul_nonneg (h3) h4) h7, mul_nonneg (mul_nonneg (h4) h5) h7]
  · unfold kB1a9; linarith [mul_nonneg (h0) h2, mul_nonneg (h0) h8, mul_nonneg (h2) h4, mul_nonneg (h4) h8, mul_nonneg (h6) h7, mul_nonneg (mul_nonneg (h0) h0) h5, mul_nonneg (mul_nonneg (h0) h1) h2, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h1) h4) h7, mul_nonneg (mul_nonneg (h1) h7) h7, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h4) h4) h5, mul_nonneg (mul_nonneg (h4) h5) h7, mul_nonneg (mul_nonneg (h4) h5) h8, mul_nonneg (mul_nonneg (mul_nonneg (h0) h2) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h0) h3) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h3) h4) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h4) h4) h5) h7, mul_nonneg (mul_nonneg (mul_nonneg (h4) h5) h5) h7]

theorem leaf_L4 {N u v : ℕ} (g0 : 4 ≤ u) (g1 : u + 10 ≤ v) (g2 : u + 2 * v + 1 ≤ N) (g3 : 301 ≤ N) (g4 : 0 ≤ u) (g5 : 0 ≤ v) (g6 : 2 * u ≤ v + 12) (g7 : v ≤ 2 * u + 15) (g8 : 8 * u + 321 ≤ N) :
    DPolys N u v := by
  have h0 : (0 : ℚ) ≤ u - 4 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g0; push_cast at h; linarith
  have h1 : (0 : ℚ) ≤ -u + v - 10 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g1; push_cast at h; linarith
  have h2 : (0 : ℚ) ≤ N - u - 2 * v - 1 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g2; push_cast at h; linarith
  have h3 : (0 : ℚ) ≤ N - 301 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g3; push_cast at h; linarith
  have h4 : (0 : ℚ) ≤ u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g4; push_cast at h; linarith
  have h5 : (0 : ℚ) ≤ v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g5; push_cast at h; linarith
  have h6 : (0 : ℚ) ≤ -2 * u + v + 12 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g6; push_cast at h; linarith
  have h7 : (0 : ℚ) ≤ 2 * u - v + 15 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g7; push_cast at h; linarith
  have h8 : (0 : ℚ) ≤ N - 8 * u - 321 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g8; push_cast at h; linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold dP1; linarith [mul_nonneg (h0) h1, mul_nonneg (h0) h6, mul_nonneg (h1) h4, mul_nonneg (h4) h5, mul_nonneg (h4) h6, mul_nonneg (mul_nonneg (h0) h0) h8, mul_nonneg (mul_nonneg (h0) h1) h8, mul_nonneg (mul_nonneg (h0) h3) h6, mul_nonneg (mul_nonneg (h1) h4) h8, mul_nonneg (mul_nonneg (h3) h4) h6, mul_nonneg (mul_nonneg (h4) h4) h6]
  · unfold dP2; linarith [mul_nonneg (mul_nonneg (h0) h1) h2, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h0) h2) h6, mul_nonneg (h0) h3, mul_nonneg (mul_nonneg (h0) h3) h5, mul_nonneg (h0) h4, mul_nonneg (mul_nonneg (h0) h4) h6, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (h3) h4, mul_nonneg (mul_nonneg (h3) h4) h4, mul_nonneg (h4) h4, mul_nonneg (mul_nonneg (h4) h6) h7, mul_nonneg (h6) h7]
  · unfold dP3; linarith []

theorem leaf_L5 {N u v : ℕ} (g0 : 4 ≤ u) (g1 : u + 10 ≤ v) (g2 : u + 2 * v + 1 ≤ N) (g3 : 301 ≤ N) (g4 : 0 ≤ u) (g5 : 0 ≤ v) (g6 : 2 * u + 16 ≤ v) (g7 : v ≤ 3 * u) (g8 : N ≤ 10 * u) :
    KeyB4 N u v := by
  have h0 : (0 : ℚ) ≤ u - 4 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g0; push_cast at h; linarith
  have h1 : (0 : ℚ) ≤ -u + v - 10 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g1; push_cast at h; linarith
  have h2 : (0 : ℚ) ≤ N - u - 2 * v - 1 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g2; push_cast at h; linarith
  have h3 : (0 : ℚ) ≤ N - 301 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g3; push_cast at h; linarith
  have h4 : (0 : ℚ) ≤ u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g4; push_cast at h; linarith
  have h5 : (0 : ℚ) ≤ v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g5; push_cast at h; linarith
  have h6 : (0 : ℚ) ≤ -2 * u + v - 16 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g6; push_cast at h; linarith
  have h7 : (0 : ℚ) ≤ 3 * u - v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g7; push_cast at h; linarith
  have h8 : (0 : ℚ) ≤ -N + 10 * u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g8; push_cast at h; linarith
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold kB4c8; linarith [mul_nonneg (mul_nonneg (h0) h0) h2, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (mul_nonneg (h0) h2) h5) h6, mul_nonneg (mul_nonneg (h0) h3) h5, mul_nonneg (mul_nonneg (mul_nonneg (h0) h3) h5) h6, mul_nonneg (h2) h3, mul_nonneg (mul_nonneg (h2) h4) h8, mul_nonneg (h2) h8, mul_nonneg (mul_nonneg (h3) h3) h3, mul_nonneg (h3) h4, mul_nonneg (mul_nonneg (mul_nonneg (h3) h5) h6) h7, mul_nonneg (mul_nonneg (h3) h6) h7, mul_nonneg (h3) h7, mul_nonneg (mul_nonneg (mul_nonneg (h4) h5) h6) h7, mul_nonneg (mul_nonneg (h5) h5) h7, mul_nonneg (mul_nonneg (h5) h6) h7, mul_nonneg (mul_nonneg (h5) h6) h8, mul_nonneg (h5) h7, mul_nonneg (mul_nonneg (h6) h6) h8, mul_nonneg (h6) h7, mul_nonneg (h6) h8]
  · unfold kB4b8; linarith [mul_nonneg (mul_nonneg (h0) h1) h6, mul_nonneg (h0) h2, mul_nonneg (mul_nonneg (h0) h2) h2, mul_nonneg (mul_nonneg (mul_nonneg (h0) h3) h3) h8, mul_nonneg (mul_nonneg (h0) h5) h6, mul_nonneg (mul_nonneg (mul_nonneg (h2) h3) h3) h6, mul_nonneg (h2) h4, mul_nonneg (h2) h5, mul_nonneg (mul_nonneg (h2) h5) h6, mul_nonneg (mul_nonneg (h2) h6) h6, mul_nonneg (mul_nonneg (mul_nonneg (h3) h3) h3) h3, mul_nonneg (mul_nonneg (mul_nonneg (h3) h3) h3) h7, mul_nonneg (h3) h4, mul_nonneg (mul_nonneg (h3) h4) h6, mul_nonneg (h3) h5, mul_nonneg (mul_nonneg (h3) h5) h6, mul_nonneg (h4) h4, mul_nonneg (mul_nonneg (h5) h6) h7]
  · unfold kB4r8; linarith [mul_nonneg (h0) h2, mul_nonneg (h1) h5, mul_nonneg (h2) h4, mul_nonneg (h2) h5, mul_nonneg (mul_nonneg (h2) h5) h6, mul_nonneg (h3) h4, mul_nonneg (h3) h5, mul_nonneg (mul_nonneg (h3) h5) h6, mul_nonneg (h3) h6, mul_nonneg (mul_nonneg (h5) h5) h6, mul_nonneg (h5) h6, mul_nonneg (mul_nonneg (h5) h6) h6, mul_nonneg (h6) h6, mul_nonneg (h7) h8]
  · unfold kB4a8; linarith [mul_nonneg (h0) h2, mul_nonneg (h1) h5, mul_nonneg (h2) h4, mul_nonneg (h6) h6, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h1) h1) h5, mul_nonneg (mul_nonneg (h1) h5) h5, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h2) h5) h5, mul_nonneg (mul_nonneg (h3) h5) h5, mul_nonneg (mul_nonneg (h5) h5) h6, mul_nonneg (mul_nonneg (mul_nonneg (h3) h5) h5) h6]
  · unfold kB4c9; linarith [mul_nonneg (h3) h7, mul_nonneg (h4) h7, mul_nonneg (h5) h7, mul_nonneg (mul_nonneg (h0) h0) h2, mul_nonneg (mul_nonneg (h0) h0) h3, mul_nonneg (mul_nonneg (h0) h2) h4, mul_nonneg (mul_nonneg (h0) h3) h4, mul_nonneg (mul_nonneg (h2) h4) h4, mul_nonneg (mul_nonneg (h3) h4) h4, mul_nonneg (mul_nonneg (h3) h5) h7, mul_nonneg (mul_nonneg (h4) h5) h7, mul_nonneg (mul_nonneg (h4) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h0) h0) h0) h6, mul_nonneg (mul_nonneg (mul_nonneg (h0) h0) h2) h6, mul_nonneg (mul_nonneg (mul_nonneg (h0) h0) h3) h6, mul_nonneg (mul_nonneg (mul_nonneg (h3) h4) h6) h7, mul_nonneg (mul_nonneg (mul_nonneg (h4) h4) h6) h7]
  · unfold kB4b9; linarith [mul_nonneg (h0) h2, mul_nonneg (h0) h3, mul_nonneg (h2) h4, mul_nonneg (h3) h4, mul_nonneg (h5) h7, mul_nonneg (h6) h7, mul_nonneg (mul_nonneg (h0) h0) h6, mul_nonneg (mul_nonneg (h0) h2) h6, mul_nonneg (mul_nonneg (h0) h3) h6, mul_nonneg (mul_nonneg (h2) h4) h6, mul_nonneg (mul_nonneg (h4) h6) h7]
  · unfold kB4r9; linarith [mul_nonneg (h0) h2, mul_nonneg (h1) h3, mul_nonneg (h1) h4, mul_nonneg (h3) h5, mul_nonneg (h5) h5, mul_nonneg (mul_nonneg (h0) h1) h6, mul_nonneg (mul_nonneg (h0) h2) h6, mul_nonneg (mul_nonneg (h0) h5) h6, mul_nonneg (mul_nonneg (h2) h4) h6, mul_nonneg (mul_nonneg (h4) h5) h6]
  · unfold kB4a9; linarith [mul_nonneg (h0) h6, mul_nonneg (h3) h6, mul_nonneg (mul_nonneg (h0) h1) h5, mul_nonneg (mul_nonneg (h0) h1) h6, mul_nonneg (mul_nonneg (h0) h2) h4, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h0) h5) h6, mul_nonneg (mul_nonneg (h1) h4) h5, mul_nonneg (mul_nonneg (h2) h4) h4, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h4) h5) h6, mul_nonneg (mul_nonneg (mul_nonneg (h0) h3) h5) h6, mul_nonneg (mul_nonneg (mul_nonneg (h3) h4) h5) h6]

theorem leaf_L6 {N u v : ℕ} (g0 : 4 ≤ u) (g1 : u + 10 ≤ v) (g2 : u + 2 * v + 1 ≤ N) (g3 : 301 ≤ N) (g4 : 0 ≤ u) (g5 : 0 ≤ v) (g6 : 2 * u + 16 ≤ v) (g7 : v ≤ 3 * u) (g8 : 10 * u ≤ N) :
    DPolys N u v := by
  have h0 : (0 : ℚ) ≤ u - 4 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g0; push_cast at h; linarith
  have h1 : (0 : ℚ) ≤ -u + v - 10 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g1; push_cast at h; linarith
  have h2 : (0 : ℚ) ≤ N - u - 2 * v - 1 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g2; push_cast at h; linarith
  have h3 : (0 : ℚ) ≤ N - 301 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g3; push_cast at h; linarith
  have h4 : (0 : ℚ) ≤ u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g4; push_cast at h; linarith
  have h5 : (0 : ℚ) ≤ v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g5; push_cast at h; linarith
  have h6 : (0 : ℚ) ≤ -2 * u + v - 16 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g6; push_cast at h; linarith
  have h7 : (0 : ℚ) ≤ 3 * u - v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g7; push_cast at h; linarith
  have h8 : (0 : ℚ) ≤ N - 10 * u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g8; push_cast at h; linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold dP1; linarith [mul_nonneg (h0) h8, mul_nonneg (h3) h4, mul_nonneg (h3) h5, mul_nonneg (h4) h5, mul_nonneg (h4) h6, mul_nonneg (h4) h8, mul_nonneg (mul_nonneg (h0) h5) h8, mul_nonneg (mul_nonneg (h2) h4) h6, mul_nonneg (mul_nonneg (h3) h4) h6, mul_nonneg (mul_nonneg (h4) h4) h6, mul_nonneg (mul_nonneg (h4) h5) h5, mul_nonneg (mul_nonneg (h4) h5) h8]
  · unfold dP2; linarith [mul_nonneg (h0) h0, mul_nonneg (h2) h6, mul_nonneg (h5) h7, mul_nonneg (mul_nonneg (h0) h0) h3, mul_nonneg (mul_nonneg (h0) h0) h5, mul_nonneg (mul_nonneg (h0) h0) h8, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h3) h4) h4, mul_nonneg (mul_nonneg (h3) h4) h5, mul_nonneg (mul_nonneg (h4) h6) h7]
  · unfold dP3; linarith []

theorem leaf_L7a {N u v : ℕ} (g0 : 4 ≤ u) (g1 : u + 10 ≤ v) (g2 : u + 2 * v + 1 ≤ N) (g3 : 301 ≤ N) (g4 : 0 ≤ u) (g5 : 0 ≤ v) (g6 : 3 * u ≤ v) (g7 : 100 * v ≤ 36 * N) :
    DPolys N u v := by
  have h0 : (0 : ℚ) ≤ u - 4 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g0; push_cast at h; linarith
  have h1 : (0 : ℚ) ≤ -u + v - 10 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g1; push_cast at h; linarith
  have h2 : (0 : ℚ) ≤ N - u - 2 * v - 1 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g2; push_cast at h; linarith
  have h3 : (0 : ℚ) ≤ N - 301 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g3; push_cast at h; linarith
  have h4 : (0 : ℚ) ≤ u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g4; push_cast at h; linarith
  have h5 : (0 : ℚ) ≤ v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g5; push_cast at h; linarith
  have h6 : (0 : ℚ) ≤ -3 * u + v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g6; push_cast at h; linarith
  have h7 : (0 : ℚ) ≤ 36 * N - 100 * v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g7; push_cast at h; linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold dP1; linarith [mul_nonneg (h0) h2, mul_nonneg (h1) h4, mul_nonneg (h3) h5, mul_nonneg (h4) h6, mul_nonneg (h5) h7, mul_nonneg (mul_nonneg (h0) h1) h5, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h0) h5) h6, mul_nonneg (mul_nonneg (h0) h6) h7, mul_nonneg (mul_nonneg (h1) h4) h7, mul_nonneg (mul_nonneg (h3) h4) h5, mul_nonneg (mul_nonneg (h4) h5) h6]
  · unfold dP2; linarith [mul_nonneg (h1) h7, mul_nonneg (h3) h5, mul_nonneg (h5) h6, mul_nonneg (h6) h7, mul_nonneg (mul_nonneg (h0) h5) h5, mul_nonneg (mul_nonneg (h0) h5) h7, mul_nonneg (mul_nonneg (h3) h4) h5, mul_nonneg (mul_nonneg (h4) h5) h7]
  · unfold dP3; linarith []

theorem leaf_L7b {N u v : ℕ} (g0 : 4 ≤ u) (g1 : u + 10 ≤ v) (g2 : u + 2 * v + 1 ≤ N) (g3 : 301 ≤ N) (g4 : 0 ≤ u) (g5 : 0 ≤ v) (g6 : 3 * u ≤ v) (g7 : 36 * N ≤ 100 * v) (g8 : 10 * u ≤ N) :
    BPolys N u v := by
  have h0 : (0 : ℚ) ≤ u - 4 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g0; push_cast at h; linarith
  have h1 : (0 : ℚ) ≤ -u + v - 10 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g1; push_cast at h; linarith
  have h2 : (0 : ℚ) ≤ N - u - 2 * v - 1 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g2; push_cast at h; linarith
  have h3 : (0 : ℚ) ≤ N - 301 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g3; push_cast at h; linarith
  have h4 : (0 : ℚ) ≤ u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g4; push_cast at h; linarith
  have h5 : (0 : ℚ) ≤ v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g5; push_cast at h; linarith
  have h6 : (0 : ℚ) ≤ -3 * u + v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g6; push_cast at h; linarith
  have h7 : (0 : ℚ) ≤ -36 * N + 100 * v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g7; push_cast at h; linarith
  have h8 : (0 : ℚ) ≤ N - 10 * u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g8; push_cast at h; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold bP1; linarith [mul_nonneg (h0) h5, mul_nonneg (h4) h5, mul_nonneg (h4) h7]
  · unfold bP2; linarith [mul_nonneg (h0) h1, mul_nonneg (h0) h2, mul_nonneg (h1) h4, mul_nonneg (h2) h4, mul_nonneg (h3) h4]
  · unfold bP3; linarith [mul_nonneg (h0) h8, mul_nonneg (h2) h3, mul_nonneg (h3) h4, mul_nonneg (mul_nonneg (h0) h0) h7, mul_nonneg (mul_nonneg (h0) h1) h2, mul_nonneg (mul_nonneg (h0) h2) h2, mul_nonneg (mul_nonneg (h0) h4) h8, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h2) h2) h4, mul_nonneg (mul_nonneg (h2) h3) h4, mul_nonneg (mul_nonneg (h2) h4) h8, mul_nonneg (mul_nonneg (h3) h4) h4, mul_nonneg (mul_nonneg (h4) h4) h8]
  · unfold bP4; linarith [mul_nonneg (h0) h5, mul_nonneg (h4) h5]
  · unfold bP5; linarith []

theorem leaf_L7c {N u v : ℕ} (g0 : 4 ≤ u) (g1 : u + 10 ≤ v) (g2 : u + 2 * v + 1 ≤ N) (g3 : 301 ≤ N) (g4 : 0 ≤ u) (g5 : 0 ≤ v) (g6 : 3 * u ≤ v) (g7 : 36 * N ≤ 100 * v) (g8 : N ≤ 10 * u) :
    DPolys N u v := by
  have h0 : (0 : ℚ) ≤ u - 4 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g0; push_cast at h; linarith
  have h1 : (0 : ℚ) ≤ -u + v - 10 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g1; push_cast at h; linarith
  have h2 : (0 : ℚ) ≤ N - u - 2 * v - 1 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g2; push_cast at h; linarith
  have h3 : (0 : ℚ) ≤ N - 301 := by
    have h := (Nat.cast_le (α := ℚ)).mpr g3; push_cast at h; linarith
  have h4 : (0 : ℚ) ≤ u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g4; push_cast at h; linarith
  have h5 : (0 : ℚ) ≤ v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g5; push_cast at h; linarith
  have h6 : (0 : ℚ) ≤ -3 * u + v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g6; push_cast at h; linarith
  have h7 : (0 : ℚ) ≤ -36 * N + 100 * v := by
    have h := (Nat.cast_le (α := ℚ)).mpr g7; push_cast at h; linarith
  have h8 : (0 : ℚ) ≤ -N + 10 * u := by
    have h := (Nat.cast_le (α := ℚ)).mpr g8; push_cast at h; linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold dP1; linarith [mul_nonneg (h0) h2, mul_nonneg (h3) h4, mul_nonneg (h3) h5, mul_nonneg (h4) h6, mul_nonneg (h5) h5, mul_nonneg (mul_nonneg (h0) h1) h2, mul_nonneg (mul_nonneg (h0) h5) h6, mul_nonneg (mul_nonneg (h1) h2) h4, mul_nonneg (mul_nonneg (h1) h3) h4, mul_nonneg (mul_nonneg (h4) h4) h6, mul_nonneg (mul_nonneg (h4) h5) h6]
  · unfold dP2; linarith [mul_nonneg (h3) h5, mul_nonneg (h7) h8, mul_nonneg (mul_nonneg (h0) h2) h5, mul_nonneg (mul_nonneg (h0) h5) h8, mul_nonneg (mul_nonneg (h2) h4) h5, mul_nonneg (mul_nonneg (h2) h5) h5, mul_nonneg (mul_nonneg (h2) h5) h8, mul_nonneg (mul_nonneg (h3) h4) h5, mul_nonneg (mul_nonneg (h3) h5) h5, mul_nonneg (mul_nonneg (h3) h7) h7, mul_nonneg (mul_nonneg (h5) h5) h8, mul_nonneg (mul_nonneg (h5) h6) h7, mul_nonneg (mul_nonneg (h7) h7) h7]
  · unfold dP3; linarith []

/-! ## The bulk covering -/

/-- The thin sets left out of the bulk: the diagonal strip `u' ≤ u + 9`, the strip
`-12 ≤ u' - 2u ≤ 15` above `u ≈ N/8 - 40`, the cluster at `(N/4, 3N/8)` near the edge, `u ≤ 3`. -/
def Thin (N u v : ℕ) : Prop :=
  u ≤ 3 ∨ v ≤ u + 9 ∨ (2 * u ≤ v + 12 ∧ v ≤ 2 * u + 15 ∧ N ≤ 8 * u + 320) ∨
    (N ≤ 4 * u + 80 ∧ 4 * u ≤ N + 40 ∧ N ≤ u + 2 * v + 81)

/-- **The bulk**: outside the thin sets, every pair of the triangle lies in an old region (`D` or
`B`) or in one of the cells A, B4, B1 (`ParOK` of `Z` in orientation `(u', u)`). -/
theorem bulk {N u v : ℕ} (hN : 301 ≤ N) (ht : u + 2 * v + 1 ≤ N) (hth : ¬ Thin N u v) :
    ArithCover.Proven N u v ∨ ParOK (consZ N v u) := by
  unfold Thin at hth
  have hu : 4 ≤ u := by omega
  have hd : u + 10 ≤ v := by omega
  have hC' : 4 * u + 81 ≤ N ∨ N + 41 ≤ 4 * u ∨ u + 2 * v + 82 ≤ N := by omega
  have hD : ∀ {N u v : ℕ}, 4 ≤ u → u ≤ v → DPolys N u v → ArithCover.Proven N u v :=
    fun hu huv h => Or.inr (Or.inr (Or.inl (regionD_of_polys hu huv h)))
  have hB : ∀ {N u v : ℕ}, 4 ≤ u → BPolys N u v → ArithCover.Proven N u v :=
    fun hu h => Or.inl (regionB_of_polys hu h)
  by_cases h1 : 2 * v ≤ 3 * u
  · right
    apply parOK_of_keyA
    rcases hC' with hc | hc | hc
    · exact leaf_L1a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact leaf_L1b (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact leaf_L1c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  by_cases h2 : v + 13 ≤ 2 * u
  · right
    apply parOK_of_keyB1
    rcases hC' with hc | hc | hc
    · exact leaf_L2a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · omega
    · exact leaf_L2c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  by_cases h3 : v ≤ 2 * u + 15
  · left
    exact hD hu (by omega)
      (leaf_L4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  by_cases h4 : v ≤ 3 * u
  · by_cases h5 : N ≤ 10 * u
    · right
      apply parOK_of_keyB4
      exact leaf_L5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · left
      exact hD hu (by omega)
        (leaf_L6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  left
  by_cases h6 : 100 * v ≤ 36 * N
  · exact hD hu (by omega)
      (leaf_L7a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  by_cases h7 : 10 * u ≤ N
  · exact hB hu (leaf_L7b (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact hD hu (by omega)
      (leaf_L7c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))

/-- The line `u' = u + 1` (`d = 1`), `5 ≤ u`, `3u + 21 ≤ N`: the slice `a = c + 1` of `X(N, s, 0)`
in orientation `(u', u)` contains the parallelogram with sides `(1, 0)`, `(δ, 1)` at
`c₀ = (2u - 5)/6`, `s₀ = (N(2u + 1) + 6)/(6(u + 2))` and `s₁ = N(2u + 1)/(6(u - 1))` (`gend1.py`). -/
theorem d1_line {N u : ℕ} (hN : 301 ≤ N) (hu : 5 ≤ u) (h3 : 3 * u + 21 ≤ N) :
    RegionSL N u (u + 1) := by
  have huq : (5 : ℚ) ≤ u := by exact_mod_cast hu
  have f0 : (0 : ℚ) ≤ (u : ℚ) - 5 := by linarith
  have f1 : (0 : ℚ) ≤ (N : ℚ) - 3 * u - 21 := by
    have h := (Nat.cast_le (α := ℚ)).mpr h3; push_cast at h; linarith
  have f2 : (0 : ℚ) ≤ (N : ℚ) - 301 := by
    have h := (Nat.cast_le (α := ℚ)).mpr hN; push_cast at h; linarith
  have f3 : (0 : ℚ) ≤ (u : ℚ) := by positivity
  have f4 : (0 : ℚ) ≤ (N : ℚ) := by positivity
  have hS : (N : ℚ) / 2 ≤ (((N + 1) / 2 : ℕ) : ℚ) := by
    have h : N ≤ 2 * ((N + 1) / 2) := by omega
    have : (N : ℚ) ≤ 2 * (((N + 1) / 2 : ℕ) : ℚ) := by exact_mod_cast h
    linarith
  have hR : ((u - 2 : ℕ) : ℚ) = (u : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hd1 : (0 : ℚ) < 6*(u : ℚ) + 12 := by linarith
  have hd2 : (0 : ℚ) < 6*(u : ℚ) - 6 := by linarith
  have hne1 : (u : ℚ) - 1 ≠ 0 := by linarith
  have hne2 : (u : ℚ) + 2 ≠ 0 := by linarith
  have hne3 : 6*(u : ℚ) - 6 ≠ 0 := by linarith
  have hne4 : 6*(u : ℚ) + 12 ≠ 0 := by linarith
  refine Or.inr (Or.inl ⟨by omega, 1, 1, Or.inl ⟨((N : ℚ)*(2*(u : ℚ) + 1) + 6)/(6*(u : ℚ) + 12), (u : ℚ)/3 - 5/6, (N : ℚ)*(2*(u : ℚ) + 1)/(6*(u : ℚ) - 6) - (((N : ℚ)*(2*(u : ℚ) + 1) + 6)/(6*(u : ℚ) + 12)), 1, 0, 0, 1, by norm_num, ?_⟩⟩)
  simp only [sliceCons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Aff.eval, hR]
  push_cast
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · refine nonneg_of_cleared (D := 6*(u : ℚ) + 12) (P := 2*(N : ℚ)*(u : ℚ) + (N : ℚ) - 6*(u : ℚ) - 6) hd1 (by linarith [mul_nonneg (f0) f2, mul_nonneg (f3) f4]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) + 12) (P := 2*(N : ℚ)*(u : ℚ) + (N : ℚ) - 6*(u : ℚ)^2 - 24*(u : ℚ) - 18) hd1 (by linarith [mul_nonneg (f0) f1, mul_nonneg (f1) f3]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) - 6) (P := 2*(N : ℚ)*(u : ℚ) - 8*(N : ℚ)) hd2 (by linarith [mul_nonneg (f0) f4, mul_nonneg (f3) f4]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) - 6) (P := 2*(N : ℚ)*(u : ℚ) - 8*(N : ℚ) - 6*(u : ℚ)^2 + 6) hd2 (by linarith [mul_nonneg (f0) f1]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6) (P := 0) (by norm_num) (by linarith []) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6) (P := 6*(u : ℚ) + 12) (by norm_num) (by linarith []) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) - 6) (P := 9*(N : ℚ) - 6*(u : ℚ) + 6) hd2 (by linarith []) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) - 6) (P := 9*(N : ℚ) + 6*(u : ℚ)^2 - 6) hd2 (by linarith [mul_nonneg (f3) f3]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) + 12) (P := 2*(N : ℚ)*(u : ℚ) - 8*(N : ℚ) - 12*(u : ℚ)) hd1 (by linarith [mul_nonneg (f0) f4, mul_nonneg (f2) f3, mul_nonneg (f3) f4]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) + 12) (P := 2*(N : ℚ)*(u : ℚ) - 8*(N : ℚ) - 6*(u : ℚ)^2 - 12*(u : ℚ) + 24) hd1 (by linarith [mul_nonneg (f0) f1]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) - 6) (P := 2*(N : ℚ)*(u : ℚ) + (N : ℚ) - 6*(u : ℚ) + 6) hd2 (by linarith [mul_nonneg (f0) f2, mul_nonneg (f3) f4]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) - 6) (P := 2*(N : ℚ)*(u : ℚ) + (N : ℚ) - 6*(u : ℚ)^2 + 12*(u : ℚ) - 6) hd2 (by linarith [mul_nonneg (f0) f1]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) + 12) (P := 9*(N : ℚ) + 6*(u : ℚ) - 6) hd1 (by linarith []) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) + 12) (P := 9*(N : ℚ) + 6*(u : ℚ)^2 + 12*(u : ℚ) - 18) hd1 (by linarith [mul_nonneg (f3) f3]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 1) (P := 0) (by norm_num) (by linarith []) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 1) (P := (u : ℚ) - 1) (by norm_num) (by linarith []) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) + 12) (P := 2*(N : ℚ)*(u : ℚ) + (N : ℚ) - 12*(u : ℚ) - 18) hd1 (by linarith [mul_nonneg (f0) f2, mul_nonneg (f2) f3, mul_nonneg (f3) f4]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) + 12) (P := 2*(N : ℚ)*(u : ℚ) + (N : ℚ) - 6*(u : ℚ) - 6) hd1 (by linarith [mul_nonneg (f0) f2, mul_nonneg (f3) f4]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) - 6) (P := 2*(N : ℚ)*(u : ℚ) + (N : ℚ) - 12*(u : ℚ) + 12) hd2 (by linarith [mul_nonneg (f0) f2, mul_nonneg (f2) f3, mul_nonneg (f3) f4]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) - 6) (P := 2*(N : ℚ)*(u : ℚ) + (N : ℚ) - 6*(u : ℚ) + 6) hd2 (by linarith [mul_nonneg (f0) f2, mul_nonneg (f3) f4]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) + 12) (P := 2*(N : ℚ)*(u : ℚ) + (N : ℚ) - 6*(u : ℚ)^2 + 30) hd1 (by linarith [mul_nonneg (f0) f1]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) + 12) (P := 2*(N : ℚ)*(u : ℚ) + (N : ℚ) - 6*(u : ℚ)^2 + 6*(u : ℚ) + 42) hd1 (by linarith [mul_nonneg (f0) f1]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) - 6) (P := 2*(N : ℚ)*(u : ℚ) + (N : ℚ) - 6*(u : ℚ)^2 + 18*(u : ℚ) - 12) hd2 (by linarith [mul_nonneg (f0) f1]) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6*(u : ℚ) - 6) (P := 2*(N : ℚ)*(u : ℚ) + (N : ℚ) - 6*(u : ℚ)^2 + 24*(u : ℚ) - 18) hd2 (by linarith [mul_nonneg (f0) f1]) ?_
    field_simp; ring
  · have h := nonneg_of_cleared (E := (N : ℚ)/2 - ((N : ℚ)*(2*(u : ℚ) + 1) + 6)/(6*(u : ℚ) + 12)) (D := 6*(u : ℚ) + 12) (P := (N : ℚ)*(u : ℚ) + 5*(N : ℚ) - 6) hd1
      (by linarith [mul_nonneg (f3) f4]) (by field_simp; ring)
    have hS' := hS
    ring_nf at h hS' ⊢; linarith
  · have h := nonneg_of_cleared (E := (N : ℚ)/2 - 1 - ((N : ℚ)*(2*(u : ℚ) + 1) + 6)/(6*(u : ℚ) + 12)) (D := 6*(u : ℚ) + 12) (P := (N : ℚ)*(u : ℚ) + 5*(N : ℚ) - 6*(u : ℚ) - 18) hd1
      (by linarith [mul_nonneg (f3) f4]) (by field_simp; ring)
    have hS' := hS
    ring_nf at h hS' ⊢; linarith
  · have h := nonneg_of_cleared (E := -(N : ℚ)*(2*(u : ℚ) + 1)/(6*(u : ℚ) - 6) + (N : ℚ)/2) (D := 6*(u : ℚ) - 6) (P := (N : ℚ)*(u : ℚ) - 4*(N : ℚ)) hd2
      (by linarith [mul_nonneg (f0) f4, mul_nonneg (f3) f4]) (by field_simp; ring)
    have hS' := hS
    ring_nf at h hS' ⊢; linarith
  · have h := nonneg_of_cleared (E := -(N : ℚ)*(2*(u : ℚ) + 1)/(6*(u : ℚ) - 6) + (N : ℚ)/2 - 1) (D := 6*(u : ℚ) - 6) (P := (N : ℚ)*(u : ℚ) - 4*(N : ℚ) - 6*(u : ℚ) + 6) hd2
      (by linarith [mul_nonneg (f0) f2, mul_nonneg (f0) f4, mul_nonneg (f2) f3, mul_nonneg (f3) f4]) (by field_simp; ring)
    have hS' := hS
    ring_nf at h hS' ⊢; linarith
  · refine nonneg_of_cleared (D := 6) (P := 2*(u : ℚ) - 5) (by norm_num) (by linarith []) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6) (P := 2*(u : ℚ) - 5) (by norm_num) (by linarith []) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6) (P := 2*(u : ℚ) + 1) (by norm_num) (by linarith []) ?_
    field_simp; ring
  · refine nonneg_of_cleared (D := 6) (P := 2*(u : ℚ) + 1) (by norm_num) (by linarith []) ?_
    field_simp; ring

/-! ## Reduction of `CoverAll` to the thin sets -/

/-- The part of the thin sets that is not proven here: `Thin` minus the line `u' = u + 1`,
`5 ≤ u`, `3u + 21 ≤ N` (`d1_line`). -/
def ThinRest (N u v : ℕ) : Prop := Thin N u v ∧ ¬ (v = u + 1 ∧ 5 ≤ u ∧ 3 * u + 21 ≤ N)

/-- The remaining statement: every mixed-parity non-special pair of the triangle in `ThinRest`
lies in `Proven2`. -/
def ThinCover (N : ℕ) : Prop :=
  ∀ u u', 2 ≤ u → u ≤ u' → u + 2 * u' + 1 ≤ N → (u + (N + 1 - u')) % 2 = 1 →
    ¬ Special N u u' → ThinRest N u u' → Proven2 N u u'

/-- **`CoverAll` from the remaining thin sets** (the bulk is `bulk`, the line `d = 1` is
`d1_line`). -/
theorem coverAll_of_thinCover {N : ℕ} (hN : 300 < N) (hT : ThinCover N) : CoverAll N := by
  intro u v h1 h2 h3 h4 h5 h6 h7
  have hu' : u + 2 * (N + 1 - v) + 1 ≤ N := by omega
  by_cases hth : Thin N u (N + 1 - v)
  · by_cases hd : N + 1 - v = u + 1 ∧ 5 ≤ u ∧ 3 * u + 21 ≤ N
    · obtain ⟨he, h5', h21⟩ := hd
      rw [he]
      exact Or.inr (Or.inr (Or.inl (d1_line (by omega) h5' h21)))
    · exact hT u (N + 1 - v) h1 (by omega) hu' (by omega) h7 ⟨hth, hd⟩
  · rcases bulk (by omega) hu' hth with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl h))

/-- **Conjecture C (2-prefixes) for all `N`, modulo the remaining thin sets for `N > 300`.** -/
theorem conjectureC_of_thinCover (hT : ∀ N, 300 < N → ThinCover N) {N m₁ m₂ : ℕ}
    (h1 : 1 ≤ m₁ ∧ m₁ ≤ N) (h2 : 1 ≤ m₂ ∧ m₂ ≤ N) (h12 : m₁ ≠ m₂)
    (hval : SemiSymmetric N [m₁, m₂]) :
    Extends N [m₁, m₂] ↔ deadB N (min m₁ m₂) (max m₁ m₂) = false :=
  conjectureC_of_coverAll (fun N hN => coverAll_of_thinCover hN (hT N hN)) h1 h2 h12 hval

end CoverAll
end Folds
