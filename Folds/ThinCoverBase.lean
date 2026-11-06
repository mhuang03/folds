import Folds.CoverAll

/-!
# `ThinCover`: generic certificate lemmas

`experiments/thincover/PROOFS.txt`.  Slices `a = p c + j` (`sliceCons`) and `c = p a + j`
(`sliceCons'`) with the lattice side `w₁ = (1, 0)`: the parallelogram with corners `(s₀, c₀)`,
`(s₀ + 1, c₀)`, `(s₁, c₀ + 1)`, `(s₁ + 1, c₀ + 1)` lies in the slice polygon as soon as the
lower bounds of `s` hold at `s₀` (resp. `s₁`), the upper ones at `s₀ + 1` (resp. `s₁ + 1`), and the
`c`-bound at `c₀` (15 conditions instead of 32).
-/

namespace Folds
namespace ThinCover

open Residual CoverAll

/-- **Slice certificate, side `(1, 0)`** (`a = p c + j`). -/
theorem sliceH {K L R α β smax amin p : ℕ} {j : ℤ} {Kq Lq Rq S c0 s0 s1 : ℚ} (hK : (K : ℚ) = Kq)
    (hL : (L : ℚ) = Lq) (hR : (R : ℚ) = Rq) (hS : S ≤ smax)
    (g1 : 0 ≤ -Lq * (s0 + 1) + (p : ℚ) * Kq * c0 + (j : ℚ) * Kq - α)
    (g1' : 0 ≤ -Lq * (s1 + 1) + (p : ℚ) * Kq * (c0 + 1) + (j : ℚ) * Kq - α)
    (g2 : 0 ≤ (Lq + 1) * s0 - (p : ℚ) * Kq * c0 + α - 1 - (j : ℚ) * Kq)
    (g2' : 0 ≤ (Lq + 1) * s1 - (p : ℚ) * Kq * (c0 + 1) + α - 1 - (j : ℚ) * Kq)
    (g3 : 0 ≤ -Rq * (s0 + 1) + Kq * c0 - β)
    (g3' : 0 ≤ -Rq * (s1 + 1) + Kq * (c0 + 1) - β)
    (g4 : 0 ≤ (Rq + 1) * s0 - Kq * c0 + β - 1)
    (g4' : 0 ≤ (Rq + 1) * s1 - Kq * (c0 + 1) + β - 1)
    (g5 : 0 ≤ s0 - 2) (g5' : 0 ≤ s1 - 2) (g6 : 0 ≤ s0 - Rq) (g6' : 0 ≤ s1 - Rq)
    (g7 : 0 ≤ S - s0 - 1) (g7' : 0 ≤ S - s1 - 1) (g8 : 0 ≤ (p : ℚ) * c0 + j - amin) :
    ParOK (sliceCons K L R α β smax amin p j) := by
  subst hK hL hR
  have hL : (0 : ℚ) ≤ L := by positivity
  have hR : (0 : ℚ) ≤ R := by positivity
  have hp : (0 : ℚ) ≤ p := by positivity
  refine ⟨s0, c0, s1 - s0, 1, 0, 0, 1, by norm_num, ?_⟩
  simp only [sliceCons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Aff.eval]
  push_cast
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> linarith

/-- **Slice certificate, side `(1, 0)`** (`c = p a + j`, variables `(s, a)`). -/
theorem sliceH' {K L R α β smax amin p : ℕ} {j : ℤ} {Kq Lq Rq S c0 s0 s1 : ℚ} (hK : (K : ℚ) = Kq)
    (hL : (L : ℚ) = Lq) (hR : (R : ℚ) = Rq) (hS : S ≤ smax)
    (g1 : 0 ≤ -Lq * (s0 + 1) + Kq * c0 - α)
    (g1' : 0 ≤ -Lq * (s1 + 1) + Kq * (c0 + 1) - α)
    (g2 : 0 ≤ (Lq + 1) * s0 - Kq * c0 + α - 1)
    (g2' : 0 ≤ (Lq + 1) * s1 - Kq * (c0 + 1) + α - 1)
    (g3 : 0 ≤ -Rq * (s0 + 1) + (p : ℚ) * Kq * c0 + (j : ℚ) * Kq - β)
    (g3' : 0 ≤ -Rq * (s1 + 1) + (p : ℚ) * Kq * (c0 + 1) + (j : ℚ) * Kq - β)
    (g4 : 0 ≤ (Rq + 1) * s0 - (p : ℚ) * Kq * c0 + β - 1 - (j : ℚ) * Kq)
    (g4' : 0 ≤ (Rq + 1) * s1 - (p : ℚ) * Kq * (c0 + 1) + β - 1 - (j : ℚ) * Kq)
    (g5 : 0 ≤ s0 - 2) (g5' : 0 ≤ s1 - 2) (g6 : 0 ≤ s0 - Rq) (g6' : 0 ≤ s1 - Rq)
    (g7 : 0 ≤ S - s0 - 1) (g7' : 0 ≤ S - s1 - 1) (g8 : 0 ≤ c0 - amin) :
    ParOK (sliceCons' K L R α β smax amin p j) := by
  subst hK hL hR
  have hL : (0 : ℚ) ≤ L := by positivity
  have hR : (0 : ℚ) ≤ R := by positivity
  have hK : (0 : ℚ) ≤ K := by positivity
  have hp : (0 : ℚ) ≤ p := by positivity
  refine ⟨s0, c0, s1 - s0, 1, 0, 0, 1, by norm_num, ?_⟩
  simp only [sliceCons', List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Aff.eval]
  push_cast
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> linarith

/-- `sliceCons` with rational parameters and `smax` replaced by `S`. -/
def sliceQ (K L R α β S amin : ℚ) (p : ℕ) (j : ℤ) : List Aff :=
  [⟨-L, (p : ℚ) * K, (j : ℚ) * K - α⟩, ⟨L + 1, -((p : ℚ) * K), α - 1 - j * K⟩,
    ⟨-R, K, -β⟩, ⟨R + 1, -K, β - 1⟩, ⟨1, 0, -2⟩, ⟨1, 0, -R⟩, ⟨-1, 0, S⟩, ⟨0, p, (j : ℚ) - amin⟩]

/-- `sliceCons'` with rational parameters and `smax` replaced by `S`. -/
def sliceQ' (K L R α β S amin : ℚ) (p : ℕ) (j : ℤ) : List Aff :=
  [⟨-L, K, -α⟩, ⟨L + 1, -K, α - 1⟩, ⟨-R, (p : ℚ) * K, (j : ℚ) * K - β⟩,
    ⟨R + 1, -((p : ℚ) * K), β - 1 - j * K⟩, ⟨1, 0, -2⟩, ⟨1, 0, -R⟩, ⟨-1, 0, S⟩, ⟨0, 1, -amin⟩]

/-- All four corners of a parallelogram in every constraint. -/
def Corners (cs : List Aff) (Pa Pc δ : ℚ) (p1 q1 p2 q2 : ℤ) : Prop :=
  ∀ f ∈ cs, 0 ≤ f.eval Pa Pc ∧ 0 ≤ f.eval (Pa + p1) (Pc + q1) ∧
      0 ≤ f.eval (Pa + (p2 + δ * p1)) (Pc + (q2 + δ * q1)) ∧
      0 ≤ f.eval (Pa + p1 + (p2 + δ * p1)) (Pc + q1 + (q2 + δ * q1))

/-- **Slice certificate, any side** (`a = p c + j`). -/
theorem sliceG {K L R α β smax amin p : ℕ} {j : ℤ} {Kq Lq Rq S : ℚ} (hK : (K : ℚ) = Kq)
    (hL : (L : ℚ) = Lq) (hR : (R : ℚ) = Rq) (hS : S ≤ smax) {Pa Pc δ : ℚ} {p1 q1 p2 q2 : ℤ}
    (hdet : p1 * q2 - p2 * q1 = 1) (h : Corners (sliceQ Kq Lq Rq α β S amin p j) Pa Pc δ p1 q1 p2 q2) :
    ParOK (sliceCons K L R α β smax amin p j) := by
  subst hK hL hR
  refine ⟨Pa, Pc, δ, p1, q1, p2, q2, hdet, ?_⟩
  simp only [Corners, sliceQ, sliceCons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Aff.eval] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, ⟨h7a, h7b, h7c, h7d⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, ⟨by linarith, by linarith, by linarith, by linarith⟩, h8⟩

/-- **Slice certificate, any side** (`c = p a + j`). -/
theorem sliceG' {K L R α β smax amin p : ℕ} {j : ℤ} {Kq Lq Rq S : ℚ} (hK : (K : ℚ) = Kq)
    (hL : (L : ℚ) = Lq) (hR : (R : ℚ) = Rq) (hS : S ≤ smax) {Pa Pc δ : ℚ} {p1 q1 p2 q2 : ℤ}
    (hdet : p1 * q2 - p2 * q1 = 1) (h : Corners (sliceQ' Kq Lq Rq α β S amin p j) Pa Pc δ p1 q1 p2 q2) :
    ParOK (sliceCons' K L R α β smax amin p j) := by
  subst hK hL hR
  refine ⟨Pa, Pc, δ, p1, q1, p2, q2, hdet, ?_⟩
  simp only [Corners, sliceQ', sliceCons', List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Aff.eval] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, ⟨h7a, h7b, h7c, h7d⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, ⟨by linarith, by linarith, by linarith, by linarith⟩, h8⟩

/-- `famCons` with rational parameters and `smax` replaced by `S`. -/
def famConsQ (K L R α β S amin : ℚ) : List Aff :=
  [(⟨K / L, 0, -α / L⟩ : Aff).gap ⟨K / (L + 1), 0, (1 - α) / (L + 1)⟩,
    (⟨K / L, 0, -α / L⟩ : Aff).gap ⟨0, K / (R + 1), (1 - β) / (R + 1)⟩,
    (⟨K / L, 0, -α / L⟩ : Aff).gap (affC R), (⟨K / L, 0, -α / L⟩ : Aff).gap (affC 2),
    (⟨0, K / R, -β / R⟩ : Aff).gap ⟨K / (L + 1), 0, (1 - α) / (L + 1)⟩,
    (⟨0, K / R, -β / R⟩ : Aff).gap ⟨0, K / (R + 1), (1 - β) / (R + 1)⟩,
    (⟨0, K / R, -β / R⟩ : Aff).gap (affC R), (⟨0, K / R, -β / R⟩ : Aff).gap (affC 2),
    (affC S).gap ⟨K / (L + 1), 0, (1 - α) / (L + 1)⟩, (affC S).gap ⟨0, K / (R + 1), (1 - β) / (R + 1)⟩,
    (affC S).gap (affC R), (affC S).gap (affC 2), ⟨1, 0, -amin⟩]

/-- **Parallelogram certificate in the witness polygon** (any side). -/
theorem pfG {K L R α β smax amin : ℕ} {Kq Lq Rq S : ℚ} (hK : (K : ℚ) = Kq)
    (hL : (L : ℚ) = Lq) (hR : (R : ℚ) = Rq) (hS : S ≤ smax) {Pa Pc δ : ℚ} {p1 q1 p2 q2 : ℤ}
    (hdet : p1 * q2 - p2 * q1 = 1)
    (h : Corners (famConsQ Kq Lq Rq α β S amin) Pa Pc δ p1 q1 p2 q2) :
    ParOK (famCons K L R α β smax amin) := by
  subst hK hL hR
  refine ⟨Pa, Pc, δ, p1, q1, p2, q2, hdet, ?_⟩
  simp only [Corners, famConsQ, famCons, affU1, affU2, affL1, affL2, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, ⟨h9a, h9b, h9c, h9d⟩, ⟨h10a, h10b, h10c, h10d⟩,
    ⟨h11a, h11b, h11c, h11d⟩, ⟨h12a, h12b, h12c, h12d⟩, h13⟩ := h
  simp only [Aff.gap, affC, Aff.eval] at h9a h9b h9c h9d h10a h10b h10c h10d h11a h11b h11c h11d h12a h12b h12c h12d
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_, ?_, ?_, h13⟩
  all_goals simp only [Aff.gap, affC, Aff.eval]
  all_goals exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- `famConsQ` with every constraint multiplied by its (positive) denominator: polynomial
coefficients. -/
def famConsC (K L R α β S amin : ℚ) : List Aff :=
  [⟨K, 0, -α * (L + 1) - (1 - α) * L - L * (L + 1)⟩,
    ⟨K * (R + 1), -(K * L), -α * (R + 1) - (1 - β) * L - L * (R + 1)⟩,
    ⟨K, 0, -α - (R + 1) * L⟩, ⟨K, 0, -α - 3 * L⟩,
    ⟨-(K * R), K * (L + 1), -β * (L + 1) - (1 - α) * R - R * (L + 1)⟩,
    ⟨0, K, -β * (R + 1) - (1 - β) * R - R * (R + 1)⟩,
    ⟨0, K, -β - (R + 1) * R⟩, ⟨0, K, -β - 3 * R⟩,
    ⟨-K, 0, (S - 1) * (L + 1) - (1 - α)⟩, ⟨0, -K, (S - 1) * (R + 1) - (1 - β)⟩,
    ⟨0, 0, S - R - 1⟩, ⟨0, 0, S - 3⟩, ⟨1, 0, -amin⟩]

theorem nonneg_of_mul {x k : ℚ} (hk : 0 < k) (h : 0 ≤ k * x) : 0 ≤ x := by
  by_contra hx
  push Not at hx
  have : k * x < 0 := mul_neg_of_pos_of_neg hk hx
  linarith

theorem corners_famConsQ {K L R α β S amin Pa Pc δ : ℚ} {p1 q1 p2 q2 : ℤ} (hL : 0 < L) (hR : 0 < R)
    (h : Corners (famConsC K L R α β S amin) Pa Pc δ p1 q1 p2 q2) :
    Corners (famConsQ K L R α β S amin) Pa Pc δ p1 q1 p2 q2 := by
  have hL1 : 0 < L + 1 := by linarith
  have hR1 : 0 < R + 1 := by linarith
  have hLne : L ≠ 0 := ne_of_gt hL
  have hRne : R ≠ 0 := ne_of_gt hR
  have hL1ne : L + 1 ≠ 0 := ne_of_gt hL1
  have hR1ne : R + 1 ≠ 0 := ne_of_gt hR1
  intro f hf
  simp only [famConsQ, List.mem_cons, List.not_mem_nil, or_false] at hf
  simp only [Corners, famConsC, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have T : ∀ (g c : Aff) (k : ℚ), 0 < k → (∀ a b : ℚ, k * g.eval a b = c.eval a b) →
      (0 ≤ c.eval Pa Pc ∧ 0 ≤ c.eval (Pa + p1) (Pc + q1) ∧
        0 ≤ c.eval (Pa + (p2 + δ * p1)) (Pc + (q2 + δ * q1)) ∧
        0 ≤ c.eval (Pa + p1 + (p2 + δ * p1)) (Pc + q1 + (q2 + δ * q1))) →
      (0 ≤ g.eval Pa Pc ∧ 0 ≤ g.eval (Pa + p1) (Pc + q1) ∧
        0 ≤ g.eval (Pa + (p2 + δ * p1)) (Pc + (q2 + δ * q1)) ∧
        0 ≤ g.eval (Pa + p1 + (p2 + δ * p1)) (Pc + q1 + (q2 + δ * q1))) := by
    intro g c k hk he ⟨c1, c2, c3, c4⟩
    exact ⟨nonneg_of_mul hk (by rw [he]; exact c1), nonneg_of_mul hk (by rw [he]; exact c2),
      nonneg_of_mul hk (by rw [he]; exact c3), nonneg_of_mul hk (by rw [he]; exact c4)⟩
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact T _ _ (L * (L + 1)) (by positivity) (fun a b => by
      simp only [Aff.gap, Aff.eval]; field_simp; ring) h1
  · exact T _ _ (L * (R + 1)) (by positivity) (fun a b => by
      simp only [Aff.gap, Aff.eval]; field_simp; ring) h2
  · exact T _ _ L hL (fun a b => by simp only [Aff.gap, affC, Aff.eval]; field_simp; ring) h3
  · exact T _ _ L hL (fun a b => by simp only [Aff.gap, affC, Aff.eval]; field_simp; ring) h4
  · exact T _ _ (R * (L + 1)) (by positivity) (fun a b => by
      simp only [Aff.gap, Aff.eval]; field_simp; ring) h5
  · exact T _ _ (R * (R + 1)) (by positivity) (fun a b => by
      simp only [Aff.gap, Aff.eval]; field_simp; ring) h6
  · exact T _ _ R hR (fun a b => by simp only [Aff.gap, affC, Aff.eval]; field_simp; ring) h7
  · exact T _ _ R hR (fun a b => by simp only [Aff.gap, affC, Aff.eval]; field_simp; ring) h8
  · exact T _ _ (L + 1) hL1 (fun a b => by simp only [Aff.gap, affC, Aff.eval]; field_simp; ring) h9
  · exact T _ _ (R + 1) hR1 (fun a b => by simp only [Aff.gap, affC, Aff.eval]; field_simp; ring) h10
  · exact T _ _ 1 one_pos (fun a b => by simp only [Aff.gap, affC, Aff.eval]; ring) h11
  · exact T _ _ 1 one_pos (fun a b => by simp only [Aff.gap, affC, Aff.eval]; ring) h12
  · exact T _ _ 1 one_pos (fun a b => by simp only [Aff.eval]; ring) h13

/-- **Parallelogram certificate in the witness polygon**, cleared form. -/
theorem pfC {K L R α β smax amin : ℕ} {Kq Lq Rq S : ℚ} (hK : (K : ℚ) = Kq)
    (hL : (L : ℚ) = Lq) (hR : (R : ℚ) = Rq) (hS : S ≤ smax) (hL0 : 0 < Lq) (hR0 : 0 < Rq)
    {Pa Pc δ : ℚ} {p1 q1 p2 q2 : ℤ} (hdet : p1 * q2 - p2 * q1 = 1)
    (h : Corners (famConsC Kq Lq Rq α β S amin) Pa Pc δ p1 q1 p2 q2) :
    ParOK (famCons K L R α β smax amin) :=
  pfG hK hL hR hS hdet (corners_famConsQ hL0 hR0 h)

end ThinCover
end Folds
