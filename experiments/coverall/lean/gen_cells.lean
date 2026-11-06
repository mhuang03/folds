import Folds.CoverAll

namespace Folds.CoverAll
open Folds.Residual

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

end Folds.CoverAll
