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
