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

