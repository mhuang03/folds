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
