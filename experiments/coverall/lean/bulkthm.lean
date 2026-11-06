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
