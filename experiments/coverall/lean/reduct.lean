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
