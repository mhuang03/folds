import Folds.WindowRule
import Folds.Blocks

/-!
# Live prefixes

`Extends N p` (from `WindowRule.lean`): the partial sequence `p` can be completed to a
semi-symmetric fold sequence.

* `extends_scale`: liveness transfers through the parity-class embedding
  `y ↦ scale c y = 2y - c` (parity blocks).
* `extends_single`: every panel is a live first step, `Extends N [m]` for `1 ≤ m ≤ N`.
-/

namespace Folds

/-- **Parity transfer.**  A live prefix of the class-`c` world `[1..(N+c)/2]` stays live
after scaling into `[1..N]`: complete it there, then append any semi-symmetric sequence of
the other class. -/
theorem extends_scale {N c : Nat} (hc : c ≤ 1) {p : List Nat}
    (hp : Extends ((N + c) / 2) p)
    (hτ : ∃ τ, IsFoldSeq ((N + (1 - c)) / 2) τ ∧ SemiSymmetric ((N + (1 - c)) / 2) τ) :
    Extends N (p.map (scale c)) := by
  obtain ⟨σ, hσf, hσs, hpre⟩ := hp
  obtain ⟨τ, hτf, hτs⟩ := hτ
  exact ⟨_, hσf.blocks hc hτf, (semiSymmetric_blocks_iff hc hσf hτf).2 ⟨hσs, hτs⟩,
    (hpre.map _).trans (List.prefix_append _ _)⟩

theorem semiSymmetric_one : SemiSymmetric 1 [1] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  obtain rfl : k = 0 := by omega
  simp [SemiStep, leftCount, rightCount, reach]

/-- **Every panel is a live first step.** -/
theorem extends_single (N : Nat) : ∀ m, 1 ≤ m → m ≤ N → Extends N [m] := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro m hm1 hmN
    by_cases hN : N = 1
    · subst hN
      obtain rfl : m = 1 := by omega
      exact ⟨[1], List.Perm.refl _, semiSymmetric_one, List.prefix_refl _⟩
    · have hc : m % 2 ≤ 1 := by omega
      have h1 := ih ((N + m % 2) / 2) (by omega) ((m + m % 2) / 2) (by omega) (by omega)
      obtain ⟨τ, hτf, hτs, -⟩ :=
        ih ((N + (1 - m % 2)) / 2) (by omega) 1 le_rfl (by omega)
      have := extends_scale hc h1 ⟨τ, hτf, hτs⟩
      have e : scale (m % 2) ((m + m % 2) / 2) = m := by unfold scale; omega
      simpa [e] using this

/-- Every strip has a semi-symmetric fold sequence. -/
theorem exists_semiSymmetric (N : Nat) : ∃ a, IsFoldSeq N a ∧ SemiSymmetric N a := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨[], List.Perm.refl _, fun k hk => absurd hk (by simp)⟩
  · obtain ⟨a, hf, hs, -⟩ := extends_single N 1 le_rfl hN
    exact ⟨a, hf, hs⟩

end Folds
