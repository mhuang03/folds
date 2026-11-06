import Folds.Live3q
import Folds.Live3s

/-!
# Live 3-prefixes: the reduction to `Live3s.Residual3T`

`experiments/live3s/PROOFS.txt`.  Combines Live3q (the base strips `N ≤ 50` and the reduction
`Live3q.extends3_iff_of_residual`) with Live3r / Live3s (near copies and the closed-form
families of `{1, 2, c}`): the 3-prefix liveness criterion for every `N ≠ 7` follows from
`Live3s.Residual3T N` for all `N > 50`.

`Live3r` restates the definitions of `Live3q` verbatim; the only non-definitional bridge is the
structural recursion `stepsB` (`stepsB_q_r`).
-/

namespace Folds
namespace Live3Final

open Live2 Live3p

theorem stepsB_q_r (N : Nat) : ∀ (ms xs : List Nat) (c2 : Nat),
    Live3q.stepsB N xs ms c2 = Live3r.stepsB N xs ms c2
  | [], xs, c2 => by simp only [Live3q.stepsB, Live3r.stepsB]; rfl
  | m :: ms, xs, c2 => by
    simp only [Live3q.stepsB, Live3r.stepsB, stepsB_q_r N ms (m :: xs) c2]; rfl

theorem covered3_r_q {N a b c : Nat} (h : Live3r.Covered3 N a b c) : Live3q.Covered3 N a b c := by
  rcases h with h | ⟨ms, c2, hl, h⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨ms, c2, hl, by rw [stepsB_q_r]; exact h⟩)
  · exact Or.inr (Or.inr h)

theorem covered3S_r_q {N a b c : Nat} (h : Live3r.Covered3S N a b c) :
    Live3q.Covered3S N a b c := by
  rcases h with h | h
  · exact Or.inl (covered3_r_q h)
  · exact Or.inr (covered3_r_q h)

theorem residual3_r_q {N : Nat} (h : Live3r.Residual3 N) : Live3q.Residual3 N :=
  fun a b c ha hab hbc hcN hv hd hc => h a b c ha hab hbc hcN hv hd (fun h' => hc (covered3S_r_q h'))

theorem base_le_50 : ∀ N, N ≤ 50 → N ≠ 7 → Live3r.Good3 N := Live3q.good3_le_50

/-- **3-prefix liveness for every `N ≠ 7`, conditional on `Residual3T`**: if every valid,
non-dead sorted triple of `[N]` (`N > 50`) that is not settled by the rules `Covered3T`
(Live3q's rules, the near copies of Live3r, the closed-form `{1, 2, c}` families of Live3s, for
the triple or its mirror image) is co-reachable, then a valid 3-prefix is live iff its set is
not `Dead3`. -/
theorem extends3_iff_of_residual3T (hres : ∀ N, 50 < N → Live3s.Residual3T N) {N x y z : Nat}
    (h7 : N ≠ 7) (hx : 1 ≤ x ∧ x ≤ N) (hy : 1 ≤ y ∧ y ≤ N) (hz : 1 ≤ z ∧ z ≤ N) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (hv : SemiSymmetric N [x, y, z]) :
    Extends N [x, y, z] ↔ ¬ Dead3 N {x, y, z} :=
  Live3q.extends3_iff_of_residual (fun N hN => residual3_r_q
    (Live3r.residual3_all_of_residual3R (M := 50) base_le_50
      (Live3s.residual3R_all_of_residual3T base_le_50 hres) N hN)) h7 hx hy hz hxy hxz hyz hv

end Live3Final
end Folds
