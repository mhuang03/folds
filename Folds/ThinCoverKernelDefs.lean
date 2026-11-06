import Folds.ThinCoverBase

/-!
# Kernel checks for the cluster box at small `N`

`clCheck N` checks (by evaluation) that every mixed-parity pair of the cluster box at `N` (outside the
diagonal and the strip) passes the exact direct test `dirAny` in one of its two orientations; the
witness search in the orientation `(u, u')` starts at `a = 0.34 u - 8` (`dirFrom`).  `experiments/thincover/PROOFS.txt`.
-/

namespace Folds
namespace ThinCover

open Live8

/-- `dirAll N x y a` for some `a` in `[g, x + 1]`. -/
def dirFrom (N x y g : ℕ) : Bool := (List.range' g (x + 2 - g)).any fun a => dirAll N x y a

theorem dirAny_of_dirFrom {N x y g : ℕ} (hg : 1 ≤ g) (h : dirFrom N x y g = true) :
    dirAny N x y = true := by
  unfold dirFrom at h
  unfold dirAny
  rw [List.any_eq_true] at h ⊢
  obtain ⟨a, ha, h⟩ := h
  refine ⟨a, ?_, h⟩
  rw [List.mem_range'_1] at ha ⊢
  omega

/-- The cluster check at one `N`. -/
def clCheck (N : ℕ) : Bool :=
  (List.range' ((N - 80) / 4) 32).all fun u =>
    (List.range' ((N - 82 - u) / 2) 42).all fun v =>
      !(decide (N ≤ 4 * u + 80) && decide (4 * u ≤ N + 40) && decide (N ≤ u + 2 * v + 81) &&
          decide (u + 2 * v + 1 ≤ N) && decide (v + 13 ≤ 2 * u) && decide (u + 10 ≤ v)) ||
        dirFrom N u v (max 1 (34 * u / 100 - 8)) || dirFrom N v u 1

theorem clCheck_spec {N u v : ℕ} (h : clCheck N = true) (c1 : N ≤ 4 * u + 80) (c2 : 4 * u ≤ N + 40)
    (c3 : N ≤ u + 2 * v + 81) (ht : u + 2 * v + 1 ≤ N) (hns : v + 13 ≤ 2 * u) (hd : u + 10 ≤ v) :
    dirAny N u v = true ∨ dirAny N v u = true := by
  unfold clCheck at h
  rw [List.all_eq_true] at h
  have hu : u ∈ List.range' ((N - 80) / 4) 32 := by rw [List.mem_range'_1]; omega
  have h' := h u hu
  rw [List.all_eq_true] at h'
  have hv : v ∈ List.range' ((N - 82 - u) / 2) 42 := by rw [List.mem_range'_1]; omega
  have h'' := h' v hv
  simp only [c1, c2, c3, ht, hns, hd, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at h''
  rcases h'' with h1 | h1
  · exact Or.inl (dirAny_of_dirFrom (le_max_left _ _) h1)
  · exact Or.inr (dirAny_of_dirFrom le_rfl h1)

/-- The cluster check on `[a, a + n)`. -/
def clRange (a n : ℕ) : Bool := (List.range' a n).all clCheck

theorem clRange_spec {a n N : ℕ} (h : clRange a n = true) (h1 : a ≤ N) (h2 : N < a + n) :
    clCheck N = true := by
  unfold clRange at h
  rw [List.all_eq_true] at h
  exact h N (by rw [List.mem_range'_1]; omega)

end ThinCover
end Folds
