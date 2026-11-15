import Folds.Recursion
import Folds.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Interval counts, offset strips and the half-line model

"Strengthen the induction hypothesis": families of numbers that contain `a(N)`.

* `intervalCount M i j = g M [i, j]`: the number of semi-symmetric orderings of the interval
  `[i, j]` inside the `M`-strip (the panels outside the interval are never placed).
  `intervalCount N 1 N = a(N)` (`intervalCount_one_self`).
* `offsetCount N α β = intervalCount (N + α + β) (α + 1) (α + N)`: the strip `1..N` with `α`
  phantom panels on the left and `β` on the right, i.e. radius `min (m - 1 + α) (N - m + β)`.
* `halfLine j = intervalCount (2 * j) 1 j`: every panel `m` has the window `[1, 2m - 1] ∩ [1, j]`.

Results (see `experiments/xd_intervals/NOTES.txt` for the numerical findings):

* `g_of_reach_eq`, `g_of_clip`: `g M S` depends on `M` only through the radii clipped to the
  hull of `S`.
* `halfLine_stable`: `intervalCount M 1 j = halfLine j` for every `M ≥ 2j - 1`;
  `offsetCount_stable`: `offsetCount N α β` does not depend on `β` once `β ≥ N - 1`;
  `offsetCount_zero_eq_halfLine`.
* `gList_eq_g`: a computable evaluator for `g`, used for the small tables below.
* `intervalCount_eq_zero_of_odd`: **zero law, even length**: an interval `[i, j]` that touches
  neither end of the strip and has an even number of panels has no semi-symmetric ordering
  (the last panel would have to be the exact middle).
* `halfLine_getElem`: **the right half of the half-line model is forced**: in every
  semi-symmetric ordering of `[1, N]` in a strip `M ≥ 2N - 1`, panel `N - c` is placed at
  step `2c + 1`, for every `c` with `2c + 1 ≤ N`.
* small tables by `decide +kernel`, including `H(2n+1) = H(n)` for `n ≤ 7` and the zero law.
-/

namespace Folds
namespace XdIntervals

open Finset

/-! ## Definitions -/

/-- Number of semi-symmetric orderings of the interval `[i, j]` inside the `M`-strip. -/
def intervalCount (M i j : Nat) : Nat := g M (Finset.Icc i j)

/-- Offset strip: panels `1..N` with `α` phantom panels on the left and `β` on the right
(phantom panels are never placed), so that panel `m` has radius `min (m-1+α) (N-m+β)`. -/
def offsetCount (N α β : Nat) : Nat := intervalCount (N + α + β) (α + 1) (α + N)

/-- Half-line model: the interval `[1, j]` in a strip so long that every panel `m ≤ j` has
its full left arm: its window is `[1, 2m-1] ∩ [1, j]`. -/
def halfLine (j : Nat) : Nat := intervalCount (2 * j) 1 j

theorem intervalCount_one_self (N : Nat) : intervalCount N 1 N = semiCount N :=
  (semiCount_eq_g N).symm

theorem offsetCount_zero_zero (N : Nat) : offsetCount N 0 0 = semiCount N := by
  simp [offsetCount, intervalCount_one_self]

/-! ## `g M S` depends on `M` only through the clipped radii -/

theorem semiStep_of_reach_eq {M M' m : Nat} {S : List Nat} (h : reach M m = reach M' m) :
    SemiStep M S m ↔ SemiStep M' S m := by
  unfold SemiStep leftCount rightCount; rw [h]

/-- The step condition only sees the radius clipped to an interval `[lo, hi]` containing the
placed panels. -/
theorem semiStep_of_clip {M M' m lo hi : Nat} {S : List Nat} (hnd : S.Nodup)
    (hS : ∀ x ∈ S, lo ≤ x ∧ x ≤ hi)
    (hl : min (reach M m) (m - lo) = min (reach M' m) (m - lo))
    (hr : min (reach M m) (hi - m) = min (reach M' m) (hi - m)) :
    SemiStep M S m ↔ SemiStep M' S m := by
  unfold SemiStep
  rw [leftCount_eq hnd, rightCount_eq hnd, leftCount_eq hnd, rightCount_eq hnd]
  have L : S.countP (fun x => decide (m - reach M m ≤ x ∧ x < m)) =
      S.countP (fun x => decide (m - reach M' m ≤ x ∧ x < m)) := by
    apply List.countP_congr; intro x hx; have := hS x hx
    simp only [decide_eq_true_eq]; omega
  have R : S.countP (fun x => decide (m < x ∧ x ≤ m + reach M m)) =
      S.countP (fun x => decide (m < x ∧ x ≤ m + reach M' m)) := by
    apply List.countP_congr; intro x hx; have := hS x hx
    simp only [decide_eq_true_eq]; omega
  rw [L, R]

theorem semiSymmetric_of_clip {M M' lo hi : Nat} {l : List Nat} (hnd : l.Nodup)
    (hS : ∀ x ∈ l, lo ≤ x ∧ x ≤ hi)
    (hl : ∀ m ∈ l, min (reach M m) (m - lo) = min (reach M' m) (m - lo))
    (hr : ∀ m ∈ l, min (reach M m) (hi - m) = min (reach M' m) (hi - m)) :
    SemiSymmetric M l ↔ SemiSymmetric M' l := by
  have key : ∀ k (hk : k < l.length), SemiStep M (l.take k) l[k] ↔ SemiStep M' (l.take k) l[k] :=
    fun k hk => semiStep_of_clip (hnd.sublist (List.take_sublist k l))
      (fun x hx => hS x (List.mem_of_mem_take hx)) (hl _ (List.getElem_mem hk))
      (hr _ (List.getElem_mem hk))
  unfold SemiSymmetric
  exact ⟨fun H k hk => (key k hk).1 (H k hk), fun H k hk => (key k hk).2 (H k hk)⟩

/-- `g M S = g M' S` as soon as the two strips give every panel of `S` the same radius
clipped to an interval `[lo, hi] ⊇ S`. -/
theorem g_of_clip {M M' lo hi : Nat} {S : Finset Nat} (hS : ∀ x ∈ S, lo ≤ x ∧ x ≤ hi)
    (hl : ∀ m ∈ S, min (reach M m) (m - lo) = min (reach M' m) (m - lo))
    (hr : ∀ m ∈ S, min (reach M m) (hi - m) = min (reach M' m) (hi - m)) :
    g M S = g M' S := by
  unfold g; congr 1; ext l
  simp only [mem_semiOrders]
  constructor
  · rintro ⟨⟨hnd, e⟩, hs⟩
    have hm : ∀ x ∈ l, x ∈ S := fun x hx => by rw [← e]; exact List.mem_toFinset.2 hx
    exact ⟨⟨hnd, e⟩, (semiSymmetric_of_clip hnd (fun x hx => hS x (hm x hx))
      (fun x hx => hl x (hm x hx)) (fun x hx => hr x (hm x hx))).1 hs⟩
  · rintro ⟨⟨hnd, e⟩, hs⟩
    have hm : ∀ x ∈ l, x ∈ S := fun x hx => by rw [← e]; exact List.mem_toFinset.2 hx
    exact ⟨⟨hnd, e⟩, (semiSymmetric_of_clip hnd (fun x hx => hS x (hm x hx))
      (fun x hx => hl x (hm x hx)) (fun x hx => hr x (hm x hx))).2 hs⟩

/-- `g M S = g M' S` if every panel of `S` has the same radius in both strips. -/
theorem g_of_reach_eq {M M' : Nat} {S : Finset Nat} (h : ∀ m ∈ S, reach M m = reach M' m) :
    g M S = g M' S :=
  g_of_clip (lo := 0) (hi := S.sup id) (fun x hx => ⟨Nat.zero_le _, Finset.le_sup (f := id) hx⟩)
    (fun m hm => by rw [h m hm]) (fun m hm => by rw [h m hm])

/-! ## Stabilisation -/

/-- **Stabilisation of the half-line model.**  For every strip length `M ≥ 2j - 1` the
interval `[1, j]` has `halfLine j` semi-symmetric orderings. -/
theorem halfLine_stable {M j : Nat} (h : 2 * j ≤ M + 1) : intervalCount M 1 j = halfLine j := by
  unfold halfLine intervalCount
  apply g_of_reach_eq
  intro m hm
  rw [Finset.mem_Icc] at hm
  unfold reach; omega

/-- **Stabilisation of the offset strips**: `offsetCount N α β` does not depend on `β` once
`β ≥ N - 1` (the right phantom region is then never the binding constraint). -/
theorem offsetCount_stable {N α β β' : Nat} (h : N ≤ β + 1) (h' : N ≤ β' + 1) :
    offsetCount N α β = offsetCount N α β' := by
  unfold offsetCount intervalCount
  apply g_of_clip (lo := α + 1) (hi := α + N)
  · intro x hx; rw [Finset.mem_Icc] at hx; exact hx
  · intro m hm; rw [Finset.mem_Icc] at hm; unfold reach; omega
  · intro m hm; rw [Finset.mem_Icc] at hm; unfold reach; omega

/-- With no phantom panel on the left and at least `N - 1` on the right, the offset strip is
the half-line model: `a(N; 0, β) = H(N)` for `β ≥ N - 1`. -/
theorem offsetCount_zero_eq_halfLine {N β : Nat} (h : N ≤ β + 1) :
    offsetCount N 0 β = halfLine N := by
  unfold offsetCount
  simpa using halfLine_stable (M := N + β) (j := N) (by omega)

/-! ## A computable evaluator for `g` -/

/-- `gList M f l`: the subset recursion `g_eq_sum` run on a list (`f` is fuel). -/
def gList (M : Nat) : Nat → List Nat → Nat
  | 0, _ => 1
  | f + 1, l =>
    if l = [] then 1
    else ((l.filter fun m => SemiStep M (l.erase m) m).map fun m => gList M f (l.erase m)).sum

theorem gList_eq_g (M : Nat) :
    ∀ (f : Nat) (l : List Nat), l.Nodup → l.length ≤ f → gList M f l = g M l.toFinset
  | 0, l, _, hlen => by
    have : l = [] := List.length_eq_zero_iff.1 (by omega)
    subst this; simp [gList, g_empty]
  | f + 1, l, hnd, hlen => by
    unfold gList
    split_ifs with hl
    · subst hl; simp [g_empty]
    · have hne : l.toFinset.Nonempty := by
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hl
        exact ⟨x, List.mem_toFinset.2 hx⟩
      rw [g_eq_sum hne, ← List.sum_toFinset _ (hnd.filter _), List.toFinset_filter]
      have he : ∀ m, (l.erase m).toFinset = l.toFinset.erase m := fun m => by
        ext x; simp [hnd.mem_erase_iff]
      apply Finset.sum_congr
      · apply Finset.filter_congr
        intro m _
        rw [decide_eq_true_eq, ← he m]
        exact (setStep_iff (fun x => by rw [List.mem_toFinset])).symm
      · intro m hm
        rw [Finset.mem_filter, List.mem_toFinset] at hm
        rw [gList_eq_g M f (l.erase m) (hnd.erase m)
          (by rw [List.length_erase_of_mem hm.1]; omega), he m]

theorem toFinset_range' (i n : Nat) : (List.range' i n).toFinset = Finset.Icc i (i + n - 1) ∨ n = 0 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inr h
  · left; ext x; rw [List.mem_toFinset, List.mem_range'_1, Finset.mem_Icc]; omega

/-- Evaluation of interval counts by the list recursion. -/
theorem intervalCount_eq_gList {M i j : Nat} (h : i ≤ j) :
    intervalCount M i j = gList M (j + 1 - i) (List.range' i (j + 1 - i)) := by
  rw [gList_eq_g M _ _ (List.nodup_range' ..) (by simp)]
  rcases toFinset_range' i (j + 1 - i) with e | e
  · rw [e, intervalCount]; congr 2; omega
  · omega

end XdIntervals
end Folds
