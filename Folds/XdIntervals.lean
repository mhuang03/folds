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
* small tables by `decide +kernel`, including `H(2n+1) = H(n)` for `n ≤ 7`, and the wall model
  `wallCount` with its halving identity `W(n, 2j+1) = W(j, n)` checked for `n ≤ 9`.
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

/-- Computable half-line count. -/
def halfLineC (j : Nat) : Nat := gList (2 * j) j (List.range' 1 j)

/-- Computable offset count. -/
def offsetCountC (N α β : Nat) : Nat := gList (N + α + β) N (List.range' (α + 1) N)

theorem halfLine_eq_halfLineC {j : Nat} (h : 1 ≤ j) : halfLine j = halfLineC j := by
  rw [halfLine, intervalCount_eq_gList h, halfLineC]; congr 2

theorem offsetCount_eq_offsetCountC {N : Nat} (h : 1 ≤ N) (α β : Nat) :
    offsetCount N α β = offsetCountC N α β := by
  rw [offsetCount, intervalCount_eq_gList (by omega), offsetCountC]
  have e : α + N + 1 - (α + 1) = N := by omega
  rw [e]

/-! ## Small tables (kernel-checked) -/

/-- `H(1..13) = 1, 1, 1, 2, 1, 4, 1, 10, 2, 26, 1, 85, 4`. -/
theorem halfLineC_table :
    (List.range' 1 13).map halfLineC = [1, 1, 1, 2, 1, 4, 1, 10, 2, 26, 1, 85, 4] := by
  decide +kernel

/-- `H(2n+1) = H(n)` for `1 ≤ n ≤ 7` (kernel check on the evaluator, which equals `halfLine`
by `halfLine_eq_halfLineC`; see `halfLine_getElem` for the forced right half, which is the
mechanism). -/
theorem halfLineC_odd_small :
    ((List.range' 1 7).all fun n => halfLineC (2 * n + 1) == halfLineC n) = true := by
  decide +kernel

/-- The rows `a(N; 0, β)`, `β = 0..N-1`, of the offset table for `N = 6, 7`. -/
theorem offsetCountC_row_six :
    (List.range 6).map (offsetCountC 6 0) = [96, 15, 12, 7, 5, 4] := by decide +kernel

theorem offsetCountC_row_seven :
    (List.range 7).map (offsetCountC 7 0) = [256, 75, 14, 7, 1, 1, 1] := by decide +kernel

/-- One phantom panel on each side: nonzero only for odd `N` (here `N = 3..8`). -/
theorem offsetCountC_one_one :
    (List.range' 3 6).map (fun N => offsetCountC N 1 1) = [2, 0, 0, 0, 24, 0] := by
  decide +kernel

/-! ## The zero law -/

theorem countP_sort (S : Finset Nat) (p : Nat → Prop) [DecidablePred p] :
    (S.sort).countP (fun x => decide (p x)) = (S.filter p).card := by
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((Finset.sort_nodup ..).filter _)]
  congr 1; ext x; simp

/-- The step condition for a set, as an equality of two cardinalities. -/
theorem setStep_iff_card {M m : Nat} {S : Finset Nat} :
    SetStep M S m ↔ (S.filter (fun x => m - reach M m ≤ x ∧ x < m)).card =
      (S.filter (fun x => m < x ∧ x ≤ m + reach M m)).card := by
  unfold SetStep SemiStep
  rw [leftCount_eq (Finset.sort_nodup ..), rightCount_eq (Finset.sort_nodup ..), countP_sort,
    countP_sort]

/-- In an interval `[i, j]` that touches neither end of the strip, the last panel placed is
the exact middle. -/
theorem last_of_interval {M i j m : Nat} (hi : 2 ≤ i) (hj : j < M) (hm : m ∈ Finset.Icc i j)
    (h : SetStep M ((Finset.Icc i j).erase m) m) : i + j = 2 * m := by
  rw [Finset.mem_Icc] at hm
  rw [setStep_iff_card] at h
  have hL : ((Finset.Icc i j).erase m).filter (fun x => m - reach M m ≤ x ∧ x < m) =
      Finset.Icc (max i (m - reach M m)) (m - 1) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]; omega
  have hR : ((Finset.Icc i j).erase m).filter (fun x => m < x ∧ x ≤ m + reach M m) =
      Finset.Icc (m + 1) (min j (m + reach M m)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]; omega
  rw [hL, hR, Nat.card_Icc, Nat.card_Icc] at h
  unfold reach at h; omega

/-- **Zero law, even length.**  An interval `[i, j]` with `2 ≤ i`, `j < M` and an even number
of panels has no semi-symmetric ordering in the `M`-strip. -/
theorem intervalCount_eq_zero_of_odd {M i j : Nat} (hi : 2 ≤ i) (hj : j < M) (hij : i ≤ j)
    (hodd : (i + j) % 2 = 1) : intervalCount M i j = 0 := by
  unfold intervalCount
  rw [g_eq_sum (Finset.nonempty_Icc.2 hij)]
  apply Finset.sum_eq_zero
  intro m hm
  rw [Finset.mem_filter] at hm
  have := last_of_interval hi hj hm.1 hm.2
  omega

/-- With the middle panel `c` removed, no panel of `[i, j]` can be placed last if the interval
is at distance at least 2 from both ends of the strip. -/
theorem no_second_last {M i j c m : Nat} (hi : 3 ≤ i) (hj : j + 2 ≤ M) (hc : i + j = 2 * c)
    (hm : m ∈ (Finset.Icc i j).erase c) :
    ¬ SetStep M (((Finset.Icc i j).erase c).erase m) m := by
  rw [Finset.mem_erase, Finset.mem_Icc] at hm
  rw [setStep_iff_card]
  rcases Nat.lt_or_ge m c with hlt | hge
  · have hL : (((Finset.Icc i j).erase c).erase m).filter (fun x => m - reach M m ≤ x ∧ x < m) =
        Finset.Icc (max i (m - reach M m)) (m - 1) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]; omega
    have hR : (((Finset.Icc i j).erase c).erase m).filter (fun x => m < x ∧ x ≤ m + reach M m) =
        (Finset.Icc (m + 1) (min j (m + reach M m))).erase c := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]; omega
    rw [hL, hR, Finset.card_erase_eq_ite, Nat.card_Icc, Nat.card_Icc]
    unfold reach
    split_ifs with h <;> rw [Finset.mem_Icc] at h <;> omega
  · have hL : (((Finset.Icc i j).erase c).erase m).filter (fun x => m - reach M m ≤ x ∧ x < m) =
        (Finset.Icc (max i (m - reach M m)) (m - 1)).erase c := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]; omega
    have hR : (((Finset.Icc i j).erase c).erase m).filter (fun x => m < x ∧ x ≤ m + reach M m) =
        Finset.Icc (m + 1) (min j (m + reach M m)) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc]; omega
    rw [hL, hR, Finset.card_erase_eq_ite, Nat.card_Icc, Nat.card_Icc]
    unfold reach
    split_ifs with h <;> rw [Finset.mem_Icc] at h <;> omega

/-- **Zero law.**  An interval `[i, j]` with at least two panels, at distance at least 2 from
both ends of the strip (`3 ≤ i`, `j ≤ M - 2`), has no semi-symmetric ordering: the last panel
would be the exact middle, and then no panel can be the second to last. -/
theorem intervalCount_eq_zero {M i j : Nat} (hi : 3 ≤ i) (hj : j + 2 ≤ M) (hij : i < j) :
    intervalCount M i j = 0 := by
  unfold intervalCount
  rw [g_eq_sum (Finset.nonempty_Icc.2 hij.le)]
  apply Finset.sum_eq_zero
  intro c hc
  rw [Finset.mem_filter] at hc
  have h2 := last_of_interval (by omega) (by omega) hc.1 hc.2
  have hne : ((Finset.Icc i j).erase c).Nonempty :=
    ⟨i, Finset.mem_erase.2 ⟨by omega, Finset.mem_Icc.2 ⟨le_refl _, hij.le⟩⟩⟩
  rw [g_eq_sum hne]
  apply Finset.sum_eq_zero
  intro m hm
  rw [Finset.mem_filter] at hm
  exact absurd hm.2 (no_second_last hi hj h2 hm.1)

/-- Offset form of the zero law: two or more phantom panels on each side leave no ordering. -/
theorem offsetCount_eq_zero {N α β : Nat} (hN : 2 ≤ N) (hα : 2 ≤ α) (hβ : 2 ≤ β) :
    offsetCount N α β = 0 :=
  intervalCount_eq_zero (by omega) (by omega) (by omega)

/-- Offset form of the even zero law: phantom panels on both sides and `N` even. -/
theorem offsetCount_eq_zero_of_even {N α β : Nat} (hN : 1 ≤ N) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (he : N % 2 = 0) : offsetCount N α β = 0 :=
  intervalCount_eq_zero_of_odd (by omega) (by omega) (by omega) (by omega)

/-! ## The right half of the half-line model is forced -/

/-- **Forced right half.**  In a strip of length `M ≥ 2N - 1`, every semi-symmetric ordering
of `[1, N]` places panel `N - c` at step `2c + 1` (index `2c`), for every `c` with
`2c + 1 ≤ N`: the panels with a full window are placed from the right end inwards, at the odd
steps. -/
theorem halfLine_getElem {M N : Nat} (hM : 2 * N ≤ M + 1) {l : List Nat}
    (hl : l ∈ semiOrders M (Finset.Icc 1 N)) :
    ∀ c, 2 * c + 1 ≤ N → l[2 * c]? = some (N - c) := by
  rw [mem_semiOrders] at hl
  obtain ⟨⟨hnd, hset⟩, hss⟩ := hl
  have hmem : ∀ x, x ∈ l ↔ 1 ≤ x ∧ x ≤ N := fun x => by
    rw [← List.mem_toFinset, hset, Finset.mem_Icc]
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem ((hmem (N - c)).2 (by omega))
    have hstep := hss k hk
    rw [hkp] at hstep
    have hndt : (l.take k).Nodup := hnd.sublist (List.take_sublist k l)
    have hr : reach M (N - c) = N - c - 1 := by unfold reach; omega
    unfold SemiStep at hstep
    rw [leftCount_eq hndt, rightCount_eq hndt, hr] at hstep
    have hne : ∀ x ∈ l.take k, x ≠ N - c := by
      intro x hx e
      have h1 : l[k] ∈ l.take k := by rw [hkp, ← e]; exact hx
      exact absurd ((getElem_mem_take_iff hnd hk).1 h1) (lt_irrefl _)
    have hb : ∀ x ∈ l.take k, 1 ≤ x ∧ x ≤ N := fun x hx =>
      (hmem x).1 (List.mem_of_mem_take hx)
    have hL : (l.take k).countP (fun x => decide (N - c - (N - c - 1) ≤ x ∧ x < N - c)) =
        (l.take k).countP (fun x => decide (x < N - c)) := by
      apply List.countP_congr; intro x hx; have := hb x hx
      simp only [decide_eq_true_eq]; omega
    have hR : (l.take k).countP (fun x => decide (N - c < x ∧ x ≤ N - c + (N - c - 1))) =
        (l.take k).countP (fun x => decide (N - c < x)) := by
      apply List.countP_congr; intro x hx; have := hb x hx
      simp only [decide_eq_true_eq]; omega
    rw [hL, hR] at hstep
    have hsum : (l.take k).countP (fun x => decide (x < N - c)) +
        (l.take k).countP (fun x => decide (N - c < x)) = k := by
      have h1 := List.length_eq_countP_add_countP (fun x => decide (x < N - c)) (l := l.take k)
      have h2 : (l.take k).countP (fun x => decide ¬(decide (x < N - c)) = true) =
          (l.take k).countP (fun x => decide (N - c < x)) := by
        apply List.countP_congr; intro x hx; have := hne x hx
        simp only [decide_eq_true_eq]; omega
      rw [h2, List.length_take] at h1
      omega
    have hB : (l.take k).countP (fun x => decide (N - c < x)) ≤ c := by
      rw [List.countP_eq_length_filter,
        ← List.toFinset_card_of_nodup (hndt.filter _)]
      calc ((l.take k).filter (fun x => decide (N - c < x))).toFinset.card
          ≤ (Finset.Icc (N - c + 1) N).card := by
            apply Finset.card_le_card
            intro x hx
            rw [List.mem_toFinset, List.mem_filter] at hx
            have := hb x hx.1
            have h3 : N - c < x := by simpa using hx.2
            rw [Finset.mem_Icc]; omega
        _ = c := by rw [Nat.card_Icc]; omega
    have hk2 : k = 2 * c := by
      by_contra hne2
      have hlt : k < 2 * c := by omega
      have h4 := ih (k / 2) (by omega) (by omega)
      have e : 2 * (k / 2) = k := by omega
      rw [e, List.getElem?_eq_getElem hk, hkp] at h4
      have h5 : N - k / 2 = N - c := (Option.some.inj h4).symm
      omega
    subst hk2
    rw [List.getElem?_eq_getElem hk, hkp]

/-- In the half-line model the last panel `N` is always placed first. -/
theorem halfLine_head {M N : Nat} (hN : 1 ≤ N) (hM : 2 * N ≤ M + 1) {l : List Nat}
    (hl : l ∈ semiOrders M (Finset.Icc 1 N)) : l[0]? = some N := by
  simpa using halfLine_getElem hM hl 0 (by omega)

/-! ## The wall model -/

/-- Step rule of the wall model `W(n, B)`: left panels `1..n` with windows `[1, 2m-1]`; before
the `k`-th left panel is placed, exactly the panels `p > max n (B - k)` to the right of `n`
are placed.  `S` is the list of left panels placed so far. -/
def wallStep (n B : Nat) (S : List Nat) (m : Nat) : Prop :=
  S.countP (fun x => decide (x < m)) =
    S.countP (fun x => decide (m < x ∧ x ≤ 2 * m - 1)) +
      (2 * m - 1 - max n (B - (S.length + 1)))

instance (n B : Nat) (S : List Nat) (m : Nat) : Decidable (wallStep n B S m) :=
  inferInstanceAs (Decidable (_ = _))

/-- Number of ways to place the panels of `rem` one by one after `S`, every step satisfying
`wallStep` (`f` is fuel). -/
def wallList (n B : Nat) : Nat → List Nat → List Nat → Nat
  | 0, _, _ => 1
  | f + 1, S, rem =>
    if rem = [] then 1
    else ((rem.filter fun m => wallStep n B S m).map fun m =>
      wallList n B f (m :: S) (rem.erase m)).sum

/-- The wall count `W(n, B)`. -/
def wallCount (n B : Nat) : Nat := wallList n B n [] (List.range' 1 n)

/-- `W(n, 2n) = H(2n)` for `n ≤ 6`: `1, 2, 4, 10, 26, 85`. -/
theorem wallCount_even_small :
    (List.range' 1 6).map (fun n => wallCount n (2 * n)) = [1, 2, 4, 10, 26, 85] ∧
    (List.range' 1 6).map (fun n => halfLineC (2 * n)) = [1, 2, 4, 10, 26, 85] := by
  constructor <;> decide +kernel

/-- **Halving identity of the wall model** (kernel check for `n ≤ 9`):
`W(n, 2j+1) = W(j, n)` whenever `n - 1 ≤ 2j ≤ 2n`.  For `j = n` this is `W(n, 2n+1) = W(n, n)`,
and with `W(n, 2n+1) = H(2n+1)`, `W(n, n) = H(n)` it is `H(2n+1) = H(n)`. -/
theorem wallCount_halving_small :
    ((List.range 10).all fun n => (List.range (n + 1)).all fun j =>
      decide (n ≤ 2 * j + 1 → wallCount n (2 * j + 1) = wallCount j n)) = true := by
  decide +kernel

/-- The row `W(8, B)`, `B = 8..18`. -/
theorem wallCount_row_eight :
    (List.range' 8 11).map (wallCount 8) = [10, 10, 16, 6, 46, 7, 162, 1, 908, 10, 10] := by
  decide +kernel

end XdIntervals
end Folds
