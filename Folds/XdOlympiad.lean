import Folds.Structure2
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Olympiad toolkit: signs, commuting steps, deleting an end panel

Notes: `experiments/xd_olympiad/NOTES.txt`.

## Sign of a fold sequence
* `inv a`: number of inversions of the word `a`; `sgn a = (-1)^(inv a)`;
  `signedCount N = ∑_{a valid} sgn a` (`D(N)` in the notes).
* `inv_add_inv_mirror`: `inv a + inv (mirror N a) = 0 + 1 + ⋯ + (|a| - 1)`.
* `signedCount_eq_zero`: `D(N) = 0` when `N ≡ 2, 3 (mod 4)` (the mirror is a sign-reversing
  involution), hence exactly half of the valid sequences are even permutations
  (`card_evenSeqs_eq_card_oddSeqs`, `two_mul_card_evenSeqs`).
* `signedCount_eq_card_sub`: `D(N) = #even − #odd` for every `N`.

## Commuting steps (partial commutation)
* `Far N x y`: neither panel lies in the window of the other.
* `far_iff`: for `1 ≤ x < y ≤ N`, `Far N x y ↔ 2x ≤ y ∧ N + 1 + x ≤ 2y`.
* `not_far_left`, `not_far_right`: two panels of the same half never commute, so a set of
  pairwise commuting panels has at most two elements (`card_le_two_of_far`): every
  commutation class of valid sequences is the set of linear extensions of a poset of
  width at most 2 (a family of lattice paths).
* `far_swap`: exchanging two consecutive commuting panels keeps a sequence semi-symmetric
  (`far_swap_mem`: and inside `semiSeqs N`); `inv_swap`: it changes `inv` by one, so
  `sgn_swap`: it reverses the sign.

## Deleting panel 1
* `del1 S`: remove panel 1 and shift the labels down.
* `semiStep_del1_right`: for a panel `m` of the right half the step condition on the
  `N`-strip is the step condition of `m - 1` on the `(N-1)`-strip after deleting panel 1.
* `semiStep_del1_left`: for `2 ≤ m ≤ (N+1)/2` the same holds iff panels `1` and `2m - 1`
  are on the same side of `m` in time (`1 ∈ S ↔ 2m - 1 ∈ S`); `semiStep_del1_left_iff`
  is the exact version (the two conditions together are equivalent to ...).
-/

namespace Folds
namespace XdOlympiad

open Finset

/-! ## Inversions and the sign -/

/-- Number of inversions of a word: pairs of positions `i < j` with `a_i > a_j`. -/
def inv : List ℕ → ℕ
  | [] => 0
  | x :: l => l.countP (· < x) + inv l

/-- The sign of a word, `(-1)^(number of inversions)`. -/
def sgn (a : List ℕ) : ℤ := (-1) ^ inv a

/-- `D(N)`: the signed number of semi-symmetric sequences. -/
def signedCount (N : ℕ) : ℤ := ∑ a ∈ semiSeqs N, sgn a

/-- The valid sequences that are even permutations. -/
def evenSeqs (N : ℕ) : Finset (List ℕ) := (semiSeqs N).filter fun a => Even (inv a)

/-- The valid sequences that are odd permutations. -/
def oddSeqs (N : ℕ) : Finset (List ℕ) := (semiSeqs N).filter fun a => ¬ Even (inv a)

theorem countP_lt_add_countP_gt {x : ℕ} {l : List ℕ} (hx : x ∉ l) :
    l.countP (· < x) + l.countP (x < ·) = l.length := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have hy : y ≠ x := fun e => hx (by simp [e])
    have hx' : x ∉ l := fun h => hx (by simp [h])
    have := ih hx'
    rcases Nat.lt_or_gt_of_ne hy with h | h
    · have h' : ¬ x < y := by omega
      simp [List.countP_cons, h, h']; omega
    · have h' : ¬ y < x := by omega
      simp [List.countP_cons, h, h']; omega

theorem countP_mirror {N x : ℕ} {l : List ℕ} (hx : x ≤ N) (hl : ∀ y ∈ l, y ≤ N) :
    (mirror N l).countP (· < N + 1 - x) = l.countP (x < ·) := by
  unfold mirror
  rw [List.countP_map]
  apply List.countP_congr
  intro y hy
  have := hl y hy
  simp only [Function.comp_apply, decide_eq_true_eq]
  omega

/-- Mirroring turns inversions into non-inversions. -/
theorem inv_add_inv_mirror {N : ℕ} : ∀ {a : List ℕ}, a.Nodup → (∀ y ∈ a, y ≤ N) →
    inv a + inv (mirror N a) = ∑ i ∈ range a.length, i
  | [], _, _ => by simp [inv, mirror]
  | x :: l, hnd, hb => by
    have hx : x ∉ l := (List.nodup_cons.1 hnd).1
    have hl : ∀ y ∈ l, y ≤ N := fun y hy => hb y (by simp [hy])
    have ih := inv_add_inv_mirror (N := N) (List.nodup_cons.1 hnd).2 hl
    have h1 := countP_lt_add_countP_gt hx
    have h2 := countP_mirror (hb x (by simp)) hl
    have e : mirror N (x :: l) = (N + 1 - x) :: mirror N l := rfl
    rw [e, List.length_cons, Finset.sum_range_succ]
    simp only [inv]
    omega

theorem sum_range_id_odd {N : ℕ} (hN : N % 4 = 2 ∨ N % 4 = 3) :
    Odd (∑ i ∈ range N, i) := by
  have h := Finset.sum_range_id_mul_two N
  rcases hN with hN | hN
  · obtain ⟨q, rfl⟩ : ∃ q, N = 4 * q + 2 := ⟨N / 4, by omega⟩
    have e : ∑ i ∈ range (4 * q + 2), i = (2 * q + 1) * (4 * q + 1) := by
      have : (4 * q + 2) * (4 * q + 2 - 1) = (2 * q + 1) * (4 * q + 1) * 2 := by
        have : 4 * q + 2 - 1 = 4 * q + 1 := by omega
        rw [this]; ring
      rw [this] at h
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
    rw [e]; exact Nat.odd_mul.2 ⟨⟨q, by ring⟩, ⟨2 * q, by ring⟩⟩
  · obtain ⟨q, rfl⟩ : ∃ q, N = 4 * q + 3 := ⟨N / 4, by omega⟩
    have e : ∑ i ∈ range (4 * q + 3), i = (4 * q + 3) * (2 * q + 1) := by
      have : (4 * q + 3) * (4 * q + 3 - 1) = (4 * q + 3) * (2 * q + 1) * 2 := by
        have : 4 * q + 3 - 1 = 4 * q + 2 := by omega
        rw [this]; ring
      rw [this] at h
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
    rw [e]; exact Nat.odd_mul.2 ⟨⟨2 * q + 1, by ring⟩, ⟨q, by ring⟩⟩

theorem sgn_mul_self (a : List ℕ) : sgn a * sgn a = 1 := by
  unfold sgn; rw [← pow_add, ← two_mul]; simp

theorem length_of_mem_semiSeqs {N : ℕ} {a : List ℕ} (ha : a ∈ semiSeqs N) : a.length = N := by
  have := (mem_semiSeqs.1 ha).1.length_eq
  simpa using this

/-- For `N ≡ 2, 3 (mod 4)` the mirror reverses the sign of a fold sequence. -/
theorem sgn_mirror {N : ℕ} (hN : N % 4 = 2 ∨ N % 4 = 3) {a : List ℕ} (ha : a ∈ semiSeqs N) :
    sgn (mirror N a) = - sgn a := by
  have hf := (mem_semiSeqs.1 ha).1
  have hsum := inv_add_inv_mirror (N := N) (nodup_of_foldSeq hf)
    (fun y hy => ((mem_range'_of_perm hf).1 hy).2)
  rw [length_of_mem_semiSeqs ha] at hsum
  have hprod : sgn a * sgn (mirror N a) = -1 := by
    unfold sgn; rw [← pow_add, hsum]; exact (sum_range_id_odd hN).neg_one_pow
  have h1 := sgn_mul_self a
  calc sgn (mirror N a) = (sgn a * sgn a) * sgn (mirror N a) := by rw [h1, one_mul]
    _ = sgn a * (sgn a * sgn (mirror N a)) := by ring
    _ = - sgn a := by rw [hprod]; ring

/-- **The signed count vanishes for `N ≡ 2, 3 (mod 4)`.** -/
theorem signedCount_eq_zero {N : ℕ} (hN : N % 4 = 2 ∨ N % 4 = 3) : signedCount N = 0 := by
  have h : signedCount N = - signedCount N := by
    unfold signedCount
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_nbij' (mirror N) (mirror N) ?_ ?_ ?_ ?_ ?_
    · intro a ha; exact mirror_mem_semiSeqs ha
    · intro a ha; exact mirror_mem_semiSeqs ha
    · intro a ha; exact mirror_mirror (mem_semiSeqs.1 ha).1
    · intro a ha; exact mirror_mirror (mem_semiSeqs.1 ha).1
    · intro a ha; rw [sgn_mirror hN ha, neg_neg]
  omega

/-- `D(N) = #even − #odd`. -/
theorem signedCount_eq_card_sub (N : ℕ) :
    signedCount N = ((evenSeqs N).card : ℤ) - (oddSeqs N).card := by
  unfold signedCount evenSeqs oddSeqs
  rw [← Finset.sum_filter_add_sum_filter_not (semiSeqs N) (fun a => Even (inv a))]
  have h1 : ∑ a ∈ (semiSeqs N).filter (fun a => Even (inv a)), sgn a =
      ∑ _a ∈ (semiSeqs N).filter (fun a => Even (inv a)), (1 : ℤ) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact (Finset.mem_filter.1 ha).2.neg_one_pow
  have h2 : ∑ a ∈ (semiSeqs N).filter (fun a => ¬ Even (inv a)), sgn a =
      ∑ _a ∈ (semiSeqs N).filter (fun a => ¬ Even (inv a)), (-1 : ℤ) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact (Nat.not_even_iff_odd.1 (Finset.mem_filter.1 ha).2).neg_one_pow
  rw [h1, h2]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
  ring

/-- For `N ≡ 2, 3 (mod 4)`: as many even as odd valid sequences. -/
theorem card_evenSeqs_eq_card_oddSeqs {N : ℕ} (hN : N % 4 = 2 ∨ N % 4 = 3) :
    (evenSeqs N).card = (oddSeqs N).card := by
  have h := signedCount_eq_card_sub N
  rw [signedCount_eq_zero hN] at h
  omega

theorem card_evenSeqs_add_card_oddSeqs (N : ℕ) :
    (evenSeqs N).card + (oddSeqs N).card = semiCount N := by
  unfold evenSeqs oddSeqs semiCount
  exact Finset.card_filter_add_card_filter_not _

/-- For `N ≡ 2, 3 (mod 4)` exactly `a(N)/2` valid sequences are even permutations. -/
theorem two_mul_card_evenSeqs {N : ℕ} (hN : N % 4 = 2 ∨ N % 4 = 3) :
    2 * (evenSeqs N).card = semiCount N := by
  have h1 := card_evenSeqs_eq_card_oddSeqs hN
  have h2 := card_evenSeqs_add_card_oddSeqs N
  omega

/-! ## Commuting panels -/

/-- Panels `x` and `y` *commute*: neither lies in the window of the other, i.e.
`|x - y| > max (reach N x) (reach N y)`. -/
def Far (N x y : ℕ) : Prop :=
  (reach N x < x - y ∨ reach N x < y - x) ∧ (reach N y < x - y ∨ reach N y < y - x)

instance (N x y : ℕ) : Decidable (Far N x y) := by unfold Far; infer_instance

theorem Far.symm {N x y : ℕ} (h : Far N x y) : Far N y x := by
  unfold Far at *; omega

/-- Explicit form: `x < y` commute iff `y` is to the right of the window of `x` and `x` is
to the left of the window of `y`. -/
theorem far_iff {N x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hy : y ≤ N) :
    Far N x y ↔ 2 * x ≤ y ∧ N + 1 + x ≤ 2 * y := by
  unfold Far reach; omega

/-- Two panels of the left half (middle included) never commute. -/
theorem not_far_left {N x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hy : 2 * y ≤ N + 1) :
    ¬ Far N x y := by
  unfold Far reach; omega

/-- Two panels of the right half (middle included) never commute. -/
theorem not_far_right {N x y : ℕ} (hx : N + 1 ≤ 2 * x) (hxy : x < y) (hy : y ≤ N) :
    ¬ Far N x y := by
  unfold Far reach; omega

/-- A set of pairwise commuting panels has at most two elements: the commutation classes
are sets of linear extensions of posets of width at most 2. -/
theorem card_le_two_of_far {N : ℕ} {s : Finset ℕ} (hs : s ⊆ Icc 1 N)
    (hfar : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Far N x y) : s.card ≤ 2 := by
  have hl : (s.filter fun x => 2 * x ≤ N + 1).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    by_contra hne
    have bx := Finset.mem_Icc.1 (hs hx.1)
    have by' := Finset.mem_Icc.1 (hs hy.1)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact not_far_left bx.1 h hy.2 (hfar x hx.1 y hy.1 hne)
    · exact not_far_left by'.1 h hx.2 (hfar y hy.1 x hx.1 (Ne.symm hne))
  have hr : (s.filter fun x => ¬ 2 * x ≤ N + 1).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    by_contra hne
    have bx := Finset.mem_Icc.1 (hs hx.1)
    have by' := Finset.mem_Icc.1 (hs hy.1)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact not_far_right (by omega) h by'.2 (hfar x hx.1 y hy.1 hne)
    · exact not_far_right (by omega) h bx.2 (hfar y hy.1 x hx.1 (Ne.symm hne))
  have := Finset.card_filter_add_card_filter_not (s := s) (fun x => 2 * x ≤ N + 1)
  omega

/-- The step condition of `m` only looks at the window of `m`. -/
theorem semiStep_congr_window {N m : ℕ} {S T : List ℕ}
    (h : ∀ d, 1 ≤ d → d ≤ reach N m →
      ((m - d ∈ S ↔ m - d ∈ T) ∧ (m + d ∈ S ↔ m + d ∈ T))) :
    SemiStep N S m ↔ SemiStep N T m := by
  have hl : leftCount N S m = leftCount N T m := by
    unfold leftCount; apply List.countP_congr
    intro d hd; rw [List.mem_range'_1] at hd
    simp [(h d (by omega) (by omega)).1]
  have hr : rightCount N S m = rightCount N T m := by
    unfold rightCount; apply List.countP_congr
    intro d hd; rw [List.mem_range'_1] at hd
    simp [(h d (by omega) (by omega)).2]
  unfold SemiStep; rw [hl, hr]

/-- A panel outside the window of `m` does not affect the step of `m`. -/
theorem semiStep_append_far {N m y : ℕ} {S : List ℕ}
    (h : reach N m < m - y ∨ reach N m < y - m) :
    SemiStep N (S ++ [y]) m ↔ SemiStep N S m := by
  apply semiStep_congr_window
  intro d h1 h2
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · constructor
    · rintro (h' | h')
      · exact h'
      · omega
    · intro h'; exact Or.inl h'
  · constructor
    · rintro (h' | h')
      · exact h'
      · omega
    · intro h'; exact Or.inl h'

/-- **Commutation.** Exchanging two consecutive commuting panels keeps a sequence
semi-symmetric. -/
theorem far_swap {N x y : ℕ} {l t : List ℕ} (hfar : Far N x y)
    (h : SemiSymmetric N (l ++ x :: y :: t)) : SemiSymmetric N (l ++ y :: x :: t) := by
  rw [semiSymmetric_append_iff] at h ⊢
  refine ⟨h.1, ?_⟩
  intro k hk
  match k, hk with
  | 0, _ =>
    have h1 := h.2 1 (by simp)
    simp only [List.take_succ_cons, List.take_zero, List.getElem_cons_succ,
      List.getElem_cons_zero] at h1
    simp only [List.take_zero, List.append_nil, List.getElem_cons_zero]
    exact (semiStep_append_far (by unfold Far at hfar; omega)).1 h1
  | 1, _ =>
    have h0 := h.2 0 (by simp)
    simp only [List.take_zero, List.append_nil, List.getElem_cons_zero] at h0
    simp only [List.take_succ_cons, List.take_zero, List.getElem_cons_succ,
      List.getElem_cons_zero]
    exact (semiStep_append_far (by unfold Far at hfar; omega)).2 h0
  | k + 2, hk =>
    have h2 := h.2 (k + 2) (by simpa using hk)
    simp only [List.take_succ_cons, List.getElem_cons_succ] at h2 ⊢
    refine (semiStep_congr ?_).1 h2
    intro z
    simp only [List.mem_append, List.mem_cons]
    tauto

theorem far_swap_mem {N x y : ℕ} {l t : List ℕ} (hfar : Far N x y)
    (h : l ++ x :: y :: t ∈ semiSeqs N) : l ++ y :: x :: t ∈ semiSeqs N := by
  rw [mem_semiSeqs] at h ⊢
  refine ⟨?_, far_swap hfar h.2⟩
  unfold IsFoldSeq at *
  exact (List.Perm.append_left l (List.Perm.swap x y t)).trans h.1

theorem inv_append (l t : List ℕ) :
    inv (l ++ t) = inv l + inv t + (l.map fun x => t.countP (· < x)).sum := by
  induction l with
  | nil => simp [inv]
  | cons x l ih =>
    simp only [List.cons_append, inv, List.countP_append, List.map_cons, List.sum_cons, ih]
    omega

/-- Exchanging two consecutive distinct entries changes the number of inversions by one. -/
theorem inv_swap {x y : ℕ} (hxy : x ≠ y) (l t : List ℕ) :
    inv (l ++ x :: y :: t) + 1 = inv (l ++ y :: x :: t) ∨
      inv (l ++ y :: x :: t) + 1 = inv (l ++ x :: y :: t) := by
  rw [inv_append, inv_append]
  have e : (l.map fun z => (x :: y :: t).countP (· < z)) =
      (l.map fun z => (y :: x :: t).countP (· < z)) := by
    apply List.map_congr_left
    intro z _
    simp only [List.countP_cons]; omega
  rw [e]
  simp only [inv, List.countP_cons]
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · have h' : ¬ y < x := by omega
    simp [h, h']; omega
  · have h' : ¬ x < y := by omega
    simp [h, h']; omega

/-- Exchanging two consecutive distinct entries reverses the sign. -/
theorem sgn_swap {x y : ℕ} (hxy : x ≠ y) (l t : List ℕ) :
    sgn (l ++ y :: x :: t) = - sgn (l ++ x :: y :: t) := by
  unfold sgn
  rcases inv_swap hxy l t with h | h
  · rw [← h, pow_succ]; ring
  · rw [← h, pow_succ]; ring

/-! ## Deleting panel 1 -/

/-- Delete panel 1 and shift the remaining labels down by one. -/
def del1 (S : List ℕ) : List ℕ := (S.filter (· ≠ 1)).map (· - 1)

theorem mem_del1 {S : List ℕ} (h0 : 0 ∉ S) {z : ℕ} : z ∈ del1 S ↔ 1 ≤ z ∧ z + 1 ∈ S := by
  unfold del1
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨w, ⟨hw, hw1⟩, rfl⟩
    have : w ≠ 0 := fun e => h0 (e ▸ hw)
    have e : w - 1 + 1 = w := by omega
    exact ⟨by omega, by rw [e]; exact hw⟩
  · rintro ⟨hz, hz1⟩
    exact ⟨z + 1, ⟨hz1, by omega⟩, by omega⟩

/-- Right half: the window does not see the deletion of panel 1. -/
theorem semiStep_del1_right {N m : ℕ} {S : List ℕ} (h0 : 0 ∉ S) (hm : N + 1 < 2 * m)
    (hmN : m ≤ N) : SemiStep N S m ↔ SemiStep (N - 1) (del1 S) (m - 1) := by
  have hr : reach (N - 1) (m - 1) = reach N m := by unfold reach; omega
  have hl : leftCount N S m = leftCount (N - 1) (del1 S) (m - 1) := by
    unfold leftCount; rw [hr]; apply List.countP_congr
    intro d hd; rw [List.mem_range'_1] at hd
    have hd2 : d ≤ N - m := by unfold reach at hd; omega
    have e : m - 1 - d + 1 = m - d := by omega
    simp [mem_del1 h0, e]; omega
  have hr' : rightCount N S m = rightCount (N - 1) (del1 S) (m - 1) := by
    unfold rightCount; rw [hr]; apply List.countP_congr
    intro d hd; rw [List.mem_range'_1] at hd
    have e : m - 1 + d + 1 = m + d := by omega
    simp [mem_del1 h0, e]; omega
  unfold SemiStep; rw [hl, hr']

/-- Left half (middle included): deleting panel 1 removes the two ends `1` and `2m - 1`
of the window of `m`.  Exact bookkeeping of the two step conditions. -/
theorem semiStep_del1_left_counts {N m : ℕ} {S : List ℕ} (h0 : 0 ∉ S) (h2 : 2 ≤ m)
    (hm : 2 * m ≤ N + 1) :
    leftCount N S m = leftCount (N - 1) (del1 S) (m - 1) + (if 1 ∈ S then 1 else 0) ∧
    rightCount N S m =
      rightCount (N - 1) (del1 S) (m - 1) + (if 2 * m - 1 ∈ S then 1 else 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hr : reach N (k + 2) = k + 1 := by unfold reach; omega
  have hr' : reach (N - 1) (k + 2 - 1) = k := by unfold reach; omega
  constructor
  · unfold leftCount
    rw [hr, hr', List.range'_1_concat, List.countP_append]
    congr 1
    · apply List.countP_congr
      intro d hd; rw [List.mem_range'_1] at hd
      have hmem : (k + 2 - 1 - d ∈ del1 S) ↔ (k + 2 - d ∈ S) := by
        rw [mem_del1 h0]
        have e : k + 2 - 1 - d + 1 = k + 2 - d := by omega
        rw [e]
        exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      simp only [decide_eq_true_eq]
      exact hmem.symm
    · have e : k + 2 - (1 + k) = 1 := by omega
      simp [e]
  · unfold rightCount
    rw [hr, hr', List.range'_1_concat, List.countP_append]
    congr 1
    · apply List.countP_congr
      intro d hd; rw [List.mem_range'_1] at hd
      have hmem : (k + 2 - 1 + d ∈ del1 S) ↔ (k + 2 + d ∈ S) := by
        rw [mem_del1 h0]
        have e : k + 2 - 1 + d + 1 = k + 2 + d := by omega
        rw [e]
        exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      simp only [decide_eq_true_eq]
      exact hmem.symm
    · have e : k + 2 + (1 + k) = 2 * (k + 2) - 1 := by omega
      simp [e]

/-- Left half: if panels `1` and `2m - 1` are on the same side of `m` in time, the step of
`m` on the `N`-strip is the step of `m - 1` on the `(N-1)`-strip after deleting panel 1. -/
theorem semiStep_del1_left {N m : ℕ} {S : List ℕ} (h0 : 0 ∉ S) (h2 : 2 ≤ m)
    (hm : 2 * m ≤ N + 1) (h : 1 ∈ S ↔ 2 * m - 1 ∈ S) :
    SemiStep N S m ↔ SemiStep (N - 1) (del1 S) (m - 1) := by
  obtain ⟨hl, hr⟩ := semiStep_del1_left_counts (S := S) h0 h2 hm
  unfold SemiStep
  rw [hl, hr]
  by_cases h1 : 1 ∈ S
  · simp [h1, h.1 h1]
  · have h3 : 2 * m - 1 ∉ S := fun h' => h1 (h.2 h')
    simp [h1, h3]

/-- Left half, converse: if both step conditions hold, then `1` and `2m - 1` are on the same
side of `m`.  So for a valid sequence `a` on `[N]`, the sequence with panel 1 deleted is valid
on `[N - 1]` iff no panel `m` with `2 ≤ m ≤ (N+1)/2` is placed between panels `1` and
`2m - 1`. -/
theorem same_side_of_semiStep_del1 {N m : ℕ} {S : List ℕ} (h0 : 0 ∉ S) (h2 : 2 ≤ m)
    (hm : 2 * m ≤ N + 1) (h : SemiStep N S m) (h' : SemiStep (N - 1) (del1 S) (m - 1)) :
    (1 ∈ S ↔ 2 * m - 1 ∈ S) := by
  obtain ⟨hl, hr⟩ := semiStep_del1_left_counts (S := S) h0 h2 hm
  unfold SemiStep at h h'
  rw [hl, hr, h'] at h
  by_cases h1 : 1 ∈ S <;> by_cases h3 : 2 * m - 1 ∈ S <;> simp [h1, h3] at h ⊢

end XdOlympiad
end Folds
