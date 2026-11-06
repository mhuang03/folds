import Folds.Congruence

/-!
# Refined counts: first panel, last panel, first pair

See `experiments/structure2/FINDINGS.txt`, section 1.2.

* `F(N,m) = firstCount N m`: valid sequences starting with panel `m`;
  `L(N,m) = lastCount N m`: those ending with `m`.
* `lastCount_eq_firstCount`: `L(N,m) = F(N,m)` (reversal).
* `firstCount_mirror`: `F(N,m) = F(N,N+1-m)` (mirror).
* `card_head_odd_eq_even`: for even `N`, exactly as many valid sequences start with an
  odd panel as with an even one, so each kind is `a(N)/2` (`two_mul_card_head_odd`).
  (For odd `N` this fails in general, e.g. `N = 7`: 118 odd-first, 138 even-first.)
* `second_of_first_one`: if a valid sequence starts with `1, x` then `N + 2 ≤ 2x`.
* `sum_firstCount`: `Σ_{m=1}^{N} F(N,m) = a(N)`.
-/

namespace Folds
namespace Structure2

/-- `F(N,m)`: number of semi-symmetric sequences whose first panel is `m`. -/
def firstCount (N m : ℕ) : ℕ := ((semiSeqs N).filter (fun a => a.head? = some m)).card

/-- `L(N,m)`: number of semi-symmetric sequences whose last panel is `m`. -/
def lastCount (N m : ℕ) : ℕ := ((semiSeqs N).filter (fun a => a.getLast? = some m)).card

/-- `L(N,m) = F(N,m)`: reversal is a bijection between the two sets. -/
theorem lastCount_eq_firstCount (N m : ℕ) : lastCount N m = firstCount N m := by
  unfold lastCount firstCount
  refine Finset.card_nbij' List.reverse List.reverse ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    exact ⟨reverse_mem_semiSeqs ha.1, by rw [List.head?_reverse]; exact ha.2⟩
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    exact ⟨reverse_mem_semiSeqs ha.1, by rw [List.getLast?_reverse]; exact ha.2⟩
  · intro a _; simp
  · intro a _; simp

theorem head?_mirror (N : ℕ) (a : List ℕ) :
    (mirror N a).head? = a.head?.map (N + 1 - ·) := by
  cases a <;> simp [mirror]

/-- `F(N,m) = F(N,N+1-m)`. -/
theorem firstCount_mirror {N m : ℕ} (h1 : 1 ≤ m) (hm : m ≤ N) :
    firstCount N m = firstCount N (N + 1 - m) := by
  unfold firstCount
  refine Finset.card_nbij' (mirror N) (mirror N) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    exact ⟨mirror_mem_semiSeqs ha.1, by rw [head?_mirror, ha.2]; rfl⟩
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    refine ⟨mirror_mem_semiSeqs ha.1, ?_⟩
    rw [head?_mirror, ha.2]; simp; omega
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha
    exact mirror_mirror (mem_semiSeqs.1 ha.1).1
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha
    exact mirror_mirror (mem_semiSeqs.1 ha.1).1

/-- For even `N`, the mirror swaps the parity of the first panel, so odd-first and
even-first valid sequences are equinumerous. -/
theorem card_head_odd_eq_even {N : ℕ} (hN : N % 2 = 0) :
    ((semiSeqs N).filter (fun a => ∃ x, a.head? = some x ∧ x % 2 = 1)).card =
      ((semiSeqs N).filter (fun a => ∃ x, a.head? = some x ∧ x % 2 = 0)).card := by
  refine Finset.card_nbij' (mirror N) (mirror N) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨hs, x, hx, hodd⟩ := ha
    have hf := (mem_semiSeqs.1 hs).1
    have hxa : x ∈ a := List.mem_of_mem_head? hx
    have hb := (mem_range'_of_perm hf).1 hxa
    refine ⟨mirror_mem_semiSeqs hs, N + 1 - x, by rw [head?_mirror, hx]; rfl, by omega⟩
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨hs, x, hx, hev⟩ := ha
    have hf := (mem_semiSeqs.1 hs).1
    have hxa : x ∈ a := List.mem_of_mem_head? hx
    have hb := (mem_range'_of_perm hf).1 hxa
    refine ⟨mirror_mem_semiSeqs hs, N + 1 - x, by rw [head?_mirror, hx]; rfl, by omega⟩
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha
    exact mirror_mirror (mem_semiSeqs.1 ha.1).1
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha
    exact mirror_mirror (mem_semiSeqs.1 ha.1).1

/-- For even `N ≥ 2`, exactly half of the valid sequences start with an odd panel. -/
theorem two_mul_card_head_odd {N : ℕ} (hN : N % 2 = 0) (hN2 : 2 ≤ N) :
    2 * ((semiSeqs N).filter (fun a => ∃ x, a.head? = some x ∧ x % 2 = 1)).card =
      semiCount N := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := semiSeqs N) (fun a => ∃ x, a.head? = some x ∧ x % 2 = 1)
  have hneg : (semiSeqs N).filter (fun a => ¬ ∃ x, a.head? = some x ∧ x % 2 = 1) =
      (semiSeqs N).filter (fun a => ∃ x, a.head? = some x ∧ x % 2 = 0) := by
    apply Finset.filter_congr
    intro a ha
    have hf := (mem_semiSeqs.1 ha).1
    have hlen : a.length = N := by rw [hf.length_eq]; simp
    obtain ⟨y, t, rfl⟩ : ∃ y t, a = y :: t := by
      cases a with
      | nil => simp at hlen; omega
      | cons y t => exact ⟨y, t, rfl⟩
    simp only [List.head?_cons, Option.some.injEq, exists_eq_left']
    omega
  rw [hneg, ← card_head_odd_eq_even hN] at hsplit
  unfold semiCount; omega

/-- If a valid sequence starts with `1, x`, then `N + 2 ≤ 2x`: panel `1` would otherwise
lie in the left arm of `x` and nothing in the right arm. -/
theorem second_of_first_one {N x : ℕ} {t : List ℕ} (h : 1 :: x :: t ∈ semiSeqs N) :
    N + 2 ≤ 2 * x := by
  have ⟨hf, hs⟩ := mem_semiSeqs.1 h
  have hnd := nodup_of_foldSeq hf
  have hx1 : x ≠ 1 := by
    intro e; subst e; simp at hnd
  have hxN := (mem_range'_of_perm hf).1 (by simp : x ∈ 1 :: x :: t)
  have step := hs 1 (by simp)
  simp only [List.take, List.getElem_cons_succ, List.getElem_cons_zero] at step
  by_contra hlt
  rw [not_le] at hlt
  have hr : reach N x = x - 1 := by unfold reach; omega
  unfold SemiStep leftCount rightCount at step
  rw [hr] at step
  have hR : (List.range' 1 (x - 1)).countP (fun d => decide (x + d ∈ [1])) = 0 := by
    rw [List.countP_eq_zero]
    intro d hd; simp at hd ⊢; omega
  have hL : 0 < (List.range' 1 (x - 1)).countP (fun d => decide (x - d ∈ [1])) := by
    rw [List.countP_pos_iff]
    exact ⟨x - 1, by rw [List.mem_range'_1]; omega, by simp; omega⟩
  omega

/-- `Σ_{m=1}^{N} F(N,m) = a(N)`. -/
theorem sum_firstCount {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Finset.Icc 1 N, firstCount N m = semiCount N := by
  unfold firstCount semiCount
  have key : ∀ a ∈ semiSeqs N, ∃ y t, a = y :: t ∧ 1 ≤ y ∧ y ≤ N := by
    intro a ha
    have hf := (mem_semiSeqs.1 ha).1
    have hlen : a.length = N := by rw [hf.length_eq]; simp
    cases a with
    | nil => simp at hlen; omega
    | cons y t => exact ⟨y, t, rfl, (mem_range'_of_perm hf).1 (by simp)⟩
  rw [Finset.card_eq_sum_card_fiberwise (f := fun a => a.head?.getD 0) (t := Finset.Icc 1 N)]
  · apply Finset.sum_congr rfl
    intro m _
    congr 1
    apply Finset.filter_congr
    intro a ha
    obtain ⟨y, t, rfl, _, _⟩ := key a ha
    simp
  · intro a ha
    obtain ⟨y, t, rfl, h1, h2⟩ := key a ha
    simp; omega

end Structure2
end Folds
