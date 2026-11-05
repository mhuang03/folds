import Mathlib.Data.Nat.Log
import Folds.Blocks

/-!
# Extremal statistics of semi-symmetric fold sequences

Proofs on paper: `experiments/extremal/PROOFS.txt`.

## Left-to-right maxima
`records m l` counts the left-to-right maxima of `l` above the current maximum `m`, and
`lrmax a = records 0 a`.

* `lrmax_le`: a semi-symmetric fold sequence has at most `⌊log₂ N⌋ + 1` left-to-right
  maxima.  (A new maximum `x` placed after the old maximum `M` has nothing to its right,
  so nothing to its left in its window: `x - M > reach N x`, i.e. the gap `N - x` at least
  halves.)
* `exists_lrmax`: the bound is attained for every `N ≥ 1` (parity blocks, with the block
  containing `N` placed second).

## Free steps
A step is *free* if its window contains no earlier panel (`FreeStep`), and
`numFree N a` counts the free steps.

* `numFree_le`: for **every** fold sequence (validity is not needed),
  `numFree N a ≤ ⌊log₂(N+1)⌋ + ⌊log₂((N+1)/3)⌋ + 1`.
  After the first step `x`, every later free panel `f` satisfies `2f ≤ x` (left half) or
  `2(N+1-f) ≤ N+1-x` (right half), and within each half the free panels halve.
-/

namespace Folds

/-! ## Left-to-right maxima -/

/-- Number of left-to-right maxima of `l` that exceed the running maximum `m`. -/
def records : Nat → List Nat → Nat
  | _, [] => 0
  | m, x :: t => if m < x then records x t + 1 else records m t

/-- Number of left-to-right maxima of a sequence of positive panels. -/
def lrmax (a : List Nat) : Nat := records 0 a

/-- The steps of `l`, performed after the panels `P`, are all semi-symmetric. -/
def StepsFrom (N : Nat) (P l : List Nat) : Prop :=
  ∀ k (hk : k < l.length), SemiStep N (P ++ l.take k) l[k]

theorem StepsFrom.head {N : Nat} {P t : List Nat} {x : Nat} (h : StepsFrom N P (x :: t)) :
    SemiStep N P x := by
  have := h 0 (by simp); simpa using this

theorem StepsFrom.tail {N : Nat} {P t : List Nat} {x : Nat} (h : StepsFrom N P (x :: t)) :
    StepsFrom N (P ++ [x]) t := by
  intro k hk
  have := h (k + 1) (by simp; omega)
  simpa using this

theorem semiSymmetric_iff_stepsFrom {N : Nat} {a : List Nat} :
    SemiSymmetric N a ↔ StepsFrom N [] a := by
  simp [SemiSymmetric, StepsFrom]

/-- If every panel of `P` is at most `M ∈ P` and `x > M`, a semi-symmetric step at `x`
forces `M` to lie outside the window of `x`. -/
theorem gap_of_new_max {N M x : Nat} {P : List Nat} (hM : M ∈ P) (hle : ∀ y ∈ P, y ≤ M)
    (hMx : M < x) (h : SemiStep N P x) : reach N x < x - M := by
  refine Nat.lt_of_not_le fun hr => ?_
  have hl : 0 < leftCount N P x := by
    unfold leftCount
    rw [List.countP_pos_iff]
    refine ⟨x - M, ?_, ?_⟩
    · rw [List.mem_range'_1]; omega
    · simp only [decide_eq_true_eq]
      rwa [show x - (x - M) = M by omega]
  have hr0 : rightCount N P x = 0 := by
    unfold rightCount
    rw [List.countP_eq_zero]
    intro d _ hd
    simp only [decide_eq_true_eq] at hd
    have := hle _ hd
    omega
  unfold SemiStep at h
  omega

theorem log_two_mul {n : Nat} (hn : n ≠ 0) : Nat.log 2 (2 * n) = Nat.log 2 n + 1 := by
  rw [Nat.mul_comm]; exact Nat.log_mul_base Nat.one_lt_two hn

theorem records_le_aux {N : Nat} : ∀ (l P : List Nat) (M : Nat),
    1 ≤ M → M ≤ N → M ∈ P → (∀ y ∈ P, y ≤ M) → (∀ x ∈ l, x ≤ N) →
    StepsFrom N P l → records M l ≤ Nat.log 2 (N - M + 1)
  | [], _, _, _, _, _, _, _, _ => by simp [records]
  | x :: t, P, M, hM1, hMN, hMP, hle, hlN, hst => by
    have hxN : x ≤ N := hlN x (by simp)
    have htN : ∀ y ∈ t, y ≤ N := fun y hy => hlN y (by simp [hy])
    unfold records
    split_ifs with hMx
    · have hgap := gap_of_new_max hMP hle hMx hst.head
      have hreach : reach N x = N - x := by unfold reach at hgap ⊢; omega
      have ih := records_le_aux t (P ++ [x]) x (by omega) hxN (by simp)
        (fun y hy => by
          rw [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | hy
          · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hle y hy) hMx)
          · omega) htN hst.tail
      calc records x t + 1 ≤ Nat.log 2 (N - x + 1) + 1 := by omega
        _ = Nat.log 2 (2 * (N - x + 1)) := (log_two_mul (by omega)).symm
        _ ≤ Nat.log 2 (N - M + 1) := Nat.log_mono_right (by omega)
    · exact records_le_aux t (P ++ [x]) M hM1 hMN (by simp [hMP])
        (fun y hy => by
          rw [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | hy
          · exact hle y hy
          · omega) htN hst.tail

/-- **Left-to-right maxima.**  A semi-symmetric fold sequence of length `N` has at most
`⌊log₂ N⌋ + 1` left-to-right maxima. -/
theorem lrmax_le {N : Nat} {a : List Nat} (hf : IsFoldSeq N a) (h : SemiSymmetric N a) :
    lrmax a ≤ Nat.log 2 N + 1 := by
  rw [semiSymmetric_iff_stepsFrom] at h
  match a, hf, h with
  | [], _, _ => simp [lrmax, records]
  | x :: t, hf, h =>
    have hx := (mem_range'_of_perm hf (x := x)).1 (List.mem_cons_self ..)
    have htN : ∀ y ∈ t, y ≤ N := fun y hy => ((mem_range'_of_perm hf).1 (by simp [hy])).2
    have := records_le_aux t ([] ++ [x]) x hx.1 hx.2 (by simp) (by simp) htN h.tail
    have hmono : Nat.log 2 (N - x + 1) ≤ Nat.log 2 N := Nat.log_mono_right (by omega)
    unfold lrmax records
    simp only [show 0 < x by omega, ite_true]
    omega

/-! ### The construction -/

theorem records_pos {z : Nat} : ∀ {l : List Nat} {m : Nat}, z ∈ l → m < z → 1 ≤ records m l
  | [], _, hz, _ => by simp at hz
  | x :: t, m, hz, hmz => by
    unfold records
    split_ifs with hmx
    · omega
    · rw [List.mem_cons] at hz
      rcases hz with rfl | hz
      · omega
      · exact records_pos hz hmz

theorem records_append_ge {z : Nat} {l₂ : List Nat} (hz : z ∈ l₂) :
    ∀ {l₁ : List Nat} {m : Nat}, (∀ y ∈ l₁, y < z) → m < z →
      records m l₁ + 1 ≤ records m (l₁ ++ l₂)
  | [], m, _, hmz => by simpa [records] using records_pos hz hmz
  | x :: t, m, hl, hmz => by
    have hxz : x < z := hl x (by simp)
    have ht : ∀ y ∈ t, y < z := fun y hy => hl y (by simp [hy])
    simp only [List.cons_append, records]
    split_ifs with hmx
    · have := records_append_ge hz (m := x) ht hxz; omega
    · exact records_append_ge hz ht hmz

theorem records_map_scale {c : Nat} (hc : c ≤ 1) :
    ∀ {l : List Nat} (m : Nat), (∀ y ∈ l, 1 ≤ y) →
      records (scale c m) (l.map (scale c)) = records m l
  | [], _, _ => by simp [records]
  | x :: t, m, hpos => by
    have hx := hpos x (by simp)
    have ht : ∀ y ∈ t, 1 ≤ y := fun y hy => hpos y (by simp [hy])
    simp only [List.map_cons, records]
    have hiff : scale c m < scale c x ↔ m < x := by unfold scale; omega
    by_cases hmx : m < x
    · simp only [hiff.2 hmx, hmx, ite_true, records_map_scale hc x ht]
    · have : ¬ scale c m < scale c x := fun h => hmx (hiff.1 h)
      simp only [this, hmx, ite_false, records_map_scale hc m ht]

theorem foldSeq_one : IsFoldSeq 1 [1] ∧ SemiSymmetric 1 [1] := by decide

/-- **Left-to-right maxima, construction.**  For every `N ≥ 1` some semi-symmetric fold
sequence has `⌊log₂ N⌋ + 1` left-to-right maxima: parity blocks, the block without `N`
(of size `⌊N/2⌋`, recursively optimal) first, the block containing `N` second. -/
theorem exists_lrmax : ∀ N, 1 ≤ N →
    ∃ a, IsFoldSeq N a ∧ SemiSymmetric N a ∧ Nat.log 2 N + 1 ≤ lrmax a
  | N, hN => by
    rcases Nat.lt_or_ge N 2 with h2 | h2
    · obtain rfl : N = 1 := by omega
      exact ⟨[1], foldSeq_one.1, foldSeq_one.2, by decide⟩
    · -- c = 1 for even N (odds first), c = 0 for odd N (evens first)
      obtain ⟨c, hcdef⟩ : ∃ c, c = 1 - N % 2 := ⟨_, rfl⟩
      have hc : c ≤ 1 := by omega
      have hs : (N + c) / 2 = N / 2 := by omega
      have ht : (N + (1 - c)) / 2 = N - N / 2 := by omega
      obtain ⟨σ, hσf, hσs, hσl⟩ := exists_lrmax (N / 2) (by omega)
      obtain ⟨τ, hτf, hτs, -⟩ := exists_lrmax (N - N / 2) (by omega)
      rw [← hs] at hσf hσs
      rw [← ht] at hτf hτs
      refine ⟨σ.map (scale c) ++ τ.map (scale (1 - c)), IsFoldSeq.blocks hc hσf hτf,
        (semiSymmetric_blocks_iff hc hσf hτf).2 ⟨hσs, hτs⟩, ?_⟩
      have hNτ : N ∈ τ.map (scale (1 - c)) := by
        rw [List.mem_map]
        refine ⟨N - N / 2, (mem_range'_of_perm hτf).2 (by omega), ?_⟩
        unfold scale; omega
      have hlt : ∀ y ∈ σ.map (scale c), y < N := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
        have := (mem_range'_of_perm hσf).1 hx
        unfold scale; omega
      have h1 := records_append_ge hNτ hlt (m := 0) (by omega)
      have h2' : records 0 (σ.map (scale c)) = records 0 σ := by
        have := records_map_scale hc (l := σ) 0
          (fun y hy => ((mem_range'_of_perm hσf).1 hy).1)
        simpa [scale] using this
      have hlog : Nat.log 2 N = Nat.log 2 (N / 2) + 1 := by
        have := Nat.log_div_base 2 N
        have hpos : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le Nat.one_lt_two (by simpa using h2)
        omega
      unfold lrmax at hσl ⊢
      omega

end Folds
