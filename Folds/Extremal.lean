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
* `exists_free` / `max_free`: for `N ≥ 2` the bound is attained by a semi-symmetric
  sequence, so the maximum is exactly `Fbound N`.  Odd `N`: parity blocks; even `N`:
  shifted parity blocks (`shifted_blocks`), whose first block `X = shX` is a copy of the
  `(n-1)`-world, balanced around the second block except for one twisted middle step
  (`X_balance`).
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

/-! ## Free steps -/

/-- A free step: no earlier panel lies in the window of `m`. -/
def FreeStep (N : Nat) (S : List Nat) (m : Nat) : Prop :=
  ∀ d ∈ List.range' 1 (reach N m), m - d ∉ S ∧ m + d ∉ S

instance (N : Nat) (S : List Nat) (m : Nat) : Decidable (FreeStep N S m) :=
  inferInstanceAs (Decidable (∀ d ∈ _, _))

/-- Number of free steps of `l`, performed after the panels `S`. -/
def freeCount (N : Nat) : List Nat → List Nat → Nat
  | _, [] => 0
  | S, x :: t => (if FreeStep N S x then 1 else 0) + freeCount N (S ++ [x]) t

/-- Number of free steps of a fold sequence. -/
def numFree (N : Nat) (a : List Nat) : Nat := freeCount N [] a

theorem FreeStep.mono {N m : Nat} {S T : List Nat} (h : FreeStep N T m)
    (hST : ∀ x ∈ S, x ∈ T) : FreeStep N S m :=
  fun d hd => ⟨fun h1 => (h d hd).1 (hST _ h1), fun h1 => (h d hd).2 (hST _ h1)⟩

/-- An earlier panel `x` lies outside the window of a free panel `f`: on the left half
(`2f ≤ N + 1`) this means `x ≥ 2f`, on the right half `x ≤ 2f - N - 1`. -/
theorem FreeStep.far {N f x : Nat} {S : List Nat} (h : FreeStep N S f) (hx : x ∈ S)
    (hxf : x ≠ f) (hx1 : 1 ≤ x) (hxN : x ≤ N) (hf1 : 1 ≤ f) (hfN : f ≤ N) :
    (2 * f ≤ N + 1 → 2 * f ≤ x) ∧ (N + 1 < 2 * f → 2 * (N + 1 - f) ≤ N + 1 - x) := by
  have key : ∀ d, 1 ≤ d → d ≤ reach N f → f - d ≠ x ∧ f + d ≠ x := by
    intro d h1 h2
    have := h d (by rw [List.mem_range'_1]; omega)
    exact ⟨fun e => this.1 (e ▸ hx), fun e => this.2 (e ▸ hx)⟩
  have h1 : x < f → reach N f < f - x := fun hlt =>
    Nat.lt_of_not_le fun hr => (key (f - x) (by omega) hr).1 (by omega)
  have h2 : f < x → reach N f < x - f := fun hgt =>
    Nat.lt_of_not_le fun hr => (key (x - f) (by omega) hr).2 (by omega)
  unfold reach at h1 h2
  constructor <;> intro <;> omega

/-- `hgt A = ⌊log₂ A⌋ + 1` for `A ≥ 1` and `hgt 0 = 0`: the longest chain
`A ≥ f₁ ≥ 2f₂, f₂ ≥ 2f₃, …` of positive integers has `hgt A` terms. -/
def hgt (A : Nat) : Nat := Nat.log 2 (2 * A)

theorem hgt_mono {A B : Nat} (h : A ≤ B) : hgt A ≤ hgt B :=
  Nat.log_mono_right (by omega)

theorem hgt_of_pos {x : Nat} (hx : 1 ≤ x) : hgt x = Nat.log 2 x + 1 :=
  log_two_mul (by omega)

theorem hgt_half {x : Nat} (hx : 1 ≤ x) : hgt (x / 2) + 1 ≤ hgt x := by
  rcases Nat.eq_zero_or_pos (x / 2) with h0 | hpos
  · rw [h0, hgt_of_pos hx]; simp [hgt]
  · rw [hgt_of_pos hpos, hgt_of_pos hx]
    have := Nat.log_div_base 2 x
    have : 1 ≤ Nat.log 2 x := Nat.le_log_of_pow_le Nat.one_lt_two (by simp; omega)
    omega

/-- **Potential bound.**  If every free panel of `l` on the left half is at most `A` and
every free panel on the right half has mirror image `N + 1 - f ≤ B`, then `l` has at most
`hgt A + hgt B` free steps. -/
theorem freeCount_le {N : Nat} : ∀ (l S : List Nat) (A B : Nat),
    (S ++ l).Nodup → (∀ x ∈ S ++ l, 1 ≤ x ∧ x ≤ N) →
    (∀ f ∈ l, 2 * f ≤ N + 1 → FreeStep N S f → f ≤ A) →
    (∀ f ∈ l, N + 1 < 2 * f → FreeStep N S f → N + 1 - f ≤ B) →
    freeCount N S l ≤ hgt A + hgt B
  | [], _, _, _, _, _, _, _ => by simp [freeCount]
  | x :: t, S, A, B, hnd, hb, hA, hB => by
    have hnd' : (S ++ [x] ++ t).Nodup := by simpa using hnd
    have hb' : ∀ y ∈ S ++ [x] ++ t, 1 ≤ y ∧ y ≤ N := fun y hy => hb y (by simpa using hy)
    have hxt : ∀ f ∈ t, x ≠ f := by
      intro f hf e; subst e
      rw [List.nodup_append] at hnd
      have := hnd.2.1; rw [List.nodup_cons] at this; exact this.1 hf
    have hx := hb x (by simp)
    have hbt : ∀ f ∈ t, 1 ≤ f ∧ f ≤ N := fun f hf => hb f (by simp [hf])
    have hsub : ∀ y ∈ S, y ∈ S ++ [x] := fun y hy => by simp [hy]
    unfold freeCount
    by_cases hfx : FreeStep N S x
    · simp only [hfx, ite_true]
      rcases Nat.lt_or_ge (N + 1) (2 * x) with hr | hl
      · have hxB : N + 1 - x ≤ B := hB x (by simp) hr hfx
        have ih := freeCount_le t (S ++ [x]) A ((N + 1 - x) / 2) hnd' hb'
          (fun f hf hfl hff => hA f (by simp [hf]) hfl (hff.mono hsub))
          (fun f hf hfr hff => by
            have := (hff.far (x := x) (by simp) (hxt f hf) hx.1 hx.2 (hbt f hf).1
              (hbt f hf).2).2 hfr
            omega)
        have := hgt_half (x := N + 1 - x) (by omega)
        have := hgt_mono hxB
        omega
      · have hxA : x ≤ A := hA x (by simp) hl hfx
        have ih := freeCount_le t (S ++ [x]) (x / 2) B hnd' hb'
          (fun f hf hfl hff => by
            have := (hff.far (x := x) (by simp) (hxt f hf) hx.1 hx.2 (hbt f hf).1
              (hbt f hf).2).1 hfl
            omega)
          (fun f hf hfr hff => hB f (by simp [hf]) hfr (hff.mono hsub))
        have := hgt_half hx.1
        have := hgt_mono hxA
        omega
    · simp only [hfx, ite_false, Nat.zero_add]
      exact freeCount_le t (S ++ [x]) A B hnd' hb'
        (fun f hf hfl hff => hA f (by simp [hf]) hfl (hff.mono hsub))
        (fun f hf hfr hff => hB f (by simp [hf]) hfr (hff.mono hsub))

theorem log_le_of_pow_le {u M : Nat} (h : 2 ^ u ≤ M) : u ≤ Nat.log 2 M :=
  Nat.le_log_of_pow_le Nat.one_lt_two h

/-- `2^u + 2^v ≤ M` forces `u + v ≤ ⌊log₂ M⌋ + ⌊log₂ (M/3)⌋`. -/
theorem pow_add_pow_le_aux {u v M : Nat} (hvu : v ≤ u) (h : 2 ^ u + 2 ^ v ≤ M) :
    u + v ≤ Nat.log 2 M + Nat.log 2 (M / 3) := by
  rcases Nat.eq_or_lt_of_le hvu with e | hlt
  · subst e
    rcases Nat.eq_zero_or_pos v with h0 | hpos
    · subst h0; simp
    · obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      have e1 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
      have hu : 2 ^ (w + 2) ≤ M := by rw [Nat.pow_succ]; omega
      have hv : 2 ^ w ≤ M / 3 := by rw [Nat.le_div_iff_mul_le (by decide)]; omega
      have := log_le_of_pow_le hu
      have := log_le_of_pow_le hv
      omega
  · have hpow : 2 ^ (v + 1) ≤ 2 ^ u := Nat.pow_le_pow_right (by decide) hlt
    have e1 : 2 ^ (v + 1) = 2 * 2 ^ v := by rw [Nat.pow_succ, Nat.mul_comm]
    have hu : 2 ^ u ≤ M := by omega
    have hv : 2 ^ v ≤ M / 3 := by rw [Nat.le_div_iff_mul_le (by decide)]; omega
    have := log_le_of_pow_le hu
    have := log_le_of_pow_le hv
    omega

theorem pow_add_pow_le {u v M : Nat} (h : 2 ^ u + 2 ^ v ≤ M) :
    u + v ≤ Nat.log 2 M + Nat.log 2 (M / 3) := by
  rcases Nat.le_total v u with hvu | huv
  · exact pow_add_pow_le_aux hvu h
  · rw [Nat.add_comm u v]; exact pow_add_pow_le_aux huv (by omega)

/-- After a first panel `x`, at most `hgt x + hgt ((N + 1 - x) / 2)` steps are free. -/
theorem hgt_first_le {N x : Nat} (hx1 : 1 ≤ x) (hxN : x ≤ N) :
    hgt x + hgt ((N + 1 - x) / 2) ≤ Nat.log 2 (N + 1) + Nat.log 2 ((N + 1) / 3) + 1 := by
  rw [hgt_of_pos hx1]
  have hux : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 (by omega)
  rcases Nat.eq_zero_or_pos ((N + 1 - x) / 2) with h0 | hpos
  · rw [h0]
    have : Nat.log 2 x ≤ Nat.log 2 (N + 1) := Nat.log_mono_right (by omega)
    simp [hgt]; omega
  · rw [hgt_of_pos hpos]
    have hy : 2 ^ Nat.log 2 ((N + 1 - x) / 2) ≤ (N + 1 - x) / 2 :=
      Nat.pow_log_le_self 2 (by omega)
    have e1 : 2 ^ (Nat.log 2 ((N + 1 - x) / 2) + 1) = 2 * 2 ^ Nat.log 2 ((N + 1 - x) / 2) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have := pow_add_pow_le (u := Nat.log 2 x) (v := Nat.log 2 ((N + 1 - x) / 2) + 1)
      (M := N + 1) (by omega)
    omega

/-- **Free steps.**  Every fold sequence of length `N` (valid or not) has at most
`⌊log₂(N+1)⌋ + ⌊log₂((N+1)/3)⌋ + 1` free steps.  (For `N ≥ 2` this is attained by
semi-symmetric sequences; see `PROOFS.txt`.) -/
theorem numFree_le {N : Nat} {a : List Nat} (hf : IsFoldSeq N a) :
    numFree N a ≤ Nat.log 2 (N + 1) + Nat.log 2 ((N + 1) / 3) + 1 := by
  match a, hf with
  | [], _ => simp [numFree, freeCount]
  | x :: t, hf =>
    have hnd := nodup_of_foldSeq hf
    have hb : ∀ y ∈ [x] ++ t, 1 ≤ y ∧ y ≤ N := fun y hy =>
      (mem_range'_of_perm hf).1 (by simpa using hy)
    have hx := hb x (by simp)
    have hxt : ∀ f ∈ t, x ≠ f := by
      intro f hf e; subst e; rw [List.nodup_cons] at hnd; exact hnd.1 hf
    have hbt : ∀ f ∈ t, 1 ≤ f ∧ f ≤ N := fun f hf => hb f (by simp [hf])
    have key := freeCount_le t [x] (x / 2) ((N + 1 - x) / 2) (by simpa using hnd) hb
      (fun f hf hfl hff => by
        have := (hff.far (x := x) (by simp) (hxt f hf) hx.1 hx.2 (hbt f hf).1
          (hbt f hf).2).1 hfl
        omega)
      (fun f hf hfr hff => by
        have := (hff.far (x := x) (by simp) (hxt f hf) hx.1 hx.2 (hbt f hf).1
          (hbt f hf).2).2 hfr
        omega)
    have h1 := hgt_half hx.1
    have h2 := hgt_first_le hx.1 hx.2
    have h3 : (if FreeStep N [] x then 1 else 0) ≤ 1 := by split <;> omega
    unfold numFree freeCount
    simp only [List.nil_append] at key ⊢
    omega

/-! ## Free steps: the construction

`exists_free`: for every `N ≥ 2` some semi-symmetric fold sequence has exactly
`⌊log₂(N+1)⌋ + ⌊log₂((N+1)/3)⌋ + 1` free steps.  Odd `N`: parity blocks.  Even `N = 2n`:
*shifted* parity blocks, first `X = {2y + [y > n/2]}` (a copy of the `(n-1)`-world), then
`Y = {2y - 1 - [y > n/2 + 1]}` (a copy of the `(n+1)`-world, with one twisted middle step
when `n` is even). -/

theorem freeStep_iff_counts {N m : Nat} {S : List Nat} :
    FreeStep N S m ↔ leftCount N S m = 0 ∧ rightCount N S m = 0 := by
  unfold FreeStep leftCount rightCount
  simp only [List.countP_eq_zero, decide_eq_true_eq]
  constructor
  · intro h; exact ⟨fun d hd => (h d hd).1, fun d hd => (h d hd).2⟩
  · intro h d hd; exact ⟨h.1 d hd, h.2 d hd⟩

theorem freeStep_of_reach_zero {N m : Nat} {S : List Nat} (h : reach N m = 0) :
    FreeStep N S m := by
  intro d hd; rw [h] at hd; simp at hd

theorem freeCount_append {N : Nat} : ∀ (A S B : List Nat),
    freeCount N S (A ++ B) = freeCount N S A + freeCount N (S ++ A) B
  | [], S, B => by simp [freeCount]
  | x :: t, S, B => by
    simp only [List.cons_append, freeCount]
    rw [freeCount_append t (S ++ [x]) B]
    simp only [List.append_assoc, List.singleton_append]
    omega

theorem freeCount_ge_countP {N : Nat} : ∀ (l S : List Nat),
    l.countP (fun m => decide (reach N m = 0)) ≤ freeCount N S l
  | [], _ => by simp [freeCount]
  | x :: t, S => by
    simp only [List.countP_cons, freeCount]
    have ih := freeCount_ge_countP (N := N) t (S ++ [x])
    by_cases h : reach N x = 0
    · simp only [h, freeStep_of_reach_zero h, decide_true, ite_true]; omega
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]; split <;> omega

theorem two_le_countP {l : List Nat} {p : Nat → Bool} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) (hpa : p a) (hpb : p b) : 2 ≤ l.countP p := by
  rw [List.countP_eq_length_filter]
  have hsub : [a, b] ⊆ l.filter p := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> simp [*]
  have := List.Nodup.length_le_of_subset (by simp [hab]) hsub
  simpa using this

/-- Panels `1` and `N` have reach `0`, so they are free whenever they are placed. -/
theorem two_le_freeCount {N : Nat} (hN : 2 ≤ N) {l S : List Nat} (h1 : 1 ∈ l) (hN' : N ∈ l) :
    2 ≤ freeCount N S l := by
  have := two_le_countP (p := fun m => decide (reach N m = 0)) h1 hN' (by omega)
    (by simp [reach]) (by simp [reach])
  exact Nat.le_trans this (freeCount_ge_countP l S)

/-! ### Transfer along window-preserving maps -/

theorem countP_map_congr {f : Nat → Nat} {T : List Nat} {p : Nat}
    {P : Nat → Prop} [DecidablePred P] {Q : Nat → Prop} [DecidablePred Q]
    (hT : ∀ z ∈ T, 1 ≤ z ∧ z ≤ p) (h : ∀ z, 1 ≤ z → z ≤ p → (P (f z) ↔ Q z)) :
    (T.map f).countP (fun x => decide (P x)) = T.countP (fun z => decide (Q z)) := by
  rw [List.countP_map]; apply List.countP_congr; intro z hz
  have := hT z hz
  simp only [Function.comp_apply, decide_eq_true_eq]; exact h z this.1 this.2

theorem nodup_of_map_right {f : Nat → Nat} {U T : List Nat} (hnd : (U ++ T.map f).Nodup) :
    T.Nodup :=
  List.Pairwise.of_map f (fun a b h e => h (by rw [e])) (List.nodup_append.1 hnd).2.1

/-- Left count after `U ++ T.map f`, when `f` maps the window of `y` (in the `p`-world)
onto the window of `f y` (in the `N`-world). -/
theorem leftCount_append_map {N p : Nat} {f : Nat → Nat} {U T : List Nat} {y : Nat}
    (hnd : (U ++ T.map f).Nodup) (hT : ∀ z ∈ T, 1 ≤ z ∧ z ≤ p)
    (hL : ∀ z, 1 ≤ z → z ≤ p →
      (f y - reach N (f y) ≤ f z ∧ f z < f y ↔ y - reach p y ≤ z ∧ z < y)) :
    leftCount N (U ++ T.map f) (f y) =
      U.countP (fun x => decide (f y - reach N (f y) ≤ x ∧ x < f y)) + leftCount p T y := by
  rw [leftCount_eq hnd, leftCount_eq (nodup_of_map_right hnd), List.countP_append,
    countP_map_congr hT hL]

theorem rightCount_append_map {N p : Nat} {f : Nat → Nat} {U T : List Nat} {y : Nat}
    (hnd : (U ++ T.map f).Nodup) (hT : ∀ z ∈ T, 1 ≤ z ∧ z ≤ p)
    (hR : ∀ z, 1 ≤ z → z ≤ p →
      (f y < f z ∧ f z ≤ f y + reach N (f y) ↔ y < z ∧ z ≤ y + reach p y)) :
    rightCount N (U ++ T.map f) (f y) =
      U.countP (fun x => decide (f y < x ∧ x ≤ f y + reach N (f y))) + rightCount p T y := by
  rw [rightCount_eq hnd, rightCount_eq (nodup_of_map_right hnd), List.countP_append,
    countP_map_congr hT hR]

/-- Window preservation of `f` at `y` (`p`-world into `N`-world). -/
def WinPres (N p : Nat) (f : Nat → Nat) (y : Nat) : Prop :=
  (∀ z, 1 ≤ z → z ≤ p →
      (f y - reach N (f y) ≤ f z ∧ f z < f y ↔ y - reach p y ≤ z ∧ z < y)) ∧
  (∀ z, 1 ≤ z → z ≤ p →
      (f y < f z ∧ f z ≤ f y + reach N (f y) ↔ y < z ∧ z ≤ y + reach p y))

theorem semiStep_map_iff {N p : Nat} {f : Nat → Nat} {T : List Nat} {y : Nat}
    (hnd : (T.map f).Nodup) (hT : ∀ z ∈ T, 1 ≤ z ∧ z ≤ p) (hw : WinPres N p f y) :
    SemiStep N (T.map f) (f y) ↔ SemiStep p T y := by
  have hnd' : ([] ++ T.map f).Nodup := by simpa using hnd
  have hl := leftCount_append_map hnd' hT hw.1
  have hr := rightCount_append_map hnd' hT hw.2
  simp only [List.nil_append, List.countP_nil, Nat.zero_add] at hl hr
  unfold SemiStep; rw [hl, hr]

theorem freeStep_map_iff {N p : Nat} {f : Nat → Nat} {T : List Nat} {y : Nat}
    (hnd : (T.map f).Nodup) (hT : ∀ z ∈ T, 1 ≤ z ∧ z ≤ p) (hw : WinPres N p f y) :
    FreeStep N (T.map f) (f y) ↔ FreeStep p T y := by
  have hnd' : ([] ++ T.map f).Nodup := by simpa using hnd
  have hl := leftCount_append_map hnd' hT hw.1
  have hr := rightCount_append_map hnd' hT hw.2
  simp only [List.nil_append, List.countP_nil, Nat.zero_add] at hl hr
  rw [freeStep_iff_counts, freeStep_iff_counts, hl, hr]

/-- A whole block placed on an empty strip through a window-preserving injective map. -/
theorem semiSymmetric_map_iff {N p : Nat} {f : Nat → Nat} {σ : List Nat}
    (hnd : (σ.map f).Nodup) (hσ : ∀ z ∈ σ, 1 ≤ z ∧ z ≤ p) (hw : ∀ y ∈ σ, WinPres N p f y) :
    SemiSymmetric N (σ.map f) ↔ SemiSymmetric p σ := by
  constructor
  · intro h k hk
    have := h k (by simpa using hk)
    rw [List.getElem_map, ← List.map_take] at this
    exact (semiStep_map_iff (by rw [List.map_take]; exact hnd.sublist (List.take_sublist _ _))
      (fun z hz => hσ z (List.mem_of_mem_take hz)) (hw _ (List.getElem_mem hk))).1 this
  · intro h k hk
    simp only [List.length_map] at hk
    rw [List.getElem_map, ← List.map_take]
    exact (semiStep_map_iff (by rw [List.map_take]; exact hnd.sublist (List.take_sublist _ _))
      (fun z hz => hσ z (List.mem_of_mem_take hz)) (hw _ (List.getElem_mem hk))).2 (h k hk)

theorem freeCount_map {N p : Nat} {f : Nat → Nat} : ∀ (l P : List Nat),
    ((P ++ l).map f).Nodup → (∀ z ∈ P ++ l, 1 ≤ z ∧ z ≤ p) → (∀ y ∈ l, WinPres N p f y) →
    freeCount N (P.map f) (l.map f) = freeCount p P l
  | [], _, _, _, _ => by simp [freeCount]
  | x :: t, P, hnd, hb, hw => by
    simp only [List.map_cons, freeCount]
    have hndP : (P.map f).Nodup := by
      rw [List.map_append] at hnd; exact (List.nodup_append.1 hnd).1
    have hfree := freeStep_map_iff (T := P) hndP (fun z hz => hb z (by simp [hz]))
      (hw x (by simp))
    have ih := freeCount_map t (P ++ [x]) (by simpa using hnd)
      (fun z hz => hb z (by simpa using hz)) (fun y hy => hw y (by simp [hy]))
    rw [List.map_append, List.map_singleton] at ih
    rw [ih]
    by_cases h : FreeStep p P x
    · simp [h, hfree.2 h]
    · have h' : ¬ FreeStep N (P.map f) (f x) := fun h' => h (hfree.1 h')
      simp [h, h']

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-! ### Shifted parity blocks -/

/-- `X`-panels: evens up to `2j`, then odds from `2j + 3`. -/
def shX (j y : Nat) : Nat := 2 * y + if j < y then 1 else 0

/-- `Y`-panels: odds up to `2j + 1`, then evens from `2j + 2`. -/
def shY (j y : Nat) : Nat := 2 * y - 1 - if j + 1 < y then 1 else 0

theorem winPres_shX {n y : Nat} (hn : 2 ≤ n) (hy1 : 1 ≤ y) (_hy : y ≤ n - 1) :
    WinPres (2 * n) (n - 1) (shX (n / 2)) y := by
  constructor <;> intro z hz1 hz <;> unfold shX reach <;> split_ifs <;> omega

theorem winPres_shY {n y : Nat} (hn : 2 ≤ n) (hy1 : 1 ≤ y) (_hy : y ≤ n + 1)
    (hmid : ¬ (n % 2 = 0 ∧ y = n / 2 + 1)) :
    WinPres (2 * n) (n + 1) (shY (n / 2)) y := by
  constructor <;> intro z hz1 hz <;> unfold shY reach <;> split_ifs <;> omega

/-- The twisted middle step (`n` even): the window of `n + 1` misses `Y`-panel `1`. -/
theorem twist_shY_left {n z : Nat} (hn : 2 ≤ n) (he : n % 2 = 0) (hz1 : 1 ≤ z) (hz : z ≤ n + 1) :
    (shY (n / 2) (n / 2 + 1) - reach (2 * n) (shY (n / 2) (n / 2 + 1)) ≤ shY (n / 2) z ∧
        shY (n / 2) z < shY (n / 2) (n / 2 + 1)) ↔ 2 ≤ z ∧ z < n / 2 + 1 := by
  unfold shY reach; split_ifs <;> omega

theorem twist_shY_right {n z : Nat} (hn : 2 ≤ n) (he : n % 2 = 0) (hz1 : 1 ≤ z) (hz : z ≤ n + 1) :
    (shY (n / 2) (n / 2 + 1) < shY (n / 2) z ∧
        shY (n / 2) z ≤ shY (n / 2) (n / 2 + 1) + reach (2 * n) (shY (n / 2) (n / 2 + 1))) ↔
      n / 2 + 1 < z ∧ z ≤ n / 2 + 1 + reach (n + 1) (n / 2 + 1) := by
  unfold shY reach; split_ifs <;> omega

theorem countP_range'_interval_from (A B s : Nat) (hs : 1 ≤ s) :
    ∀ n, (List.range' s n).countP (fun y => decide (A ≤ y ∧ y ≤ B)) =
      min B (s + n - 1) + 1 - max A s
  | 0 => by simp; omega
  | n + 1 => by
    rw [List.range'_concat, List.countP_append, countP_range'_interval_from A B s hs n]
    simp only [List.countP_cons, List.countP_nil]
    by_cases h : A ≤ s + n ∧ s + n ≤ B
    · simp [h]; omega
    · simp [h]; omega

/-- The canonical `X` list for `N = 2n`. -/
def Xl (n : Nat) : List Nat := (List.range' 1 (n - 1)).map (shX (n / 2))

theorem countP_eq_interval {n : Nat} {p : Nat → Bool} {A B : Nat}
    (h : ∀ z, 1 ≤ z → z ≤ n → (p z = true ↔ A ≤ z ∧ z ≤ B)) :
    (List.range' 1 n).countP p = min B n + 1 - max A 1 := by
  rw [← countP_range'_interval A B n]
  apply List.countP_congr; intro z hz; rw [List.mem_range'_1] at hz
  rw [h z (by omega) (by omega)]; simp

/-- **Balance of `X`** around every `Y`-panel, except the twisted middle one (`n` even),
which sees one more `X`-panel on its left. -/
theorem X_balance {n y m : Nat} (hn : 2 ≤ n) (hy1 : 1 ≤ y) (hy : y ≤ n + 1)
    (hm : m = shY (n / 2) y) :
    (Xl n).countP (fun x => decide (m - reach (2 * n) m ≤ x ∧ x < m)) =
      (Xl n).countP (fun x => decide (m < x ∧ x ≤ m + reach (2 * n) m)) +
        (if n % 2 = 0 ∧ y = n / 2 + 1 then 1 else 0) := by
  unfold Xl
  rw [List.countP_map, List.countP_map]
  subst hm
  obtain ⟨j, hj⟩ : ∃ j, j = n / 2 := ⟨_, rfl⟩
  rw [← hj]
  have hn2 : n = 2 * j ∨ n = 2 * j + 1 := by omega
  rcases Nat.lt_or_ge (j + 1) y with h | h
  · have hm' : shY j y = 2 * y - 2 := by unfold shY; rw [ite_pos' h]; omega
    have hr : reach (2 * n) (2 * y - 2) = 2 * n - (2 * y - 2) := by unfold reach; omega
    rw [hm', hr, ite_neg' (by omega), countP_eq_interval (A := 2 * y - 2 - n) (B := y - 2),
      countP_eq_interval (A := y - 1) (B := n - 1)]
    · omega
    all_goals
      intro z hz1 hz
      simp only [Function.comp_apply, decide_eq_true_eq]
      unfold shX; split_ifs <;> omega
  · have hm' : shY j y = 2 * y - 1 := by unfold shY; rw [ite_neg' (by omega)]; omega
    rw [hm']
    by_cases ht : n % 2 = 0 ∧ y = j + 1
    · rw [ite_pos' ht]
      obtain ⟨rfl, rfl⟩ : n = 2 * j ∧ y = j + 1 := ⟨by omega, ht.2⟩
      have hr : reach (2 * (2 * j)) (2 * (j + 1) - 1) = 2 * j - 1 := by unfold reach; omega
      rw [hr, countP_eq_interval (A := 1) (B := j), countP_eq_interval (A := j + 1) (B := 2 * j - 1)]
      · omega
      all_goals
        intro z hz1 hz
        simp only [Function.comp_apply, decide_eq_true_eq]
        unfold shX; split_ifs <;> omega
    · rw [ite_neg' ht]
      have hr : reach (2 * n) (2 * y - 1) = 2 * y - 2 := by unfold reach; omega
      rw [hr, countP_eq_interval (A := 1) (B := y - 1), countP_eq_interval (A := y) (B := 2 * y - 2)]
      · omega
      all_goals
        intro z hz1 hz
        simp only [Function.comp_apply, decide_eq_true_eq]
        unfold shX; split_ifs <;> omega

theorem shX_bounds {n y : Nat} (hy1 : 1 ≤ y) (hy : y ≤ n - 1) :
    1 ≤ shX (n / 2) y ∧ shX (n / 2) y ≤ 2 * n := by
  unfold shX; split_ifs <;> omega

theorem shY_bounds {n y : Nat} (hn : 2 ≤ n) (hy1 : 1 ≤ y) (hy : y ≤ n + 1) :
    1 ≤ shY (n / 2) y ∧ shY (n / 2) y ≤ 2 * n := by
  unfold shY; split_ifs <;> omega

theorem shX_inj {j a b : Nat} (h : shX j a = shX j b) : a = b := by
  unfold shX at h; split_ifs at h <;> omega

theorem shY_inj {j a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : shY j a = shY j b) : a = b := by
  unfold shY at h; split_ifs at h <;> omega

theorem shX_ne_shY {j a b : Nat} (hb : 1 ≤ b) : shX j a ≠ shY j b := by
  unfold shX shY; split_ifs <;> omega

theorem perm_Xl {n : Nat} {σ : List Nat} (hσ : IsFoldSeq (n - 1) σ) :
    (σ.map (shX (n / 2))).Perm (Xl n) :=
  hσ.map _

/-- In a nodup list containing distinct `a` and `b`, either `a` comes before `b`, or it does
in the reversed list. -/
theorem before_or_reverse_before {l : List Nat} (hnd : l.Nodup) {a b : Nat} (ha : a ∈ l)
    (hb : b ∈ l) (hab : a ≠ b) :
    (∀ k (hk : k < l.length), l[k] = b → a ∈ l.take k) ∨
      (∀ k (hk : k < l.reverse.length), l.reverse[k] = b → a ∈ l.reverse.take k) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
  obtain ⟨i', hi', rfl⟩ := List.mem_iff_getElem.1 hb
  have hii : i ≠ i' := fun e => hab (by subst e; rfl)
  rcases Nat.lt_or_gt_of_ne hii with h | h
  · left
    intro k hk e
    have : k = i' := (List.Nodup.getElem_inj hnd).1 e
    rw [getElem_mem_take_iff hnd hi]; omega
  · right
    have hndr : l.reverse.Nodup := (List.reverse_perm l).nodup_iff.2 hnd
    intro k hk e
    rw [List.getElem_reverse] at e
    have hk' : k < l.length := by simpa using hk
    have : l.length - 1 - k = i' := (List.Nodup.getElem_inj hnd).1 e
    have hpos : l.length - 1 - i < l.reverse.length := by simp; omega
    have er : l.reverse[l.length - 1 - i] = l[i] := by
      rw [List.getElem_reverse]; congr 1; omega
    rw [← er, getElem_mem_take_iff hndr hpos]; omega

theorem countP_split_one {T : List Nat} (hnd : T.Nodup) (h1 : 1 ∈ T) (c : Nat) (hc : 1 < c) :
    T.countP (fun z => decide (1 ≤ z ∧ z < c)) = T.countP (fun z => decide (2 ≤ z ∧ z < c)) + 1 := by
  rw [countP_split T (fun z => decide (1 ≤ z ∧ z < c)) (fun z => decide (z = 1))]
  have e1 : T.countP (fun z => decide (1 ≤ z ∧ z < c) && decide (z = 1)) =
      T.countP (fun z => z = 1) := by
    apply List.countP_congr; intro z _; simp; omega
  have e2 : T.countP (fun z => decide (1 ≤ z ∧ z < c) && !decide (z = 1)) =
      T.countP (fun z => decide (2 ≤ z ∧ z < c)) := by
    apply List.countP_congr; intro z _; simp; omega
  rw [e1, e2, countP_eq_nodup hnd, ite_pos' h1]; omega

/-- **Shifted parity blocks** (`N = 2n`): `σ` (on `n - 1` panels) through `shX`, then `τ`
(on `n + 1` panels) through `shY`.  For even `n`, `τ` must place panel `1` before its middle
panel `n/2 + 1`.  The result is semi-symmetric and has at least two more free steps than
`σ` (panels `1` and `2n`). -/
theorem shifted_blocks {n : Nat} (hn : 2 ≤ n) {σ τ : List Nat}
    (hσ : IsFoldSeq (n - 1) σ) (hσs : SemiSymmetric (n - 1) σ)
    (hτ : IsFoldSeq (n + 1) τ) (hτs : SemiSymmetric (n + 1) τ)
    (hmid : n % 2 = 0 → ∀ k (hk : k < τ.length), τ[k] = n / 2 + 1 → 1 ∈ τ.take k) :
    IsFoldSeq (2 * n) (σ.map (shX (n / 2)) ++ τ.map (shY (n / 2))) ∧
      SemiSymmetric (2 * n) (σ.map (shX (n / 2)) ++ τ.map (shY (n / 2))) ∧
      numFree (n - 1) σ + 2 ≤ numFree (2 * n) (σ.map (shX (n / 2)) ++ τ.map (shY (n / 2))) := by
  have bσ : ∀ z ∈ σ, 1 ≤ z ∧ z ≤ n - 1 := fun z hz => (mem_range'_of_perm hσ).1 hz
  have bτ : ∀ z ∈ τ, 1 ≤ z ∧ z ≤ n + 1 := fun z hz => (mem_range'_of_perm hτ).1 hz
  have hndσ := nodup_of_foldSeq hσ
  have hndτ := nodup_of_foldSeq hτ
  have hndA : (σ.map (shX (n / 2))).Nodup :=
    nodup_map_of_injOn hndσ fun a _ b _ e => shX_inj e
  have hndB : (τ.map (shY (n / 2))).Nodup :=
    nodup_map_of_injOn hndτ fun a ha b hb e => shY_inj (bτ a ha).1 (bτ b hb).1 e
  have hnd : (σ.map (shX (n / 2)) ++ τ.map (shY (n / 2))).Nodup := by
    refine List.nodup_append.2 ⟨hndA, hndB, ?_⟩
    intro a ha b hb
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact shX_ne_shY (bτ y hy).1
  have hbnd : ∀ x ∈ σ.map (shX (n / 2)) ++ τ.map (shY (n / 2)), 1 ≤ x ∧ x ≤ 2 * n := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact shX_bounds (bσ y hy).1 (bσ y hy).2
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact shY_bounds hn (bτ y hy).1 (bτ y hy).2
  have hlen : (σ.map (shX (n / 2)) ++ τ.map (shY (n / 2))).length = 2 * n := by
    simp [hσ.length_eq, hτ.length_eq]; omega
  have hfold : IsFoldSeq (2 * n) (σ.map (shX (n / 2)) ++ τ.map (shY (n / 2))) :=
    perm_range'_of_nodup_subset hnd hbnd hlen
  refine ⟨hfold, ?_, ?_⟩
  · rw [semiSymmetric_append_iff]
    refine ⟨(semiSymmetric_map_iff hndA bσ fun y hy =>
      winPres_shX hn (bσ y hy).1 (bσ y hy).2).2 hσs, ?_⟩
    intro k hk
    have hk' : k < τ.length := by simpa using hk
    rw [List.getElem_map, ← List.map_take]
    have hndk : (σ.map (shX (n / 2)) ++ (τ.take k).map (shY (n / 2))).Nodup := by
      rw [List.map_take]
      exact hnd.sublist ((List.take_sublist _ _).append_left _)
    have hT : ∀ z ∈ τ.take k, 1 ≤ z ∧ z ≤ n + 1 := fun z hz => bτ z (List.mem_of_mem_take hz)
    have hy := bτ _ (List.getElem_mem hk')
    have hstep := hτs k hk'
    have hbal := X_balance hn hy.1 hy.2 rfl
    by_cases hm : n % 2 = 0 ∧ τ[k] = n / 2 + 1
    · -- the twisted middle step
      rw [ite_pos' hm] at hbal
      have h1 : 1 ∈ τ.take k := hmid hm.1 k hk' hm.2
      have hndT : (τ.take k).Nodup := take_nodup hndτ k
      unfold SemiStep at hstep ⊢
      rw [leftCount_eq hndk, rightCount_append_map hndk hT
        (by rw [hm.2]; intro z hz1 hz; exact twist_shY_right hn hm.1 hz1 hz),
        List.countP_append, (perm_Xl hσ).countP_eq, (perm_Xl hσ).countP_eq]
      rw [leftCount_eq hndT, rightCount_eq hndT] at hstep
      have hL : ((τ.take k).map (shY (n / 2))).countP (fun x => decide
          (shY (n / 2) τ[k] - reach (2 * n) (shY (n / 2) τ[k]) ≤ x ∧ x < shY (n / 2) τ[k])) =
          (τ.take k).countP (fun z => decide (2 ≤ z ∧ z < n / 2 + 1)) := by
        rw [hm.2]; exact countP_map_congr hT fun z hz1 hz => twist_shY_left hn hm.1 hz1 hz
      have hreach : τ[k] - reach (n + 1) τ[k] = 1 := by rw [hm.2]; unfold reach; omega
      rw [hreach, hm.2, countP_split_one hndT h1 _ (by omega)] at hstep
      rw [hL, rightCount_eq hndT]
      rw [hm.2] at hbal ⊢
      omega
    · rw [ite_neg' hm] at hbal
      have hw := winPres_shY hn hy.1 hy.2 hm
      unfold SemiStep at hstep ⊢
      rw [leftCount_append_map hndk hT hw.1, rightCount_append_map hndk hT hw.2, (perm_Xl hσ).countP_eq,
        (perm_Xl hσ).countP_eq]
      omega
  · unfold numFree
    rw [freeCount_append, List.nil_append]
    have h1 := freeCount_map (N := 2 * n) (p := n - 1) (f := shX (n / 2)) σ []
      (by simpa using hndA) (by simpa using bσ)
      (fun y hy => winPres_shX hn (bσ y hy).1 (bσ y hy).2)
    simp only [List.map_nil] at h1
    have h2 : 2 ≤ freeCount (2 * n) (σ.map (shX (n / 2))) (τ.map (shY (n / 2))) := by
      apply two_le_freeCount (by omega)
      · exact List.mem_map.2 ⟨1, (mem_range'_of_perm hτ).2 (by omega), by unfold shY; simp⟩
      · exact List.mem_map.2 ⟨n + 1, (mem_range'_of_perm hτ).2 (by omega), by
          unfold shY; rw [ite_pos' (by omega)]; omega⟩
    omega

/-! ### The free-step bound is attained -/

theorem winPres_scale0 {n y : Nat} (hy1 : 1 ≤ y) (hy : y ≤ n) :
    WinPres (2 * n + 1) n (scale 0) y := by
  constructor <;> intro z hz1 hz <;> unfold scale reach <;> omega

theorem log_two_eq_half {m : Nat} (hm : 2 ≤ m) : Nat.log 2 m = Nat.log 2 (m / 2) + 1 := by
  have := Nat.log_div_base 2 m
  have : 1 ≤ Nat.log 2 m := Nat.le_log_of_pow_le Nat.one_lt_two (by simpa using hm)
  omega

/-- `F(N) = ⌊log₂(N+1)⌋ + ⌊log₂((N+1)/3)⌋ + 1`. -/
def Fbound (N : Nat) : Nat := Nat.log 2 (N + 1) + Nat.log 2 ((N + 1) / 3) + 1

theorem Fbound_odd {m : Nat} (hm : 2 ≤ m) : Fbound (2 * m + 1) = Fbound m + 2 := by
  unfold Fbound
  rw [log_two_eq_half (m := 2 * m + 1 + 1) (by omega),
    log_two_eq_half (m := (2 * m + 1 + 1) / 3) (by omega)]
  have e1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  have e2 : (2 * m + 1 + 1) / 3 / 2 = (m + 1) / 3 := by omega
  rw [e1, e2]; omega

theorem log_pair_odd {K : Nat} (hK : 5 ≤ K) (ho : K % 2 = 1) :
    Nat.log 2 K + Nat.log 2 (K / 3) = Nat.log 2 (K - 1) + Nat.log 2 ((K - 1) / 3) := by
  rw [log_two_eq_half (m := K) (by omega), log_two_eq_half (m := K - 1) (by omega)]
  have e1 : K / 2 = (K - 1) / 2 := by omega
  rw [e1]
  by_cases h : K / 3 = (K - 1) / 3
  · rw [h]
  · obtain ⟨q, rfl⟩ : ∃ q, K = 6 * q + 3 := ⟨K / 6, by omega⟩
    have e3 : (6 * q + 3) / 3 = 2 * q + 1 := by omega
    have e4 : (6 * q + 3 - 1) / 3 = 2 * q := by omega
    rw [e3, e4, log_two_eq_half (m := 2 * q + 1) (by omega), log_two_eq_half (m := 2 * q) (by omega)]
    have e5 : (2 * q + 1) / 2 = 2 * q / 2 := by omega
    rw [e5]

theorem Fbound_even {M : Nat} (hM : 4 ≤ M) (he : M % 2 = 0) : Fbound M = Fbound (M - 1) := by
  unfold Fbound
  have e0 : M - 1 + 1 = M := by omega
  have := log_pair_odd (K := M + 1) (by omega) (by omega)
  rw [e0]
  simp only [Nat.add_sub_cancel] at this
  omega

theorem Fbound_small : Fbound 2 = 2 ∧ Fbound 3 = 3 ∧ Fbound 4 = 3 := by
  have l1 : Nat.log 2 1 = 0 := Nat.log_one_right 2
  have l3 : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  have l4 : Nat.log 2 4 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  have l5 : Nat.log 2 5 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  unfold Fbound
  simp only [show (2 + 1) / 3 = 1 by decide, show 2 + 1 = 3 by decide, show 3 + 1 = 4 by decide,
    show 4 + 1 = 5 by decide, l1, l3, l4, l5]
  decide

/-- **Free steps, construction.**  For every `N ≥ 2` some semi-symmetric fold sequence has
at least (hence, by `numFree_le`, exactly) `⌊log₂(N+1)⌋ + ⌊log₂((N+1)/3)⌋ + 1` free steps. -/
theorem exists_free : ∀ N, 2 ≤ N →
    ∃ a, IsFoldSeq N a ∧ SemiSymmetric N a ∧ Fbound N ≤ numFree N a
  | N, hN => by
    rcases (show N = 2 ∨ N = 3 ∨ 4 ≤ N by omega) with rfl | rfl | h4
    · exact ⟨[1, 2], by decide, by decide, by rw [Fbound_small.1]; decide⟩
    · exact ⟨[2, 3, 1], by decide, by decide, by rw [Fbound_small.2.1]; decide⟩
    · obtain ⟨m, hm⟩ : ∃ m, N = 2 * m ∨ N = 2 * m + 1 := ⟨N / 2, by omega⟩
      rcases hm with rfl | rfl
      · -- N = 2m: shifted parity blocks
        obtain ⟨σ, hσ, hσs, hσf⟩ : ∃ σ, IsFoldSeq (m - 1) σ ∧ SemiSymmetric (m - 1) σ ∧
            Fbound (2 * m) ≤ numFree (m - 1) σ + 2 := by
          rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | h3
          · exact ⟨[1], by decide, by decide, by rw [Fbound_small.2.2]; decide⟩
          · obtain ⟨σ, hσ, hσs, hσf⟩ := exists_free (m - 1) (by omega)
            refine ⟨σ, hσ, hσs, ?_⟩
            have h1 := Fbound_even (M := 2 * m) (by omega) (by omega)
            have h2 := Fbound_odd (m := m - 1) (by omega)
            rw [show 2 * (m - 1) + 1 = 2 * m - 1 by omega] at h2
            omega
        obtain ⟨τ0, hτ0, hτ0s, -⟩ := exists_lrmax (m + 1) (by omega)
        obtain ⟨τ, hτ, hτs, hmid⟩ : ∃ τ, IsFoldSeq (m + 1) τ ∧ SemiSymmetric (m + 1) τ ∧
            (∀ k (hk : k < τ.length), τ[k] = m / 2 + 1 → 1 ∈ τ.take k) := by
          rcases before_or_reverse_before (nodup_of_foldSeq hτ0) (a := 1) (b := m / 2 + 1)
            ((mem_range'_of_perm hτ0).2 (by omega)) ((mem_range'_of_perm hτ0).2 (by omega))
            (by omega) with h | h
          · exact ⟨τ0, hτ0, hτ0s, h⟩
          · exact ⟨τ0.reverse, (List.reverse_perm τ0).trans hτ0,
              SemiSymmetric.reverse hτ0 hτ0s, h⟩
        obtain ⟨hf, hs, hfr⟩ := shifted_blocks (n := m) (by omega) hσ hσs hτ hτs (fun _ => hmid)
        exact ⟨_, hf, hs, by omega⟩
      · -- N = 2m + 1: parity blocks, evens first
        obtain ⟨σ, hσ, hσs, hσf⟩ := exists_free m (by omega)
        obtain ⟨τ, hτ, hτs, -⟩ := exists_lrmax (m + 1) (by omega)
        have e1 : (2 * m + 1 + 0) / 2 = m := by omega
        have e2 : (2 * m + 1 + (1 - 0)) / 2 = m + 1 := by omega
        have hσ' : IsFoldSeq ((2 * m + 1 + 0) / 2) σ := by rwa [e1]
        have hτ' : IsFoldSeq ((2 * m + 1 + (1 - 0)) / 2) τ := by rwa [e2]
        refine ⟨σ.map (scale 0) ++ τ.map (scale (1 - 0)), IsFoldSeq.blocks (by omega) hσ' hτ',
          (semiSymmetric_blocks_iff (by omega) hσ' hτ').2 ⟨by rwa [e1], by rwa [e2]⟩, ?_⟩
        have bσ : ∀ z ∈ σ, 1 ≤ z ∧ z ≤ m := fun z hz => (mem_range'_of_perm hσ).1 hz
        have hndA : (σ.map (scale 0)).Nodup :=
          nodup_map_of_injOn (nodup_of_foldSeq hσ) fun _ _ _ _ e => scale_inj (by omega) e
        unfold numFree
        rw [freeCount_append, List.nil_append]
        have h1 := freeCount_map (N := 2 * m + 1) (p := m) (f := scale 0) σ []
          (by simpa using hndA) (by simpa using bσ)
          (fun y hy => winPres_scale0 (bσ y hy).1 (bσ y hy).2)
        simp only [List.map_nil] at h1
        have h2 : 2 ≤ freeCount (2 * m + 1) (σ.map (scale 0)) (τ.map (scale (1 - 0))) := by
          apply two_le_freeCount (by omega)
          · exact List.mem_map.2 ⟨1, (mem_range'_of_perm hτ).2 (by omega), by unfold scale; omega⟩
          · exact List.mem_map.2 ⟨m + 1, (mem_range'_of_perm hτ).2 (by omega),
              by unfold scale; omega⟩
        have h3 := Fbound_odd (m := m) (by omega)
        unfold numFree at hσf
        omega

/-- **Maximum number of free steps.**  For `N ≥ 2`, the maximum over semi-symmetric fold
sequences of the number of free steps is exactly `⌊log₂(N+1)⌋ + ⌊log₂((N+1)/3)⌋ + 1`. -/
theorem max_free {N : Nat} (hN : 2 ≤ N) :
    (∃ a, IsFoldSeq N a ∧ SemiSymmetric N a ∧ numFree N a = Fbound N) ∧
      ∀ a, IsFoldSeq N a → numFree N a ≤ Fbound N := by
  refine ⟨?_, fun a hf => numFree_le hf⟩
  obtain ⟨a, hf, hs, h⟩ := exists_free N hN
  exact ⟨a, hf, hs, Nat.le_antisymm (numFree_le hf) h⟩

end Folds
