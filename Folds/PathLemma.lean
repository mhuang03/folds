import Folds.Upper
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The Path Lemma reduction

See `experiments/pathlemma/PROOFS.txt`.

For a prefix `p` (a list of panels) let `V_k = |moves N (p.take k)|` be the number of valid
next panels after the first `k` panels, and let the *path product* be
`pathProd N p = ∏_{k < |p|} V_k`.  For a full valid sequence `a` of `[1..N]` the
*path deficit* is
`pathDeficit N a = ∑_{k < N} ln ((N - k) / V_k)`,
so that `pathProd N a = N! · exp (-pathDeficit N a)` (`pathProd_eq_factorial_mul_exp`).

## 1. The path form of the tree bound

`semiCount_le_of_pathProd_le`: if every valid sequence has path product at most `B`, then
`a(N) ≤ B`.  Proof: a uniformly random descent in the tree of valid prefixes reaches a given
leaf `a` with probability `1 / pathProd N a`, and distinct leaves are disjoint events, so
`∑_{a} 1 / pathProd N a ≤ 1` (`sum_inv_pathProd_le`).

Consequences:
* `semiCount_le_of_deficit_ge`: if every valid sequence has `pathDeficit ≥ D`, then
  `a(N) ≤ N! · e^{-D}`;
* `PathLemma` (the conjecture: the minimal deficit is `ω(N)`) implies
  `a(N) ≤ N! · e^{-c N}` eventually, for every `c` (`PathLemma.eventually_le`), i.e.
  `a(N) = N! · e^{-ω(N)}`.

## 2. Local structure of the cyclic defect

`cycDefect_succ`: `I(m+1) - I(m) = [2m ∈ S] + [2m+1 ∈ S] - 2 [m ∈ S]` (panels mod `N`).
Hence `I` is non-decreasing across free panels (`cycDefect_mono_of_free`), and two consecutive
free valid panels `m, m+1` force both panels `2m, 2m+1` (mod `N`) to be free
(`consecutive_valid`).  Two zeros `y < y'` of `I` satisfy the doubling relation
`P̃(2y'-1) - P̃(2y-1) = 2 (P(y'-1) - P(y-1))` (`doubling_of_zeros`).
-/

namespace Folds

open Finset

/-! ## 1. Path products -/

/-- The product of the numbers of valid moves along the prefix `p`. -/
def pathProd (N : Nat) (p : List Nat) : Nat :=
  ∏ i ∈ Finset.range p.length, (moves N (p.take i)).card

theorem pathProd_append (N : Nat) (p : List Nat) (m : Nat) :
    pathProd N (p ++ [m]) = pathProd N p * (moves N p).card := by
  unfold pathProd
  rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length le_rfl, List.take_length]

theorem pathProd_pos (N : Nat) : ∀ k, ∀ p ∈ prefixes N k, 0 < pathProd N p
  | 0, p, hp => by
    simp only [prefixes, Finset.mem_singleton] at hp; subst hp; simp [pathProd]
  | k + 1, p, hp => by
    simp only [prefixes, Finset.mem_biUnion, Finset.mem_image] at hp
    obtain ⟨q, hq, m, hm, rfl⟩ := hp
    rw [pathProd_append]
    exact Nat.mul_pos (pathProd_pos N k q hq) (Finset.card_pos.2 ⟨m, hm⟩)

/-- **Random descent.**  `∑_{p valid of length k} 1 / pathProd N p ≤ 1`. -/
theorem sum_inv_pathProd_le (N : Nat) :
    ∀ k, ∑ p ∈ prefixes N k, (1 : ℝ) / pathProd N p ≤ 1
  | 0 => by simp [prefixes, pathProd]
  | k + 1 => by
    have hdisj : (prefixes N k : Set (List Nat)).PairwiseDisjoint
        (fun p => (moves N p).image fun m => p ++ [m]) := by
      intro p hp p' hp' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro q hq hq'
      simp only [Finset.mem_image] at hq hq'
      obtain ⟨m, _, rfl⟩ := hq
      obtain ⟨m', _, e⟩ := hq'
      have l1 := (mem_prefixes (Finset.mem_coe.1 hp)).1
      have l2 := (mem_prefixes (Finset.mem_coe.1 hp')).1
      have := (List.append_inj e (by rw [l1, l2])).1
      exact hne this.symm
    rw [prefixes, Finset.sum_biUnion hdisj]
    calc ∑ p ∈ prefixes N k, ∑ q ∈ (moves N p).image (fun m => p ++ [m]),
          (1 : ℝ) / pathProd N q
        = ∑ p ∈ prefixes N k, ∑ _m ∈ moves N p,
          (1 : ℝ) / ((pathProd N p : ℝ) * (moves N p).card) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.sum_image (fun x _ y _ e => by simpa using e)]
          apply Finset.sum_congr rfl
          intro m _
          rw [pathProd_append]; push_cast; rfl
      _ ≤ ∑ p ∈ prefixes N k, (1 : ℝ) / pathProd N p := by
          apply Finset.sum_le_sum
          intro p _
          rw [Finset.sum_const, nsmul_eq_mul]
          rcases Nat.eq_zero_or_pos (moves N p).card with h0 | hpos
          · rw [h0]; simp
          · have hc : ((moves N p).card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
            rw [mul_one_div, mul_comm (pathProd N p : ℝ), ← div_div, div_self hc]
      _ ≤ 1 := sum_inv_pathProd_le N k

/-- A full-length valid prefix is a valid fold sequence. -/
theorem prefixes_subset_semiSeqs (N : Nat) : prefixes N N ⊆ semiSeqs N := by
  intro a ha
  obtain ⟨hl, hnd, hb, hs⟩ := mem_prefixes ha
  refine mem_semiSeqs.2 ⟨?_, hs⟩
  apply List.perm_of_nodup_nodup_toFinset_eq hnd List.nodup_range'
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [List.mem_toFinset] at hx ⊢
    rw [List.mem_range'_1]
    have := hb x hx; omega
  · rw [List.toFinset_card_of_nodup hnd, List.toFinset_card_of_nodup List.nodup_range',
      List.length_range', hl]

theorem semiSeqs_eq_prefixes (N : Nat) : semiSeqs N = prefixes N N := by
  apply Finset.Subset.antisymm _ (prefixes_subset_semiSeqs N)
  intro a ha
  have := take_mem_prefixes ha N le_rfl
  rw [mem_semiSeqs] at ha
  rwa [List.take_of_length_le (by rw [ha.1.length_eq]; simp)] at this

/-- **Path form of the tree bound** (real bound `B ≥ 0`). -/
theorem semiCount_le_of_pathProd_le_real (N : Nat) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ a ∈ semiSeqs N, (pathProd N a : ℝ) ≤ B) : (semiCount N : ℝ) ≤ B := by
  unfold semiCount
  rw [semiSeqs_eq_prefixes] at h ⊢
  rcases (prefixes N N).eq_empty_or_nonempty with he | ⟨a0, ha0⟩
  · rw [he]; simpa using hB
  have hBpos : 0 < B := lt_of_lt_of_le (by exact_mod_cast pathProd_pos N N a0 ha0) (h a0 ha0)
  have key : ∑ _a ∈ prefixes N N, (1 : ℝ) / B ≤ ∑ a ∈ prefixes N N, (1 : ℝ) / pathProd N a := by
    apply Finset.sum_le_sum
    intro a ha
    apply one_div_le_one_div_of_le (by exact_mod_cast pathProd_pos N N a ha) (h a ha)
  have := key.trans (sum_inv_pathProd_le N N)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div, div_le_one hBpos] at this
  exact this

/-- **Path form of the tree bound.**  If every valid fold sequence of `[1..N]` has path
product at most `B`, then `a(N) ≤ B`. -/
theorem semiCount_le_of_pathProd_le (N B : Nat) (h : ∀ a ∈ semiSeqs N, pathProd N a ≤ B) :
    semiCount N ≤ B := by
  have := semiCount_le_of_pathProd_le_real N B (by positivity)
    (fun a ha => by exact_mod_cast h a ha)
  exact_mod_cast this

/-! ### The deficit form -/

/-- The path deficit `∑_{k < N} ln ((N - k) / V_k)` of a sequence `a`. -/
noncomputable def pathDeficit (N : Nat) (a : List Nat) : ℝ :=
  ∑ k ∈ Finset.range N, Real.log (((N - k : Nat) : ℝ) / (moves N (a.take k)).card)

theorem prod_sub_eq_factorial (N : Nat) :
    ∏ k ∈ Finset.range N, ((N - k : Nat) : ℝ) = (N.factorial : ℝ) := by
  rw [← Finset.prod_range_reflect, ← Finset.prod_range_add_one_eq_factorial]
  push_cast
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have : N - (N - 1 - j) = j + 1 := by omega
  rw [this]; push_cast; ring

/-- Every valid sequence has `V_k ≥ 1` at every step `k < N`. -/
theorem card_moves_take_pos {N : Nat} {a : List Nat} (ha : a ∈ semiSeqs N) {k : Nat}
    (hk : k < N) : 0 < (moves N (a.take k)).card := by
  rw [semiSeqs_eq_prefixes] at ha
  have hpos := pathProd_pos N N a ha
  have hl := (mem_prefixes ha).1
  unfold pathProd at hpos
  rw [hl] at hpos
  exact Nat.pos_of_ne_zero
    ((Finset.prod_ne_zero_iff.1 hpos.ne') k (Finset.mem_range.2 hk))

/-- `pathProd N a = N! · exp (-pathDeficit N a)` for every valid sequence. -/
theorem pathProd_eq_factorial_mul_exp {N : Nat} {a : List Nat} (ha : a ∈ semiSeqs N) :
    (pathProd N a : ℝ) = N.factorial * Real.exp (-pathDeficit N a) := by
  have hl : a.length = N := by
    have := (mem_semiSeqs.1 ha).1.length_eq; simpa using this
  unfold pathDeficit
  rw [← Finset.sum_neg_distrib, Real.exp_sum, ← prod_sub_eq_factorial, ← Finset.prod_mul_distrib]
  unfold pathProd
  rw [hl]; push_cast
  apply Finset.prod_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hV : (0 : ℝ) < (moves N (a.take k)).card := by
    exact_mod_cast card_moves_take_pos ha hk
  have hN : (0 : ℝ) < ((N - k : Nat) : ℝ) := by
    have : 0 < N - k := by omega
    exact_mod_cast this
  rw [Real.exp_neg, Real.exp_log (div_pos hN hV)]
  field_simp

/-- **Deficit form of the tree bound.**  If every valid fold sequence has path deficit at
least `D`, then `a(N) ≤ N! · e^{-D}`. -/
theorem semiCount_le_of_deficit_ge (N : Nat) (D : ℝ)
    (h : ∀ a ∈ semiSeqs N, D ≤ pathDeficit N a) :
    (semiCount N : ℝ) ≤ N.factorial * Real.exp (-D) := by
  apply semiCount_le_of_pathProd_le_real N _ (by positivity)
  intro a ha
  rw [pathProd_eq_factorial_mul_exp ha]
  have : Real.exp (-pathDeficit N a) ≤ Real.exp (-D) := Real.exp_le_exp.2 (by linarith [h a ha])
  have hf : (0 : ℝ) ≤ N.factorial := by positivity
  exact mul_le_mul_of_nonneg_left this hf

/-- **The Path Lemma** (conjecture): some lower bound `D(N)` on the path deficit of every
valid fold sequence of `[1..N]` satisfies `D(N) / N → ∞`. -/
def PathLemma : Prop :=
  ∃ D : ℕ → ℝ, Filter.Tendsto (fun N => D N / N) Filter.atTop Filter.atTop ∧
    ∀ N, ∀ a ∈ semiSeqs N, D N ≤ pathDeficit N a

/-- **Path Lemma ⇒ `a(N) ≤ N! e^{-ω(N)}`.**  Under the Path Lemma, for every `c` we
eventually have `a(N) ≤ N! · e^{-c N}`. -/
theorem PathLemma.eventually_le (hP : PathLemma) (c : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, (semiCount N : ℝ) ≤ N.factorial * Real.exp (-(c * N)) := by
  obtain ⟨D, hD, hpath⟩ := hP
  filter_upwards [hD.eventually_ge_atTop c, Filter.eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcD : c * N ≤ D N := by rwa [le_div_iff₀ hNpos] at hN
  refine (semiCount_le_of_deficit_ge N (D N) (hpath N)).trans ?_
  have : Real.exp (-D N) ≤ Real.exp (-(c * N)) := Real.exp_le_exp.2 (by linarith)
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-! ### Linearisation (Jensen) -/

/-- **Linearisation.**  If the mean acceptance `(1/N) ∑_k V_k / (N - k)` of a valid sequence
is at most `ε`, then its deficit is at least `N ln (1/ε)`. -/
theorem pathDeficit_ge_of_mean_le {N : Nat} {a : List Nat} (ha : a ∈ semiSeqs N) {ε : ℝ}
    (hε : 0 < ε)
    (h : ∑ k ∈ Finset.range N, ((moves N (a.take k)).card : ℝ) / ((N - k : Nat) : ℝ) ≤ ε * N) :
    N * Real.log (1 / ε) ≤ pathDeficit N a := by
  unfold pathDeficit
  have key : ∀ k ∈ Finset.range N,
      Real.log (1 / ε) + 1 - (((moves N (a.take k)).card : ℝ) / ((N - k : Nat) : ℝ)) / ε ≤
        Real.log (((N - k : Nat) : ℝ) / (moves N (a.take k)).card) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hV : (0 : ℝ) < (moves N (a.take k)).card := by
      exact_mod_cast card_moves_take_pos ha hk
    have hN : (0 : ℝ) < ((N - k : Nat) : ℝ) := by
      have : 0 < N - k := by omega
      exact_mod_cast this
    set x := ((moves N (a.take k)).card : ℝ) / ((N - k : Nat) : ℝ) / ε with hx
    have hxpos : 0 < x := by positivity
    have hl := Real.log_le_sub_one_of_pos hxpos
    have e1 : Real.log x = Real.log ((moves N (a.take k)).card) - Real.log ((N - k : Nat) : ℝ)
        - Real.log ε := by
      rw [hx, Real.log_div (by positivity) hε.ne', Real.log_div hV.ne' hN.ne']
    have e2 : Real.log (((N - k : Nat) : ℝ) / (moves N (a.take k)).card) =
        Real.log ((N - k : Nat) : ℝ) - Real.log ((moves N (a.take k)).card) :=
      Real.log_div hN.ne' hV.ne'
    have e3 : Real.log (1 / ε) = - Real.log ε := by rw [one_div, Real.log_inv]
    rw [e2, e3]
    linarith
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.sum_div] at hsum
  have hdiv : (∑ k ∈ Finset.range N,
      ((moves N (a.take k)).card : ℝ) / ((N - k : Nat) : ℝ)) / ε ≤ N := by
    rw [div_le_iff₀ hε]; linarith
  have : (N : ℝ) * (Real.log (1 / ε) + 1) - N ≤ (N : ℝ) * (Real.log (1 / ε) + 1) -
      (∑ k ∈ Finset.range N, ((moves N (a.take k)).card : ℝ) / ((N - k : Nat) : ℝ)) / ε := by
    linarith
  nlinarith

/-- **Linear form of the Path Lemma**: the mean acceptance `(1/N) ∑_k V_k/(N-k)` of every
valid sequence is at most `ε(N)`, with `ε(N) → 0`.  It implies the Path Lemma. -/
def LinearPathLemma : Prop :=
  ∃ ε : ℕ → ℝ, (∀ N, 0 < ε N) ∧ Filter.Tendsto ε Filter.atTop (nhds 0) ∧
    ∀ N, ∀ a ∈ semiSeqs N,
      ∑ k ∈ Finset.range N, ((moves N (a.take k)).card : ℝ) / ((N - k : Nat) : ℝ) ≤ ε N * N

theorem LinearPathLemma.pathLemma (h : LinearPathLemma) : PathLemma := by
  obtain ⟨ε, hpos, hlim, hb⟩ := h
  refine ⟨fun N => N * Real.log (1 / ε N), ?_, fun N a ha => pathDeficit_ge_of_mean_le ha (hpos N) (hb N a ha)⟩
  have h1 : Filter.Tendsto ε Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Filter.Eventually.of_forall hpos⟩
  have h2 : Filter.Tendsto (fun N => Real.log (1 / ε N)) Filter.atTop Filter.atTop := by
    have := (Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp h1))
    refine this.congr (fun N => ?_)
    simp [Function.comp, one_div]
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have h1N : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : (N : ℝ) ≠ 0 := by linarith
  field_simp

/-! ## 2. Local structure of the cyclic defect -/

section Local

variable {N : Nat} {S : List Nat}

/-- Indicator of membership, as an integer. -/
def ind (S : List Nat) (x : Nat) : Int := if x ∈ S then 1 else 0

theorem ind_nonneg (S : List Nat) (x : Nat) : 0 ≤ ind S x := by
  unfold ind; split <;> norm_num

theorem cycBelow_succ (hnd : S.Nodup) (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (hN : 0 < N) (j : Nat) :
    (cycBelow N S (j + 1) : Int) = cycBelow N S j + ind S (j % N + 1) := by
  rw [cycBelow_eq_cnt hnd hS hN, cycBelow_eq_cnt hnd hS hN, cnt_succ, Nat.zero_add]
  unfold ind
  by_cases h : j % N + 1 ∈ S <;> simp [h]

/-- **Increment of the cyclic defect**:
`I(m+1) - I(m) = [2m ∈ S] + [2m+1 ∈ S] - 2 [m ∈ S]`, where the panels `2m`, `2m+1` are taken
mod `N` (as `(2m-1) % N + 1` and `(2m) % N + 1`). -/
theorem cycDefect_succ (hnd : S.Nodup) (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (hN : 0 < N) {m : Nat}
    (hm : 1 ≤ m) :
    cycDefect N S (m + 1) =
      cycDefect N S m + ind S ((2 * m - 1) % N + 1) + ind S ((2 * m) % N + 1) - 2 * ind S m := by
  unfold cycDefect
  have e1 : 2 * (m + 1) - 1 = (2 * m - 1) + 1 + 1 := by omega
  have e2 : (2 * m - 1) + 1 = 2 * m := by omega
  rw [e1, cycBelow_succ hnd hS hN, cycBelow_succ hnd hS hN, e2]
  have hb := below_succ hnd (m - 1)
  rw [show m - 1 + 1 = m by omega] at hb
  rw [show m + 1 - 1 = m by omega, hb]
  unfold ind
  by_cases h : m ∈ S <;> simp [h] <;> ring

/-- Across a free panel the cyclic defect does not decrease. -/
theorem cycDefect_mono_of_free (hnd : S.Nodup) (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (hN : 0 < N)
    {m : Nat} (hm : 1 ≤ m) (hmS : m ∉ S) : cycDefect N S m ≤ cycDefect N S (m + 1) := by
  rw [cycDefect_succ hnd hS hN hm]
  have h0 : ind S m = 0 := by simp [ind, hmS]
  have := ind_nonneg S ((2 * m - 1) % N + 1)
  have := ind_nonneg S ((2 * m) % N + 1)
  linarith

/-- **Consecutive valid panels.**  If `m` and `m + 1` are both free and both valid, then the
two panels `2m`, `2m + 1` (mod `N`) of their doubled position are free as well. -/
theorem consecutive_valid (hnd : S.Nodup) (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) {m : Nat}
    (hm : 1 ≤ m) (hmN : m + 1 ≤ N) (hmS : m ∉ S) (hm1S : m + 1 ∉ S)
    (h1 : SemiStep N S m) (h2 : SemiStep N S (m + 1)) :
    (2 * m - 1) % N + 1 ∉ S ∧ (2 * m) % N + 1 ∉ S := by
  have hN : 0 < N := by omega
  rw [semiStep_iff_cycDefect hnd hS hm (by omega) hmS] at h1
  rw [semiStep_iff_cycDefect hnd hS (by omega) hmN hm1S, cycDefect_succ hnd hS hN hm, h1] at h2
  have h0 : ind S m = 0 := by simp [ind, hmS]
  have a1 := ind_nonneg S ((2 * m - 1) % N + 1)
  have a2 := ind_nonneg S ((2 * m) % N + 1)
  constructor
  · intro hx
    have : ind S ((2 * m - 1) % N + 1) = 1 := by simp [ind, hx]
    linarith
  · intro hx
    have : ind S ((2 * m) % N + 1) = 1 := by simp [ind, hx]
    linarith

/-- **Doubling relation between zeros.**  If the cyclic defect vanishes at `m` and `m'`, the
doubled arc `(2m-1, 2m'-1]` contains twice as many panels of `S` as the arc `(m-1, m'-1]`. -/
theorem doubling_of_zeros {m m' : Nat} (h : cycDefect N S m = 0) (h' : cycDefect N S m' = 0) :
    (cycBelow N S (2 * m' - 1) : Int) - cycBelow N S (2 * m - 1) =
      2 * ((below S (m' - 1) : Int) - below S (m - 1)) := by
  unfold cycDefect at h h'
  linarith

end Local

/-! ### The run bound -/

/-- Right ends of the runs of free panels: `e ∉ S` with `e = N` or `e + 1 ∈ S`. -/
def runEnds (N : Nat) (S : List Nat) : Finset Nat :=
  (Finset.Icc 1 N).filter fun e => e ∉ S ∧ (e = N ∨ e + 1 ∈ S)

/-- Panels `m < N` such that `m`, `m + 1` and the doubled panels `2m`, `2m + 1` (mod `N`) are
all free. -/
def pairFree (N : Nat) (S : List Nat) : Finset Nat :=
  (Finset.Icc 1 N).filter fun m =>
    m + 1 ≤ N ∧ m ∉ S ∧ m + 1 ∉ S ∧ (2 * m - 1) % N + 1 ∉ S ∧ (2 * m) % N + 1 ∉ S

/-- Inside a run of free panels the defect is non-decreasing. -/
theorem cycDefect_mono_run (hnd : S.Nodup) (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (hN : 0 < N)
    {b : Nat} (hb : 1 ≤ b) : ∀ d, (∀ j, b ≤ j → j ≤ b + d → j ∉ S) →
      cycDefect N S b ≤ cycDefect N S (b + d)
  | 0, _ => le_rfl
  | d + 1, hfree => by
    have ih := cycDefect_mono_run hnd hS hN hb d (fun j h1 h2 => hfree j h1 (by omega))
    have := cycDefect_mono_of_free hnd hS hN (m := b + d) (by omega)
      (hfree (b + d) (by omega) (by omega))
    rw [← Nat.add_assoc]; exact ih.trans this

/-- **Run bound.**  `V(S) ≤ #(runs of free panels) + #{m : m, m+1, 2m, 2m+1 free}`: in a run
of free panels the defect is non-decreasing, so the valid panels of a run form one block, and
two consecutive valid panels need a free doubled pair (`consecutive_valid`). -/
theorem card_moves_le_runs (hnd : S.Nodup) (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) :
    (moves N S).card ≤ (runEnds N S).card + (pairFree N S).card := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0; simp [moves]
  set M1 := (moves N S).filter (fun m => m + 1 ∈ moves N S) with hM1
  set M2 := (moves N S).filter (fun m => m + 1 ∉ moves N S) with hM2
  have hsplit : M1.card + M2.card = (moves N S).card :=
    Finset.card_filter_add_card_filter_not _
  -- consecutive valid panels
  have h1 : M1 ⊆ pairFree N S := by
    intro m hm
    rw [hM1, Finset.mem_filter, mem_moves, mem_moves] at hm
    obtain ⟨⟨⟨hm1, hmN⟩, hmS, hv⟩, ⟨⟨_, hm1N⟩, hm1S, hv1⟩⟩ := hm
    have := consecutive_valid hnd hS hm1 hm1N hmS hm1S hv hv1
    rw [pairFree, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hm1, hmN⟩, hm1N, hmS, hm1S, this.1, this.2⟩
  -- block ends: one per run
  have hwit : ∀ b ∈ M2, ∃ e ∈ runEnds N S, b ≤ e ∧ ∀ b' ∈ M2, b < b' → e < b' := by
    intro b hb
    rw [hM2, Finset.mem_filter, mem_moves] at hb
    obtain ⟨⟨⟨hb1, hbN⟩, hbS, hbv⟩, hnext⟩ := hb
    have hex : ∃ e, b ≤ e ∧ (N ≤ e ∨ e + 1 ∈ S) := ⟨N, hbN, Or.inl le_rfl⟩
    set e := Nat.find hex with he
    have hespec := Nat.find_spec hex
    have heN : e ≤ N := Nat.find_min' hex ⟨hbN, Or.inl le_rfl⟩
    have hfree : ∀ j, b ≤ j → j ≤ e → j ∉ S := by
      intro j hj1 hj2
      rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
      · exact hbS
      · have hmin := Nat.find_min hex (m := j - 1) (by omega)
        push Not at hmin
        have := hmin (by omega)
        rw [show j - 1 + 1 = j by omega] at this
        exact this.2
    refine ⟨e, ?_, hespec.1, ?_⟩
    · rw [runEnds, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, heN⟩, hfree e hespec.1 le_rfl, ?_⟩
      rcases hespec.2 with h | h
      · left; omega
      · right; exact h
    · intro b' hb' hbb'
      by_contra hcon
      push Not at hcon
      rw [hM2, Finset.mem_filter, mem_moves] at hb'
      obtain ⟨⟨⟨_, hb'N⟩, hb'S, hb'v⟩, _⟩ := hb'
      have hz : cycDefect N S b = 0 := (semiStep_iff_cycDefect hnd hS hb1 hbN hbS).1 hbv
      have hz' : cycDefect N S b' = 0 := (semiStep_iff_cycDefect hnd hS (by omega) hb'N hb'S).1 hb'v
      have hb1S : b + 1 ∉ S := hfree (b + 1) (by omega) (by omega)
      have hnz : cycDefect N S (b + 1) ≠ 0 := by
        intro h0
        apply hnext
        rw [mem_moves]
        exact ⟨⟨by omega, by omega⟩, hb1S,
          (semiStep_iff_cycDefect hnd hS (by omega) (by omega) hb1S).2 h0⟩
      have hmono1 := cycDefect_mono_of_free hnd hS hN hb1 hbS
      have hmono2 := cycDefect_mono_run hnd hS hN (b := b + 1) (by omega) (b' - (b + 1))
        (fun j h1 h2 => hfree j (by omega) (by omega))
      rw [show b + 1 + (b' - (b + 1)) = b' by omega] at hmono2
      have : 0 < cycDefect N S (b + 1) := lt_of_le_of_ne (hz ▸ hmono1) (Ne.symm hnz)
      omega
  have hne : ∀ b ∈ M2, ((runEnds N S).filter (b ≤ ·)).Nonempty := by
    intro b hb
    obtain ⟨e, he, hbe, _⟩ := hwit b hb
    exact ⟨e, Finset.mem_filter.2 ⟨he, hbe⟩⟩
  let r : Nat → Nat := fun b =>
    if h : ((runEnds N S).filter (b ≤ ·)).Nonempty then ((runEnds N S).filter (b ≤ ·)).min' h
    else 0
  have hr_mem : ∀ b ∈ M2, r b ∈ runEnds N S ∧ b ≤ r b := by
    intro b hb
    simp only [r, hne b hb, ↓reduceDIte]
    exact Finset.mem_filter.1 (Finset.min'_mem _ _)
  have h2 : M2.card ≤ (runEnds N S).card := by
    apply Finset.card_le_card_of_injOn r (fun b hb => (hr_mem b hb).1)
    intro b hb b' hb' hrr
    have key : ∀ x ∈ M2, ∀ y ∈ M2, x < y → r x < r y := by
      intro x hx y hy hxy
      obtain ⟨e, he, hxe, hlt⟩ := hwit x hx
      have h1 : r x ≤ e := by
        simp only [r, hne x hx, ↓reduceDIte]
        exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨he, hxe⟩)
      have := hlt y hy hxy
      have := (hr_mem y hy).2
      omega
    rcases lt_trichotomy b b' with h | h | h
    · exact absurd hrr (key b hb b' hb' h).ne
    · exact h
    · exact absurd hrr (key b' hb' b hb h).ne'
  have := Finset.card_le_card h1
  omega

end Folds
