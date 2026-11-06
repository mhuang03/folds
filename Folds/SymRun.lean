import Folds.SymStructure2
import Mathlib.Order.Lattice.Nat

/-!
# The minimal opening run of 3-AP-free permutations: Conjecture F′

See `experiments/symrun/PROOFS.txt` (and `experiments/symstruct/PROOFS.txt`, section 3).

`f(N)` (`fRun N`) is the least `k` such that some 3-AP-free permutation of `[1, N]` has its
entry at index `k` of the other parity than its first entry (the minimal length of the
opening same-parity run).  `δ(N) = ⌊N/2⌋ - f(N)`.

**Conjecture F′** (`fRun_block`): for `M = 2^j` and `36M ≤ N < 72M`,
`δ(N) = pat M N`, where
* `δ = 4` on `[36M, 40M+1]` and at `40M+3`,
* `δ = 6` at `48M+2` and on `[48M+4, 56M-2]`,
* `δ = 5` otherwise.

Proof outline.
* `Good m K L`: an extendable prefix of `[1,K]` of length `m` inside `(L, K]`, i.e.
  `G(K, K-L) ≥ m`.  `good_halve`: Theorem F (3) (`top_rec`) in these coordinates,
  `(K, L) ↦ ((K+p)/2, (L+p)/2)`.
* The *diagonal states* `φ(K) = (K, ⌊K/2⌋)`, `ψ(K) = (K, ⌈K/2⌉)` are closed under halving:
  `φ(2m) ~ φ(m)`, `φ(2m+1) ~ φ(m) ∨ φ(m+1)`, `ψ(2m) ~ φ(m)`, `ψ(2m+1) ~ ψ(m) ∨ ψ(m+1)`
  (`phi_even`, `phi_odd`, `psi_odd`).
* `Body M K`: the values of `φ, ψ` on `[18M, 36M]` are given by explicit dyadic intervals;
  `body_double` proves `Body M → Body 2M` (pure linear arithmetic), the base `M = 1` is
  `body_18` … `body_36` (witnesses checked by `extB`, upper bounds by `noLong`).
* `change_of_good` (construction: `D` = evens, first odd entry `1`) and `no_change`
  (the reduction of `../symstruct` section 3 with the exact non-linked sets) turn the
  values of `φ`/`ψ` at `⌊N/2⌋` into `f(N)`.
-/

namespace Folds
namespace SymRun

open SymParity SymStructure SymStructure2

/-! ## Prefixes inside a top segment -/

/-- `Good m K L`: some extendable prefix of `[1, K]` of length `m` has all entries `> L`
(so `G(K, K - L) ≥ m` in the notation of `../symstruct/PROOFS.txt`). -/
def Good (m K L : ℕ) : Prop := ∃ π : List ℕ, π.length = m ∧ Ext K π ∧ ∀ v ∈ π, L < v

theorem Good.mono' {m K L m' K' L' : ℕ} (h : Good m K L) (hK : K = K') (hm : m' ≤ m)
    (hL : L' ≤ L) : Good m' K' L' := by
  subst hK
  obtain ⟨π, hl, hE, hv⟩ := h
  exact ⟨π.take m', by simp; omega, hE.of_prefix (List.take_prefix _ _),
    fun v hv' => by have := hv v (List.mem_of_mem_take hv'); omega⟩

/-- Lifting from a rescaled class (valid for every `K`). -/
theorem good_lift {m K L p : ℕ} (hp : p ≤ 1) (h : Good m ((K + p) / 2) ((L + p) / 2)) :
    Good m K L := by
  obtain ⟨ρ, hl, hE, hv⟩ := h
  rcases ρ with _ | ⟨r, ρ'⟩
  · exact ⟨[], hl, ext_nil _, by simp⟩
  refine ⟨(r :: ρ').map (lift p), by simpa using hl, ext_lift hp hE (by simp), ?_⟩
  intro v hv'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv'
  have := hv x hx
  simp only [lift]; omega

/-- **Theorem F (3)** in the coordinates `(K, L)`: for `K ≥ 28` and `K ≤ 2L + 1`,
`G(K, K-L) = max_p G((K+p)/2, (K+p)/2 - (L+p)/2)`. -/
theorem good_halve {m K L : ℕ} (hK : 28 ≤ K) (hR : K ≤ 2 * L + 1) (hLK : L ≤ K) :
    Good m K L ↔ ∃ p ≤ 1, Good m ((K + p) / 2) ((L + p) / 2) := by
  constructor
  · rintro ⟨π, hl, hE, hv⟩
    obtain ⟨p, hp, ρ, hl', hE', hv'⟩ := (top_rec (a := K - L) (m := m) hK (by omega)).1
      ⟨π, hl, hE, fun v hv'' => by have := hv v hv''; have := hE.range v hv''; omega⟩
    refine ⟨p, hp, ρ, hl', hE', fun r hr => ?_⟩
    have := hv' r hr; have := hE'.range r hr; omega
  · rintro ⟨p, hp, h⟩; exact good_lift hp h

/-- Theorem F (2): never more than `6`. -/
theorem not_good_seven {K L : ℕ} (hR : K ≤ 2 * L + 1) : ¬ Good 7 K L := by
  rintro ⟨π, hl, hE, hv⟩
  have := le_six_top K (K - L) (by omega) π hE
    (fun v hv' => by have := hv v hv'; have := hE.range v hv'; omega)
  omega

/-- Boolean certificate for `Good`. -/
def goodB (m K L : ℕ) (π : List ℕ) : Bool :=
  (π.length == m) && decide π.Nodup &&
    π.all (fun v => decide (1 ≤ v) && decide (v ≤ K) && decide (L < v)) && extB K K π

theorem good_of_goodB {m K L : ℕ} {π : List ℕ} (h : goodB m K L π = true) : Good m K L := by
  simp only [goodB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hl, hnd⟩, hall⟩, hB⟩ := h
  have hr : ∀ v ∈ π, 1 ≤ v ∧ v ≤ K := fun v hv => ⟨(hall v hv).1.1, (hall v hv).1.2⟩
  exact ⟨π, hl, (extB_iff K K π le_rfl hnd hr).1 hB, fun v hv => (hall v hv).2⟩

theorem not_good_of_noLong {d K L : ℕ} (h : noLong K (K - L) d [] = true) : ¬ Good d K L := by
  rintro ⟨π, hl, hE, hv⟩
  exact noLong_spec d [] h π hl
    (fun v hv' => by have := hv v hv'; have := hE.range v hv'; omega) (by simpa using hE)

/-! ## The diagonal states `φ(K) = (K, ⌊K/2⌋)` and `ψ(K) = (K, ⌈K/2⌉)` -/

theorem phi_even {d m : ℕ} (hm : 14 ≤ m) : Good d (2 * m) m ↔ Good d m (m / 2) := by
  rw [good_halve (by omega) (by omega) (by omega)]
  constructor
  · rintro ⟨p, hp, h⟩
    exact h.mono' (by omega) le_rfl (by omega)
  · intro h; exact ⟨0, by omega, h.mono' (by omega) le_rfl (by omega)⟩

theorem phi_odd {d m : ℕ} (hm : 14 ≤ m) :
    Good d (2 * m + 1) m ↔ Good d m (m / 2) ∨ Good d (m + 1) ((m + 1) / 2) := by
  rw [good_halve (by omega) (by omega) (by omega)]
  constructor
  · rintro ⟨p, hp, h⟩
    interval_cases p
    · exact Or.inl (h.mono' (by omega) le_rfl (by omega))
    · exact Or.inr (h.mono' (by omega) le_rfl (by omega))
  · rintro (h | h)
    · exact ⟨0, by omega, h.mono' (by omega) le_rfl (by omega)⟩
    · exact ⟨1, le_rfl, h.mono' (by omega) le_rfl (by omega)⟩

theorem psi_odd {d m : ℕ} (hm : 14 ≤ m) :
    Good d (2 * m + 1) (m + 1) ↔ Good d m ((m + 1) / 2) ∨ Good d (m + 1) ((m + 1 + 1) / 2) := by
  rw [good_halve (by omega) (by omega) (by omega)]
  constructor
  · rintro ⟨p, hp, h⟩
    interval_cases p
    · exact Or.inl (h.mono' (by omega) le_rfl (by omega))
    · exact Or.inr (h.mono' (by omega) le_rfl (by omega))
  · rintro (h | h)
    · exact ⟨0, by omega, h.mono' (by omega) le_rfl (by omega)⟩
    · exact ⟨1, le_rfl, h.mono' (by omega) le_rfl (by omega)⟩

/-- The values of `φ` and `ψ` on `[18M, 36M]`:
`φ = 4` on `[18M, 20M]`, `5` on `[20M+1, 24M]`, `6` on `[24M+1, 28M-1]`, `5` on
`[28M, 36M-1]`, `4` at `36M`; `ψ = 4` on `[18M, 20M+1]`, `5` on `[20M+2, 24M+1]`,
`6` on `[24M+2, 28M-2]`, `5` on `[28M-1, 36M-1]`, `4` at `36M`. -/
def Body (M K : ℕ) : Prop :=
  Good 4 K ((K + 1) / 2) ∧
  (Good 5 K (K / 2) ↔ 20 * M + 1 ≤ K ∧ K + 1 ≤ 36 * M) ∧
  (Good 6 K (K / 2) ↔ 24 * M + 1 ≤ K ∧ K + 1 ≤ 28 * M) ∧
  (Good 5 K ((K + 1) / 2) ↔ 20 * M + 2 ≤ K ∧ K + 1 ≤ 36 * M) ∧
  (Good 6 K ((K + 1) / 2) ↔ 24 * M + 2 ≤ K ∧ K + 2 ≤ 28 * M)

/-- The induction step `M → 2M` (only linear arithmetic once the recursion is applied). -/
theorem body_double {M : ℕ} (hM : 1 ≤ M) (h : ∀ K, 18 * M ≤ K → K ≤ 36 * M → Body M K) :
    ∀ K, 18 * (2 * M) ≤ K → K ≤ 36 * (2 * M) → Body (2 * M) K := by
  intro K h1 h2
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' K
  · have e1 : 2 * m / 2 = m := by omega
    have e2 : (2 * m + 1) / 2 = m := by omega
    obtain ⟨a4, a5, a6, -, -⟩ := h m (by omega) (by omega)
    rw [Body, e1, e2, phi_even (d := 4) (by omega), phi_even (d := 5) (by omega),
      phi_even (d := 6) (by omega), a5, a6]
    exact ⟨a4.mono' rfl le_rfl (by omega), by omega, by omega, by omega, by omega⟩
  · have e1 : (2 * m + 1) / 2 = m := by omega
    have e2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    obtain ⟨a4, a5, a6, b5, b6⟩ := h m (by omega) (by omega)
    obtain ⟨-, c5, c6, d5, d6⟩ := h (m + 1) (by omega) (by omega)
    rw [Body, e1, e2, phi_odd (d := 5) (by omega), phi_odd (d := 6) (by omega),
      psi_odd (d := 4) (by omega), psi_odd (d := 5) (by omega), psi_odd (d := 6) (by omega),
      a5, a6, b5, b6, c5, c6, d5, d6]
    exact ⟨Or.inl a4, by omega, by omega, by omega, by omega⟩

/-! ### The base block `M = 1` (`18 ≤ K ≤ 36`), generated by `experiments/symrun/gen_base.py` -/

set_option maxRecDepth 100000

theorem body_18 : Body 1 18 := by
  have p_psi4 : Good 4 18 ((18 + 1) / 2) :=
    good_of_goodB (π := [10, 18, 14, 16]) (by decide +kernel)
  have n_phi5 : ¬ Good 5 18 (18 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi4.mono' rfl (by norm_num) (by norm_num)),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_19 : Body 1 19 := by
  have p_psi4 : Good 4 19 ((19 + 1) / 2) :=
    good_of_goodB (π := [11, 19, 15, 17]) (by decide +kernel)
  have n_phi5 : ¬ Good 5 19 (19 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi4.mono' rfl (by norm_num) (by norm_num)),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_20 : Body 1 20 := by
  have p_psi4 : Good 4 20 ((20 + 1) / 2) :=
    good_of_goodB (π := [11, 19, 15, 17]) (by decide +kernel)
  have n_phi5 : ¬ Good 5 20 (20 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi4.mono' rfl (by norm_num) (by norm_num)),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_21 : Body 1 21 := by
  have p_phi5 : Good 5 21 (21 / 2) :=
    good_of_goodB (π := [11, 19, 15, 17, 21]) (by decide +kernel)
  have p_psi4 : Good 4 21 ((21 + 1) / 2) :=
    good_of_goodB (π := [12, 20, 16, 18]) (by decide +kernel)
  have n_phi6 : ¬ Good 6 21 (21 / 2) :=
    not_good_of_noLong (by decide +kernel)
  have n_psi5 : ¬ Good 5 21 ((21 + 1) / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi4.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_phi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_psi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_22 : Body 1 22 := by
  have p_psi5 : Good 5 22 ((22 + 1) / 2) :=
    good_of_goodB (π := [12, 20, 16, 18, 22]) (by decide +kernel)
  have n_phi6 : ¬ Good 6 22 (22 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi5.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_23 : Body 1 23 := by
  have p_psi5 : Good 5 23 ((23 + 1) / 2) :=
    good_of_goodB (π := [13, 21, 17, 19, 23]) (by decide +kernel)
  have n_phi6 : ¬ Good 6 23 (23 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi5.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_24 : Body 1 24 := by
  have p_psi5 : Good 5 24 ((24 + 1) / 2) :=
    good_of_goodB (π := [13, 21, 17, 19, 23]) (by decide +kernel)
  have n_phi6 : ¬ Good 6 24 (24 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi5.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_25 : Body 1 25 := by
  have p_phi6 : Good 6 25 (25 / 2) :=
    good_of_goodB (π := [13, 21, 17, 25, 19, 23]) (by decide +kernel)
  have p_psi5 : Good 5 25 ((25 + 1) / 2) :=
    good_of_goodB (π := [14, 22, 18, 20, 24]) (by decide +kernel)
  have n_psi6 : ¬ Good 6 25 ((25 + 1) / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi5.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_phi6.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_true (p_phi6.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_psi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_26 : Body 1 26 := by
  have p_psi6 : Good 6 26 ((26 + 1) / 2) :=
    good_of_goodB (π := [14, 22, 18, 26, 20, 24]) (by decide +kernel)
  exact ⟨(p_psi6.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_psi6.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_true (p_psi6.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_true (p_psi6.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_true (p_psi6.mono' rfl (by norm_num) (by norm_num)) (by norm_num)⟩

theorem body_27 : Body 1 27 := by
  have p_phi6 : Good 6 27 (27 / 2) :=
    good_of_goodB (π := [14, 22, 18, 26, 20, 24]) (by decide +kernel)
  have p_psi5 : Good 5 27 ((27 + 1) / 2) :=
    good_of_goodB (π := [15, 23, 19, 27, 25]) (by decide +kernel)
  have n_psi6 : ¬ Good 6 27 ((27 + 1) / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi5.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_phi6.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_true (p_phi6.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_psi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_28 : Body 1 28 := by
  have p_psi5 : Good 5 28 ((28 + 1) / 2) :=
    good_of_goodB (π := [15, 23, 19, 27, 25]) (by decide +kernel)
  have n_phi6 : ¬ Good 6 28 (28 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi5.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_29 : Body 1 29 := by
  have p_psi5 : Good 5 29 ((29 + 1) / 2) :=
    good_of_goodB (π := [16, 24, 20, 28, 26]) (by decide +kernel)
  have n_phi6 : ¬ Good 6 29 (29 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi5.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_30 : Body 1 30 := by
  have p_psi5 : Good 5 30 ((30 + 1) / 2) :=
    good_of_goodB (π := [16, 24, 20, 28, 26]) (by decide +kernel)
  have n_phi6 : ¬ Good 6 30 (30 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi5.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_31 : Body 1 31 := by
  have p_psi5 : Good 5 31 ((31 + 1) / 2) :=
    good_of_goodB (π := [17, 25, 21, 29, 27]) (by decide +kernel)
  have n_phi6 : ¬ Good 6 31 (31 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi5.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_32 : Body 1 32 := by
  have p_psi5 : Good 5 32 ((32 + 1) / 2) :=
    good_of_goodB (π := [17, 25, 21, 29, 27]) (by decide +kernel)
  have n_phi6 : ¬ Good 6 32 (32 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi5.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_33 : Body 1 33 := by
  have p_psi5 : Good 5 33 ((33 + 1) / 2) :=
    good_of_goodB (π := [18, 26, 22, 30, 28]) (by decide +kernel)
  have n_phi6 : ¬ Good 6 33 (33 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi5.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_34 : Body 1 34 := by
  have p_psi5 : Good 5 34 ((34 + 1) / 2) :=
    good_of_goodB (π := [19, 27, 23, 31, 33]) (by decide +kernel)
  have n_phi6 : ¬ Good 6 34 (34 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi5.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_35 : Body 1 35 := by
  have p_psi5 : Good 5 35 ((35 + 1) / 2) :=
    good_of_goodB (π := [20, 28, 24, 32, 34]) (by decide +kernel)
  have n_phi6 : ¬ Good 6 35 (35 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi5.mono' rfl (by norm_num) (by norm_num)),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_true (p_psi5.mono' rfl (by norm_num) (by norm_num)) (by norm_num),
    iff_of_false (fun h => n_phi6 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_36 : Body 1 36 := by
  have p_psi4 : Good 4 36 ((36 + 1) / 2) :=
    good_of_goodB (π := [19, 35, 27, 31]) (by decide +kernel)
  have n_phi5 : ¬ Good 5 36 (36 / 2) :=
    not_good_of_noLong (by decide +kernel)
  exact ⟨(p_psi4.mono' rfl (by norm_num) (by norm_num)),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num),
    iff_of_false (fun h => n_phi5 (h.mono' rfl (by norm_num) (by norm_num))) (by norm_num)⟩

theorem body_one : ∀ K, 18 * 1 ≤ K → K ≤ 36 * 1 → Body 1 K := by
  intro K h1 h2
  interval_cases K
  all_goals first
    | exact body_18 | exact body_19 | exact body_20 | exact body_21 | exact body_22
    | exact body_23 | exact body_24 | exact body_25 | exact body_26 | exact body_27
    | exact body_28 | exact body_29 | exact body_30 | exact body_31 | exact body_32
    | exact body_33 | exact body_34 | exact body_35 | exact body_36

theorem body_pow (j : ℕ) : ∀ K, 18 * 2 ^ j ≤ K → K ≤ 36 * 2 ^ j → Body (2 ^ j) K := by
  induction j with
  | zero => simpa using body_one
  | succ j ih =>
    rw [pow_succ']
    exact body_double (Nat.one_le_two_pow) ih

/-! ## From top-segment prefixes to the opening run -/

/-- Some 3-AP-free permutation of `[1, N]` has its entry at index `k` of the other parity
than its first entry. -/
def ChangeAt (N k : ℕ) : Prop := ∃ a ∈ symSeqs N, ∃ h : k < a.length, a[k] % 2 ≠ a[0] % 2

/-- `f(N)`: the minimal length of the opening same-parity run of a 3-AP-free
permutation of `[1, N]`. -/
noncomputable def fRun (N : ℕ) : ℕ := sInf {k | ChangeAt N k}

theorem fRun_eq {N k : ℕ} (h1 : ChangeAt N k) (h2 : ∀ i < k, ¬ ChangeAt N i) : fRun N = k := by
  apply le_antisymm (Nat.sInf_le h1)
  by_contra hlt
  push Not at hlt
  exact h2 _ hlt (Nat.sInf_mem (s := {k | ChangeAt N k}) ⟨k, h1⟩)

/-- **Construction.**  If `G(⌊N/2⌋, ⌊N/2⌋ - ⌊(N+1)/4⌋) ≥ m` then some 3-AP-free
permutation of `[1, N]` starts with `⌊N/2⌋ - m` even entries followed by `1`: take a
3-AP-free permutation `σ` of `[1, ⌊N/2⌋]` ending with the reverse of the witness, and
`π = 2σ_1, …, 2σ_{K-m}, 1`; by Theorem E (`ext_of_cond`) `π` extends, since the evens
after `1` are `> (N+1)/2`, hence not linked to `1`. -/
theorem change_of_good {N m : ℕ} (h : Good m (N / 2) ((N + 1) / 4)) (hm : m < N / 2) :
    ChangeAt N (N / 2 - m) := by
  obtain ⟨ρ, hl, hE, hv⟩ := h
  obtain ⟨s, hP, hap⟩ := hE
  have hsl : s.length = N / 2 - m := by
    have := hP.length; simp at this; omega
  obtain ⟨w0, t0, hs⟩ : ∃ w0 t0, s.reverse = w0 :: t0 := by
    cases h' : s.reverse with
    | nil => simp at h'; simp [h'] at hsl; omega
    | cons w0 t0 => exact ⟨w0, t0, rfl⟩
  have hmem : ∀ r, r ∈ w0 :: t0 ↔ r ∈ s := by intro r; rw [← hs, List.mem_reverse]
  have hrange : ∀ r ∈ w0 :: t0, 1 ≤ r ∧ r ≤ N / 2 := fun r hr =>
    (hP.2 r).1 (List.mem_append_right _ ((hmem r).1 hr))
  have hnd0 : (w0 :: t0).Nodup := by
    rw [← hs, List.nodup_reverse]; exact (List.nodup_append.1 hP.1).2.1
  have hev : ∀ v ∈ (w0 :: t0).map (lift 0), v % 2 = 0 ∧ 2 ≤ v ∧ v ≤ N := by
    intro v hv'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv'
    have := hrange r hr
    simp only [lift]; omega
  set π := (w0 :: t0).map (lift 0) ++ [1] with hπdef
  have hπ : π = lift 0 w0 :: (t0.map (lift 0) ++ [1]) := rfl
  have hw : lift 0 w0 % 2 = 0 := (hev _ (by simp)).1
  have hπmem : ∀ v ∈ π, v = 1 ∨ v ∈ (w0 :: t0).map (lift 0) := by
    intro v hv'
    rcases List.mem_append.1 hv' with h' | h'
    · exact Or.inr h'
    · exact Or.inl (by simpa using h')
  have hnd : π.Nodup := by
    rw [hπdef, List.nodup_append]
    refine ⟨hnd0.map (lift_inj (by omega)), by simp, ?_⟩
    intro x hx y hy
    have := (hev x hx).1
    simp at hy; omega
  have hE : Ext N π := by
    refine ext_of_cond hπ hnd ?_ ?_ ?_ ?_ ?_
    · intro v hv'
      rcases hπmem v hv' with rfl | h'
      · omega
      · have := hev v h'; omega
    · intro y hy u hu hyw huw _
      rw [hw] at hyw huw
      have hu1 : u = 1 := by
        rcases hπmem u hu with h' | h'
        · exact h'
        · exact absurd (hev u h').1 huw
      have hy' : y ∈ (w0 :: t0).map (lift 0) := by
        rcases hπmem y hy with h' | h'
        · omega
        · exact h'
      rw [hu1, hπdef]
      exact bef_append_mid hy' (by simp)
    · intro u hu y hy hyπ hyw huw hl
      rw [hw] at hyw huw
      have hu1 : u = 1 := by
        rcases hπmem u hu with h' | h'
        · exact h'
        · exact absurd (hev u h').1 huw
      subst hu1
      rw [List.mem_range'_1] at hy
      have hyK : y / 2 ∈ ρ ++ s := (hP.2 _).2 (by omega)
      have hyρ : y / 2 ∈ ρ := by
        rcases List.mem_append.1 hyK with h' | h'
        · exact h'
        · exfalso
          apply hyπ
          rw [hπdef]
          refine List.mem_append_left _ (List.mem_map.2 ⟨y / 2, (hmem _).2 h', ?_⟩)
          simp only [lift]; omega
      have := hv _ hyρ
      simp only [Linked] at hl
      omega
    · rw [hw, hπdef, cls_append, cls_map_lift (by omega) (fun r hr => (hrange r hr).1)]
      have : cls 0 [1] = [] := by decide
      rw [this, List.append_nil, ← hs]
      refine ⟨ρ.reverse, ?_, ?_⟩
      · rw [← List.reverse_append]
        exact ⟨List.nodup_reverse.2 hP.1, fun v => by rw [List.mem_reverse]; exact hP.2 v⟩
      · rw [← List.reverse_append]; exact hap.reverse
    · rw [hw, hπdef, cls_append, cls_map_lift_other (by omega) (by omega)
        (fun r hr => (hrange r hr).1)]
      have : cls (1 - 0) [1] = [1] := by decide
      rw [this, List.nil_append]
      exact (ext_nil_one _).2 (by omega)
  obtain ⟨a, ha, s', rfl⟩ := ext_iff_mem_symSeqs.1 hE
  have hlm : ((w0 :: t0).map (lift 0)).length = N / 2 - m := by
    rw [List.length_map, ← hs, List.length_reverse, hsl]
  have hA : π ++ s' = (w0 :: t0).map (lift 0) ++ (1 :: s') := by rw [hπdef]; simp
  rw [hA] at ha
  have key : ∀ (L1 : List ℕ) (n : ℕ), L1.length = n → ∀ (s' : List ℕ)
      (h : n < (L1 ++ 1 :: s').length), (L1 ++ 1 :: s')[n] = 1 := by
    intro L1 n hn s' h; subst hn; simp
  refine ⟨_, ha, by simp at hlm ⊢; omega, ?_⟩
  rw [key _ _ hlm]
  have h0 : ((w0 :: t0).map (lift 0) ++ (1 :: s'))[0]'(by simp) = lift 0 w0 := by simp
  rw [h0, hw]; omega

/-- **The `D`-entries after the first `C`-entry.**  In a 3-AP-free permutation `a` of
`[1, N]` with `a[k]` of the other parity than `a[0] = w` (`p = w % 2`, `K_p = ⌊(N+p)/2⌋`):
the `D`-entries after index `k` (there are at least `K_p - k`) give, rescaled and reversed,
an extendable prefix of `[1, K_p]` inside the top values `> ⌊(N+1+2p)/4⌋` (if
`2a[k] ≤ N+1`), or, mirrored, inside the values `> K_p - ⌊(N+2p)/4⌋`. -/
theorem D_after_good {N w : ℕ} {a tl : List ℕ} (ha : a = w :: tl) (hP : IsPermOf N a)
    (hap : APF a) {k : ℕ} (hk : k < a.length) (hu : a[k] % 2 ≠ w % 2) :
    Good ((N + w % 2) / 2 - k) ((N + w % 2) / 2) ((N + 1 + 2 * (w % 2)) / 4) ∨
    Good ((N + w % 2) / 2 - k) ((N + w % 2) / 2) ((N + w % 2) / 2 - (N + 2 * (w % 2)) / 4) := by
  have hsplit : a = (a.take k ++ [a[k]]) ++ a.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hk,
      List.take_append_drop]
  have hu1 := (hP.2 a[k]).1 (List.getElem_mem hk)
  have hnl : ∀ y ∈ a.drop (k + 1), y % 2 = w % 2 → ¬ Linked N y a[k] := by
    intro y hy hyw
    refine not_linked_of_bef ha hP.1 hP.2 hap hyw hu ?_
    have : Bef ((a.take k ++ [a[k]]) ++ a.drop (k + 1)) a[k] y := by
      rw [List.append_assoc]; exact bef_append_right (bef_head hy)
    rwa [← hsplit] at this
  have hσ : IsPermOf ((N + w % 2) / 2) (cls (w % 2) a) := cls_isPermOf (by omega) hP
  have hσa : APF (cls (w % 2) a) := cls_apf hap
  have hlenσ := hσ.length
  rw [hsplit, cls_append] at hσ hσa
  rw [hsplit, cls_append, cls_append, List.length_append, List.length_append] at hlenσ
  have h1 : (cls (w % 2) (a.take k)).length ≤ k := by
    rw [cls, List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)
  have h2 : (cls (w % 2) [a[k]]).length = 0 := by
    simp [cls, hu]
  have hE : Ext ((N + w % 2) / 2) (cls (w % 2) (a.drop (k + 1))).reverse := by
    refine ⟨(cls (w % 2) (a.take k ++ [a[k]])).reverse, ?_, ?_⟩
    · rw [← List.reverse_append]
      exact ⟨List.nodup_reverse.2 hσ.1, fun v => by rw [List.mem_reverse]; exact hσ.2 v⟩
    · rw [← List.reverse_append]; exact hσa.reverse
  set ρ := (cls (w % 2) (a.drop (k + 1))).reverse with hρ
  have hge : (N + w % 2) / 2 - k ≤ ρ.length := by
    rw [hρ, List.length_reverse]; omega
  have hρmem : ∀ r ∈ ρ, ∃ y ∈ a.drop (k + 1), y % 2 = w % 2 ∧ half y = r ∧ ¬ Linked N y a[k]
      ∧ 1 ≤ y ∧ y ≤ N := by
    intro r hr
    rw [hρ, List.mem_reverse] at hr
    obtain ⟨y, hy, hyw, rfl⟩ := mem_cls.1 hr
    exact ⟨y, hy, hyw, rfl, hnl y hy hyw, (hP.2 y).1 (List.mem_of_mem_drop hy)⟩
  by_cases h2u : 2 * a[k] ≤ N + 1
  · left
    refine (show Good ρ.length _ _ from ⟨ρ, rfl, hE, ?_⟩).mono' rfl hge le_rfl
    intro r hr
    obtain ⟨y, -, hyw, rfl, hl, hy1, hyN⟩ := hρmem r hr
    simp only [Linked] at hl
    simp only [half]; omega
  · right
    refine (show Good ρ.length _ _ from ⟨ρ.map (fun v => (N + w % 2) / 2 + 1 - v), by simp,
      hE.mirror, ?_⟩).mono' rfl hge le_rfl
    intro v hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv
    obtain ⟨y, -, hyw, rfl, hl, hy1, hyN⟩ := hρmem r hr
    simp only [Linked] at hl
    simp only [half]; omega

/-- **Lower bound for `f`.**  If `G` at the state `(⌊N/2⌋, ⌊(N+1)/4⌋)` is `≤ d` and, for
odd `N`, `G` at `(⌈N/2⌉, ⌊(N+2)/4⌋)` is `≤ d + 1`, then every 3-AP-free permutation of
`[1, N]` keeps the parity of its first entry on the first `⌊N/2⌋ - d` entries. -/
theorem no_change {N d : ℕ} (h0 : ¬ Good (d + 1) (N / 2) ((N + 1) / 4))
    (h1 : N % 2 = 1 → ¬ Good (d + 2) ((N + 1) / 2) ((N + 2) / 4)) {i : ℕ}
    (hi : i + d < N / 2) : ¬ ChangeAt N i := by
  rintro ⟨a, ha, hk, hch⟩
  obtain ⟨hP, hap⟩ := mem_symSeqs_iff.1 ha
  obtain ⟨w, tl, rfl⟩ : ∃ w tl, a = w :: tl := by
    cases a with
    | nil => simp at hk
    | cons w tl => exact ⟨w, tl, rfl⟩
  have hu : (w :: tl)[i] % 2 ≠ w % 2 := hch
  have hw : w % 2 = 0 ∨ w % 2 = 1 := by omega
  rcases D_after_good rfl hP hap hk hu with h | h <;> rcases hw with hw | hw
  · exact h0 (h.mono' (by omega) (by omega) (by omega))
  · rcases Nat.mod_two_eq_zero_or_one N with hN | hN
    · exact h0 (h.mono' (by omega) (by omega) (by omega))
    · exact h1 hN (h.mono' (by omega) (by omega) (by omega))
  · exact h0 (h.mono' (by omega) (by omega) (by omega))
  · rcases Nat.mod_two_eq_zero_or_one N with hN | hN
    · exact h0 (h.mono' (by omega) (by omega) (by omega))
    · exact h1 hN (h.mono' (by omega) (by omega) (by omega))

/-! ## Conjecture F′ -/

/-- The conjectured value of `δ(N) = ⌊N/2⌋ - f(N)` on the block `[36M, 72M)`. -/
def pat (M N : ℕ) : ℕ :=
  if N ≤ 40 * M + 1 ∨ N = 40 * M + 3 then 4
  else if N = 48 * M + 2 ∨ (48 * M + 4 ≤ N ∧ N + 2 ≤ 56 * M) then 6 else 5

theorem pat_ge (M N : ℕ) : 4 ≤ pat M N := by unfold pat; split_ifs <;> omega
theorem pat_le (M N : ℕ) : pat M N ≤ 6 := by unfold pat; split_ifs <;> omega

/-- `G` at the state of `N` equals `pat`, and the odd-`N` side condition holds. -/
theorem good_state {j N : ℕ} (h1 : 36 * 2 ^ j ≤ N) (h2 : N < 72 * 2 ^ j) :
    Good (pat (2 ^ j) N) (N / 2) ((N + 1) / 4) ∧
    ¬ Good (pat (2 ^ j) N + 1) (N / 2) ((N + 1) / 4) ∧
    (N % 2 = 1 → ¬ Good (pat (2 ^ j) N + 2) ((N + 1) / 2) ((N + 2) / 4)) := by
  have hB := body_pow j
  have hM : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  generalize 2 ^ j = M at hB hM h1 h2 ⊢
  obtain ⟨a4, a5, a6, b5, b6⟩ := hB (N / 2) (by omega) (by omega)
  obtain ⟨-, c5, c6, -, -⟩ := hB ((N + 1) / 2) (by omega) (by omega)
  have hodd : N % 2 = 1 → (N + 2) / 4 = (N + 1) / 2 / 2 := fun _ => by omega
  by_cases h3 : N % 4 = 3
  · rw [show (N + 1) / 4 = (N / 2 + 1) / 2 by omega]
    unfold pat
    split_ifs with hA hC <;> refine ⟨?_, ?_, fun hN => ?_⟩ <;> try rw [hodd hN]
    all_goals first
      | exact a4.mono' rfl le_rfl le_rfl
      | exact b5.2 (by omega)
      | exact b6.2 (by omega)
      | exact fun g => absurd (b5.1 g) (by omega)
      | exact fun g => absurd (b6.1 g) (by omega)
      | exact fun g => absurd (c6.1 g) (by omega)
      | exact fun g => not_good_seven (by omega) (g.mono' rfl (by omega) le_rfl)
  · rw [show (N + 1) / 4 = N / 2 / 2 by omega]
    unfold pat
    split_ifs with hA hC <;> refine ⟨?_, ?_, fun hN => ?_⟩ <;> try rw [hodd hN]
    all_goals first
      | exact a4.mono' rfl le_rfl (by omega)
      | exact a5.2 (by omega)
      | exact a6.2 (by omega)
      | exact fun g => absurd (a5.1 g) (by omega)
      | exact fun g => absurd (a6.1 g) (by omega)
      | exact fun g => absurd (c6.1 g) (by omega)
      | exact fun g => not_good_seven (by omega) (g.mono' rfl (by omega) le_rfl)

/-- **Conjecture F′ (now a theorem).**  For `M = 2^j` and `36M ≤ N < 72M`,
`f(N) = ⌊N/2⌋ - pat M N`. -/
theorem fRun_block {j N : ℕ} (h1 : 36 * 2 ^ j ≤ N) (h2 : N < 72 * 2 ^ j) :
    fRun N = N / 2 - pat (2 ^ j) N := by
  obtain ⟨hg, hn, ho⟩ := good_state h1 h2
  have := pat_le (2 ^ j) N
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  exact fRun_eq (change_of_good hg (by omega)) (fun i hi => no_change hn ho (by omega))

/-- `δ(N) = ⌊N/2⌋ - f(N)`. -/
noncomputable def delta (N : ℕ) : ℕ := N / 2 - fRun N

/-- **Conjecture F′**, in the form of the statement: on `[36M, 72M)` (`M = 2^j`),
`δ = 4` on `[36M, 40M+1]` and at `40M+3`; `δ = 6` at `48M+2` and on `[48M+4, 56M-2]`;
`δ = 5` otherwise. -/
theorem delta_block {j N : ℕ} (h1 : 36 * 2 ^ j ≤ N) (h2 : N < 72 * 2 ^ j) :
    delta N = pat (2 ^ j) N := by
  have := pat_le (2 ^ j) N
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [delta, fRun_block h1 h2]; omega

theorem exists_block {N : ℕ} (hN : 36 ≤ N) : ∃ j, 36 * 2 ^ j ≤ N ∧ N < 72 * 2 ^ j := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  by_cases h : N < 72
  · exact ⟨0, by simpa using hN, by simpa using h⟩
  obtain ⟨j, h1, h2⟩ := ih (N / 2) (by omega) (by omega)
  exact ⟨j + 1, by rw [pow_succ]; omega, by rw [pow_succ]; omega⟩

/-- `4 ≤ δ(N) ≤ 6` for every `N ≥ 36`: `⌊N/2⌋ - 6 ≤ f(N) ≤ ⌊N/2⌋ - 4`. -/
theorem fRun_bounds {N : ℕ} (hN : 36 ≤ N) : N / 2 - 6 ≤ fRun N ∧ fRun N ≤ N / 2 - 4 := by
  obtain ⟨j, h1, h2⟩ := exists_block hN
  have := pat_le (2 ^ j) N
  have := pat_ge (2 ^ j) N
  rw [fRun_block h1 h2]; omega

/-- **Sharpness of Sharma's bound along `48·2^j + 2`**: `f(N) = ⌊N/2⌋ - 6`. -/
theorem fRun_sharp (j : ℕ) : fRun (48 * 2 ^ j + 2) = (48 * 2 ^ j + 2) / 2 - 6 := by
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [fRun_block (j := j) (by omega) (by omega)]
  unfold pat
  split_ifs <;> omega

/-- Equality in Sharma's bound holds exactly at the `δ = 6` points of F′. -/
theorem fRun_eq_sub_six_iff {j N : ℕ} (h1 : 36 * 2 ^ j ≤ N) (h2 : N < 72 * 2 ^ j) :
    fRun N = N / 2 - 6 ↔ N = 48 * 2 ^ j + 2 ∨ (48 * 2 ^ j + 4 ≤ N ∧ N + 2 ≤ 56 * 2 ^ j) := by
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [fRun_block h1 h2]
  unfold pat
  split_ifs <;> omega

/-- `liminf δ = 4` and `limsup δ = 6`: both values occur in every block. -/
theorem delta_four_and_six (j : ℕ) :
    delta (36 * 2 ^ j) = 4 ∧ delta (48 * 2 ^ j + 2) = 6 := by
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [delta_block (j := j) (by omega) (by omega), delta_block (j := j) (by omega) (by omega)]
  unfold pat
  constructor <;> split_ifs <;> omega

end SymRun
end Folds
