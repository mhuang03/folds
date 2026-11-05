import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Order.Interval.Finset.Nat
import Folds.Counting
import Folds.Cyclic

/-!
# Slips and a super-exponential lower bound

`N = 2n`.  Fix `d : ℕ → ℕ` with values in `{0, 1}`, `d 0 = 0` and `d n = 0` (the slip set
is `D = {k : d k = 1} ⊆ [1, n-1]`).  Put

* `slipF d i = 2i + d i`        (the evens, with `2k` replaced by `2k+1` for `k ∈ D`),
* `slipS d i = 2i - 1 - d (i-1)` (the odds, with `2k+1` replaced by `2k` for `k ∈ D`).

For `k ∈ D` a slip exchanges the panels `2k` and `2k+1` between the two parity blocks.
Each slip changes exactly one window relation in each block, and the changed relation is
harmless as soon as one order relation holds in the block sequence:

* `slipF_semiSymmetric`: if `τ` is semi-symmetric for `n` and, whenever `τ` places a
  `j ∈ D`, the panel `q j = 2j mod* n` has not been placed yet, then `τ.map (slipF d)`
  is semi-symmetric for `2n`;
* `slipS_steps`: if `σ` is semi-symmetric for `n` and, whenever `σ` places `j` with
  `j - 1 ∈ D`, the panel `p (j-1) = 2j - 1 mod* n` HAS been placed, then every step of
  `σ.map (slipS d)` is semi-symmetric on top of the complete first block;
* `slip_mem_semiSeqs`: the concatenation is a semi-symmetric fold sequence of `2n`.

(`x mod* n` is the representative of `x` in `[1, n]`.)

Counting (`semiCount_slip`): the slip map is injective, so
`∑_{D ⊆ [1, n-1]} #{τ : cond_F(D)} · #{σ : cond_S(D)} ≤ a(2n)`.

Parity-block inputs (`semiCount_paritySlip`): if `τ` and `σ` are odds-first parity-block
sequences of `[n]`, the conditions hold for every `D ⊆ C_n` (odd `k`; for odd `n` also
`2k + 1 ≤ n`), because `k`, `p(k)` are odd and `q(k)`, `k + 1` even.  Hence
* `a(2n) ≥ 2^{|C_n|} · (a(⌈n/2⌉) · a(⌊n/2⌋))²`,
* `semiCount_four_mul`: `a(4m) ≥ 2^m · a(m)^4`,
* `semiCount_four_mul_add_two`: `a(4m+2) ≥ 2^{⌊(m+1)/2⌋} · a(m)² · a(m+1)²`,
* `pow_le_semiCount_pow_four`: `N^N ≤ a(N)^8` for `N = 4^j`, i.e. `a(N) ≥ N^{N/8}`:
  **a super-exponential lower bound**.

Paper proof of `ln a(N) ≥ (1/32) N ln N - (ln 2 / 4) N` for all `N` from these
recursions: `experiments/superexp/PROOFS.txt`.
-/

namespace Folds
namespace Slip

/-- First block: `f i = 2i + d i`. -/
def slipF (d : Nat → Nat) (i : Nat) : Nat := 2 * i + d i

/-- Second block: `s i = 2i - 1 - d (i - 1)`. -/
def slipS (d : Nat → Nat) (i : Nat) : Nat := 2 * i - 1 - d (i - 1)

/-- `qq n j = 2j mod* n` (the representative in `[1, n]`), for `j ≥ 1`. -/
def qq (n j : Nat) : Nat := (2 * j - 1) % n + 1

/-- `pp n k = (2k + 1) mod* n`. -/
def pp (n k : Nat) : Nat := (2 * k) % n + 1

/-- Admissible slip indicator for the strip `[1, n]`. -/
structure Adm (n : Nat) (d : Nat → Nat) : Prop where
  le_one : ∀ i, d i ≤ 1
  zero : d 0 = 0
  top : d n = 0

/-! ## Prefix counts -/

theorem below_succ {U : List Nat} (hnd : U.Nodup) (y : Nat) :
    below U (y + 1) = below U y + (if y + 1 ∈ U then 1 else 0) := by
  rw [below_split U (Nat.le_succ y), ← countP_eq_nodup hnd]
  congr 1
  apply List.countP_congr; intro x _; simp only [decide_eq_true_eq]; omega

/-- `cycBelow` on the representation `y = n a + r`, `r ≤ n`. -/
theorem cycBelow_rep {n : Nat} {U : List Nat} (hn : 0 < n) (h0 : below U 0 = 0)
    (hN : below U n = U.length) (a : Nat) {r : Nat} (hr : r ≤ n) :
    cycBelow n U (n * a + r) = below U r + a * U.length := by
  unfold cycBelow
  rcases Nat.lt_or_ge r n with h | h
  · have hm : (n * a + r) % n = r := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
    have hdv : (n * a + r) / n = a := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt h, Nat.zero_add]
    rw [hm, hdv]
  · have e : r = n := by omega
    rw [e]
    have e2 : n * a + n = 0 + n * (a + 1) := by rw [Nat.mul_succ]; omega
    rw [e2, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hn, Nat.zero_mod,
      Nat.zero_div, h0, hN]
    simp only [Nat.zero_add, Nat.add_mul, Nat.one_mul]
    omega

theorem below_zero_of {U : List Nat} {n : Nat} (hU : ∀ x ∈ U, 1 ≤ x ∧ x ≤ n) :
    below U 0 = 0 := below_zero fun x hx => (hU x hx).1

theorem below_top_of {U : List Nat} {n : Nat} (hU : ∀ x ∈ U, 1 ≤ x ∧ x ≤ n) :
    below U n = U.length := below_eq_length fun x hx => (hU x hx).2

/-- One step of the cyclic count: it grows by `[y mod n + 1 ∈ U]`. -/
theorem cycBelow_succ {n : Nat} {U : List Nat} (hn : 0 < n) (hnd : U.Nodup)
    (hU : ∀ x ∈ U, 1 ≤ x ∧ x ≤ n) (y : Nat) :
    cycBelow n U (y + 1) = cycBelow n U y + (if y % n + 1 ∈ U then 1 else 0) := by
  have h0 := below_zero_of hU
  have hN := below_top_of hU
  obtain ⟨a, r, hr, rfl⟩ : ∃ a r, r < n ∧ y = n * a + r :=
    ⟨y / n, y % n, Nat.mod_lt _ hn, (Nat.div_add_mod y n).symm⟩
  rw [show n * a + r + 1 = n * a + (r + 1) by omega, cycBelow_rep hn h0 hN a (by omega),
    cycBelow_rep hn h0 hN a hr.le, below_succ hnd,
    show (n * a + r) % n = r by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]]
  omega

/-! ## The first block -/

section First
variable {n : Nat} {d : Nat → Nat}

theorem slipF_le_iff (hd : Adm n d) {x j : Nat} : slipF d x ≤ 2 * j + 1 ↔ x ≤ j := by
  have := hd.le_one x; unfold slipF; omega

theorem slipF_lt_iff (hd : Adm n d) {x j : Nat} : slipF d x < slipF d j ↔ x < j := by
  by_cases e : x = j
  · subst e; simp
  · have := hd.le_one x; have := hd.le_one j; unfold slipF; omega

theorem slipF_bounds (hd : Adm n d) {x : Nat} (hx : 1 ≤ x ∧ x ≤ n) :
    1 ≤ slipF d x ∧ slipF d x ≤ 2 * n := by
  have := hd.le_one x
  rcases Nat.lt_or_ge x n with h | h
  · unfold slipF; omega
  · have e : x = n := by omega
    subst e; unfold slipF; rw [hd.top]; omega

theorem below_mapF (hd : Adm n d) (T : List Nat) (r : Nat) :
    below (T.map (slipF d)) (2 * r + 1) = below T r := by
  unfold below; rw [List.countP_map]
  apply List.countP_congr; intro x _
  simp only [Function.comp_apply, decide_eq_true_eq]; exact slipF_le_iff hd

/-- Doubling transfer for the first block. -/
theorem cycBelow_mapF (hd : Adm n d) (hn : 0 < n) {T : List Nat}
    (hT : ∀ x ∈ T, 1 ≤ x ∧ x ≤ n) {y : Nat} (hy : y < 2 * n) :
    cycBelow (2 * n) (T.map (slipF d)) (2 * y + 1) = cycBelow n T y := by
  have hTm : ∀ z ∈ T.map (slipF d), 1 ≤ z ∧ z ≤ 2 * n := by
    intro z hz; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz; exact slipF_bounds hd (hT x hx)
  obtain ⟨a, r, hr, rfl⟩ : ∃ a r, r < n ∧ y = n * a + r :=
    ⟨y / n, y % n, Nat.mod_lt _ hn, (Nat.div_add_mod y n).symm⟩
  rw [show 2 * (n * a + r) + 1 = 2 * n * a + (2 * r + 1) by rw [Nat.mul_assoc]; omega,
    cycBelow_rep (by omega) (below_zero_of hTm) (below_top_of hTm) a (by omega),
    cycBelow_rep hn (below_zero_of hT) (below_top_of hT) a hr.le, below_mapF hd]
  simp

theorem below_mapF_pred (hd : Adm n d) {T : List Nat} {j : Nat} :
    below (T.map (slipF d)) (slipF d j - 1) = below T (j - 1) := by
  unfold below; rw [List.countP_map]
  apply List.countP_congr; intro x _
  simp only [Function.comp_apply, decide_eq_true_eq]
  have := (slipF_lt_iff hd (x := x) (j := j))
  have := hd.le_one x; have := hd.le_one j; have := hd.zero
  by_cases hx0 : x = 0
  · subst hx0; by_cases hj0 : j = 0
    · subst hj0; unfold slipF at *; omega
    · unfold slipF at *; omega
  · unfold slipF at *; omega

/-- **Slip lemma, one step of the first block.** -/
theorem semiStep_slipF_iff (hd : Adm n d) {T : List Nat} (hnd : T.Nodup)
    (hT : ∀ x ∈ T, 1 ≤ x ∧ x ≤ n) {j : Nat} (hj : 1 ≤ j ∧ j ≤ n) (hjT : j ∉ T)
    (hq : d j = 1 → qq n j ∉ T) :
    SemiStep (2 * n) (T.map (slipF d)) (slipF d j) ↔ SemiStep n T j := by
  have hn : 0 < n := by omega
  have hTm : ∀ z ∈ T.map (slipF d), 1 ≤ z ∧ z ≤ 2 * n := by
    intro z hz; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz; exact slipF_bounds hd (hT x hx)
  have hndm : (T.map (slipF d)).Nodup := nodup_map_of_injOn hnd fun x _ y _ e => by
    have h1 := (slipF_lt_iff hd (x := x) (j := y)); have h2 := (slipF_lt_iff hd (x := y) (j := x))
    omega
  have hfj := slipF_bounds hd hj
  have hjTm : slipF d j ∉ T.map (slipF d) := by
    intro h; obtain ⟨x, hx, e⟩ := List.mem_map.1 h
    have h1 := (slipF_lt_iff hd (x := x) (j := j)); have h2 := (slipF_lt_iff hd (x := j) (j := x))
    have : x = j := by omega
    exact hjT (this ▸ hx)
  rw [semiStep_iff_cyclicStep hndm hTm hfj.1 hfj.2 hjTm, semiStep_iff_cyclicStep hnd hT hj.1 hj.2 hjT]
  unfold CyclicStep
  have hdj := hd.le_one j
  have hy : 2 * j - 1 + d j < 2 * n := by
    rcases Nat.lt_or_ge j n with h | h
    · omega
    · have e : j = n := by omega
      subst e; rw [hd.top]; omega
  rw [show 2 * slipF d j - 1 = 2 * (2 * j - 1 + d j) + 1 by unfold slipF; omega,
    cycBelow_mapF hd hn hT hy, below_mapF_pred hd]
  rcases Nat.lt_or_ge (d j) 1 with h0 | h1
  · rw [show d j = 0 by omega, Nat.add_zero]
  · have e : d j = 1 := by omega
    rw [e, cycBelow_succ hn hnd hT]
    have : ¬ ((2 * j - 1) % n + 1 ∈ T) := hq e
    simp [this]

/-- **Slip lemma, first block.** -/
theorem slipF_semiSymmetric (hd : Adm n d) {τ : List Nat} (hf : IsFoldSeq n τ)
    (hs : SemiSymmetric n τ)
    (hq : ∀ k (hk : k < τ.length), d τ[k] = 1 → qq n τ[k] ∉ τ.take k) :
    SemiSymmetric (2 * n) (τ.map (slipF d)) := by
  have hnd := nodup_of_foldSeq hf
  have bτ : ∀ y ∈ τ, 1 ≤ y ∧ y ≤ n := fun y hy => by
    have := (mem_range'_of_perm hf).1 hy; omega
  intro k hk
  simp only [List.length_map] at hk
  rw [List.getElem_map, ← List.map_take]
  refine (semiStep_slipF_iff hd (take_nodup hnd k) (fun x hx => bτ x (List.mem_of_mem_take hx))
    (bτ _ (List.getElem_mem hk)) ?_ (hq k hk)).2 (hs k hk)
  exact fun h => absurd ((getElem_mem_take_iff hnd hk).1 h) (lt_irrefl k)

end First

/-! ## The second block -/

section Second
variable {n : Nat} {d : Nat → Nat}

/-- The complete first block `[f 1, …, f n]`. -/
def firstBlock (n : Nat) (d : Nat → Nat) : List Nat := (List.range' 1 n).map (slipF d)

theorem slipS_le_iff (hd : Adm n d) {x r : Nat} (hx : 1 ≤ x) :
    slipS d x ≤ 2 * r + 1 ↔ x ≤ r + 1 := by
  have := hd.le_one (x - 1); unfold slipS; omega

theorem slipS_lt_iff (hd : Adm n d) {x j : Nat} (hx : 1 ≤ x) (hj : 1 ≤ j) :
    slipS d x < slipS d j ↔ x < j := by
  by_cases e : x = j
  · subst e; simp
  · have := hd.le_one (x - 1); have := hd.le_one (j - 1); unfold slipS; omega

theorem slipS_bounds (hd : Adm n d) {x : Nat} (hx : 1 ≤ x ∧ x ≤ n) :
    1 ≤ slipS d x ∧ slipS d x ≤ 2 * n := by
  have := hd.le_one (x - 1); have := hd.zero
  by_cases h1 : x = 1
  · subst h1; unfold slipS; rw [show 1 - 1 = 0 from rfl, hd.zero]; omega
  · unfold slipS; omega

theorem slipS_pos (hd : Adm n d) {x : Nat} (hx : 1 ≤ x) : 1 ≤ slipS d x := by
  have := hd.le_one (x - 1)
  by_cases h1 : x = 1
  · subst h1; unfold slipS; rw [show 1 - 1 = 0 from rfl, hd.zero]
  · unfold slipS; omega

theorem slipF_ne_slipS (hd : Adm n d) {x y : Nat} (hy : 1 ≤ y) : slipF d x ≠ slipS d y := by
  have := hd.le_one x; have := hd.le_one (y - 1)
  by_cases e : x = y - 1
  · subst e; unfold slipF slipS; omega
  · unfold slipF slipS; omega

theorem below_firstBlock_odd (hd : Adm n d) {r : Nat} (hr : r ≤ n) :
    below (firstBlock n d) (2 * r + 1) = r := by
  unfold firstBlock below; rw [List.countP_map]
  have : (List.range' 1 n).countP ((fun x => decide (x ≤ 2 * r + 1)) ∘ slipF d) =
      (List.range' 1 n).countP (fun y => decide (1 ≤ y ∧ y ≤ r)) := by
    apply List.countP_congr; intro x hx; rw [List.mem_range'_1] at hx
    simp only [Function.comp_apply, decide_eq_true_eq, slipF_le_iff hd]; omega
  rw [this, countP_range'_interval]; omega

theorem below_firstBlock_pred (hd : Adm n d) {j : Nat} (hj : 1 ≤ j ∧ j ≤ n) :
    below (firstBlock n d) (slipS d j - 1) = j - 1 - d (j - 1) := by
  unfold firstBlock below; rw [List.countP_map]
  have : (List.range' 1 n).countP ((fun x => decide (x ≤ slipS d j - 1)) ∘ slipF d) =
      (List.range' 1 n).countP (fun y => decide (1 ≤ y ∧ y ≤ j - 1 - d (j - 1))) := by
    apply List.countP_congr; intro x hx; rw [List.mem_range'_1] at hx
    simp only [Function.comp_apply, decide_eq_true_eq]
    have := hd.le_one x; have := hd.le_one (j - 1)
    by_cases e : x = j - 1
    · rw [e]; unfold slipF slipS; omega
    · unfold slipF slipS; omega
  rw [this, countP_range'_interval]; have := hd.le_one (j - 1); omega

theorem below_mapS_pred (hd : Adm n d) {U : List Nat} (hU : ∀ x ∈ U, 1 ≤ x) {j : Nat}
    (hj : 1 ≤ j) : below (U.map (slipS d)) (slipS d j - 1) = below U (j - 1) := by
  unfold below; rw [List.countP_map]
  apply List.countP_congr; intro x hx
  simp only [Function.comp_apply, decide_eq_true_eq]
  have := slipS_lt_iff hd (hU x hx) hj; have := slipS_pos hd hj; omega

theorem below_mapS_odd (hd : Adm n d) {U : List Nat} (hU : ∀ x ∈ U, 1 ≤ x) (r : Nat) :
    below (U.map (slipS d)) (2 * r + 1) = below U (r + 1) := by
  unfold below; rw [List.countP_map]
  apply List.countP_congr; intro x hx
  simp only [Function.comp_apply, decide_eq_true_eq]; exact slipS_le_iff hd (hU x hx)

/-- Doubling transfer for the second block (on top of the complete first block). -/
theorem cycBelow_second (hd : Adm n d) (hn : 0 < n) {F U : List Nat}
    (hF : F.Perm (firstBlock n d)) (hU : ∀ x ∈ U, 1 ≤ x ∧ x ≤ n) {y : Nat} (hy : y < 2 * n) :
    cycBelow (2 * n) (F ++ U.map (slipS d)) (2 * y + 1) = y + cycBelow n U (y + 1) := by
  have hFl : F.length = n := by rw [hF.length_eq]; simp [firstBlock]
  have hPl : ∀ z ∈ F ++ U.map (slipS d), 1 ≤ z ∧ z ≤ 2 * n := by
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hF.subset hz)
      rw [List.mem_range'_1] at hx; exact slipF_bounds hd (by omega)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz; exact slipS_bounds hd (hU x hx)
  have hU1 : ∀ x ∈ U, 1 ≤ x := fun x hx => (hU x hx).1
  obtain ⟨a, r, hr, rfl⟩ : ∃ a r, r < n ∧ y = n * a + r :=
    ⟨y / n, y % n, Nat.mod_lt _ hn, (Nat.div_add_mod y n).symm⟩
  rw [show 2 * (n * a + r) + 1 = 2 * n * a + (2 * r + 1) by rw [Nat.mul_assoc]; omega,
    cycBelow_rep (by omega) (below_zero_of hPl) (below_top_of hPl) a (by omega),
    show n * a + r + 1 = n * a + (r + 1) by omega,
    cycBelow_rep hn (below_zero_of hU) (below_top_of hU) a (by omega)]
  have e1 : below (F ++ U.map (slipS d)) (2 * r + 1) = r + below U (r + 1) := by
    unfold below; rw [List.countP_append, hF.countP_eq]
    have := below_firstBlock_odd hd (r := r) (by omega)
    have := below_mapS_odd hd hU1 r
    unfold below at *; omega
  rw [e1, List.length_append, List.length_map, hFl, Nat.mul_add, Nat.mul_comm a n]
  omega

/-- **Slip lemma, one step of the second block.** -/
theorem semiStep_slipS_iff (hd : Adm n d) {F U : List Nat} (hF : F.Perm (firstBlock n d))
    (hnd : U.Nodup) (hU : ∀ x ∈ U, 1 ≤ x ∧ x ≤ n) {j : Nat} (hj : 1 ≤ j ∧ j ≤ n)
    (hjU : j ∉ U) (hp : d (j - 1) = 1 → pp n (j - 1) ∈ U) :
    SemiStep (2 * n) (F ++ U.map (slipS d)) (slipS d j) ↔ SemiStep n U j := by
  have hn : 0 < n := by omega
  have hU1 : ∀ x ∈ U, 1 ≤ x := fun x hx => (hU x hx).1
  have hFnd : F.Nodup := by
    rw [hF.nodup_iff]; unfold firstBlock
    exact nodup_map_of_injOn (List.nodup_range' ..) fun x _ y _ e => by
      have h1 := slipF_lt_iff hd (x := x) (j := y); have h2 := slipF_lt_iff hd (x := y) (j := x)
      omega
  have hPl : ∀ z ∈ F ++ U.map (slipS d), 1 ≤ z ∧ z ≤ 2 * n := by
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hF.subset hz)
      rw [List.mem_range'_1] at hx; exact slipF_bounds hd (by omega)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz; exact slipS_bounds hd (hU x hx)
  have hndS : (U.map (slipS d)).Nodup := nodup_map_of_injOn hnd fun x hx y hy e => by
    have h1 := slipS_lt_iff hd (hU1 x hx) (hU1 y hy)
    have h2 := slipS_lt_iff hd (hU1 y hy) (hU1 x hx)
    omega
  have hndPl : (F ++ U.map (slipS d)).Nodup := by
    refine List.nodup_append.2 ⟨hFnd, hndS, ?_⟩
    intro a ha b hb e
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 (hF.subset ha)
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact slipF_ne_slipS hd (hU1 y hy) e
  have hsj := slipS_bounds hd hj
  have hjPl : slipS d j ∉ F ++ U.map (slipS d) := by
    intro h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨x, -, e⟩ := List.mem_map.1 (hF.subset h)
      exact slipF_ne_slipS hd hj.1 e
    · obtain ⟨x, hx, e⟩ := List.mem_map.1 h
      have h1 := slipS_lt_iff hd (hU1 x hx) hj.1
      have h2 := slipS_lt_iff hd hj.1 (hU1 x hx)
      have : x = j := by omega
      exact hjU (this ▸ hx)
  rw [semiStep_iff_cyclicStep hndPl hPl hsj.1 hsj.2 hjPl,
    semiStep_iff_cyclicStep hnd hU hj.1 hj.2 hjU]
  unfold CyclicStep
  have he := hd.le_one (j - 1)
  have he1 : j = 1 → d (j - 1) = 0 := fun h => by rw [h]; exact hd.zero
  have hy : 2 * j - 2 - d (j - 1) < 2 * n := by omega
  have hbelow : below (F ++ U.map (slipS d)) (slipS d j - 1) =
      j - 1 - d (j - 1) + below U (j - 1) := by
    unfold below; rw [List.countP_append, hF.countP_eq]
    have := below_firstBlock_pred hd hj
    have := below_mapS_pred hd hU1 hj.1
    unfold below at *; omega
  rw [show 2 * slipS d j - 1 = 2 * (2 * j - 2 - d (j - 1)) + 1 by
      unfold slipS; have := he1; by_cases h : j = 1
      · rw [h, hd.zero]
      · omega,
    cycBelow_second hd hn hF hU hy, hbelow]
  rcases Nat.lt_or_ge (d (j - 1)) 1 with h0 | h1
  · rw [show d (j - 1) = 0 by omega, Nat.sub_zero, Nat.sub_zero,
      show 2 * j - 2 + 1 = 2 * j - 1 by omega]
    omega
  · have e : d (j - 1) = 1 := by omega
    have hj2 : 2 ≤ j := by
      by_contra h; have := he1 (by omega); omega
    rw [e, show 2 * j - 2 - 1 + 1 = 2 * j - 2 by omega,
      show 2 * j - 1 = (2 * j - 2) + 1 by omega, cycBelow_succ hn hnd hU (2 * j - 2)]
    have hmem : (2 * j - 2) % n + 1 ∈ U := by
      have := hp e; unfold pp at this; rwa [show 2 * (j - 1) = 2 * j - 2 by omega] at this
    simp only [hmem, ite_true]
    omega

/-- **Slip lemma, second block**: every step of `σ.map (slipS d)` is valid on top of the
complete first block. -/
theorem slipS_steps (hd : Adm n d) {F σ : List Nat} (hF : F.Perm (firstBlock n d))
    (hf : IsFoldSeq n σ) (hs : SemiSymmetric n σ)
    (hp : ∀ k (hk : k < σ.length), d (σ[k] - 1) = 1 → pp n (σ[k] - 1) ∈ σ.take k) :
    ∀ k (hk : k < (σ.map (slipS d)).length),
      SemiStep (2 * n) (F ++ (σ.map (slipS d)).take k) (σ.map (slipS d))[k] := by
  have hnd := nodup_of_foldSeq hf
  have bσ : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ n := fun y hy => by
    have := (mem_range'_of_perm hf).1 hy; omega
  intro k hk
  simp only [List.length_map] at hk
  rw [List.getElem_map, ← List.map_take]
  refine (semiStep_slipS_iff hd hF (take_nodup hnd k)
    (fun x hx => bσ x (List.mem_of_mem_take hx)) (bσ _ (List.getElem_mem hk)) ?_
    (hp k hk)).2 (hs k hk)
  exact fun h => absurd ((getElem_mem_take_iff hnd hk).1 h) (lt_irrefl k)

end Second


/-! ## The slip sequence and the counting inequality -/

section Count
variable {n : Nat} {d : Nat → Nat}

theorem slipF_injective (hd : Adm n d) : Function.Injective (slipF d) := fun x y e => by
  have h1 := slipF_lt_iff hd (x := x) (j := y); have h2 := slipF_lt_iff hd (x := y) (j := x)
  omega

theorem slipS_injective (hd : Adm n d) : Function.Injective (slipS d) := fun x y e => by
  rcases Nat.eq_zero_or_pos x with hx | hx <;> rcases Nat.eq_zero_or_pos y with hy | hy
  · omega
  · subst hx; have := slipS_pos hd hy; unfold slipS at *; omega
  · subst hy; have := slipS_pos hd hx; unfold slipS at *; omega
  · have h1 := slipS_lt_iff hd hx hy; have h2 := slipS_lt_iff hd hy hx; omega

theorem slip_isFoldSeq (hd : Adm n d) {τ σ : List Nat} (hτ : IsFoldSeq n τ)
    (hσ : IsFoldSeq n σ) : IsFoldSeq (2 * n) (τ.map (slipF d) ++ σ.map (slipS d)) := by
  have bτ : ∀ y ∈ τ, 1 ≤ y ∧ y ≤ n := fun y hy => by
    have := (mem_range'_of_perm hτ).1 hy; omega
  have bσ : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ n := fun y hy => by
    have := (mem_range'_of_perm hσ).1 hy; omega
  apply perm_range'_of_nodup_subset
  · refine List.nodup_append.2 ⟨(nodup_of_foldSeq hτ).map (slipF_injective hd),
      (nodup_of_foldSeq hσ).map (slipS_injective hd), ?_⟩
    intro a ha b hb e
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact slipF_ne_slipS hd (bσ y hy).1 e
  · intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz; exact slipF_bounds hd (bτ x hx)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz; exact slipS_bounds hd (bσ x hx)
  · simp [hτ.length_eq, hσ.length_eq]; omega

/-- **Slip lemma.**  Under the order conditions, `τ.map (slipF d) ++ σ.map (slipS d)` is a
semi-symmetric fold sequence of `2n`. -/
theorem slip_mem_semiSeqs (hd : Adm n d) {τ σ : List Nat} (hτ : τ ∈ semiSeqs n)
    (hσ : σ ∈ semiSeqs n)
    (hq : ∀ k (hk : k < τ.length), d τ[k] = 1 → qq n τ[k] ∉ τ.take k)
    (hp : ∀ k (hk : k < σ.length), d (σ[k] - 1) = 1 → pp n (σ[k] - 1) ∈ σ.take k) :
    τ.map (slipF d) ++ σ.map (slipS d) ∈ semiSeqs (2 * n) := by
  rw [mem_semiSeqs] at hτ hσ ⊢
  refine ⟨slip_isFoldSeq hd hτ.1 hσ.1, ?_⟩
  rw [semiSymmetric_append_iff]
  refine ⟨slipF_semiSymmetric hd hτ.1 hτ.2 hq, slipS_steps hd ?_ hσ.1 hσ.2 hp⟩
  unfold firstBlock; exact hτ.1.map _

/-- The slip indicator of a finite set `D`. -/
def ind (D : Finset Nat) (i : Nat) : Nat := if i ∈ D then 1 else 0

theorem adm_ind {n : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 (n - 1)) (hn : 1 ≤ n) :
    Adm n (ind D) where
  le_one i := by unfold ind; split <;> omega
  zero := by
    unfold ind; rw [ite_eq_right_iff.2]; intro h; have := Finset.mem_Icc.1 (hD h); omega
  top := by
    unfold ind; rw [ite_eq_right_iff.2]; intro h; have := Finset.mem_Icc.1 (hD h); omega

open Classical in
/-- Valid first-block sequences for the slip set `D`: every `j ∈ D` comes before `qq n j`. -/
noncomputable def condF (n : Nat) (D : Finset Nat) : Finset (List Nat) :=
  (semiSeqs n).filter fun τ =>
    ∀ k (hk : k < τ.length), ind D τ[k] = 1 → qq n τ[k] ∉ τ.take k

open Classical in
/-- Valid second-block sequences for `D`: for `k ∈ D`, `pp n k` comes before `k + 1`. -/
noncomputable def condS (n : Nat) (D : Finset Nat) : Finset (List Nat) :=
  (semiSeqs n).filter fun σ =>
    ∀ k (hk : k < σ.length), ind D (σ[k] - 1) = 1 → pp n (σ[k] - 1) ∈ σ.take k

/-- The slip map `(D, τ, σ) ↦ τ.map (slipF D) ++ σ.map (slipS D)`. -/
def slipMap (x : (_ : Finset Nat) × (List Nat × List Nat)) : List Nat :=
  x.2.1.map (slipF (ind x.1)) ++ x.2.2.map (slipS (ind x.1))

theorem slipMap_injOn {n : Nat} (hn : 1 ≤ n) :
    Set.InjOn slipMap
      (((Finset.Icc 1 (n - 1)).powerset.sigma fun D => condF n D ×ˢ condS n D :
        Finset ((_ : Finset Nat) × (List Nat × List Nat))) : Set _) := by
  rintro ⟨D, τ, σ⟩ hx ⟨D', τ', σ'⟩ hx' e
  simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_powerset,
    Finset.mem_product, condF, condS, Finset.mem_filter, mem_semiSeqs] at hx hx'
  obtain ⟨hD, ⟨⟨hτ, -⟩, -⟩, ⟨⟨hσ, -⟩, -⟩⟩ := hx
  obtain ⟨hD', ⟨⟨hτ', -⟩, -⟩, ⟨⟨hσ', -⟩, -⟩⟩ := hx'
  have hA := adm_ind hD hn; have hA' := adm_ind hD' hn
  unfold slipMap at e; simp only at e
  have l1 : (τ.map (slipF (ind D))).length = (τ'.map (slipF (ind D'))).length := by
    simp [hτ.length_eq, hτ'.length_eq]
  obtain ⟨e1, e2⟩ := List.append_inj e l1
  -- the slip set is read off the first block: `i ∈ D ↔ 2i+1` is in it
  have key : ∀ (E : Finset Nat) (ρ : List Nat), E ⊆ Finset.Icc 1 (n - 1) → IsFoldSeq n ρ →
      ∀ i, i ∈ E ↔ (1 ≤ i ∧ i ≤ n - 1 ∧ 2 * i + 1 ∈ ρ.map (slipF (ind E))) := by
    intro E ρ hE hρ i
    constructor
    · intro hi
      have := Finset.mem_Icc.1 (hE hi)
      refine ⟨this.1, this.2, List.mem_map.2 ⟨i, (mem_range'_of_perm hρ).2 (by omega), ?_⟩⟩
      unfold slipF ind; rw [ite_eq_left_iff.2 (fun h => absurd hi h)]
    · rintro ⟨-, -, h⟩
      obtain ⟨x, -, hx⟩ := List.mem_map.1 h
      unfold slipF ind at hx
      split at hx
      · have : x = i := by omega
        subst this; assumption
      · omega
  have hDD : D = D' := by
    ext i; rw [key D τ hD hτ i, key D' τ' hD' hτ' i, e1]
  subst hDD
  have hττ : τ = τ' := (List.map_injective_iff.2 (slipF_injective hA)) e1
  have hσσ : σ = σ' := (List.map_injective_iff.2 (slipS_injective hA)) e2
  subst hττ; subst hσσ; rfl

/-- **Slip count inequality.**
`∑_{D ⊆ [1, n-1]} #{τ ∈ V_n : j ∈ D ⇒ j before 2j mod* n} ·
   #{σ ∈ V_n : k ∈ D ⇒ (2k+1) mod* n before k+1}  ≤  a(2n)`. -/
theorem semiCount_slip {n : Nat} (hn : 1 ≤ n) :
    ∑ D ∈ (Finset.Icc 1 (n - 1)).powerset, (condF n D).card * (condS n D).card ≤
      semiCount (2 * n) := by
  have hsub : ((Finset.Icc 1 (n - 1)).powerset.sigma fun D => condF n D ×ˢ condS n D).image
      slipMap ⊆ semiSeqs (2 * n) := by
    intro x hx
    obtain ⟨⟨D, τ, σ⟩, hy, rfl⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_product, condF, condS,
      Finset.mem_filter] at hy
    obtain ⟨hD, ⟨hτ, hq⟩, ⟨hσ, hp⟩⟩ := hy
    exact slip_mem_semiSeqs (adm_ind hD hn) hτ hσ hq hp
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (slipMap_injOn hn), Finset.card_sigma] at this
  simpa [Finset.card_product, semiCount] using this

end Count

/-! ## Parity-block inputs: `a(2n) ≥ 2^{|C_n|} a(⌈n/2⌉)² a(⌊n/2⌋)²` -/

section ParitySlip

/-- Number of guaranteed slip positions: `n/2` for even `n`, `⌊(n+1)/4⌋` for odd `n`. -/
def cnt (n : Nat) : Nat := if n % 2 = 0 then n / 2 else (n + 1) / 4

/-- The guaranteed slip positions `C_n`: the odd `k ≤ n - 1` (`n` even), resp. the odd `k`
with `2k + 1 ≤ n` (`n` odd). -/
def cset (n : Nat) : Finset Nat := (Finset.range (cnt n)).image fun i => 2 * i + 1

theorem card_cset (n : Nat) : (cset n).card = cnt n := by
  unfold cset
  rw [Finset.card_image_of_injective _ (fun x y e => by
    have : 2 * x + 1 = 2 * y + 1 := e
    omega), Finset.card_range]

theorem mem_cset {n k : Nat} (hk : k ∈ cset n) :
    k % 2 = 1 ∧ 1 ≤ k ∧ k + 1 ≤ n ∧ (n % 2 = 0 ∨ 2 * k + 1 ≤ n) := by
  unfold cset cnt at hk
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hk
  rw [Finset.mem_range] at hi
  split at hi <;> omega

theorem cset_sub (n : Nat) : cset n ⊆ Finset.Icc 1 (n - 1) := fun k hk => by
  have := mem_cset hk; rw [Finset.mem_Icc]; omega

/-- For `k ∈ C_n`, `qq n k = 2k mod* n` is even. -/
theorem qq_even {n k : Nat} (hk : k ∈ cset n) : qq n k % 2 = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_cset hk
  unfold qq
  rcases h4 with he | ho
  · have := Nat.mod_mod_of_dvd (2 * k - 1) (Nat.dvd_of_mod_eq_zero he)
    omega
  · have hlt : 2 * k - 1 < n := by omega
    rw [Nat.mod_eq_of_lt hlt]; omega

/-- For `k ∈ C_n`, `pp n k = (2k + 1) mod* n` is odd and at most `n`. -/
theorem pp_odd {n k : Nat} (hk : k ∈ cset n) : pp n k % 2 = 1 ∧ pp n k ≤ n := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_cset hk
  unfold pp
  have hlt : 2 * k % n < n := Nat.mod_lt _ (by omega)
  rcases h4 with he | ho
  · have := Nat.mod_mod_of_dvd (2 * k) (Nat.dvd_of_mod_eq_zero he)
    omega
  · have hlt2 : 2 * k < n := by omega
    rw [Nat.mod_eq_of_lt hlt2]; omega

/-- The odds-first parity-block sequences of `[n]`. -/
noncomputable def oddFirst (n : Nat) : Finset (List Nat) :=
  (semiSeqs ((n + 1) / 2) ×ˢ semiSeqs ((n + (1 - 1)) / 2)).image (blockMap 1)

theorem card_oddFirst (n : Nat) :
    (oddFirst n).card = semiCount ((n + 1) / 2) * semiCount (n / 2) := by
  unfold oddFirst
  rw [Finset.card_image_of_injOn (blockMap_injOn (N := n) (c := 1) le_rfl), Finset.card_product]
  rfl

/-- Structure of an odds-first parity-block sequence. -/
theorem oddFirst_struct {n : Nat} {ρ : List Nat} (h : ρ ∈ oddFirst n) :
    ρ ∈ semiSeqs n ∧ ∃ A B : List Nat, ρ = A ++ B ∧ (∀ x ∈ A, x % 2 = 1) ∧
      (∀ x ∈ B, x % 2 = 0) ∧ (∀ x, x % 2 = 1 → 1 ≤ x → x ≤ n → x ∈ A) := by
  unfold oddFirst at h
  obtain ⟨⟨α, β⟩, hp, rfl⟩ := Finset.mem_image.1 h
  refine ⟨blockMap_mem le_rfl hp, ?_⟩
  rw [Finset.mem_product, mem_semiSeqs, mem_semiSeqs] at hp
  refine ⟨α.map (scale 1), β.map (scale (1 - 1)), rfl, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have := (mem_range'_of_perm hp.1.1).1 hy; unfold scale; omega
  · intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; unfold scale; omega
  · intro x hx1 hx0 hxn
    refine List.mem_map.2 ⟨(x + 1) / 2, (mem_range'_of_perm hp.1.1).2 (by omega), ?_⟩
    unfold scale; omega

theorem oddFirst_sub_condF {n : Nat} {D : Finset Nat} (hD : D ⊆ cset n) :
    oddFirst n ⊆ condF n D := by
  intro ρ hρ
  obtain ⟨hmem, A, B, rfl, hA, hB, -⟩ := oddFirst_struct hρ
  unfold condF
  rw [Finset.mem_filter]
  refine ⟨hmem, fun k hk hd => ?_⟩
  have hjD : (A ++ B)[k] ∈ D := by
    unfold ind at hd; split at hd
    · assumption
    · omega
  have hj := mem_cset (hD hjD)
  have hk' : k < A.length + B.length := by simpa using hk
  have hkA : k < A.length := by
    by_contra hc
    have e : (A ++ B)[k] = B[k - A.length]'(by omega) :=
      List.getElem_append_right (by omega)
    have := hB _ (List.getElem_mem (l := B) (n := k - A.length) (by omega))
    rw [← e] at this
    omega
  intro hq
  rw [List.take_append_of_le_length hkA.le] at hq
  have := hA _ (List.mem_of_mem_take hq)
  have := qq_even (hD hjD)
  omega

theorem oddFirst_sub_condS {n : Nat} {D : Finset Nat} (hD : D ⊆ cset n) :
    oddFirst n ⊆ condS n D := by
  intro ρ hρ
  obtain ⟨hmem, A, B, rfl, hA, hB, hAall⟩ := oddFirst_struct hρ
  unfold condS
  rw [Finset.mem_filter]
  refine ⟨hmem, fun k hk hd => ?_⟩
  have hjD : (A ++ B)[k] - 1 ∈ D := by
    unfold ind at hd; split at hd
    · assumption
    · omega
  have hj := mem_cset (hD hjD)
  have hkA : A.length ≤ k := by
    by_contra hc
    have e : (A ++ B)[k] = A[k]'(by omega) := List.getElem_append_left (by omega)
    have := hA _ (List.getElem_mem (l := A) (n := k) (by omega))
    rw [← e] at this
    omega
  have hpp := pp_odd (hD hjD)
  have hmA : pp n ((A ++ B)[k] - 1) ∈ A := hAall _ hpp.1 (by omega) hpp.2
  rw [List.take_append, List.take_of_length_le hkA]
  exact List.mem_append_left _ hmA

/-- **Parity-slip recursion.**  `2^{|C_n|} · (a(⌈n/2⌉) · a(⌊n/2⌋))² ≤ a(2n)`. -/
theorem semiCount_paritySlip {n : Nat} (hn : 1 ≤ n) :
    2 ^ cnt n * (semiCount ((n + 1) / 2) * semiCount (n / 2)) ^ 2 ≤ semiCount (2 * n) := by
  refine le_trans ?_ (semiCount_slip hn)
  have hsub : (cset n).powerset ⊆ (Finset.Icc 1 (n - 1)).powerset :=
    Finset.powerset_mono.2 (cset_sub n)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
  have : ∀ D ∈ (cset n).powerset,
      (semiCount ((n + 1) / 2) * semiCount (n / 2)) ^ 2 ≤ (condF n D).card * (condS n D).card := by
    intro D hD
    rw [Finset.mem_powerset] at hD
    rw [Nat.pow_two, ← card_oddFirst]
    exact Nat.mul_le_mul (Finset.card_le_card (oddFirst_sub_condF hD))
      (Finset.card_le_card (oddFirst_sub_condS hD))
  refine le_trans ?_ (Finset.sum_le_sum this)
  rw [Finset.sum_const, Finset.card_powerset, card_cset]
  exact le_of_eq rfl

/-- `a(4m) ≥ 2^m · a(m)^4`. -/
theorem semiCount_four_mul {m : Nat} (hm : 1 ≤ m) :
    2 ^ m * semiCount m ^ 4 ≤ semiCount (4 * m) := by
  have := semiCount_paritySlip (n := 2 * m) (by omega)
  rw [show cnt (2 * m) = m by unfold cnt; split <;> omega,
    show (2 * m + 1) / 2 = m by omega, show 2 * m / 2 = m by omega,
    show 2 * (2 * m) = 4 * m by omega, ← Nat.pow_two, ← Nat.pow_mul] at this
  exact this

/-- `a(4m+2) ≥ 2^{⌊(m+1)/2⌋} · a(m)² · a(m+1)²`. -/
theorem semiCount_four_mul_add_two (m : Nat) :
    2 ^ ((m + 1) / 2) * (semiCount (m + 1) * semiCount m) ^ 2 ≤ semiCount (4 * m + 2) := by
  have := semiCount_paritySlip (n := 2 * m + 1) (by omega)
  rw [show cnt (2 * m + 1) = (m + 1) / 2 by unfold cnt; split <;> omega,
    show (2 * m + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1) / 2 = m by omega,
    show 2 * (2 * m + 1) = 4 * m + 2 by omega] at this
  exact this

/-- **Super-exponential lower bound** along `N = 4^j`:  `N^N ≤ a(N)^8`, i.e.
`a(N) ≥ N^{N/8}`. -/
theorem pow_le_semiCount_pow_four (j : Nat) : (4 ^ j) ^ (4 ^ j) ≤ semiCount (4 ^ j) ^ 8 := by
  induction j with
  | zero =>
    have := semiCount_one_pos
    simp only [Nat.pow_zero, Nat.pow_one]
    exact Nat.one_le_pow _ _ this
  | succ j ih =>
    have hpos : 1 ≤ 4 ^ j := Nat.one_le_pow _ _ (by omega)
    have key := semiCount_four_mul hpos
    rw [show 4 ^ (j + 1) = 4 * 4 ^ j by rw [Nat.pow_succ, Nat.mul_comm]]
    have e1 : (4 : Nat) ^ (4 * 4 ^ j) = (2 ^ (4 ^ j)) ^ 8 :=
      calc (4 : Nat) ^ (4 * 4 ^ j) = (2 ^ 2) ^ (4 * 4 ^ j) := rfl
        _ = 2 ^ (2 * (4 * 4 ^ j)) := (Nat.pow_mul 2 2 _).symm
        _ = 2 ^ (4 ^ j * 8) := by congr 1; omega
        _ = (2 ^ (4 ^ j)) ^ 8 := Nat.pow_mul 2 _ 8
    have e2 : (4 ^ j) ^ (4 * 4 ^ j) = ((4 ^ j) ^ (4 ^ j)) ^ 4 := by
      rw [show 4 * 4 ^ j = 4 ^ j * 4 by omega, Nat.pow_mul]
    calc (4 * 4 ^ j) ^ (4 * 4 ^ j)
        = (2 ^ (4 ^ j)) ^ 8 * ((4 ^ j) ^ (4 ^ j)) ^ 4 := by rw [Nat.mul_pow, e1, e2]
      _ ≤ (2 ^ (4 ^ j)) ^ 8 * (semiCount (4 ^ j) ^ 8) ^ 4 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ih 4)
      _ = (2 ^ (4 ^ j) * semiCount (4 ^ j) ^ 4) ^ 8 := by
          rw [Nat.mul_pow]; congr 1; rw [← Nat.pow_mul, ← Nat.pow_mul]
      _ ≤ semiCount (4 * 4 ^ j) ^ 8 := Nat.pow_le_pow_left key 8

end ParitySlip

end Slip
end Folds
