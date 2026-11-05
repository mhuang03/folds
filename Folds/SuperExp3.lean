import Folds.SuperExp

/-!
# The general slip lemma

`experiments/superexp3/PROOFS.txt`, Theorem A.  A *block* of the `N`-strip is an increasing
enumeration `g : [1, n₂] → [1, N]` together with its counting function `μ`
(`g x ≤ y ↔ x ≤ μ y`).  Placing the block in the order `σ` (a list of indices) on top of an
arbitrary list `F` of already placed panels disjoint from it, each step is valid iff an
*induced* window condition holds for `σ`:

  `P̃_F(2 g_j − 1) + ũ(μ̃(2 g_j − 1)) = 2 (P_F(g_j − 1) + u(j − 1))`

where `u` counts the indices placed before `j`, `ũ` is its cyclic version with modulus `n₂`
and `μ̃(N a + r) = n₂ a + μ r` (`semiStep_block_iff`).  With `F = []` this is the condition
`ũ(μ̃(2 g_j − 1)) = 2 u(j − 1)` for a first block (`semiStep_first_iff`); with `F` the complete
first block `X` it is the second-block condition.  Nothing is assumed about `X`: the classical
slip lemma (`Folds.Slip`, `X = {2i + d_i}`), the parity-block theorem and the residue-class
compositions are the special cases where the induced condition is (nearly) the strip
condition of `[1, n₂]`.  `defectFree_iff`: when the defect vanishes,
`μ̃(2 g_j − 1) = 2j − 1` and `F` contributes the right amount, the step is valid in the
`N`-strip iff it is valid in the `n₂`-strip.

`Block.ofMono`: every increasing enumeration of a set of panels is a block (with
`μ y = #{i : g i ≤ y}`), so the lemma applies to every split `[N] = X ⊔ Xᶜ`.
`block_semiSymmetric_iff` and `blocks_mem_semiSeqs_iff` assemble whole sequences (an iff:
the induced conditions are also necessary); `card_mul_le` turns the lemma into the counting
bound `#{τ : first-block conditions} · #{σ : second-block conditions} ≤ a(N)` for each split.

This file does not improve the exponents 1/6 (`N = 2^L`) and 1/22 (all `N`) of
`Folds.SuperExp2`; see `experiments/superexp3/PROOFS.txt` for why the extra freedom it
exposes could not be certified recursively.
-/

namespace Folds
namespace GSlip

open Slip

/-- An increasing enumeration `g : [1, n] → [1, N]` with counting function `μ`. -/
structure Block (N n : Nat) (g μ : Nat → Nat) : Prop where
  pos : ∀ x, 1 ≤ x → x ≤ n → 1 ≤ g x
  le : ∀ x, 1 ≤ x → x ≤ n → g x ≤ N
  mono : ∀ x y, 1 ≤ x → y ≤ n → x < y → g x < g y
  count : ∀ x y, 1 ≤ x → x ≤ n → (g x ≤ y ↔ x ≤ μ y)
  cle : ∀ y, μ y ≤ n

/-- The counting function of an increasing enumeration. -/
theorem count_iff (f : Nat → Nat) : ∀ n : Nat, (∀ x y, 1 ≤ x → y ≤ n → x < y → f x < f y) →
    ∀ y, (∀ x, 1 ≤ x → x ≤ n →
      (f x ≤ y ↔ x ≤ (List.range' 1 n).countP (fun i => f i ≤ y))) ∧
      (List.range' 1 n).countP (fun i => f i ≤ y) ≤ n := by
  intro n
  induction n with
  | zero => intro _ y; exact ⟨fun x h1 h2 => by omega, by simp⟩
  | succ n ih =>
    intro hm y
    obtain ⟨ih1, ih2⟩ := ih (fun x z h1 h2 h3 => hm x z h1 (by omega) h3) y
    rw [List.range'_concat, List.countP_append]
    simp only [List.countP_cons, List.countP_nil, Nat.one_mul, Nat.zero_add]
    by_cases hy : f (1 + n) ≤ y
    · have hc : (List.range' 1 n).countP (fun i => f i ≤ y) = n := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simp
        · have := (ih1 n hpos le_rfl).1 (le_of_lt (lt_of_lt_of_le (hm n (1 + n) hpos (by omega) (by omega)) hy))
          omega
      simp only [hy, decide_true, ite_true, hc]
      refine ⟨fun x h1 h2 => ?_, by omega⟩
      constructor
      · intro; omega
      · intro
        rcases Nat.lt_or_ge x (n + 1) with h | h
        · exact le_of_lt (lt_of_lt_of_le (hm x (1 + n) h1 (by omega) (by omega)) hy)
        · rw [show x = 1 + n by omega]; exact hy
    · simp only [hy, decide_false]
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      refine ⟨fun x h1 h2 => ?_, by omega⟩
      rcases Nat.lt_or_ge x (n + 1) with h | h
      · exact ih1 x h1 (by omega)
      · have e : x = 1 + n := by omega
        subst e; constructor
        · intro h'; exact absurd h' hy
        · intro h'; omega

/-- Every increasing enumeration of a set of panels is a block, with counting function
`μ y = #{i ∈ [1, n] : g i ≤ y}` (= `below ((List.range' 1 n).map g) y`): Theorem A applies to
an arbitrary set `X`. -/
theorem Block.ofMono {N n : Nat} {g : Nat → Nat} (hpos : ∀ x, 1 ≤ x → x ≤ n → 1 ≤ g x)
    (hle : ∀ x, 1 ≤ x → x ≤ n → g x ≤ N) (hm : ∀ x y, 1 ≤ x → y ≤ n → x < y → g x < g y) :
    Block N n g (fun y => (List.range' 1 n).countP (fun i => g i ≤ y)) :=
  ⟨hpos, hle, hm, fun x y h1 h2 => (count_iff g n hm y).1 x h1 h2,
    fun y => (count_iff g n hm y).2⟩

/-- The cyclic extension `μ̃(N a + r) = n a + μ r`. -/
def ext (N n : Nat) (μ : Nat → Nat) (z : Nat) : Nat := n * (z / N) + μ (z % N)

section
variable {N n : Nat} {g μ : Nat → Nat}

theorem Block.inj (hb : Block N n g μ) {x y : Nat} (hx : 1 ≤ x ∧ x ≤ n) (hy : 1 ≤ y ∧ y ≤ n)
    (e : g x = g y) : x = y := by
  rcases Nat.lt_trichotomy x y with h | h | h
  · have := hb.mono x y hx.1 hy.2 h; omega
  · exact h
  · have := hb.mono y x hy.1 hx.2 h; omega

theorem below_map (hb : Block N n g μ) {U : List Nat} (hU : ∀ x ∈ U, 1 ≤ x ∧ x ≤ n) (y : Nat) :
    below (U.map g) y = below U (μ y) := by
  unfold below; rw [List.countP_map]
  apply List.countP_congr; intro x hx
  simp only [Function.comp_apply, decide_eq_true_eq]
  exact hb.count x y (hU x hx).1 (hU x hx).2

/-- **Transfer**: the cyclic count of a block is the cyclic count of its indices, read at
`μ̃`. -/
theorem cycBelow_map (hb : Block N n g μ) (hn : 0 < n) {U : List Nat}
    (hU : ∀ x ∈ U, 1 ≤ x ∧ x ≤ n) (z : Nat) :
    cycBelow N (U.map g) z = cycBelow n U (ext N n μ z) := by
  unfold ext
  rw [cycBelow_rep hn (below_zero_of hU) (below_top_of hU) (z / N) (hb.cle _)]
  unfold cycBelow
  rw [below_map hb hU, List.length_map]

theorem below_map_pred (hb : Block N n g μ) {U : List Nat} (hU : ∀ x ∈ U, 1 ≤ x ∧ x ≤ n)
    {j : Nat} (hj : 1 ≤ j ∧ j ≤ n) :
    below (U.map g) (g j - 1) = below U (j - 1) := by
  unfold below; rw [List.countP_map]
  apply List.countP_congr; intro x hx
  simp only [Function.comp_apply, decide_eq_true_eq]
  have hx' := hU x hx
  have hgj := hb.pos j hj.1 hj.2
  constructor
  · intro h
    by_contra hc
    rcases Nat.lt_or_ge j x with hjx | hjx
    · have := hb.mono j x hj.1 hx'.2 hjx; omega
    · have : x = j := by omega
      subst this; omega
  · intro h
    have := hb.mono x j hx'.1 hj.2 (by omega); omega

theorem cycBelow_append (N : Nat) (A B : List Nat) (z : Nat) :
    cycBelow N (A ++ B) z = cycBelow N A z + cycBelow N B z := by
  unfold cycBelow below; rw [List.countP_append, List.length_append]; ring

theorem below_append (A B : List Nat) (y : Nat) : below (A ++ B) y = below A y + below B y := by
  unfold below; rw [List.countP_append]

/-- **General slip lemma, one step** (any block, on top of any disjoint placed list `F`). -/
theorem semiStep_block_iff (hb : Block N n g μ) {F U : List Nat} (hFnd : F.Nodup)
    (hF : ∀ z ∈ F, 1 ≤ z ∧ z ≤ N) (hdisj : ∀ x, 1 ≤ x → x ≤ n → g x ∉ F)
    (hnd : U.Nodup) (hU : ∀ x ∈ U, 1 ≤ x ∧ x ≤ n) {j : Nat} (hj : 1 ≤ j ∧ j ≤ n) (hjU : j ∉ U) :
    SemiStep N (F ++ U.map g) (g j) ↔
      cycBelow N F (2 * g j - 1) + cycBelow n U (ext N n μ (2 * g j - 1)) =
        2 * (below F (g j - 1) + below U (j - 1)) := by
  have hn : 0 < n := by omega
  have hndU : (U.map g).Nodup :=
    nodup_map_of_injOn hnd fun x hx y hy e => hb.inj (hU x hx) (hU y hy) e
  have hnd' : (F ++ U.map g).Nodup := by
    refine List.nodup_append.2 ⟨hFnd, hndU, ?_⟩
    intro a ha b hb' e
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb'
    exact hdisj y (hU y hy).1 (hU y hy).2 (e ▸ ha)
  have hS : ∀ z ∈ F ++ U.map g, 1 ≤ z ∧ z ≤ N := by
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact hF z hz
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
      exact ⟨hb.pos x (hU x hx).1 (hU x hx).2, hb.le x (hU x hx).1 (hU x hx).2⟩
  have hjS : g j ∉ F ++ U.map g := by
    intro h
    rcases List.mem_append.1 h with h | h
    · exact hdisj j hj.1 hj.2 h
    · obtain ⟨x, hx, e⟩ := List.mem_map.1 h
      exact hjU (hb.inj (hU x hx) hj e ▸ hx)
  rw [semiStep_iff_cyclicStep hnd' hS (hb.pos j hj.1 hj.2) (hb.le j hj.1 hj.2) hjS]
  unfold CyclicStep
  rw [cycBelow_append, cycBelow_map hb hn hU, below_append, below_map_pred hb hU hj]

/-- **General slip lemma, first block** (`F = []`). -/
theorem semiStep_first_iff (hb : Block N n g μ) {U : List Nat} (hnd : U.Nodup)
    (hU : ∀ x ∈ U, 1 ≤ x ∧ x ≤ n) {j : Nat} (hj : 1 ≤ j ∧ j ≤ n) (hjU : j ∉ U) :
    SemiStep N (U.map g) (g j) ↔
      cycBelow n U (ext N n μ (2 * g j - 1)) = 2 * below U (j - 1) := by
  have := semiStep_block_iff hb List.nodup_nil (by simp) (by simp) hnd hU hj hjU
  simpa [cycBelow, below] using this

/-- **Defect-free steps.**  If the block is doubling-compatible at `j`
(`μ̃(2 g_j − 1) = 2j − 1`) and the placed list `F` is balanced there
(`P̃_F(2 g_j − 1) = 2 P_F(g_j − 1)`), the step is valid in the `N`-strip iff the index step is
valid in the `n`-strip. -/
theorem defectFree_iff (hb : Block N n g μ) {F U : List Nat} (hFnd : F.Nodup)
    (hF : ∀ z ∈ F, 1 ≤ z ∧ z ≤ N) (hdisj : ∀ x, 1 ≤ x → x ≤ n → g x ∉ F)
    (hnd : U.Nodup) (hU : ∀ x ∈ U, 1 ≤ x ∧ x ≤ n) {j : Nat} (hj : 1 ≤ j ∧ j ≤ n) (hjU : j ∉ U)
    (hdef : ext N n μ (2 * g j - 1) = 2 * j - 1)
    (hbal : cycBelow N F (2 * g j - 1) = 2 * below F (g j - 1)) :
    SemiStep N (F ++ U.map g) (g j) ↔ SemiStep n U j := by
  rw [semiStep_block_iff hb hFnd hF hdisj hnd hU hj hjU, hdef, hbal,
    semiStep_iff_cyclicStep hnd hU hj.1 hj.2 hjU]
  unfold CyclicStep
  omega

/-- **General slip lemma, whole block**: `σ.map g` is a valid continuation of `F` iff every
step satisfies the induced condition. -/
theorem block_steps_iff (hb : Block N n g μ) {F σ : List Nat} (hFnd : F.Nodup)
    (hF : ∀ z ∈ F, 1 ≤ z ∧ z ≤ N) (hdisj : ∀ x, 1 ≤ x → x ≤ n → g x ∉ F)
    (hσ : IsFoldSeq n σ) :
    (∀ k (hk : k < (σ.map g).length), SemiStep N (F ++ (σ.map g).take k) (σ.map g)[k]) ↔
      ∀ k (hk : k < σ.length),
        cycBelow N F (2 * g σ[k] - 1) + cycBelow n (σ.take k) (ext N n μ (2 * g σ[k] - 1)) =
          2 * (below F (g σ[k] - 1) + below (σ.take k) (σ[k] - 1)) := by
  have hnd := nodup_of_foldSeq hσ
  have bσ : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ n := fun y hy => by
    have := (mem_range'_of_perm hσ).1 hy; omega
  have key : ∀ k (hk : k < σ.length),
      SemiStep N (F ++ (σ.map g).take k) (g σ[k]) ↔
        cycBelow N F (2 * g σ[k] - 1) + cycBelow n (σ.take k) (ext N n μ (2 * g σ[k] - 1)) =
          2 * (below F (g σ[k] - 1) + below (σ.take k) (σ[k] - 1)) := by
    intro k hk
    rw [← List.map_take]
    exact semiStep_block_iff hb hFnd hF hdisj (take_nodup hnd k)
      (fun x hx => bσ x (List.mem_of_mem_take hx)) (bσ _ (List.getElem_mem hk))
      (fun h => absurd ((getElem_mem_take_iff hnd hk).1 h) (lt_irrefl k))
  constructor
  · intro h k hk
    have := h k (by simpa using hk)
    rw [List.getElem_map] at this
    exact (key k hk).1 this
  · intro h k hk
    simp only [List.length_map] at hk
    rw [List.getElem_map]
    exact (key k hk).2 (h k hk)

/-- First block alone: `τ.map f` is semi-symmetric iff every step satisfies
`t̃(κ̃(2 f_j − 1)) = 2 t(j − 1)`. -/
theorem block_semiSymmetric_iff (hb : Block N n g μ) {τ : List Nat} (hτ : IsFoldSeq n τ) :
    SemiSymmetric N (τ.map g) ↔
      ∀ k (hk : k < τ.length),
        cycBelow n (τ.take k) (ext N n μ (2 * g τ[k] - 1)) = 2 * below (τ.take k) (τ[k] - 1) := by
  have := block_steps_iff hb (F := []) List.nodup_nil (by simp) (by simp) hτ
  simp only [List.nil_append] at this
  unfold SemiSymmetric
  rw [this]
  simp [cycBelow, below]

end

/-! ## Two complementary blocks -/

section Two
variable {N n₁ n₂ : Nat} {f κ g μ : Nat → Nat}

/-- Two blocks `f : [1, n₁] → [1, N]`, `g : [1, n₂] → [1, N]` with disjoint images,
`n₁ + n₂ = N`: a split of the `N`-strip. -/
structure Split (N n₁ n₂ : Nat) (f κ g μ : Nat → Nat) : Prop where
  bf : Block N n₁ f κ
  bg : Block N n₂ g μ
  disj : ∀ x y, 1 ≤ x → x ≤ n₁ → 1 ≤ y → y ≤ n₂ → f x ≠ g y
  sum : n₁ + n₂ = N

theorem Split.first_perm (hs : Split N n₁ n₂ f κ g μ) :
    ∀ z ∈ (List.range' 1 n₁).map f, 1 ≤ z ∧ z ≤ N := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
  rw [List.mem_range'_1] at hx
  exact ⟨hs.bf.pos x (by omega) (by omega), hs.bf.le x (by omega) (by omega)⟩

theorem Split.isFoldSeq (hs : Split N n₁ n₂ f κ g μ) {τ σ : List Nat} (hτ : IsFoldSeq n₁ τ)
    (hσ : IsFoldSeq n₂ σ) : IsFoldSeq N (τ.map f ++ σ.map g) := by
  have bτ : ∀ y ∈ τ, 1 ≤ y ∧ y ≤ n₁ := fun y hy => by
    have := (mem_range'_of_perm hτ).1 hy; omega
  have bσ : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ n₂ := fun y hy => by
    have := (mem_range'_of_perm hσ).1 hy; omega
  apply perm_range'_of_nodup_subset
  · refine List.nodup_append.2 ⟨nodup_map_of_injOn (nodup_of_foldSeq hτ)
      fun x hx y hy e => hs.bf.inj (bτ x hx) (bτ y hy) e,
      nodup_map_of_injOn (nodup_of_foldSeq hσ) fun x hx y hy e => hs.bg.inj (bσ x hx) (bσ y hy) e,
      ?_⟩
    intro a ha b hb e
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact hs.disj x y (bτ x hx).1 (bτ x hx).2 (bσ y hy).1 (bσ y hy).2 e
  · intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
      exact ⟨hs.bf.pos x (bτ x hx).1 (bτ x hx).2, hs.bf.le x (bτ x hx).1 (bτ x hx).2⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
      exact ⟨hs.bg.pos x (bσ x hx).1 (bσ x hx).2, hs.bg.le x (bσ x hx).1 (bσ x hx).2⟩
  · simp [hτ.length_eq, hσ.length_eq, hs.sum]

/-- The induced first-block condition on an index sequence `τ`. -/
def FirstCond (N n₁ : Nat) (f κ : Nat → Nat) (τ : List Nat) : Prop :=
  ∀ k (hk : k < τ.length),
    cycBelow n₁ (τ.take k) (ext N n₁ κ (2 * f τ[k] - 1)) = 2 * below (τ.take k) (τ[k] - 1)

/-- The induced second-block condition on `σ`, on top of the complete first block `F`. -/
def SecondCond (N n₂ : Nat) (F : List Nat) (g μ : Nat → Nat) (σ : List Nat) : Prop :=
  ∀ k (hk : k < σ.length),
    cycBelow N F (2 * g σ[k] - 1) + cycBelow n₂ (σ.take k) (ext N n₂ μ (2 * g σ[k] - 1)) =
      2 * (below F (g σ[k] - 1) + below (σ.take k) (σ[k] - 1))

/-- **General slip lemma** (PROOFS.txt Theorem A): for any split, `τ.map f ++ σ.map g` is a
semi-symmetric fold sequence iff `τ`, `σ` are permutations satisfying the induced conditions.
(The complete first block may be listed in any order: only its set enters.) -/
theorem blocks_mem_semiSeqs_iff (hs : Split N n₁ n₂ f κ g μ) {τ σ : List Nat}
    (hτ : IsFoldSeq n₁ τ) (hσ : IsFoldSeq n₂ σ) :
    τ.map f ++ σ.map g ∈ semiSeqs N ↔
      FirstCond N n₁ f κ τ ∧ SecondCond N n₂ ((List.range' 1 n₁).map f) g μ σ := by
  have bτ : ∀ y ∈ τ, 1 ≤ y ∧ y ≤ n₁ := fun y hy => by
    have := (mem_range'_of_perm hτ).1 hy; omega
  have hFp : (τ.map f).Perm ((List.range' 1 n₁).map f) := hτ.map f
  have hFnd : (τ.map f).Nodup :=
    nodup_map_of_injOn (nodup_of_foldSeq hτ) fun x hx y hy e => hs.bf.inj (bτ x hx) (bτ y hy) e
  have hF : ∀ z ∈ τ.map f, 1 ≤ z ∧ z ≤ N := fun z hz => hs.first_perm z (hFp.subset hz)
  have hdisj : ∀ x, 1 ≤ x → x ≤ n₂ → g x ∉ τ.map f := by
    intro x hx1 hx2 h
    obtain ⟨y, hy, e⟩ := List.mem_map.1 h
    exact hs.disj y x (bτ y hy).1 (bτ y hy).2 hx1 hx2 e
  rw [mem_semiSeqs, semiSymmetric_append_iff, block_semiSymmetric_iff hs.bf hτ,
    block_steps_iff hs.bg hFnd hF hdisj hσ]
  have hc : ∀ z, cycBelow N (τ.map f) z = cycBelow N ((List.range' 1 n₁).map f) z := by
    intro z; unfold cycBelow below; rw [hFp.countP_eq, hFp.length_eq]
  have hb : ∀ z, below (τ.map f) z = below ((List.range' 1 n₁).map f) z := by
    intro z; unfold below; rw [hFp.countP_eq]
  simp only [hc, hb]
  unfold FirstCond SecondCond
  exact ⟨fun h => h.2, fun h => ⟨hs.isFoldSeq hτ hσ, h⟩⟩

open Classical in
/-- **Counting**: for each split, `#{τ : FirstCond} · #{σ : SecondCond} ≤ a(N)` (`τ`, `σ`
ranging over all permutations of the index sets). -/
theorem card_mul_le (hs : Split N n₁ n₂ f κ g μ) :
    (((List.range' 1 n₁).permutations.toFinset.filter (FirstCond N n₁ f κ)).card *
      ((List.range' 1 n₂).permutations.toFinset.filter
        (SecondCond N n₂ ((List.range' 1 n₁).map f) g μ)).card) ≤ semiCount N := by
  set A := (List.range' 1 n₁).permutations.toFinset.filter (FirstCond N n₁ f κ)
  set B := (List.range' 1 n₂).permutations.toFinset.filter
    (SecondCond N n₂ ((List.range' 1 n₁).map f) g μ)
  have hA : ∀ τ ∈ A, IsFoldSeq n₁ τ ∧ FirstCond N n₁ f κ τ := by
    intro τ h; simp only [A, Finset.mem_filter, List.mem_toFinset, List.mem_permutations] at h
    exact h
  have hB : ∀ σ ∈ B, IsFoldSeq n₂ σ ∧ SecondCond N n₂ ((List.range' 1 n₁).map f) g μ σ := by
    intro σ h; simp only [B, Finset.mem_filter, List.mem_toFinset, List.mem_permutations] at h
    exact h
  rw [← Finset.card_product]
  unfold semiCount
  refine Finset.card_le_card_of_injOn (fun p => p.1.map f ++ p.2.map g) ?_ ?_
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_product] at hp
    exact (blocks_mem_semiSeqs_iff hs (hA _ hp.1).1 (hB _ hp.2).1).2 ⟨(hA _ hp.1).2, (hB _ hp.2).2⟩
  · intro p hp q hq e
    rw [Finset.mem_coe, Finset.mem_product] at hp hq
    have lp := (hA _ hp.1).1.length_eq; have lq := (hA _ hq.1).1.length_eq
    simp only [List.length_range'] at lp lq
    have hl : (p.1.map f).length = (q.1.map f).length := by simp [lp, lq]
    obtain ⟨e1, e2⟩ := List.append_inj e hl
    have bp1 : ∀ y ∈ p.1, 1 ≤ y ∧ y ≤ n₁ := fun y hy => by
      have := (mem_range'_of_perm (hA _ hp.1).1).1 hy; omega
    have bq1 : ∀ y ∈ q.1, 1 ≤ y ∧ y ≤ n₁ := fun y hy => by
      have := (mem_range'_of_perm (hA _ hq.1).1).1 hy; omega
    have bp2 : ∀ y ∈ p.2, 1 ≤ y ∧ y ≤ n₂ := fun y hy => by
      have := (mem_range'_of_perm (hB _ hp.2).1).1 hy; omega
    have bq2 : ∀ y ∈ q.2, 1 ≤ y ∧ y ≤ n₂ := fun y hy => by
      have := (mem_range'_of_perm (hB _ hq.2).1).1 hy; omega
    have i1 : p.1 = q.1 := map_injOn_eq e1 bp1 bq1 hs.bf
    have i2 : p.2 = q.2 := map_injOn_eq e2 bp2 bq2 hs.bg
    exact Prod.ext i1 i2
where
  map_injOn_eq {n : Nat} {g μ : Nat → Nat} {l l' : List Nat} (e : l.map g = l'.map g)
      (hl : ∀ y ∈ l, 1 ≤ y ∧ y ≤ n) (hl' : ∀ y ∈ l', 1 ≤ y ∧ y ≤ n) (hb : Block N n g μ) :
      l = l' := by
    induction l generalizing l' with
    | nil => cases l' with
      | nil => rfl
      | cons _ _ => simp at e
    | cons a t ih => cases l' with
      | nil => simp at e
      | cons b t' =>
        simp only [List.map_cons, List.cons.injEq] at e
        have hab := hb.inj (hl a (by simp)) (hl' b (by simp)) e.1
        rw [hab, ih e.2 (fun y hy => hl y (by simp [hy])) (fun y hy => hl' y (by simp [hy]))]

end Two

end GSlip
end Folds
