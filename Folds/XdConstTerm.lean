import Folds.Recursion
import Folds.Cyclic
import Folds.Wallis
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Group.Int.Even

/-!
# Constant-term form, balanced tournaments, mod-`p` relaxations and a signed count

Notation of `experiments/xd_constterm/NOTES.txt`.

For a fold sequence `a` and a panel `m`, `Dp N a m` is the imbalance
`D_m = #(earlier panels in the left arm of m) − #(earlier panels in the right arm of m)`.

* `semiSymmetric_iff_Dp`, `semiCount_eq_card_Dp`: `a(N) = #{a : ∀ m, D_m(a) = 0}`
  (the constant-term form `a(N) = CT ∑_a ∏_m z_m^{D_m(a)}`).
* `modCount p N` (`a_p(N)`): sequences with `p ∣ D_m` for all `m`.
  `semiCount_le_modCount`: `a(N) ≤ a_p(N)`; `modCount_eq_semiCount`: `a_p(N) = a(N)` when `N ≤ 2p`.
* Tournaments: a tournament on `[1,N]` is its inversion set `I ⊆ pairs N` (the pairs `x < y` in
  which `y` is earlier).  `DT N I m` is the imbalance of `m`, `Balanced`, `balCount N = B(N)`.
  `DT_invSet`: the tournament of a fold sequence has the same imbalances;
  `invSet_injOn`: a fold sequence is determined by its tournament;
  `semiCount_le_balCount`: `a(N) ≤ B(N)`.
* `sum_DT`, `sum_Dp` (pair-sum formula): `∑_m D_m = ∑_{x<y} (if y earlier then −d_{xy} else c_{xy})`
  with `c_{xy} = [x ∈ W(y)]`, `d_{xy} = [y ∈ W(x)]`: a weighted graph-inversion statistic.
* Signed count.  `sgn N a = ∏_m (−1)^{D_m(a)}` (`sgn_eq`).  `sgn_rotate`: moving the first panel
  `p` to the end multiplies the sign by `(−1)^{#{m ≠ p : p ∈ W(m)}}`; for `N = 2n` that number
  is `n − 1` (`card_inWindow`).  Hence `sum_sgn_eq_zero`: `∑_a ∏_m (−1)^{D_m(a)} = 0` when
  `4 ∣ N`.
-/

namespace Folds
namespace XdConstTerm

open Finset

/-! ## The imbalance `D` -/

/-- Imbalance of a step: earlier panels in the left arm minus earlier panels in the right arm. -/
def Dstep (N : ℕ) (S : List ℕ) (m : ℕ) : ℤ := (leftCount N S m : ℤ) - (rightCount N S m : ℤ)

theorem semiStep_iff_Dstep {N m : ℕ} {S : List ℕ} : SemiStep N S m ↔ Dstep N S m = 0 := by
  unfold SemiStep Dstep; omega

theorem leftCount_le (N : ℕ) (S : List ℕ) (m : ℕ) : leftCount N S m ≤ reach N m := by
  have := List.countP_le_length (p := fun d => decide (m - d ∈ S)) (l := List.range' 1 (reach N m))
  simpa [leftCount] using this

theorem rightCount_le (N : ℕ) (S : List ℕ) (m : ℕ) : rightCount N S m ≤ reach N m := by
  have := List.countP_le_length (p := fun d => decide (m + d ∈ S)) (l := List.range' 1 (reach N m))
  simpa [rightCount] using this

/-- `|D| ≤ r`. -/
theorem natAbs_Dstep_le (N : ℕ) (S : List ℕ) (m : ℕ) : (Dstep N S m).natAbs ≤ reach N m := by
  have := leftCount_le N S m
  have := rightCount_le N S m
  unfold Dstep; omega

/-- `D_m(a)`: the imbalance of panel `m` at the moment it is placed in the sequence `a`. -/
def Dp (N : ℕ) (a : List ℕ) (m : ℕ) : ℤ := Dstep N (a.take (a.idxOf m)) m

theorem semiSymmetric_iff_Dp {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a) :
    SemiSymmetric N a ↔ ∀ m ∈ Icc 1 N, Dp N a m = 0 := by
  have hnd : a.Nodup := hf.nodup_iff.2 (List.nodup_range' ..)
  constructor
  · intro h m hm
    have hma : m ∈ a := (mem_range'_of_perm hf).2 (mem_Icc.1 hm)
    have hk := List.idxOf_lt_length_of_mem hma
    have h1 := h (a.idxOf m) hk
    have h2 : a[a.idxOf m] = m := List.getElem_idxOf hk
    rw [h2] at h1
    exact semiStep_iff_Dstep.1 h1
  · intro h k hk
    have hm : a[k] ∈ Icc 1 N := mem_Icc.2 ((mem_range'_of_perm hf).1 (List.getElem_mem hk))
    have h1 := h a[k] hm
    unfold Dp at h1
    rw [hnd.idxOf_getElem k hk] at h1
    exact semiStep_iff_Dstep.2 h1

/-- All fold sequences of length `N`. -/
def perms (N : ℕ) : Finset (List ℕ) := (List.range' 1 N).permutations.toFinset

theorem mem_perms {N : ℕ} {a : List ℕ} : a ∈ perms N ↔ IsFoldSeq N a := by
  simp [perms, IsFoldSeq]

/-- All imbalances of `a` vanish. -/
def AllZero (N : ℕ) (a : List ℕ) : Prop := ∀ m ∈ Icc 1 N, Dp N a m = 0

instance (N : ℕ) : DecidablePred (AllZero N) := fun a => by
  unfold AllZero; infer_instance

/-- All imbalances of `a` are divisible by `p`. -/
def AllDvd (p N : ℕ) (a : List ℕ) : Prop := ∀ m ∈ Icc 1 N, (p : ℤ) ∣ Dp N a m

instance (p N : ℕ) : DecidablePred (AllDvd p N) := fun a => by
  unfold AllDvd; infer_instance

/-- `a(N) = #{a : D_m(a) = 0 for all m}`. -/
theorem semiCount_eq_card_Dp (N : ℕ) :
    semiCount N = ((perms N).filter (AllZero N)).card := by
  unfold semiCount semiSeqs perms
  congr 1
  apply Finset.filter_congr
  intro a ha
  exact semiSymmetric_iff_Dp (mem_perms.1 ha)

/-! ## The mod-`p` relaxations -/

/-- `a_p(N)`: the number of fold sequences with `D_m ≡ 0 (mod p)` for every panel. -/
def modCount (p N : ℕ) : ℕ := ((perms N).filter (AllDvd p N)).card

theorem semiCount_le_modCount (p N : ℕ) : semiCount N ≤ modCount p N := by
  rw [semiCount_eq_card_Dp]
  apply Finset.card_le_card
  intro a ha
  rw [mem_filter] at ha ⊢
  exact ⟨ha.1, fun m hm => by rw [ha.2 m hm]; exact dvd_zero _⟩

/-- `a_p(N) = a(N)` as soon as `N ≤ 2p` (then `|D_m| ≤ r_m < p`). -/
theorem modCount_eq_semiCount {p N : ℕ} (h : N ≤ 2 * p) : modCount p N = semiCount N := by
  rw [semiCount_eq_card_Dp]
  unfold modCount
  congr 1
  apply Finset.filter_congr
  intro a _
  constructor
  · intro H m hm
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (H m hm)
    have h1 := natAbs_Dstep_le N (a.take (a.idxOf m)) m
    have h2 : reach N m < p := by
      rw [mem_Icc] at hm; unfold reach; omega
    rw [Int.natAbs_natCast]
    unfold Dp; omega
  · intro H m hm
    rw [H m hm]; exact dvd_zero _

/-! ## Tournaments -/

/-- The pairs `x < y` of panels. -/
def pairs (N : ℕ) : Finset (ℕ × ℕ) := (Icc 1 N ×ˢ Icc 1 N).filter fun p => p.1 < p.2

/-- A tournament is given by its inversion set `I` (pairs `x < y` with `y` earlier than `x`).
`Before I x y`: `x` is earlier than `y`. -/
def Before (I : Finset (ℕ × ℕ)) (x y : ℕ) : Prop :=
  (x < y ∧ (x, y) ∉ I) ∨ (y < x ∧ (y, x) ∈ I)

instance (I : Finset (ℕ × ℕ)) (x y : ℕ) : Decidable (Before I x y) := by
  unfold Before; infer_instance

/-- Imbalance of panel `m` in the tournament `I`. -/
def DT (N : ℕ) (I : Finset (ℕ × ℕ)) (m : ℕ) : ℤ :=
  (((Ico (m - reach N m) m).filter fun x => Before I x m).card : ℤ) -
    (((Ioc m (m + reach N m)).filter fun x => Before I x m).card : ℤ)

/-- A tournament is balanced if every panel has imbalance `0`. -/
def Balanced (N : ℕ) (I : Finset (ℕ × ℕ)) : Prop := ∀ m ∈ Icc 1 N, DT N I m = 0

instance (N : ℕ) : DecidablePred (Balanced N) := fun I => by
  unfold Balanced; infer_instance

/-- `B(N)`: the number of balanced tournaments on `[1,N]`,
`B(N) = CT ∏_{x<y} (z_y^{[x ∈ W(y)]} + z_x^{-[y ∈ W(x)]})`. -/
def balCount (N : ℕ) : ℕ := ((pairs N).powerset.filter (Balanced N)).card

/-- The tournament (inversion set) of a sequence. -/
def invSet (N : ℕ) (a : List ℕ) : Finset (ℕ × ℕ) :=
  (pairs N).filter fun p => a.idxOf p.2 < a.idxOf p.1

theorem before_invSet {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a) {x m : ℕ}
    (hx : 1 ≤ x ∧ x ≤ N) (hm : 1 ≤ m ∧ m ≤ N) (hne : x ≠ m) :
    Before (invSet N a) x m ↔ a.idxOf x < a.idxOf m := by
  have hxa : x ∈ a := (mem_range'_of_perm hf).2 hx
  have hidx : a.idxOf x ≠ a.idxOf m := fun e => hne ((List.idxOf_inj hxa).1 e)
  unfold Before invSet pairs
  simp only [mem_filter, mem_product, mem_Icc]
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · constructor
    · rintro (⟨-, h1⟩ | ⟨h2, -⟩)
      · by_contra h3
        exact h1 ⟨⟨⟨hx, hm⟩, h⟩, by omega⟩
      · omega
    · intro h3
      exact Or.inl ⟨h, fun h4 => absurd h4.2 (by omega)⟩
  · constructor
    · rintro (⟨h2, -⟩ | ⟨-, h1⟩)
      · omega
      · exact h1.2
    · intro h3
      exact Or.inr ⟨h, ⟨⟨hm, hx⟩, h⟩, h3⟩

theorem mem_take_idxOf {a : List ℕ} (hnd : a.Nodup) {x m : ℕ} (hx : x ∈ a) :
    x ∈ a.take (a.idxOf m) ↔ a.idxOf x < a.idxOf m := by
  have hk := List.idxOf_lt_length_of_mem hx
  have h1 := getElem_mem_take_iff hnd (p := a.idxOf x) (j := a.idxOf m) hk
  have h2 : a[a.idxOf x] = x := List.getElem_idxOf hk
  rwa [h2] at h1

/-- The tournament of a fold sequence has the same imbalances as the sequence. -/
theorem DT_invSet {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a) {m : ℕ} (hm : m ∈ Icc 1 N) :
    DT N (invSet N a) m = Dp N a m := by
  have hnd : a.Nodup := hf.nodup_iff.2 (List.nodup_range' ..)
  have hnd' : (a.take (a.idxOf m)).Nodup := hnd.sublist (List.take_sublist _ _)
  rw [mem_Icc] at hm
  have e1 : ((Ico (m - reach N m) m).filter fun x => Before (invSet N a) x m) =
      (a.take (a.idxOf m)).toFinset.filter (fun x => m - reach N m ≤ x ∧ x < m) := by
    ext x
    simp only [mem_filter, mem_Ico, List.mem_toFinset]
    constructor
    · rintro ⟨⟨h1, h2⟩, hb⟩
      have hx : 1 ≤ x ∧ x ≤ N := by unfold reach at h1; omega
      exact ⟨(mem_take_idxOf hnd ((mem_range'_of_perm hf).2 hx)).2
        ((before_invSet hf hx hm (by omega)).1 hb), h1, h2⟩
    · rintro ⟨ht, h1, h2⟩
      have hx : 1 ≤ x ∧ x ≤ N := by unfold reach at h1; omega
      exact ⟨⟨h1, h2⟩, (before_invSet hf hx hm (by omega)).2
        ((mem_take_idxOf hnd ((mem_range'_of_perm hf).2 hx)).1 ht)⟩
  have e2 : ((Ioc m (m + reach N m)).filter fun x => Before (invSet N a) x m) =
      (a.take (a.idxOf m)).toFinset.filter (fun x => m < x ∧ x ≤ m + reach N m) := by
    ext x
    simp only [mem_filter, mem_Ioc, List.mem_toFinset]
    constructor
    · rintro ⟨⟨h1, h2⟩, hb⟩
      have hx : 1 ≤ x ∧ x ≤ N := by unfold reach at h2; omega
      exact ⟨(mem_take_idxOf hnd ((mem_range'_of_perm hf).2 hx)).2
        ((before_invSet hf hx hm (by omega)).1 hb), h1, h2⟩
    · rintro ⟨ht, h1, h2⟩
      have hx : 1 ≤ x ∧ x ≤ N := by unfold reach at h2; omega
      exact ⟨⟨h1, h2⟩, (before_invSet hf hx hm (by omega)).2
        ((mem_take_idxOf hnd ((mem_range'_of_perm hf).2 hx)).1 ht)⟩
  unfold DT Dp Dstep
  rw [leftCount_eq hnd', rightCount_eq hnd', countP_eq_card_filter hnd',
    countP_eq_card_filter hnd', e1, e2]

/-- A fold sequence is determined by its tournament. -/
theorem invSet_injOn (N : ℕ) {a b : List ℕ} (ha : IsFoldSeq N a) (hb : IsFoldSeq N b)
    (e : invSet N a = invSet N b) : a = b := by
  have hnda : a.Nodup := ha.nodup_iff.2 (List.nodup_range' ..)
  have hndb : b.Nodup := hb.nodup_iff.2 (List.nodup_range' ..)
  have key : ∀ x y, x ∈ b → y ∈ b → b.idxOf x < b.idxOf y → a.idxOf x < a.idxOf y := by
    intro x y hx hy hlt
    have hx' := (mem_range'_of_perm hb).1 hx
    have hy' := (mem_range'_of_perm hb).1 hy
    have hne : x ≠ y := fun h => by subst h; omega
    have h1 := (before_invSet hb hx' hy' hne).2 hlt
    rw [← e] at h1
    exact (before_invSet ha hx' hy' hne).1 h1
  refine List.Perm.eq_of_pairwise (le := fun x y => a.idxOf x ≤ a.idxOf y) ?_ ?_ ?_
    (ha.trans hb.symm)
  · intro x y hx _ h1 h2
    exact (List.idxOf_inj hx).1 (le_antisymm h1 h2)
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [hnda.idxOf_getElem i hi, hnda.idxOf_getElem j hj]
    omega
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    apply Nat.le_of_lt
    apply key _ _ (List.getElem_mem hi) (List.getElem_mem hj)
    rw [hndb.idxOf_getElem i hi, hndb.idxOf_getElem j hj]
    exact hij

theorem invSet_mem {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a) (h : SemiSymmetric N a) :
    invSet N a ∈ (pairs N).powerset.filter (Balanced N) := by
  rw [mem_filter, mem_powerset]
  refine ⟨filter_subset _ _, fun m hm => ?_⟩
  rw [DT_invSet hf hm]
  exact (semiSymmetric_iff_Dp hf).1 h m hm

/-- **`a(N) ≤ B(N)`**: semi-symmetric fold sequences are the transitive balanced tournaments. -/
theorem semiCount_le_balCount (N : ℕ) : semiCount N ≤ balCount N := by
  unfold semiCount balCount
  apply Finset.card_le_card_of_injOn (invSet N)
  · intro a ha
    simp only [Finset.mem_coe, mem_semiSeqs] at ha
    exact Finset.mem_coe.2 (invSet_mem ha.1 ha.2)
  · intro a ha b hb e
    simp only [Finset.mem_coe, mem_semiSeqs] at ha hb
    exact invSet_injOn N ha.1 hb.1 e

/-! ## The pair-sum formula for `∑_m D_m` -/

/-- `c_{xy} = [x ∈ W(y)]` for a pair `x < y`. -/
def cw (N : ℕ) (p : ℕ × ℕ) : ℤ := if p.2 - p.1 ≤ reach N p.2 then 1 else 0

/-- `d_{xy} = [y ∈ W(x)]` for a pair `x < y`. -/
def dw (N : ℕ) (p : ℕ × ℕ) : ℤ := if p.2 - p.1 ≤ reach N p.1 then 1 else 0

theorem DT_eq_sum {N : ℕ} (I : Finset (ℕ × ℕ)) {m : ℕ} (hm : m ∈ Icc 1 N) :
    DT N I m = ∑ x ∈ Icc 1 N,
      ((if x < m ∧ m - x ≤ reach N m ∧ (x, m) ∉ I then (1 : ℤ) else 0) -
        (if m < x ∧ x - m ≤ reach N m ∧ (m, x) ∈ I then (1 : ℤ) else 0)) := by
  rw [mem_Icc] at hm
  have hr : reach N m = min (m - 1) (N - m) := rfl
  have e1 : ((Ico (m - reach N m) m).filter fun x => Before I x m) =
      (Icc 1 N).filter (fun x => x < m ∧ m - x ≤ reach N m ∧ (x, m) ∉ I) := by
    ext x
    simp only [mem_filter, mem_Ico, mem_Icc]
    unfold Before
    constructor
    · rintro ⟨⟨h1, h2⟩, (⟨-, h3⟩ | ⟨h4, -⟩)⟩
      · refine ⟨⟨?_, ?_⟩, h2, ?_, h3⟩ <;> omega
      · omega
    · rintro ⟨-, h2, h3, h4⟩
      exact ⟨⟨by omega, h2⟩, Or.inl ⟨h2, h4⟩⟩
  have e2 : ((Ioc m (m + reach N m)).filter fun x => Before I x m) =
      (Icc 1 N).filter (fun x => m < x ∧ x - m ≤ reach N m ∧ (m, x) ∈ I) := by
    ext x
    simp only [mem_filter, mem_Ioc, mem_Icc]
    unfold Before
    constructor
    · rintro ⟨⟨h1, h2⟩, (⟨h4, -⟩ | ⟨-, h3⟩)⟩
      · omega
      · refine ⟨⟨?_, ?_⟩, h1, ?_, h3⟩ <;> omega
    · rintro ⟨-, h2, h3, h4⟩
      exact ⟨⟨h2, by omega⟩, Or.inr ⟨h2, h4⟩⟩
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  unfold DT
  rw [e1, e2]

/-- **Pair-sum formula** (tournaments): `∑_m D_m = ∑_{x<y} (if y earlier then −d_{xy} else c_{xy})`.
So `∑_m D_m = ∑ c − ∑_{inversions} (c + d)`: a graph-inversion statistic with weights
`c + d ∈ {0,1,2}`. -/
theorem sum_DT (N : ℕ) (I : Finset (ℕ × ℕ)) :
    ∑ m ∈ Icc 1 N, DT N I m = ∑ p ∈ pairs N, (if p ∈ I then -dw N p else cw N p) := by
  have h1 : ∑ m ∈ Icc 1 N, DT N I m = ∑ m ∈ Icc 1 N, ∑ x ∈ Icc 1 N,
      ((if x < m ∧ m - x ≤ reach N m ∧ (x, m) ∉ I then (1 : ℤ) else 0) -
        (if m < x ∧ x - m ≤ reach N m ∧ (m, x) ∈ I then (1 : ℤ) else 0)) :=
    Finset.sum_congr rfl fun m hm => DT_eq_sum I hm
  have hA : ∑ m ∈ Icc 1 N, ∑ x ∈ Icc 1 N,
        (if x < m ∧ m - x ≤ reach N m ∧ (x, m) ∉ I then (1 : ℤ) else 0)
      = ∑ p ∈ Icc 1 N ×ˢ Icc 1 N,
        (if p.1 < p.2 ∧ p.2 - p.1 ≤ reach N p.2 ∧ p ∉ I then (1 : ℤ) else 0) := by
    rw [Finset.sum_product, Finset.sum_comm]
  have hB : ∑ m ∈ Icc 1 N, ∑ x ∈ Icc 1 N,
        (if m < x ∧ x - m ≤ reach N m ∧ (m, x) ∈ I then (1 : ℤ) else 0)
      = ∑ p ∈ Icc 1 N ×ˢ Icc 1 N,
        (if p.1 < p.2 ∧ p.2 - p.1 ≤ reach N p.1 ∧ p ∈ I then (1 : ℤ) else 0) := by
    rw [Finset.sum_product]
  rw [h1]
  simp only [Finset.sum_sub_distrib]
  rw [hA, hB, ← Finset.sum_sub_distrib]
  unfold pairs
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  rintro ⟨x, y⟩ _
  simp only [cw, dw]
  by_cases h : x < y <;> by_cases hI : (x, y) ∈ I <;> by_cases c : y - x ≤ reach N y <;>
    by_cases d : y - x ≤ reach N x <;> simp [h, hI, c, d]

/-- **Pair-sum formula** for fold sequences. -/
theorem sum_Dp {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a) :
    ∑ m ∈ Icc 1 N, Dp N a m =
      ∑ p ∈ pairs N, (if a.idxOf p.2 < a.idxOf p.1 then -dw N p else cw N p) := by
  rw [← Finset.sum_congr rfl (fun m hm => DT_invSet hf hm), sum_DT]
  apply Finset.sum_congr rfl
  intro p hp
  have hiff : p ∈ invSet N a ↔ a.idxOf p.2 < a.idxOf p.1 := by simp [invSet, hp]
  by_cases h : a.idxOf p.2 < a.idxOf p.1
  · have h' := hiff.2 h
    simp [h, h']
  · have h' : p ∉ invSet N a := fun h' => h (hiff.1 h')
    simp [h, h']

/-! ## The signed count `∑_a ∏_m (−1)^{D_m(a)}` -/

/-- `(−1)^{D}` of a step, written with `l + r` instead of `l − r`. -/
def sgnStep (N : ℕ) (S : List ℕ) (m : ℕ) : ℤ := (-1) ^ (leftCount N S m + rightCount N S m)

theorem sgnStep_eq (N : ℕ) (S : List ℕ) (m : ℕ) :
    sgnStep N S m = if Even (Dstep N S m) then 1 else -1 := by
  unfold sgnStep Dstep
  rw [neg_one_pow_eq_ite]
  have hiff : Even ((leftCount N S m : ℤ) - (rightCount N S m : ℤ)) ↔
      Even (leftCount N S m + rightCount N S m) := by
    rw [Int.even_sub, Nat.even_add, Int.even_coe_nat, Int.even_coe_nat]
  by_cases h : Even (leftCount N S m + rightCount N S m)
  · have h' := hiff.2 h
    simp [h, h']
  · have h' : ¬ Even ((leftCount N S m : ℤ) - (rightCount N S m : ℤ)) := fun h' => h (hiff.1 h')
    simp [h, h']

/-- `sgn N a = ∏_m (−1)^{D_m(a)} = (−1)^{∑_m D_m(a)}`. -/
def sgn (N : ℕ) (a : List ℕ) : ℤ := ∏ m ∈ Icc 1 N, sgnStep N (a.take (a.idxOf m)) m

theorem sgn_eq (N : ℕ) (a : List ℕ) :
    sgn N a = ∏ m ∈ Icc 1 N, (if Even (Dp N a m) then (1 : ℤ) else -1) :=
  Finset.prod_congr rfl fun m _ => sgnStep_eq N _ m

/-- Adding one earlier panel `p` flips the sign of the step of `m` iff `p ∈ W(m)`. -/
theorem sgnStep_cons {N m p : ℕ} {T : List ℕ} (hT : (p :: T).Nodup) :
    sgnStep N (p :: T) m = sgnStep N T m *
      (-1) ^ (if p ≠ m ∧ m - reach N m ≤ p ∧ p ≤ m + reach N m then 1 else 0) := by
  have hT' : T.Nodup := (List.nodup_cons.1 hT).2
  have key : (if m - reach N m ≤ p ∧ p < m then 1 else 0) +
      (if m < p ∧ p ≤ m + reach N m then 1 else 0) =
      (if p ≠ m ∧ m - reach N m ≤ p ∧ p ≤ m + reach N m then 1 else 0) := by
    split_ifs <;> omega
  unfold sgnStep
  rw [leftCount_eq hT, rightCount_eq hT, leftCount_eq hT', rightCount_eq hT', List.countP_cons,
    List.countP_cons, ← pow_add, ← key]
  simp only [decide_eq_true_eq]
  congr 1
  ring

/-- **Rotation lemma.** Moving the first panel `p` to the end multiplies the sign by
`(−1)^{#{m ≠ p : p ∈ W(m)}}`. -/
theorem sgn_rotate {N p : ℕ} {t : List ℕ} (hf : IsFoldSeq N (p :: t)) :
    sgn N (p :: t) = sgn N (t ++ [p]) *
      (-1) ^ ((Icc 1 N).filter fun m => p ≠ m ∧ m - reach N m ≤ p ∧ p ≤ m + reach N m).card := by
  have hnd : (p :: t).Nodup := hf.nodup_iff.2 (List.nodup_range' ..)
  have hpt : p ∉ t := (List.nodup_cons.1 hnd).1
  have hndt : t.Nodup := (List.nodup_cons.1 hnd).2
  unfold sgn
  rw [Finset.card_filter, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro m hm
  have hm' := mem_Icc.1 hm
  by_cases hmp : m = p
  · subst hmp
    have h1 : (m :: t).idxOf m = 0 := List.idxOf_cons_self
    have h2 : (t ++ [m]).idxOf m = t.length := by
      rw [List.idxOf_append_of_notMem hpt]; simp
    have hin : ∀ x, 1 ≤ x → x ≤ N → x ≠ m → x ∈ t := by
      intro x hx1 hx2 hne
      rcases List.mem_cons.1 ((mem_range'_of_perm hf).2 ⟨hx1, hx2⟩) with h | h
      · exact absurd h hne
      · exact h
    have hl : leftCount N t m = reach N m := by
      unfold leftCount
      have := (List.countP_eq_length (p := fun d => decide (m - d ∈ t))
        (l := List.range' 1 (reach N m))).2 (by
          intro d hd
          rw [List.mem_range'_1] at hd
          have : m - d ∈ t := hin _ (by unfold reach at hd; omega) (by omega)
            (by unfold reach at hd; omega)
          simpa using this)
      simpa using this
    have hr : rightCount N t m = reach N m := by
      unfold rightCount
      have := (List.countP_eq_length (p := fun d => decide (m + d ∈ t))
        (l := List.range' 1 (reach N m))).2 (by
          intro d hd
          rw [List.mem_range'_1] at hd
          have : m + d ∈ t := hin _ (by omega) (by unfold reach at hd; omega) (by omega)
          simpa using this)
      simpa using this
    rw [h1, h2, List.take_zero, List.take_left' rfl]
    have e0 : sgnStep N [] m = 1 := by simp [sgnStep, leftCount, rightCount]
    have e1 : sgnStep N t m = 1 := by
      unfold sgnStep
      rw [hl, hr]
      exact Even.neg_one_pow ⟨reach N m, rfl⟩
    rw [e0, e1]
    simp
  · have hmt : m ∈ t := by
      rcases List.mem_cons.1 ((mem_range'_of_perm hf).2 hm') with h | h
      · exact absurd h hmp
      · exact h
    have hk := List.idxOf_lt_length_of_mem hmt
    rw [List.idxOf_cons_ne _ (fun h => hmp h.symm), List.take_succ_cons,
      List.idxOf_append_of_mem hmt, List.take_append_of_le_length (Nat.le_of_lt hk)]
    exact sgnStep_cons (List.nodup_cons.2 ⟨fun h => hpt (List.mem_of_mem_take h),
      hndt.sublist (List.take_sublist _ _)⟩)

/-- For `N = 2n`, every panel `p` lies in the windows of exactly `n − 1` other panels. -/
theorem card_inWindow {n p : ℕ} (hp : p ∈ Icc 1 (2 * n)) :
    ((Icc 1 (2 * n)).filter fun m =>
      p ≠ m ∧ m - reach (2 * n) m ≤ p ∧ p ≤ m + reach (2 * n) m).card = n - 1 := by
  rw [mem_Icc] at hp
  have hset : (Icc 1 (2 * n)).filter (fun m =>
      p ≠ m ∧ m - reach (2 * n) m ≤ p ∧ p ≤ m + reach (2 * n) m)
      = Icc ((p + 2) / 2) (p - 1) ∪ Icc (p + 1) ((2 * n + p) / 2) := by
    ext m
    have hr : reach (2 * n) m = min (m - 1) (2 * n - m) := rfl
    simp only [mem_filter, mem_Icc, mem_union]
    omega
  rw [hset, Finset.card_union_of_disjoint, Nat.card_Icc, Nat.card_Icc]
  · omega
  · rw [Finset.disjoint_left]
    intro m h1 h2
    rw [mem_Icc] at h1 h2
    omega

/-- Rotation on fold sequences of even length `2n` multiplies the sign by `(−1)^{n−1}`. -/
theorem sgn_rotate_even {n : ℕ} {a : List ℕ} (ha : a ∈ perms (2 * n)) (hn : 0 < n) :
    sgn (2 * n) a = (-1) ^ (n - 1) * sgn (2 * n) (a.rotate 1) := by
  rw [mem_perms] at ha
  cases a with
  | nil =>
    have := ha.length_eq
    simp at this
    omega
  | cons p t =>
    have hp : p ∈ Icc 1 (2 * n) := mem_Icc.2 ((mem_range'_of_perm ha).1 List.mem_cons_self)
    rw [List.rotate_cons_succ, List.rotate_zero, sgn_rotate ha, card_inWindow hp, mul_comm]

theorem sum_sgn_rotate {n : ℕ} (hn : 0 < n) :
    ∑ a ∈ perms (2 * n), sgn (2 * n) a = (-1) ^ (n - 1) * ∑ a ∈ perms (2 * n), sgn (2 * n) a := by
  rw [Finset.mul_sum]
  apply Finset.sum_nbij' (fun a => a.rotate 1) (fun a => a.rotate (2 * n - 1))
  · intro a ha
    rw [mem_perms] at ha ⊢
    exact (List.rotate_perm a 1).trans ha
  · intro a ha
    rw [mem_perms] at ha ⊢
    exact (List.rotate_perm a _).trans ha
  · intro a ha
    rw [mem_perms] at ha
    have hl : 1 + (2 * n - 1) = a.length := by
      rw [ha.length_eq, List.length_range']; omega
    rw [List.rotate_rotate, hl, List.rotate_length]
  · intro a ha
    rw [mem_perms] at ha
    have hl : 2 * n - 1 + 1 = a.length := by
      rw [ha.length_eq, List.length_range']; omega
    rw [List.rotate_rotate, hl, List.rotate_length]
  · intro a ha
    exact sgn_rotate_even ha hn

/-- **Signed count.** For `4 ∣ N`, `N > 0`: `∑_a ∏_m (−1)^{D_m(a)} = 0`, i.e. exactly half of
all fold sequences have `∑_m D_m` even. -/
theorem sum_sgn_eq_zero {N : ℕ} (hN : 0 < N) (h4 : 4 ∣ N) : ∑ a ∈ perms N, sgn N a = 0 := by
  obtain ⟨k, rfl⟩ := h4
  have e : 4 * k = 2 * (2 * k) := by ring
  rw [e]
  have h := sum_sgn_rotate (n := 2 * k) (by omega)
  have hodd : (-1 : ℤ) ^ (2 * k - 1) = -1 := Odd.neg_one_pow ⟨k - 1, by omega⟩
  rw [hodd] at h
  linarith

/-- The same statement with the signs written as `(−1)^{D_m}`. -/
theorem sum_prod_neg_one_pow_D_eq_zero {N : ℕ} (hN : 0 < N) (h4 : 4 ∣ N) :
    ∑ a ∈ perms N, ∏ m ∈ Icc 1 N, (if Even (Dp N a m) then (1 : ℤ) else -1) = 0 := by
  rw [← sum_sgn_eq_zero hN h4]
  exact Finset.sum_congr rfl fun a _ => (sgn_eq N a).symm

/-! ## Small values -/

theorem balCount_one : balCount 1 = 1 := by decide +kernel
theorem balCount_two : balCount 2 = 2 := by decide +kernel
theorem balCount_three : balCount 3 = 4 := by decide +kernel

end XdConstTerm
end Folds
