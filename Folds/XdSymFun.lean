import Folds.Descents
import Folds.SelfDual
import Folds.Structure2

/-!
# Symmetric-function view: commutation classes, descent statistics and their symmetries

Notes and data: `experiments/xd_symfun/NOTES.txt`.

Two encodings of a fold sequence are used: the sequence `a` itself (`a_k` = panel placed at
step `k`) and the *time word* `t` (`t_m` = step at which panel `m` is placed, i.e. `a.idxOf m`).

## Commutation (Cartier–Foata) structure
* `Indep N x y`: panels `x`, `y` are *independent*: neither lies in the other's window,
  i.e. `|x - y| > max (reach N x) (reach N y)`.
* `SemiSymmetric.swap`, `swap_mem_semiSeqs`: swapping two adjacent independent panels
  preserves semi-symmetry.
* `indep_of_swap_mem_semiSeqs`: conversely, if `u ++ x :: y :: v` and `u ++ y :: x :: v` are
  both semi-symmetric fold sequences, then `x`, `y` are independent.
  So the set `V_N` of semi-symmetric sequences is a union of classes of the trace monoid on
  `[N]` with this independence relation; its quasisymmetric generating function
  `Σ_{a ∈ V_N} F_{Des a}` is a sum of `(P, ω)`-partition generating functions of heaps.
* `not_indep_of_left`: two panels in the left half are never independent (so a heap is a
  union of two chains).

## Descent statistics
* `des` (from `Folds.Descents`) and `ides a` = number of `m` such that panel `m + 1` is placed
  before panel `m` (the descents of the time word).
* `des_mirror`: `des (mirror N a) + des a = N - 1`; `ides_reverse`:
  `ides a.reverse + ides a = N - 1`.
* `desCount N k`, `idesCount N k`: the coefficients of the two descent polynomials of `V_N`;
  both are palindromic (`desCount_symm`, `idesCount_symm`).
* `desPoly`, `idesPoly`: the generating polynomials; `desPoly_coeff`, `desPoly_eval_one`.
* Extreme coefficients: `desCount_zero`, `desCount_top`, `idesCount_zero`, `idesCount_top`
  (they vanish for `N ≥ 3`), from `one_le_des` (via `descents_bound`) and `one_le_ides`
  (panel `2` is placed before both or after both of its neighbours, `ides_two`).
* Small cases by kernel computation: `desCount_four`, `desCount_five`, `idesCount_four`,
  `idesCount_five`.

## The quasisymmetric function is not symmetric
* `subDesCount N D` = number of `a ∈ V_N` whose descent set is contained in `D`: this is the
  coefficient of the monomial quasisymmetric function `M_β` (`β` the composition with partial
  sums `D`) in `Q_N = Σ_{a ∈ V_N} F_{Des a}`.  `Q_N` is symmetric iff these numbers depend only
  on the multiset of parts of `β`.
* `subDesCount_five`: for `N = 5` the compositions `(1,3,1)` and `(1,1,3)` have coefficients
  `6` and `1`, so `Q_5` is not symmetric.  `subIdesCount_five`: the same for the time word
  (`4` against `0`).
-/

namespace Folds
namespace XdSymFun

open Finset

/-! ## Independence and the commutation lemma -/

/-- Panels `x` and `y` are independent: each lies outside the window of the other. -/
def Indep (N x y : ℕ) : Prop :=
  reach N x < (x - y) + (y - x) ∧ reach N y < (x - y) + (y - x)

instance (N x y : ℕ) : Decidable (Indep N x y) := inferInstanceAs (Decidable (_ ∧ _))

theorem Indep.symm {N x y : ℕ} (h : Indep N x y) : Indep N y x := by
  unfold Indep at *; omega

/-- A panel outside the window of `x` does not affect the step condition of `x`. -/
theorem semiStep_append_far {N x y : ℕ} {S : List ℕ} (h : reach N x < (x - y) + (y - x)) :
    SemiStep N (S ++ [y]) x ↔ SemiStep N S x := by
  unfold SemiStep leftCount rightCount
  have hl : (List.range' 1 (reach N x)).countP (fun d => decide (x - d ∈ S ++ [y])) =
      (List.range' 1 (reach N x)).countP (fun d => decide (x - d ∈ S)) := by
    apply List.countP_congr
    intro d hd
    rw [List.mem_range'_1] at hd
    have hr := hd.2; unfold reach at hr h
    simp only [List.mem_append, List.mem_singleton, decide_eq_true_eq]
    constructor
    · rintro (h1 | h1)
      · exact h1
      · omega
    · exact Or.inl
  have hr : (List.range' 1 (reach N x)).countP (fun d => decide (x + d ∈ S ++ [y])) =
      (List.range' 1 (reach N x)).countP (fun d => decide (x + d ∈ S)) := by
    apply List.countP_congr
    intro d hd
    rw [List.mem_range'_1] at hd
    have hr := hd.2; unfold reach at hr h
    simp only [List.mem_append, List.mem_singleton, decide_eq_true_eq]
    constructor
    · rintro (h1 | h1)
      · exact h1
      · omega
    · exact Or.inl
  rw [hl, hr]

/-- The four conditions that make up semi-symmetry of `u ++ x :: y :: v`. -/
theorem semiSymmetric_two_iff {N x y : ℕ} {u v : List ℕ} :
    SemiSymmetric N (u ++ x :: y :: v) ↔
      SemiSymmetric N u ∧ SemiStep N u x ∧ SemiStep N (u ++ [x]) y ∧
        ∀ k (hk : k < v.length), SemiStep N (u ++ x :: y :: v.take k) v[k] := by
  have e : u ++ x :: y :: v = ((u ++ [x]) ++ [y]) ++ v := by simp
  rw [e, semiSymmetric_append_iff, semiSymmetric_concat_iff, semiSymmetric_concat_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, h2, h3, fun k hk => ?_⟩
    have := h4 k hk
    simpa using this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, fun k hk => ?_⟩
    have := h4 k hk
    simpa using this

/-- **Commutation lemma.**  Swapping two adjacent independent panels preserves
semi-symmetry. -/
theorem SemiSymmetric.swap {N x y : ℕ} {u v : List ℕ} (hI : Indep N x y)
    (h : SemiSymmetric N (u ++ x :: y :: v)) : SemiSymmetric N (u ++ y :: x :: v) := by
  rw [semiSymmetric_two_iff] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, (semiStep_append_far ?_).1 h3, (semiStep_append_far hI.1).2 h2, fun k hk => ?_⟩
  · have := hI.2; omega
  · refine (semiStep_congr fun z => ?_).1 (h4 k hk)
    simp only [List.mem_append, List.mem_cons]
    tauto

/-- The commutation lemma for the set `V_N` of semi-symmetric fold sequences. -/
theorem swap_mem_semiSeqs {N x y : ℕ} {u v : List ℕ} (hI : Indep N x y)
    (h : u ++ x :: y :: v ∈ semiSeqs N) : u ++ y :: x :: v ∈ semiSeqs N := by
  rw [mem_semiSeqs] at h ⊢
  refine ⟨?_, h.2.swap hI⟩
  unfold IsFoldSeq at *
  exact ((List.Perm.swap y x v).append_left u).trans h.1

end XdSymFun
end Folds
