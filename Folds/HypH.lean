import Folds.Live3

/-!
# Hypothesis H: the X-balance form of the second chain condition

`experiments/hyph/PROOFS.txt`, section 1.

**Lemma X** (`xbal`), the general-`ν` form of Lemma P (`Live3.prec`, `ν = 1`).  Let
`X = [1, ν]`.  For a class `s` with `ν < s ≤ q` and a set `A` of earlier classes that is
balanced around `s` in the `q`-strip (`CycBal q A s (s - 1)`), the second chain condition
`CycBal q A s ((ν - s) mod q)` holds iff
    `#(A ∩ X) = #(A ∩ (2s - X))`,
where `2s - X = {2s - 1, …, 2s - ν} (mod q)` is the set of `t` with
`q - s + 1 ≤ (s - t) mod q ≤ q - s + ν`.  So `GoodL q ν π` says: `π` is a valid sequence of
the `q`-strip and at every step the window `2s - X` (the reflection of `X` through `s`)
holds as many earlier classes as `X`.  (For `s ≤ ν` the same statement holds numerically,
see `checkx.py`; it is not needed here.)

This is the starting point of the odd near-reduction (Theorem R of PROOFS.txt), which is
verified numerically only; Hypothesis H itself is NOT proven here.
-/

namespace Folds
namespace HypH

open Live2 Live3

/-- The window `2s - X`, `X = [1, ν]`, in offset form. -/
def inRefl (q s ν t : Nat) : Bool := decide (q - s + 1 ≤ cc q s t ∧ cc q s t ≤ q - s + ν)

/-- **Lemma X.** -/
theorem xbal {q ν s : Nat} {A : List Nat} (hA : ∀ t ∈ A, 1 ≤ t ∧ t ≤ q)
    (hs : ν < s ∧ s ≤ q) (c1 : CycBal q A s (s - 1)) :
    CycBal q A s ((ν + q - s) % q) ↔
      A.countP (fun t => decide (t ≤ ν)) = A.countP (inRefl q s ν) := by
  have hs' : 1 ≤ s ∧ s ≤ q := ⟨by omega, hs.2⟩
  have e : (ν + q - s) % q = q - 1 - (s - 1 - ν) := by
    rw [Nat.mod_eq_of_lt (show ν + q - s < q by omega)]; omega
  rw [e, ← cycBal_dual hA hs' (by omega)]
  rw [cycBal_iff hA hs' (by omega)] at c1
  rw [cycBal_iff hA hs' (by omega)]
  have a1 : A.countP (fun t => decide (1 ≤ cc q s t ∧ cc q s t ≤ s - 1 - ν)) +
      A.countP (fun t => decide (s - ν ≤ cc q s t ∧ cc q s t ≤ s - 1)) =
        A.countP (fun t => decide (1 ≤ cc q s t ∧ cc q s t ≤ s - 1)) :=
    countP_add_of fun t ht => by simp only [decide_eq_true_eq]; split_ifs <;> omega
  have a2 : A.countP (fun t => decide (q - (s - 1 - ν) ≤ cc q s t)) +
      A.countP (inRefl q s ν) =
        A.countP (fun t => decide (q - (s - 1) ≤ cc q s t)) :=
    countP_add_of fun t ht => by
      unfold inRefl; simp only [decide_eq_true_eq]; split_ifs <;> omega
  have b1 : A.countP (fun t => decide (s - ν ≤ cc q s t ∧ cc q s t ≤ s - 1)) =
      A.countP (fun t => decide (t ≤ ν)) := by
    apply List.countP_congr
    intro t ht
    have := hA t ht
    simp only [decide_eq_true_eq]
    rw [cc_eq hs.2 (hA t ht)]
    split_ifs <;> omega
  omega

end HypH
end Folds
