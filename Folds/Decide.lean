import Folds.Basic

/-!
# Decidability

Boolean step-by-step checkers, proven equivalent to the `Prop` definitions, giving
`Decidable` instances for `Symmetric` and `SemiSymmetric`.  Brute-force counting
lives in the Rust crate, not here.
-/

namespace Folds

theorem symStep_iff_all {N : Nat} {S : List Nat} {m : Nat} :
    SymStep N S m ↔ ∀ d ∈ List.range' 1 (reach N m), (m - d ∈ S ↔ m + d ∈ S) := by
  unfold SymStep
  constructor
  · intro h d hd; rw [List.mem_range'_1] at hd; exact h d (by omega) (by omega)
  · intro h d h1 h2; exact h d (by rw [List.mem_range'_1]; omega)

instance (N : Nat) (S : List Nat) (m : Nat) : Decidable (SymStep N S m) :=
  decidable_of_iff _ symStep_iff_all.symm

/-- Walk along `a`, checking `P (already folded) (current)` at every step. -/
def allSteps (P : List Nat → Nat → Prop) [∀ S m, Decidable (P S m)] :
    List Nat → List Nat → Bool
  | _, [] => true
  | S, m :: t => decide (P S m) && allSteps P (S ++ [m]) t

theorem allSteps_iff (P : List Nat → Nat → Prop) [∀ S m, Decidable (P S m)]
    (a S : List Nat) :
    allSteps P S a = true ↔ ∀ k (h : k < a.length), P (S ++ a.take k) a[k] := by
  induction a generalizing S with
  | nil => simp [allSteps]
  | cons m t ih =>
    simp only [allSteps, Bool.and_eq_true, decide_eq_true_eq, ih, List.length_cons]
    constructor
    · rintro ⟨h0, ht⟩ k hk
      cases k with
      | zero => simpa using h0
      | succ k => simpa using ht k (by omega)
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun k hk => ?_⟩
      have := h (k + 1) (by omega)
      simp only [List.take_succ_cons, List.getElem_cons_succ] at this
      simpa using this

instance (N : Nat) (a : List Nat) : Decidable (SemiSymmetric N a) :=
  decidable_of_iff (allSteps (SemiStep N) [] a = true) (by
    rw [allSteps_iff]; simp [SemiSymmetric])

instance (N : Nat) (a : List Nat) : Decidable (Symmetric N a) :=
  decidable_of_iff (allSteps (SymStep N) [] a = true) (by
    rw [allSteps_iff]; simp [Symmetric])

/-! ## The cyclic ("doubling") reformulation of a semi-symmetric step

Write `P(j) = #{x ∈ S | x ≤ j}` and `s = |S|`, and extend `P` quasi-periodically:
`P̃(j) = P(j mod N) + ⌊j / N⌋ · s` (wrap the strip into a circle of length `N`,
counting one extra `s` per full turn).  Then for `m ∉ S` the step is semi-symmetric
iff `P̃(2m - 1) = 2 · P(m - 1)`: a single formula covering both the left half
(where `2m - 1 ≤ N` is the reference crease measured from the left edge) and the
right half (where it wraps around).  (Statement only; proof is TODO.) -/

def below (S : List Nat) (j : Nat) : Nat := S.countP (· ≤ j)

def cycBelow (N : Nat) (S : List Nat) (j : Nat) : Nat :=
  below S (j % N) + (j / N) * S.length

def CyclicStep (N : Nat) (S : List Nat) (m : Nat) : Prop :=
  cycBelow N S (2 * m - 1) = 2 * below S (m - 1)

instance (N : Nat) (S : List Nat) (m : Nat) : Decidable (CyclicStep N S m) :=
  inferInstanceAs (Decidable (_ = _))

end Folds
