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

/-! The cyclic reformulation `CyclicStep` (with its `Decidable` instance) and its proof
`semiStep_iff_cyclicStep` live in `Folds/Cyclic.lean`. -/

end Folds
