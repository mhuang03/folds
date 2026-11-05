import Folds.Basic

/-!
# Executable checkers and small-`N` counts

Boolean checkers proven equivalent to the `Prop` definitions, so that
`decide`/`native_decide` statements below are about the real definitions.
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

/-! ## Enumerating permutations -/

def insertAll (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAll x ys).map (y :: ·)

def perms : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (insertAll x)

/-- Number of semi-symmetric fold sequences of length `N` (by brute force). -/
def semiCount (N : Nat) : Nat :=
  (perms (List.range' 1 N)).countP fun a => decide (SemiSymmetric N a)

/-- Number of symmetric fold sequences of length `N` (by brute force). -/
def symCount (N : Nat) : Nat :=
  (perms (List.range' 1 N)).countP fun a => decide (Symmetric N a)

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Sanity check: the enumerator produces `N!` distinct fold sequences for small `N`. -/
theorem perms_ok : ∀ N ∈ List.range 9,
    (perms (List.range' 1 N)).length = fact N ∧
    (perms (List.range' 1 N)).Nodup ∧
    ∀ a ∈ perms (List.range' 1 N), IsFoldSeq N a := by native_decide

theorem semiCount_values :
    (List.range 9).map semiCount = [1, 1, 2, 4, 10, 28, 96, 256, 1120] := by native_decide

theorem symCount_values :
    (List.range 9).map symCount = [1, 1, 2, 4, 10, 20, 48, 104, 282] := by native_decide

/-! ## Faster count by pruned search (not proven equal to `semiCount`;
checked against it above for `N ≤ 8`). -/

def countFrom (P : List Nat → Nat → Prop) [∀ S m, Decidable (P S m)] :
    Nat → List Nat → List Nat → Nat
  | 0, _, _ => 1
  | fuel + 1, S, rem =>
    rem.foldl (fun acc m => if P S m then acc + countFrom P fuel (S ++ [m]) (rem.erase m)
      else acc) 0

def semiCountFast (N : Nat) : Nat := countFrom (SemiStep N) N [] (List.range' 1 N)

theorem semiCountFast_agrees : ∀ N ∈ List.range 9, semiCountFast N = semiCount N := by
  native_decide

/-! ## The cyclic ("doubling") reformulation of a semi-symmetric step

Write `P(j) = #{x ∈ S | x ≤ j}` and `s = |S|`, and extend `P` quasi-periodically:
`P̃(j) = P(j mod N) + ⌊j / N⌋ · s` (wrap the strip into a circle of length `N`,
counting one extra `s` per full turn).  Then for `m ∉ S` the step is semi-symmetric
iff `P̃(2m - 1) = 2 · P(m - 1)`: a single formula covering both the left half
(where `2m - 1 ≤ N` is the reference crease measured from the left edge) and the
right half (where it wraps around).  Verified below for every `N ≤ 10`, every
`S ⊆ [1, N]` and every `m ∉ S`. -/

def below (S : List Nat) (j : Nat) : Nat := S.countP (· ≤ j)

def cycBelow (N : Nat) (S : List Nat) (j : Nat) : Nat :=
  below S (j % N) + (j / N) * S.length

def CyclicStep (N : Nat) (S : List Nat) (m : Nat) : Prop :=
  cycBelow N S (2 * m - 1) = 2 * below S (m - 1)

instance (N : Nat) (S : List Nat) (m : Nat) : Decidable (CyclicStep N S m) :=
  inferInstanceAs (Decidable (_ = _))

def subsets : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => subsets xs ++ (subsets xs).map (x :: ·)

theorem semiStep_iff_cyclicStep_small : ∀ N ∈ List.range 11,
    ∀ S ∈ subsets (List.range' 1 N), ∀ m ∈ List.range' 1 N, m ∉ S →
      (SemiStep N S m ↔ CyclicStep N S m) := by
  native_decide

end Folds
