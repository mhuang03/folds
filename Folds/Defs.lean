/-!
# Fold sequences: symmetric and semi-symmetric bisection orders

Panels are numbered `1, …, N`.  A *fold sequence* is a permutation `a = [a₁, …, a_N]`
of `[1, …, N]`: panel `aₖ` is bisected at step `k`.

To bisect panel `m` we fold the nearer usable edge onto a reference fold.  The
panels lying strictly between that edge and the reference fold are `m - d` and
`m + d` for `1 ≤ d ≤ reach N m`, where `reach N m = min (m - 1) (N - m)`.
(In the informal statement this was written `min (N - k) (k - 1)`; the index that
matters is the *panel* `aₖ`, not the step `k`.)
-/

namespace Folds

/-- Number of panels on each side of panel `m` that lie between the edge and the
reference fold used to bisect `m`. -/
def reach (N m : Nat) : Nat := min (m - 1) (N - m)

/-- `a` is a fold sequence of length `N`: a permutation of `[1, …, N]`. -/
def IsFoldSeq (N : Nat) (a : List Nat) : Prop := a.Perm (List.range' 1 N)

instance (N : Nat) (a : List Nat) : Decidable (IsFoldSeq N a) :=
  inferInstanceAs (Decidable (a.Perm _))

/-! ## The condition for a single step

`S` is the list of panels already bisected, `m` the panel being bisected now. -/

/-- Symmetric step: the already-bisected panels inside the window are mirror-symmetric
about `m`. -/
def SymStep (N : Nat) (S : List Nat) (m : Nat) : Prop :=
  ∀ d, 1 ≤ d → d ≤ reach N m → (m - d ∈ S ↔ m + d ∈ S)

/-- Number of already-bisected panels in the window, to the left of `m`. -/
def leftCount (N : Nat) (S : List Nat) (m : Nat) : Nat :=
  (List.range' 1 (reach N m)).countP fun d => m - d ∈ S

/-- Number of already-bisected panels in the window, to the right of `m`. -/
def rightCount (N : Nat) (S : List Nat) (m : Nat) : Nat :=
  (List.range' 1 (reach N m)).countP fun d => m + d ∈ S

/-- Semi-symmetric step: equally many already-bisected panels on either side of `m`
inside the window. -/
def SemiStep (N : Nat) (S : List Nat) (m : Nat) : Prop :=
  leftCount N S m = rightCount N S m

instance (N : Nat) (S : List Nat) (m : Nat) : Decidable (SemiStep N S m) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Whole sequences -/

/-- Every step of `a` is symmetric. -/
def Symmetric (N : Nat) (a : List Nat) : Prop :=
  ∀ k (h : k < a.length), SymStep N (a.take k) a[k]

/-- Every step of `a` is semi-symmetric. -/
def SemiSymmetric (N : Nat) (a : List Nat) : Prop :=
  ∀ k (h : k < a.length), SemiStep N (a.take k) a[k]

/-- `a` contains no 3-term arithmetic progression `x, (x+y)/2, y` as a subsequence,
i.e. the average of two terms never occurs between them. -/
def APFree (a : List Nat) : Prop :=
  ∀ i j k (hi : i < j) (hj : j < k) (hk : k < a.length),
    a[i] + a[k] ≠ 2 * a[j]

end Folds
