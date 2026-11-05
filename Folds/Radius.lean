import Folds.Parity

/-!
# Capping the window radius

`CapStep c N S m` is the semi-symmetric step condition with the window radius capped at
`c`, i.e. only the panels `m ± d` with `1 ≤ d ≤ min c (reach N m)` are compared.

`capSemiSymmetric_one_iff`: with radius `1`, a fold sequence satisfies all capped steps
iff every interior panel is bisected at a local extremum of time: whenever panels
`m - 1, m, m + 1` are bisected at steps `i, j, k`, either `j` is before both or after both
(`i < j ↔ k < j`).  (Counting these gives the alternating permutations, `2·E_N`; the
count itself is not formalized here.)
-/

namespace Folds

def capLeftCount (c N : Nat) (S : List Nat) (m : Nat) : Nat :=
  (List.range' 1 (min c (reach N m))).countP fun d => m - d ∈ S

def capRightCount (c N : Nat) (S : List Nat) (m : Nat) : Nat :=
  (List.range' 1 (min c (reach N m))).countP fun d => m + d ∈ S

/-- Semi-symmetric step with window radius capped at `c`. -/
def CapStep (c N : Nat) (S : List Nat) (m : Nat) : Prop :=
  capLeftCount c N S m = capRightCount c N S m

def CapSemiSymmetric (c N : Nat) (a : List Nat) : Prop :=
  ∀ k (h : k < a.length), CapStep c N (a.take k) a[k]

/-- A cap at least as large as every reach is no cap. -/
theorem capStep_iff_of_le {c N m : Nat} {S : List Nat} (h : reach N m ≤ c) :
    CapStep c N S m ↔ SemiStep N S m := by
  unfold CapStep capLeftCount capRightCount SemiStep leftCount rightCount
  rw [Nat.min_eq_right h]

theorem capSemiSymmetric_iff_of_le {c N : Nat} (h : (N - 1) / 2 ≤ c) {a : List Nat} :
    CapSemiSymmetric c N a ↔ SemiSymmetric N a :=
  forall_congr' fun k => forall_congr' fun _ =>
    capStep_iff_of_le (by unfold reach; omega)

/-- **Radius 1.**  Capping the radius at `1`, the semi-symmetric condition says exactly
that each interior panel's time is a local maximum or minimum relative to its two
neighbours. -/
theorem capSemiSymmetric_one_iff {N : Nat} {a : List Nat} (hf : IsFoldSeq N a) :
    CapSemiSymmetric 1 N a ↔
      ∀ i j k (hi : i < a.length) (hj : j < a.length) (hk : k < a.length),
        a[i] + 1 = a[j] → a[j] + 1 = a[k] → (i < j ↔ k < j) := by
  have hnd := nodup_of_foldSeq hf
  have bnd : ∀ (p : Nat) (hp : p < a.length), 1 ≤ a[p] ∧ a[p] ≤ N :=
    fun p hp => (mem_range'_of_perm hf).1 (List.getElem_mem hp)
  have key : ∀ j (hj : j < a.length), 2 ≤ a[j] → a[j] + 1 ≤ N →
      (CapStep 1 N (a.take j) a[j] ↔ (a[j] - 1 ∈ a.take j ↔ a[j] + 1 ∈ a.take j)) := by
    intro j hj h1 h2
    have : min 1 (reach N a[j]) = 1 := by unfold reach; omega
    unfold CapStep capLeftCount capRightCount
    rw [this]
    simp only [List.range'_one, List.countP_cons, List.countP_nil]
    by_cases hl : a[j] - 1 ∈ a.take j <;> by_cases hr : a[j] + 1 ∈ a.take j <;> simp [hl, hr]
  constructor
  · intro h i j k hi hj hk e1 e2
    have b := bnd i hi; have b' := bnd k hk
    have := (key j hj (by omega) (by omega)).1 (h j hj)
    rw [show a[j] - 1 = a[i] by omega, e2, getElem_mem_take_iff hnd hi,
      getElem_mem_take_iff hnd hk] at this
    exact this
  · intro h j hj
    have b := bnd j hj
    by_cases hin : 2 ≤ a[j] ∧ a[j] + 1 ≤ N
    · rw [key j hj hin.1 hin.2]
      obtain ⟨i, hi, ei⟩ := List.mem_iff_getElem.1
        ((mem_range'_of_perm hf).2 (show 1 ≤ a[j] - 1 ∧ a[j] - 1 ≤ N by omega))
      obtain ⟨k, hk, ek⟩ := List.mem_iff_getElem.1
        ((mem_range'_of_perm hf).2 (show 1 ≤ a[j] + 1 ∧ a[j] + 1 ≤ N by omega))
      rw [← ei, ← ek, getElem_mem_take_iff hnd hi, getElem_mem_take_iff hnd hk]
      exact h i j k hi hj hk (by omega) ek.symm
    · have : min 1 (reach N a[j]) = 0 := by unfold reach; omega
      unfold CapStep capLeftCount capRightCount
      rw [this]; rfl

end Folds
