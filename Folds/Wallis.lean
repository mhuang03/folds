import Folds.Recursion
import Folds.Cyclic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# The single-constraint (Wallis) count

Fix a panel `1 ≤ m ≤ N` with `r = reach N m`.  `card_wallisSeqs`: the number of fold
sequences in which the step bisecting `m` is semi-symmetric satisfies
`card · (2r+1)! = N! · 4^r · (r!)²`.

Proof outline.
* `card_filter_before`: split an ordering `l = u ++ m :: v` at `m`; the orderings whose
  set of panels before `m` is `A` number `|A|! · (N - 1 - |A|)!`.
* `semiStep_iff_balanced`: the step is valid iff the set `A` has equally many elements in
  the left part `[m-r, m)` and the right part `(m, m+r]` of the window.
* `sum_balanced`: splitting `A` into its left, right and outside parts,
  the count is `∑_j C(r,j)² ∑_i C(M,i) (2j+i)! (N-1-2j-i)!` with `M = N - 1 - 2r`.
* `sum_choose_factorial` (Beta integral):
  `∑_{i+k=M} C(M,i) (a+i)! (b+k)! · (a+b+1)! = a! b! (a+b+M+1)!`.
* `sum_centralBinom_antidiagonal`: `∑_{i+k=n} C(2i,i) C(2k,k) = 4^n`, hence
  `sum_choose_sq_factorial`: `∑_{j+k=r} C(r,j)² (2j)! (2k)! = 4^r (r!)²`.
-/

namespace Folds

open Finset Nat

/-! ## Arithmetic identities -/

/-- `∑_{i + k = n} C(2i, i) · C(2k, k) = 4 ^ n`. -/
theorem sum_centralBinom_antidiagonal (n : ℕ) :
    ∑ p ∈ antidiagonal n, p.1.centralBinom * p.2.centralBinom = 4 ^ n := by
  set S : ℕ → ℕ := fun n => ∑ p ∈ antidiagonal n, p.1.centralBinom * p.2.centralBinom
    with hS
  set T : ℕ → ℕ := fun n =>
    ∑ p ∈ antidiagonal n, p.1 * (p.1.centralBinom * p.2.centralBinom) with hT
  have hsym : ∀ n, 2 * T n = n * S n := by
    intro n
    have hs : T n = ∑ p ∈ antidiagonal n, p.2 * (p.1.centralBinom * p.2.centralBinom) := by
      rw [hT, ← Finset.Nat.sum_antidiagonal_swap]
      apply sum_congr rfl; intro p _; simp only [Prod.fst_swap, Prod.snd_swap]; ring
    rw [two_mul]; nth_rw 2 [hs]
    rw [hT, ← sum_add_distrib, hS, mul_sum]
    apply sum_congr rfl; intro p hp; rw [mem_antidiagonal] at hp; rw [← hp]; ring
  have hstep : ∀ n, T (n + 1) = 4 * T n + 2 * S n := by
    intro n
    simp only [hT, hS]
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp only [zero_mul, zero_add]
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro p _
    have := Nat.succ_mul_centralBinom_succ p.1
    calc (p.1 + 1) * ((p.1 + 1).centralBinom * p.2.centralBinom)
        = ((p.1 + 1) * (p.1 + 1).centralBinom) * p.2.centralBinom := by ring
      _ = _ := by rw [this]; ring
  have hrec : ∀ n, S (n + 1) = 4 * S n := by
    intro n
    have h1 := hsym (n + 1)
    have h2 := hsym n
    rw [hstep n] at h1
    have : (n + 1) * S (n + 1) = (n + 1) * (4 * S n) := by
      rw [← h1]; nlinarith
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  show S n = 4 ^ n
  induction n with
  | zero => simp [hS]
  | succ n ih => rw [hrec, ih, pow_succ]; ring

/-- `∑_{i + k = M} C(M, i) (a + i)! (b + k)! · (a + b + 1)! = a! b! (a + b + M + 1)!`
(a Beta-integral identity). -/
theorem sum_choose_factorial (M : ℕ) : ∀ a b : ℕ,
    (∑ p ∈ antidiagonal M, M.choose p.1 * ((a + p.1)! * (b + p.2)!)) * (a + b + 1)! =
      a ! * b ! * (a + b + M + 1)! := by
  induction M with
  | zero => intro a b; simp
  | succ M ih =>
    intro a b
    have split : ∑ p ∈ antidiagonal (M + 1), (M + 1).choose p.1 * ((a + p.1)! * (b + p.2)!) =
        ∑ p ∈ antidiagonal M, M.choose p.1 * ((a + 1 + p.1)! * (b + p.2)!) +
        ∑ p ∈ antidiagonal M, M.choose p.1 * ((a + p.1)! * (b + 1 + p.2)!) := by
      rw [Finset.Nat.sum_antidiagonal_succ]
      simp only [Nat.choose_succ_succ', add_mul, sum_add_distrib]
      have e2 : ∑ p ∈ antidiagonal M, M.choose p.1 * ((a + p.1)! * (b + 1 + p.2)!) =
          (M.choose 0 * ((a + 0)! * (b + (M + 1))!) +
          ∑ p ∈ antidiagonal M, M.choose (p.1 + 1) * ((a + (p.1 + 1))! * (b + p.2)!)) := by
        have := Finset.Nat.sum_antidiagonal_succ
          (f := fun p : ℕ × ℕ => M.choose p.1 * ((a + p.1)! * (b + p.2)!)) (n := M)
        rw [Finset.Nat.sum_antidiagonal_succ'] at this
        simp only [Nat.choose_succ_self, zero_mul, zero_add] at this
        rw [← this]
        apply sum_congr rfl; intro p _; congr 3; omega
      rw [e2]
      simp only [Nat.choose_zero_right]
      have e1 : ∑ p ∈ antidiagonal M, M.choose p.1 * ((a + (p.1 + 1))! * (b + p.2)!) =
          ∑ p ∈ antidiagonal M, M.choose p.1 * ((a + 1 + p.1)! * (b + p.2)!) := by
        apply sum_congr rfl; intro p _; congr 3; omega
      rw [e1]; ring
    have h1 := ih (a + 1) b
    have h2 := ih a (b + 1)
    rw [split]
    apply Nat.eq_of_mul_eq_mul_left (show 0 < a + b + 2 by omega)
    have f1 : (a + 1 + b + 1)! = (a + b + 2) * (a + b + 1)! := by
      rw [show a + 1 + b + 1 = (a + b + 1) + 1 by omega, Nat.factorial_succ]
    have f2 : (a + (b + 1) + 1)! = (a + b + 2) * (a + b + 1)! := by
      rw [show a + (b + 1) + 1 = (a + b + 1) + 1 by omega, Nat.factorial_succ]
    rw [f1] at h1; rw [f2] at h2
    rw [show a + 1 + b + M + 1 = a + b + (M + 1) + 1 by omega, Nat.factorial_succ a] at h1
    rw [show a + (b + 1) + M + 1 = a + b + (M + 1) + 1 by omega, Nat.factorial_succ b] at h2
    calc (a + b + 2) * ((∑ p ∈ antidiagonal M, M.choose p.1 * ((a + 1 + p.1)! * (b + p.2)!) +
          ∑ p ∈ antidiagonal M, M.choose p.1 * ((a + p.1)! * (b + 1 + p.2)!)) * (a + b + 1)!)
        = (∑ p ∈ antidiagonal M, M.choose p.1 * ((a + 1 + p.1)! * (b + p.2)!)) *
            ((a + b + 2) * (a + b + 1)!) +
          (∑ p ∈ antidiagonal M, M.choose p.1 * ((a + p.1)! * (b + 1 + p.2)!)) *
            ((a + b + 2) * (a + b + 1)!) := by ring
      _ = (a + b + 2) * (a ! * b ! * (a + b + (M + 1) + 1)!) := by rw [h1, h2]; ring

/-- `∑_{j + k = r} C(r, j)² (2j)! (2k)! = 4^r (r!)²`. -/
theorem sum_choose_sq_factorial (r : ℕ) :
    ∑ p ∈ antidiagonal r, r.choose p.1 ^ 2 * ((2 * p.1)! * (2 * p.2)!) = 4 ^ r * r ! ^ 2 := by
  rw [← sum_centralBinom_antidiagonal, sum_mul]
  apply sum_congr rfl
  intro p hp
  rw [mem_antidiagonal] at hp
  have c1 := Nat.choose_mul_factorial_mul_factorial (show p.1 ≤ r by omega)
  have c2 := Nat.choose_mul_factorial_mul_factorial (show p.1 ≤ 2 * p.1 by omega)
  have c3 := Nat.choose_mul_factorial_mul_factorial (show p.2 ≤ 2 * p.2 by omega)
  rw [show r - p.1 = p.2 by omega] at c1
  rw [show 2 * p.1 - p.1 = p.1 by omega] at c2
  rw [show 2 * p.2 - p.2 = p.2 by omega] at c3
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose, ← c1, ← c2, ← c3]
  ring

/-- The arithmetic core of the Wallis count:
`∑_j C(r,j)² ∑_i C(M,i) (2j+i)! (2r+M-2j-i)! · (2r+1)! = (2r+M+1)! 4^r (r!)²`. -/
theorem wallis_arith (r M : ℕ) :
    (∑ j ∈ range (r + 1), r.choose j * (r.choose j * ∑ i ∈ range (M + 1),
      M.choose i * ((j + j + i)! * (2 * r + M - (j + j + i))!))) * (2 * r + 1)! =
      (2 * r + M + 1)! * 4 ^ r * r ! ^ 2 := by
  rw [sum_mul]
  have hj : ∀ j ∈ range (r + 1), r.choose j * (r.choose j * ∑ i ∈ range (M + 1),
      M.choose i * ((j + j + i)! * (2 * r + M - (j + j + i))!)) * (2 * r + 1)! =
      r.choose j ^ 2 * ((2 * j)! * (2 * (r - j))!) * (2 * r + M + 1)! := by
    intro j hj
    rw [mem_range] at hj
    have h := sum_choose_factorial M (2 * j) (2 * (r - j))
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => M.choose i * ((2 * j + i)! * (2 * (r - j) + k)!)) M] at h
    have e : ∑ i ∈ range (M + 1), M.choose i * ((j + j + i)! * (2 * r + M - (j + j + i))!) =
        ∑ k ∈ range M.succ, M.choose k * ((2 * j + k)! * (2 * (r - j) + (M - k))!) := by
      apply sum_congr rfl; intro i hi; rw [mem_range] at hi
      congr 3 <;> omega
    rw [e]
    rw [show 2 * j + 2 * (r - j) + 1 = 2 * r + 1 by omega,
      show 2 * j + 2 * (r - j) + M + 1 = 2 * r + M + 1 by omega] at h
    calc r.choose j * (r.choose j * ∑ k ∈ range M.succ,
          M.choose k * ((2 * j + k)! * (2 * (r - j) + (M - k))!)) * (2 * r + 1)!
        = r.choose j ^ 2 * ((∑ k ∈ range M.succ,
          M.choose k * ((2 * j + k)! * (2 * (r - j) + (M - k))!)) * (2 * r + 1)!) := by ring
      _ = _ := by rw [h]; ring
  rw [sum_congr rfl hj, ← sum_mul]
  have h2 := sum_choose_sq_factorial r
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j k => r.choose j ^ 2 * ((2 * j)! * (2 * k)!)) r] at h2
  rw [h2]; ring

/-! ## Orderings, split at a given panel -/

theorem card_orderings (S : Finset ℕ) : (orderings S).card = S.card ! := by
  rw [orderings, List.toFinset_card_of_nodup (List.nodup_permutations _ (Finset.sort_nodup _ _)),
    List.length_permutations, Finset.length_sort]

/-- The set of panels listed before `m` in `l`. -/
def before (l : List ℕ) (m : ℕ) : Finset ℕ := (l.take (l.idxOf m)).toFinset

theorem eq_take_idxOf {l : List ℕ} {m : ℕ} (hm : m ∈ l) :
    l = l.take (l.idxOf m) ++ m :: l.drop (l.idxOf m + 1) := by
  have hi := List.idxOf_lt_length_of_mem hm
  conv_lhs => rw [← List.take_append_drop (l.idxOf m) l, List.drop_eq_getElem_cons hi,
    List.getElem_idxOf hi]

theorem idxOf_append_cons {u v : List ℕ} {m : ℕ} (h : m ∉ u) :
    (u ++ m :: v).idxOf m = u.length := by
  rw [List.idxOf_append]; simp [h]

theorem take_idxOf_append_cons {u v : List ℕ} {m : ℕ} (h : m ∉ u) :
    (u ++ m :: v).take ((u ++ m :: v).idxOf m) = u := by
  rw [idxOf_append_cons h, List.take_left' rfl]

theorem drop_idxOf_append_cons {u v : List ℕ} {m : ℕ} (h : m ∉ u) :
    (u ++ m :: v).drop ((u ++ m :: v).idxOf m + 1) = v := by
  rw [idxOf_append_cons h, show u.length + 1 = (u ++ [m]).length by simp,
    show u ++ m :: v = (u ++ [m]) ++ v by simp, List.drop_left' rfl]

/-- `u ++ m :: v` orders `X` with `u` ordering `A` iff `u` orders `A` and `v` orders the rest. -/
theorem split_mem_orderings {X A : Finset ℕ} {m : ℕ} (hm : m ∈ X) (hA : A ⊆ X.erase m)
    {u v : List ℕ} :
    (u ++ m :: v ∈ orderings X ∧ u.toFinset = A) ↔
      (u ∈ orderings A ∧ v ∈ orderings (X.erase m \ A)) := by
  simp only [mem_orderings, List.nodup_append, List.nodup_cons]
  constructor
  · rintro ⟨⟨⟨hu, ⟨hmv, hv⟩, hd⟩, hX⟩, hA'⟩
    refine ⟨⟨hu, hA'⟩, hv, ?_⟩
    ext x
    simp only [List.mem_toFinset, mem_sdiff, mem_erase, ← hX, ← hA', List.toFinset_append,
      mem_union, List.toFinset_cons, mem_insert]
    constructor
    · intro hx
      refine ⟨⟨fun e => hmv (e ▸ hx), Or.inr (Or.inr hx)⟩, fun hxu => ?_⟩
      exact hd x hxu x (List.mem_cons_of_mem _ hx) rfl
    · rintro ⟨⟨hxm, hx⟩, hxu⟩
      rcases hx with hx | hx | hx
      · exact absurd hx hxu
      · exact absurd hx hxm
      · exact hx
  · rintro ⟨⟨hu, hA'⟩, hv, hv'⟩
    have hvm : ∀ x ∈ v, x ∈ X ∧ x ≠ m ∧ x ∉ A := by
      intro x hx
      have := List.mem_toFinset.2 hx
      rw [hv'] at this
      simp only [mem_sdiff, mem_erase] at this
      exact ⟨this.1.2, this.1.1, this.2⟩
    have hum : ∀ x ∈ u, x ∈ X ∧ x ≠ m ∧ x ∈ A := by
      intro x hx
      have := List.mem_toFinset.2 hx
      rw [hA'] at this
      have h2 := mem_erase.1 (hA this)
      exact ⟨h2.2, h2.1, this⟩
    refine ⟨⟨⟨hu, ⟨fun h => (hvm m h).2.1 rfl, hv⟩, ?_⟩, ?_⟩, hA'⟩
    · intro a ha b hb e
      subst e
      rcases List.mem_cons.1 hb with hb | hb
      · exact (hum a ha).2.1 hb
      · exact (hvm a hb).2.2 (hum a ha).2.2
    · ext x
      simp only [List.toFinset_append, List.toFinset_cons, mem_union, mem_insert,
        List.mem_toFinset]
      constructor
      · rintro (hx | hx | hx)
        · exact (hum x hx).1
        · exact hx ▸ hm
        · exact (hvm x hx).1
      · intro hx
        by_cases hxm : x = m
        · exact Or.inr (Or.inl hxm)
        by_cases hxA : x ∈ A
        · left; rw [← List.mem_toFinset, hA']; exact hxA
        · right; right
          rw [← List.mem_toFinset, hv']
          simp only [mem_sdiff, mem_erase]
          exact ⟨⟨hxm, hx⟩, hxA⟩

/-- The orderings of `X` in which exactly the panels of `A` come before `m`. -/
theorem card_orderings_before {X A : Finset ℕ} {m : ℕ} (hm : m ∈ X) (hA : A ⊆ X.erase m) :
    ((orderings X).filter (fun l => before l m = A)).card =
      A.card ! * (X.card - 1 - A.card)! := by
  have hB : (X.erase m \ A).card = X.card - 1 - A.card := by
    rw [card_sdiff_of_subset hA, card_erase_of_mem hm]
  rw [← hB, ← card_orderings, ← card_orderings, ← card_product]
  apply card_nbij' (fun l => (l.take (l.idxOf m), l.drop (l.idxOf m + 1)))
    (fun p => p.1 ++ m :: p.2)
  · intro l hl
    simp only [coe_filter, Set.mem_ofPred_eq] at hl
    obtain ⟨hl, hb⟩ := hl
    have hml : m ∈ l := by
      rw [← List.mem_toFinset, (mem_orderings.1 hl).2]; exact hm
    rw [eq_take_idxOf hml] at hl
    simp only [coe_product, Set.mem_prod, mem_coe]
    exact (split_mem_orderings hm hA).1 ⟨hl, hb⟩
  · rintro ⟨u, v⟩ hp
    simp only [coe_product, Set.mem_prod, mem_coe] at hp
    have h := (split_mem_orderings hm hA).2 hp
    have hmu : m ∉ u := by
      intro hmu
      have := hA (h.2 ▸ List.mem_toFinset.2 hmu)
      simp at this
    simp only [coe_filter, Set.mem_ofPred_eq]
    refine ⟨h.1, ?_⟩
    rw [before, take_idxOf_append_cons hmu, h.2]
  · intro l hl
    simp only [coe_filter, Set.mem_ofPred_eq] at hl
    have hml : m ∈ l := by
      rw [← List.mem_toFinset, (mem_orderings.1 hl.1).2]; exact hm
    exact (eq_take_idxOf hml).symm
  · rintro ⟨u, v⟩ hp
    simp only [coe_product, Set.mem_prod, mem_coe] at hp
    have h := (split_mem_orderings hm hA).2 hp
    have hmu : m ∉ u := by
      intro hmu
      have := hA (h.2 ▸ List.mem_toFinset.2 hmu)
      simp at this
    simp only [take_idxOf_append_cons hmu, drop_idxOf_append_cons hmu]

/-- Counting orderings of `X` by the set of panels placed before `m`. -/
theorem card_filter_before {X : Finset ℕ} {m : ℕ} (hm : m ∈ X) (Q : Finset ℕ → Prop)
    [DecidablePred Q] :
    ((orderings X).filter (fun l => Q (before l m))).card =
      ∑ A ∈ (X.erase m).powerset.filter Q, A.card ! * (X.card - 1 - A.card)! := by
  rw [card_eq_sum_card_fiberwise (f := fun l => before l m)
    (t := (X.erase m).powerset.filter Q)]
  · apply sum_congr rfl
    intro A hA
    rw [mem_filter, mem_powerset] at hA
    rw [← card_orderings_before hm hA.1, filter_filter]
    congr 1
    apply filter_congr
    intro l _
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hA.2, h⟩
  · intro l hl
    simp only [coe_filter, Set.mem_ofPred_eq] at hl
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powerset]
    refine ⟨?_, hl.2⟩
    obtain ⟨hnd, hX⟩ := mem_orderings.1 hl.1
    have hml : m ∈ l := by rw [← List.mem_toFinset, hX]; exact hm
    intro x hx
    rw [before, List.mem_toFinset] at hx
    have e := eq_take_idxOf hml
    have hnd' := hnd
    rw [e, List.nodup_append] at hnd'
    rw [mem_erase, ← hX, List.mem_toFinset]
    refine ⟨fun h => hnd'.2.2 x hx m (List.mem_cons_self) h, List.mem_of_mem_take hx⟩

/-! ## The window condition as a condition on the set of earlier panels -/

/-- The set `A` of already-bisected panels has equally many elements in the left and in the
right part of the window of `m`. -/
def BalancedBefore (N m : ℕ) (A : Finset ℕ) : Prop :=
  (A.filter (fun x => m - reach N m ≤ x ∧ x < m)).card =
    (A.filter (fun x => m < x ∧ x ≤ m + reach N m)).card

instance (N m : ℕ) (A : Finset ℕ) : Decidable (BalancedBefore N m A) :=
  inferInstanceAs (Decidable (_ = _))

theorem countP_eq_card_filter {S : List ℕ} (hnd : S.Nodup) (p : ℕ → Prop) [DecidablePred p] :
    S.countP (fun x => decide (p x)) = (S.toFinset.filter p).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _),
    List.toFinset_filter]
  simp

theorem semiStep_iff_balanced {N m : ℕ} {S : List ℕ} (hnd : S.Nodup) :
    SemiStep N S m ↔ BalancedBefore N m S.toFinset := by
  unfold SemiStep BalancedBefore
  rw [leftCount_eq hnd, rightCount_eq hnd, countP_eq_card_filter hnd, countP_eq_card_filter hnd]

/-! ## Summing over subsets of a disjoint union -/

theorem sum_powerset_union {U V : Finset ℕ} (h : Disjoint U V) (f : Finset ℕ → ℕ) :
    ∑ A ∈ (U ∪ V).powerset, f A = ∑ B ∈ U.powerset, ∑ C ∈ V.powerset, f (B ∪ C) := by
  rw [← sum_product' (f := fun B C => f (B ∪ C))]
  apply sum_nbij' (fun A => (A ∩ U, A ∩ V)) (fun p => p.1 ∪ p.2)
  · intro A _
    rw [mem_product, mem_powerset, mem_powerset]
    exact ⟨inter_subset_right, inter_subset_right⟩
  · intro p hp
    rw [mem_product, mem_powerset, mem_powerset] at hp
    rw [mem_powerset]
    exact union_subset_union hp.1 hp.2
  · intro A hA
    rw [mem_powerset] at hA
    show A ∩ U ∪ A ∩ V = A
    rw [← inter_union_distrib_left, inter_eq_left.2 hA]
  · rintro ⟨B, C⟩ hp
    rw [mem_product, mem_powerset, mem_powerset] at hp
    have hCU : C ∩ U = ∅ := disjoint_iff_inter_eq_empty.1
      (disjoint_of_subset_left hp.2 h.symm)
    have hBV : B ∩ V = ∅ := disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left hp.1 h)
    simp only [union_inter_distrib_right, hCU, hBV, union_empty, empty_union,
      inter_eq_left.2 hp.1, inter_eq_left.2 hp.2]
  · intro A hA
    rw [mem_powerset] at hA
    show f A = f (A ∩ U ∪ A ∩ V)
    rw [← inter_union_distrib_left, inter_eq_left.2 hA]

/-- The summand after splitting the earlier set into its left, right and outside parts. -/
def wallisTerm (N j k i : ℕ) : ℕ := if j = k then (j + k + i)! * (N - 1 - (j + k + i))! else 0

theorem sum_balanced {N m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ N) :
    ∑ A ∈ ((Icc 1 N).erase m).powerset.filter (BalancedBefore N m),
      A.card ! * (N - 1 - A.card)! =
    ∑ j ∈ range (reach N m + 1), (reach N m).choose j * ((reach N m).choose j *
      ∑ i ∈ range (N - 1 - 2 * reach N m + 1), (N - 1 - 2 * reach N m).choose i *
        ((j + j + i)! * (N - 1 - (j + j + i))!)) := by
  set r := reach N m with hr
  have hr1 : r + 1 ≤ m := by rw [hr]; unfold reach; omega
  have hr2 : m + r ≤ N := by rw [hr]; unfold reach; omega
  set E := (Icc 1 N).erase m with hE
  set pL : ℕ → Prop := fun x => m - r ≤ x ∧ x < m with hpL
  set pR : ℕ → Prop := fun x => m < x ∧ x ≤ m + r with hpR
  set L := E.filter pL with hL
  set R := E.filter pR with hR
  set O := E.filter (fun x => ¬ pL x ∧ ¬ pR x) with hO
  have hLRO : E = L ∪ (R ∪ O) := by
    ext x; simp only [hL, hR, hO, mem_union, mem_filter]; tauto
  have dRO : Disjoint R O := by
    rw [hR, hO, disjoint_filter]; intro x _ h h'; exact h'.2 h
  have dL : Disjoint L (R ∪ O) := by
    rw [disjoint_union_right]; constructor
    · rw [hL, hR, disjoint_filter]; intro x _ h h'
      simp only [hpL, hpR] at h h'; omega
    · rw [hL, hO, disjoint_filter]; intro x _ h h'; exact h'.1 h
  have cL : L.card = r := by
    have : L = Ico (m - r) m := by
      ext x; simp only [hL, hE, hpL, mem_filter, mem_erase, mem_Icc, mem_Ico]; omega
    rw [this, Nat.card_Ico]; omega
  have cR : R.card = r := by
    have : R = Ioc m (m + r) := by
      ext x; simp only [hR, hE, hpR, mem_filter, mem_erase, mem_Icc, mem_Ioc]; omega
    rw [this, Nat.card_Ioc]; omega
  have cO : O.card = N - 1 - 2 * r := by
    have hc : E.card = L.card + (R.card + O.card) := by
      rw [hLRO, card_union_of_disjoint dL, card_union_of_disjoint dRO]
    have : E.card = N - 1 := by rw [hE, card_erase_of_mem (by simp; omega), Nat.card_Icc]; omega
    omega
  rw [sum_filter, hLRO, sum_powerset_union dL]
  -- rewrite the summand
  have step1 : ∀ B ∈ L.powerset, ∑ A ∈ (R ∪ O).powerset,
      (if BalancedBefore N m (B ∪ A) then (B ∪ A).card ! * (N - 1 - (B ∪ A).card)! else 0) =
      ∑ C ∈ R.powerset, ∑ D ∈ O.powerset, wallisTerm N B.card C.card D.card := by
    intro B hB
    rw [sum_powerset_union dRO]
    apply sum_congr rfl; intro C hC; apply sum_congr rfl; intro D hD
    rw [mem_powerset] at hB hC hD
    have fL : (B ∪ (C ∪ D)).filter pL = B := by
      rw [filter_union, filter_union, filter_true_of_mem, filter_false_of_mem,
        filter_false_of_mem, union_empty, union_empty]
      · intro x hx; exact (mem_filter.1 (hD hx)).2.1
      · intro x hx h; have := (mem_filter.1 (hC hx)).2; simp only [hpL, hpR] at h this; omega
      · intro x hx; exact (mem_filter.1 (hB hx)).2
    have fR : (B ∪ (C ∪ D)).filter pR = C := by
      rw [filter_union, filter_union, filter_false_of_mem, filter_true_of_mem,
        filter_false_of_mem, empty_union, union_empty]
      · intro x hx; exact (mem_filter.1 (hD hx)).2.2
      · intro x hx; exact (mem_filter.1 (hC hx)).2
      · intro x hx h; have := (mem_filter.1 (hB hx)).2; simp only [hpL, hpR] at h this; omega
    have cU : (B ∪ (C ∪ D)).card = B.card + C.card + D.card := by
      rw [card_union_of_disjoint (disjoint_of_subset_left hB
        (disjoint_of_subset_right (union_subset_union hC hD) dL)),
        card_union_of_disjoint (disjoint_of_subset_left hC (disjoint_of_subset_right hD dRO))]
      ring
    have hbal : BalancedBefore N m (B ∪ (C ∪ D)) ↔ B.card = C.card := by
      unfold BalancedBefore; rw [← hr]
      change ((B ∪ (C ∪ D)).filter pL).card = ((B ∪ (C ∪ D)).filter pR).card ↔ _
      rw [fL, fR]
    unfold wallisTerm
    rw [cU]
    simp only [hbal]
  rw [sum_congr rfl step1]
  have step2 : ∀ B ∈ L.powerset, ∑ C ∈ R.powerset, ∑ D ∈ O.powerset,
      wallisTerm N B.card C.card D.card =
      ∑ k ∈ range (R.card + 1), R.card.choose k * ∑ i ∈ range (O.card + 1),
        O.card.choose i * wallisTerm N B.card k i := by
    intro B _
    have h3 := sum_powerset_apply_card (fun k => ∑ i ∈ range (O.card + 1),
        O.card.choose i * wallisTerm N B.card k i) (x := R)
    simp only [nsmul_eq_mul, Nat.cast_id] at h3
    rw [← h3]
    apply sum_congr rfl; intro C _
    have h4 := sum_powerset_apply_card (wallisTerm N B.card C.card) (x := O)
    simp only [nsmul_eq_mul, Nat.cast_id] at h4
    exact h4
  rw [sum_congr rfl step2]
  have h5 := sum_powerset_apply_card (fun j => ∑ k ∈ range (R.card + 1), R.card.choose k *
    ∑ i ∈ range (O.card + 1), O.card.choose i * wallisTerm N j k i) (x := L)
  simp only [nsmul_eq_mul, Nat.cast_id] at h5
  rw [h5]
  simp only [cL, cR, cO]
  apply sum_congr rfl; intro j hj
  congr 1
  rw [sum_eq_single j]
  · congr 1; apply sum_congr rfl; intro i _; simp [wallisTerm]
  · intro k _ hk; simp [wallisTerm, Ne.symm hk]
  · intro h; exact absurd hj h

/-! ## The single-constraint (Wallis) count -/

/-- Fold sequences of length `N` in which the step placing panel `m` is semi-symmetric. -/
def wallisSeqs (N m : ℕ) : Finset (List ℕ) :=
  (List.range' 1 N).permutations.toFinset.filter fun a => SemiStep N (a.take (a.idxOf m)) m

theorem wallisSeqs_eq {N m : ℕ} :
    wallisSeqs N m = (orderings (Icc 1 N)).filter fun l => BalancedBefore N m (before l m) := by
  ext a
  rw [wallisSeqs, mem_filter, mem_filter, List.mem_toFinset, List.mem_permutations, before]
  have e : a.Perm (List.range' 1 N) ↔ a ∈ orderings (Icc 1 N) := by
    rw [mem_orderings, ← isFoldSeq_iff]; rfl
  rw [e]
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨h, (semiStep_iff_balanced (take_nodup (mem_orderings.1 h).1 _)).1 hs⟩
  · rintro ⟨h, hs⟩
    exact ⟨h, (semiStep_iff_balanced (take_nodup (mem_orderings.1 h).1 _)).2 hs⟩

/-- **Single-constraint (Wallis) count.**  For a panel `1 ≤ m ≤ N` with `r = reach N m`, the
number of fold sequences in which the step bisecting `m` is semi-symmetric is
`N! · 4^r · (r!)² / (2r+1)!`, i.e. a fraction `∏_{i=1}^r 2i/(2i+1)` of all `N!` sequences. -/
theorem card_wallisSeqs {N m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ N) :
    (wallisSeqs N m).card * (2 * reach N m + 1)! = N ! * 4 ^ reach N m * (reach N m)! ^ 2 := by
  have hm : m ∈ Icc 1 N := by simp; omega
  have hr : 2 * reach N m ≤ N - 1 := by unfold reach; omega
  rw [wallisSeqs_eq, card_filter_before hm, Nat.card_Icc, Nat.add_sub_cancel, sum_balanced h1 h2]
  have e : ∀ j i, N - 1 - (j + j + i) = 2 * reach N m + (N - 1 - 2 * reach N m) - (j + j + i) := by
    intro j i; congr 1; omega
  simp only [e]
  rw [wallis_arith, show 2 * reach N m + (N - 1 - 2 * reach N m) + 1 = N by omega]

end Folds
