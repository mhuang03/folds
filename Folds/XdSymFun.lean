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
* `desPolyList`, `idesPolyList`: the polynomials as coefficient lists; `sum_desCount`.
* Extreme coefficients: `desCount_zero`, `desCount_top`, `idesCount_zero`, `idesCount_top`
  (they vanish for `N ≥ 3`), from `one_le_des` (via `descents_bound`) and `one_le_ides`
  (panel `2` is placed before both or after both of its neighbours, `ides_two`).
* Small cases by kernel computation: `desPolyList_four`, `desPolyList_five`,
  `idesPolyList_four`, `idesPolyList_five`.

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
  refine ⟨?_, SemiSymmetric.swap hI h.2⟩
  unfold IsFoldSeq at *
  exact ((List.Perm.swap x y v).append_left u).trans h.1

/-- Two panels in the left half are never independent: the larger one has the smaller one
in its window.  (By the mirror the same holds in the right half, so the heap of a
semi-symmetric sequence is a union of two chains.) -/
theorem not_indep_of_left {N x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hx2 : 2 * x ≤ N + 1)
    (hy2 : 2 * y ≤ N + 1) : ¬ Indep N x y := by
  unfold Indep reach; omega

/-! ### The converse: dependent panels do not commute -/

theorem countP_or_disjoint (l : List ℕ) (p q : ℕ → Bool)
    (h : ∀ d ∈ l, ¬ (p d = true ∧ q d = true)) :
    l.countP (fun d => p d || q d) = l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have := ih (fun d hd => h d (by simp [hd]))
    simp only [List.countP_cons, this]
    revert ha; cases p a <;> cases q a <;> simp <;> omega

theorem leftCount_append {N x y : ℕ} {S : List ℕ} (hy : y ∉ S) :
    leftCount N (S ++ [y]) x = leftCount N S x +
      (List.range' 1 (reach N x)).countP (fun d => decide (x - d = y)) := by
  have key := countP_or_disjoint (List.range' 1 (reach N x)) (fun d => decide (x - d ∈ S))
    (fun d => decide (x - d = y)) (by
      intro d _ h
      simp only [decide_eq_true_eq] at h
      exact hy (h.2 ▸ h.1))
  unfold leftCount
  rw [← key]
  apply List.countP_congr
  intro d _
  simp [List.mem_append]

theorem rightCount_append {N x y : ℕ} {S : List ℕ} (hy : y ∉ S) :
    rightCount N (S ++ [y]) x = rightCount N S x +
      (List.range' 1 (reach N x)).countP (fun d => decide (x + d = y)) := by
  have key := countP_or_disjoint (List.range' 1 (reach N x)) (fun d => decide (x + d ∈ S))
    (fun d => decide (x + d = y)) (by
      intro d _ h
      simp only [decide_eq_true_eq] at h
      exact hy (h.2 ▸ h.1))
  unfold rightCount
  rw [← key]
  apply List.countP_congr
  intro d _
  simp [List.mem_append]

/-- If `x` is valid both after `S` and after `S ++ [y]`, then `y` is outside the window
of `x`. -/
theorem far_of_steps {N x y : ℕ} {S : List ℕ} (hxy : x ≠ y) (hy : y ∉ S)
    (h1 : SemiStep N S x) (h2 : SemiStep N (S ++ [y]) x) :
    reach N x < (x - y) + (y - x) := by
  by_contra hle
  rw [not_lt] at hle
  unfold SemiStep at h1 h2
  rw [leftCount_append hy, rightCount_append hy] at h2
  have hr1 : reach N x ≤ x - 1 := by unfold reach; omega
  rcases Nat.lt_or_gt_of_ne hxy with hlt | hgt
  · have c1 : (List.range' 1 (reach N x)).countP (fun d => decide (x + d = y)) = 1 :=
      countP_range'_eq_one (fun d => x + d = y) (c := y - x) (by omega) (by omega)
        (fun d _ _ => by omega)
    have c0 : (List.range' 1 (reach N x)).countP (fun d => decide (x - d = y)) = 0 := by
      rw [List.countP_eq_zero]
      intro d _
      simp only [decide_eq_true_eq]
      omega
    omega
  · have c1 : (List.range' 1 (reach N x)).countP (fun d => decide (x - d = y)) = 1 :=
      countP_range'_eq_one (fun d => x - d = y) (c := x - y) (by omega) (by omega)
        (fun d _ hd => by omega)
    have c0 : (List.range' 1 (reach N x)).countP (fun d => decide (x + d = y)) = 0 := by
      rw [List.countP_eq_zero]
      intro d _
      simp only [decide_eq_true_eq]
      omega
    omega

/-- **Converse of the commutation lemma.**  If a semi-symmetric fold sequence stays
semi-symmetric after swapping the adjacent panels `x`, `y`, then they are independent. -/
theorem indep_of_swap_mem_semiSeqs {N x y : ℕ} {u v : List ℕ}
    (h1 : u ++ x :: y :: v ∈ semiSeqs N) (h2 : u ++ y :: x :: v ∈ semiSeqs N) :
    Indep N x y := by
  rw [mem_semiSeqs] at h1 h2
  have hnd := nodup_of_foldSeq h1.1
  rw [List.nodup_append] at hnd
  obtain ⟨-, hxyv, hdis⟩ := hnd
  have hxy : x ≠ y := by
    rw [List.nodup_cons] at hxyv
    intro e
    exact hxyv.1 (by rw [e]; simp)
  have hxu : x ∉ u := fun hx => hdis x hx x (by simp) rfl
  have hyu : y ∉ u := fun hy => hdis y hy y (by simp) rfl
  obtain ⟨-, a2, a3, -⟩ := semiSymmetric_two_iff.1 h1.2
  obtain ⟨-, b2, b3, -⟩ := semiSymmetric_two_iff.1 h2.2
  have f1 := far_of_steps hxy hyu a2 b3
  have f2 := far_of_steps (Ne.symm hxy) hxu b2 a3
  unfold Indep
  omega

/-! ## Descents of the fold sequence -/

theorem getD_eq {a : List ℕ} {i : ℕ} (hi : i < a.length) : a.getD i 0 = a[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem getD_mirror {N : ℕ} {a : List ℕ} {i : ℕ} (hi : i < a.length) :
    (mirror N a).getD i 0 = N + 1 - a[i] := by
  simp [mirror, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem length_of_foldSeq {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a) : a.length = N := by
  rw [hf.length_eq]; simp

/-- The mirror `m ↦ N + 1 - m` exchanges descents and ascents. -/
theorem des_mirror {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a) :
    des (mirror N a) + des a = N - 1 := by
  have hlen := length_of_foldSeq hf
  have hnd := nodup_of_foldSeq hf
  have hm : (mirror N a).length = a.length := by simp [mirror]
  unfold des desBefore
  rw [hm]
  have e : (List.range (a.length - 1)).countP (descentAt (mirror N a)) =
      (List.range (a.length - 1)).countP (fun i => decide (¬ descentAt a i = true)) := by
    apply List.countP_congr
    intro i hi
    rw [List.mem_range] at hi
    have h1 : i < a.length := by omega
    have h2 : i + 1 < a.length := by omega
    have b1 := (mem_range'_of_perm hf).1 (List.getElem_mem h1)
    have b2 := (mem_range'_of_perm hf).1 (List.getElem_mem h2)
    have hne : a[i] ≠ a[i + 1] := fun e => by
      have := (List.Nodup.getElem_inj_iff hnd).1 e
      omega
    unfold descentAt
    rw [getD_mirror h2, getD_mirror h1, getD_eq h2, getD_eq h1]
    simp only [decide_eq_true_eq]
    omega
  rw [e]
  have key := List.length_eq_countP_add_countP (descentAt a) (l := List.range (a.length - 1))
  simp only [List.length_range] at key
  omega

/-- `des a < N` (for `N ≥ 1`). -/
theorem des_lt {N : ℕ} {a : List ℕ} (hN : 1 ≤ N) (hf : IsFoldSeq N a) : des a < N := by
  have hlen := length_of_foldSeq hf
  unfold des desBefore
  have := List.countP_le_length (p := descentAt a) (l := List.range (a.length - 1))
  simp only [List.length_range] at this
  omega

/-- Coefficient of `q^k` in the descent polynomial `Σ_{a ∈ V_N} q^{des a}`. -/
def desCount (N k : ℕ) : ℕ := ((semiSeqs N).filter (fun a => des a = k)).card

/-- The descent polynomial of `V_N` as a coefficient list (degrees `0, …, N - 1`). -/
def desPolyList (N : ℕ) : List ℕ := (List.range N).map (desCount N)

/-- **The descent polynomial of `V_N` is palindromic.** -/
theorem desCount_symm {N k : ℕ} (hk : k ≤ N - 1) : desCount N (N - 1 - k) = desCount N k := by
  unfold desCount
  refine Finset.card_nbij' (mirror N) (mirror N) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    have := des_mirror (mem_semiSeqs.1 ha.1).1
    exact ⟨mirror_mem_semiSeqs ha.1, by omega⟩
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    have := des_mirror (mem_semiSeqs.1 ha.1).1
    exact ⟨mirror_mem_semiSeqs ha.1, by omega⟩
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha
    exact mirror_mirror (mem_semiSeqs.1 ha.1).1
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha
    exact mirror_mirror (mem_semiSeqs.1 ha.1).1

/-- The coefficients of the descent polynomial sum to `a(N)`. -/
theorem sum_desCount {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range N, desCount N k = semiCount N := by
  unfold desCount semiCount
  rw [Finset.card_eq_sum_card_fiberwise (f := des) (t := Finset.range N)]
  intro a ha
  rw [Finset.mem_coe, Finset.mem_range]
  exact des_lt hN (mem_semiSeqs.1 ha).1

theorem log_add_two_lt {n : ℕ} (hn : 5 ≤ n) : Nat.log 2 n + 2 < n := by
  have h : n < 2 ^ (n - 2) := by
    induction n, hn using Nat.le_induction with
    | base => decide
    | succ n hn ih =>
      have e : n + 1 - 2 = (n - 2) + 1 := by omega
      rw [e, pow_succ]
      omega
  have := Nat.log_lt_of_lt_pow (b := 2) (by omega : n ≠ 0) h
  omega

/-- A kernel-computable enumeration of `V_N` (`List.permutations'` is structurally
recursive, unlike `List.permutations`). -/
def semiList (N : ℕ) : List (List ℕ) :=
  (List.range' 1 N).permutations'.filter (fun a => decide (SemiSymmetric N a))

theorem mem_semiList {N : ℕ} {a : List ℕ} : a ∈ semiList N ↔ a ∈ semiSeqs N := by
  rw [mem_semiSeqs]
  simp [semiList, List.mem_permutations', IsFoldSeq]

/-- Counting in `V_N` through the computable enumeration. -/
theorem card_filter_semiSeqs (N : ℕ) (p : List ℕ → Prop) [DecidablePred p]
    (hnd : (semiList N).Nodup) :
    ((semiSeqs N).filter p).card = ((semiList N).filter (fun a => decide (p a))).length := by
  have e : (semiSeqs N).filter p = ((semiList N).filter (fun a => decide (p a))).toFinset := by
    ext a
    simp [mem_semiList]
  rw [e, List.toFinset_card_of_nodup (hnd.filter _)]

theorem one_le_des_three : ∀ a ∈ semiSeqs 3, 1 ≤ des a := by
  have h : ∀ a ∈ semiList 3, 1 ≤ des a := by decide +kernel
  exact fun a ha => h a (mem_semiList.2 ha)

/-- Every semi-symmetric fold sequence of length `N ≥ 3` has a descent
(from `descents_bound`; `N = 3` by enumeration). -/
theorem one_le_des {N : ℕ} {a : List ℕ} (hN : 3 ≤ N) (ha : a ∈ semiSeqs N) : 1 ≤ des a := by
  rcases Nat.eq_or_lt_of_le hN with h3 | h4
  · subst h3; exact one_le_des_three a ha
  · obtain ⟨hf, hs⟩ := mem_semiSeqs.1 ha
    have hb := descents_bound hf hs
    by_contra h
    have h0 : des a = 0 := by omega
    rw [h0, zero_add, pow_one] at hb
    have := log_add_two_lt (n := N + 1) (by omega)
    omega

/-- The constant coefficient of the descent polynomial vanishes for `N ≥ 3`. -/
theorem desCount_zero {N : ℕ} (hN : 3 ≤ N) : desCount N 0 = 0 := by
  unfold desCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a ha h
  have := one_le_des hN ha
  omega

/-- The top coefficient (`q^{N-1}`) of the descent polynomial vanishes for `N ≥ 3`. -/
theorem desCount_top {N : ℕ} (hN : 3 ≤ N) : desCount N (N - 1) = 0 := by
  have h := desCount_symm (N := N) (k := 0) (by omega)
  rw [Nat.sub_zero] at h
  rw [h]
  exact desCount_zero hN

/-! ## Descents of the time word (inverse descents) -/

/-- Number of descents of the time word `t` (`t_m = a.idxOf m`): the number of `m` such
that panel `m + 1` is placed before panel `m`. -/
def ides (a : List ℕ) : ℕ :=
  (List.range' 1 (a.length - 1)).countP (fun m => decide (a.idxOf (m + 1) < a.idxOf m))

theorem idxOf_reverse {a : List ℕ} (hnd : a.Nodup) {x : ℕ} (hx : x ∈ a) :
    a.reverse.idxOf x + a.idxOf x + 1 = a.length := by
  have hi := List.idxOf_lt_length_of_mem hx
  have hj : a.length - 1 - a.idxOf x < a.reverse.length := by
    rw [List.length_reverse]; omega
  have e : a.reverse[a.length - 1 - a.idxOf x] = x := by
    rw [List.getElem_reverse]
    have h3 : a.length - 1 - (a.length - 1 - a.idxOf x) = a.idxOf x := by omega
    simp only [h3]
    exact List.getElem_idxOf hi
  have key := List.Nodup.idxOf_getElem (List.nodup_reverse.2 hnd) (a.length - 1 - a.idxOf x) hj
  rw [e] at key
  omega

/-- Reversal of the fold sequence complements the time word, so it exchanges its descents
and ascents. -/
theorem ides_reverse {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a) :
    ides a.reverse + ides a = N - 1 := by
  have hlen := length_of_foldSeq hf
  have hnd := nodup_of_foldSeq hf
  unfold ides
  rw [List.length_reverse]
  have e : (List.range' 1 (a.length - 1)).countP
        (fun m => decide (a.reverse.idxOf (m + 1) < a.reverse.idxOf m)) =
      (List.range' 1 (a.length - 1)).countP
        (fun m => decide (¬ decide (a.idxOf (m + 1) < a.idxOf m) = true)) := by
    apply List.countP_congr
    intro m hm
    rw [List.mem_range'_1] at hm
    have m1 : m ∈ a := (mem_range'_of_perm hf).2 ⟨by omega, by omega⟩
    have m2 : m + 1 ∈ a := (mem_range'_of_perm hf).2 ⟨by omega, by omega⟩
    have r1 := idxOf_reverse hnd m1
    have r2 := idxOf_reverse hnd m2
    have hne : a.idxOf (m + 1) ≠ a.idxOf m := fun e => by
      have := (List.idxOf_inj m2).1 e
      omega
    simp only [decide_eq_true_eq]
    omega
  rw [e]
  have key := List.length_eq_countP_add_countP
    (fun m => decide (a.idxOf (m + 1) < a.idxOf m)) (l := List.range' 1 (a.length - 1))
  simp only [List.length_range'] at key
  omega

/-- Coefficient of `q^k` in the inverse-descent polynomial `Σ_{a ∈ V_N} q^{ides a}`. -/
def idesCount (N k : ℕ) : ℕ := ((semiSeqs N).filter (fun a => ides a = k)).card

/-- The inverse-descent polynomial of `V_N` as a coefficient list. -/
def idesPolyList (N : ℕ) : List ℕ := (List.range N).map (idesCount N)

/-- **The inverse-descent polynomial of `V_N` is palindromic.** -/
theorem idesCount_symm {N k : ℕ} (hk : k ≤ N - 1) :
    idesCount N (N - 1 - k) = idesCount N k := by
  unfold idesCount
  refine Finset.card_nbij' List.reverse List.reverse ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    have := ides_reverse (mem_semiSeqs.1 ha.1).1
    exact ⟨reverse_mem_semiSeqs ha.1, by omega⟩
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    have := ides_reverse (mem_semiSeqs.1 ha.1).1
    exact ⟨reverse_mem_semiSeqs ha.1, by omega⟩
  · intro a _; simp
  · intro a _; simp

/-- Panel `2` is placed before both of its neighbours or after both: the time word has a
peak or a valley at `2`. -/
theorem ides_two {N : ℕ} {a : List ℕ} (hN : 3 ≤ N) (ha : a ∈ semiSeqs N) :
    a.idxOf 1 < a.idxOf 2 ↔ a.idxOf 3 < a.idxOf 2 := by
  obtain ⟨hf, hs⟩ := mem_semiSeqs.1 ha
  have hb := timeBalanced_of_semiSymmetric hf hs 2 (by omega) (by omega)
  have hr : reach N 2 = 1 := by unfold reach; omega
  have hl : List.range' 1 1 = [1] := rfl
  have e1 : (2 : ℕ) - 1 = 1 := rfl
  have e3 : (2 : ℕ) + 1 = 3 := rfl
  rw [hr, hl] at hb
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq, e1, e3] at hb
  constructor
  · intro h
    by_contra h'
    simp only [h, h', ite_true, ite_false] at hb
    omega
  · intro h
    by_contra h'
    simp only [h, h', ite_true, ite_false] at hb
    omega

/-- The time word of a semi-symmetric sequence of length `N ≥ 3` has a descent. -/
theorem one_le_ides {N : ℕ} {a : List ℕ} (hN : 3 ≤ N) (ha : a ∈ semiSeqs N) : 1 ≤ ides a := by
  obtain ⟨hf, hs⟩ := mem_semiSeqs.1 ha
  have hlen := length_of_foldSeq hf
  have h2 := ides_two hN ha
  have m2 : 2 ∈ a := (mem_range'_of_perm hf).2 ⟨by omega, by omega⟩
  have hne : a.idxOf 2 ≠ a.idxOf 1 := fun e => by
    have := (List.idxOf_inj m2).1 e
    omega
  unfold ides
  rw [List.one_le_countP_iff]
  by_cases h : a.idxOf 1 < a.idxOf 2
  · refine ⟨2, by rw [List.mem_range'_1]; omega, ?_⟩
    have := h2.1 h
    simpa using this
  · refine ⟨1, by rw [List.mem_range'_1]; omega, ?_⟩
    have : a.idxOf 2 < a.idxOf 1 := by omega
    simpa using this

theorem idesCount_zero {N : ℕ} (hN : 3 ≤ N) : idesCount N 0 = 0 := by
  unfold idesCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a ha h
  have := one_le_ides hN ha
  omega

theorem idesCount_top {N : ℕ} (hN : 3 ≤ N) : idesCount N (N - 1) = 0 := by
  have h := idesCount_symm (N := N) (k := 0) (by omega)
  rw [Nat.sub_zero] at h
  rw [h]
  exact idesCount_zero hN

/-! ## Small cases (kernel computation) -/

theorem nodup_semiList_four : (semiList 4).Nodup := by decide +kernel

theorem nodup_semiList_five : (semiList 5).Nodup := by decide +kernel

theorem desPolyList_four : desPolyList 4 = [0, 5, 5, 0] := by
  have h : desPolyList 4 = (List.range 4).map
      (fun k => ((semiList 4).filter (fun a => decide (des a = k))).length) :=
    List.map_congr_left (fun k _ => card_filter_semiSeqs 4 _ nodup_semiList_four)
  rw [h]; decide +kernel

theorem desPolyList_five : desPolyList 5 = [0, 2, 24, 2, 0] := by
  have h : desPolyList 5 = (List.range 5).map
      (fun k => ((semiList 5).filter (fun a => decide (des a = k))).length) :=
    List.map_congr_left (fun k _ => card_filter_semiSeqs 5 _ nodup_semiList_five)
  rw [h]; decide +kernel

theorem idesPolyList_four : idesPolyList 4 = [0, 5, 5, 0] := by
  have h : idesPolyList 4 = (List.range 4).map
      (fun k => ((semiList 4).filter (fun a => decide (ides a = k))).length) :=
    List.map_congr_left (fun k _ => card_filter_semiSeqs 4 _ nodup_semiList_four)
  rw [h]; decide +kernel

theorem idesPolyList_five : idesPolyList 5 = [0, 0, 28, 0, 0] := by
  have h : idesPolyList 5 = (List.range 5).map
      (fun k => ((semiList 5).filter (fun a => decide (ides a = k))).length) :=
    List.map_congr_left (fun k _ => card_filter_semiSeqs 5 _ nodup_semiList_five)
  rw [h]; decide +kernel

/-! ## The quasisymmetric generating function is not symmetric -/

/-- The descent set of `a`, as the list of 0-based positions `i` with `a[i] > a[i+1]`. -/
def desSet (a : List ℕ) : List ℕ := (List.range (a.length - 1)).filter (descentAt a)

theorem des_eq_length_desSet (a : List ℕ) : des a = (desSet a).length := by
  unfold des desBefore desSet
  rw [List.countP_eq_length_filter]

/-- The descent set of the time word: the `m` with panel `m + 1` placed before panel `m`. -/
def idesSet (a : List ℕ) : List ℕ :=
  (List.range' 1 (a.length - 1)).filter (fun m => decide (a.idxOf (m + 1) < a.idxOf m))

theorem ides_eq_length_idesSet (a : List ℕ) : ides a = (idesSet a).length := by
  unfold ides idesSet
  rw [List.countP_eq_length_filter]

/-- Number of `a ∈ V_N` with descent set contained in `D`: the coefficient of the monomial
quasisymmetric function indexed by `D` in `Σ_{a ∈ V_N} F_{Des a}`. -/
def subDesCount (N : ℕ) (D : List ℕ) : ℕ :=
  ((semiSeqs N).filter (fun a => ∀ i ∈ desSet a, i ∈ D)).card

/-- The same for the time word. -/
def subIdesCount (N : ℕ) (D : List ℕ) : ℕ :=
  ((semiSeqs N).filter (fun a => ∀ i ∈ idesSet a, i ∈ D)).card

/-- `Q_5 = Σ_{a ∈ V_5} F_{Des a}` is not symmetric: the compositions `(1,3,1)` (descent
positions `{1,4}`, 0-based `[0,3]`) and `(1,1,3)` (positions `{1,2}`, 0-based `[0,1]`) are
rearrangements of each other but have different monomial coefficients. -/
theorem subDesCount_five : subDesCount 5 [0, 3] = 6 ∧ subDesCount 5 [0, 1] = 1 := by
  unfold subDesCount
  rw [card_filter_semiSeqs 5 _ nodup_semiList_five, card_filter_semiSeqs 5 _ nodup_semiList_five]
  decide +kernel

/-- The quasisymmetric function of the time words of `V_5` is not symmetric either. -/
theorem subIdesCount_five : subIdesCount 5 [1, 4] = 4 ∧ subIdesCount 5 [1, 2] = 0 := by
  unfold subIdesCount
  rw [card_filter_semiSeqs 5 _ nodup_semiList_five, card_filter_semiSeqs 5 _ nodup_semiList_five]
  decide +kernel

end XdSymFun
end Folds
