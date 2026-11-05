import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Folds.Cyclic

/-!
# The imbalance field and its dipole update

For a list `S` of already-bisected panels and a panel `m`, the *imbalance*
`imb N S m = rightCount N S m - leftCount N S m` (an integer) vanishes exactly when the
step `(S, m)` is semi-symmetric (`semiStep_iff_imb`).  This is the field `J` used in the
asymptotic analysis (`experiments/asymptotics/NOTES.txt`): the valid next panels are
the free zeros of `J`.

Main result (`imb_cons`, the *dipole lemma*): adding a new panel `x` (not in `S`, with
`S` duplicate-free) changes the imbalance at every panel `m ≠ x` of the strip by
  `+1` if `m < x ≤ 2m - 1`        (`x` lies in the right arm of `m`),
  `-1` if `2m - N ≤ x < m`        (`x` lies in the left arm of `m`),
   `0` otherwise.
So `x` acts on the field as a dipole: `+1` on the panels `⌈(x+1)/2⌉ … x-1`, `-1` on the
panels `x+1 … ⌊(N+x)/2⌋`.  The supports have `⌊(x-1)/2⌋` and `⌊(N-x)/2⌋` panels
(`card_plus_support`, `card_minus_support`), so every panel touches about half of the strip.
A panel `m` whose window does not contain `x` keeps its imbalance (`imb_cons_of_not_mem_window`).

Second result (`dyadic_defect`, `semiStep_iff_dyadic`): for `N = 2^L` the cyclic defect
`P̃(2m-1) - 2P(m-1)` is a sum over the one-bits `j` of `x = m - 1` of the doubling-balance
terms `#(image of I_j under doubling) - 2·#I_j` of the dyadic intervals `I_j` along the binary
expansion of `x`, plus `[2x mod N + 1 ∈ S]` (see the section below).

Third result (`half_balance`): for `N = 2h`, if the antipodal panels `m` and `m + h` are both
valid, exactly half of `S` lies in `[m, m + h - 1]` (the parity lemma is the case `|S|` odd).
-/

namespace Folds

/-- The imbalance of panel `m`: right-arm count minus left-arm count. -/
def imb (N : Nat) (S : List Nat) (m : Nat) : Int :=
  (rightCount N S m : Int) - (leftCount N S m : Int)

theorem semiStep_iff_imb (N : Nat) (S : List Nat) (m : Nat) :
    SemiStep N S m ↔ imb N S m = 0 := by
  unfold SemiStep imb; omega

/-- `x` lies in the right arm of `m`. -/
theorem inRight_iff {N m x : Nat} (hx : x ≤ N) :
    (m < x ∧ x ≤ m + reach N m) ↔ (m < x ∧ x + 1 ≤ 2 * m) := by
  unfold reach
  constructor
  · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rcases Nat.le_total (m - 1) (N - m) with h | h
    · rw [Nat.min_eq_left h] at h2; omega
    · rw [Nat.min_eq_right h] at h2; omega
  · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rcases Nat.le_total (m - 1) (N - m) with h | h
    · rw [Nat.min_eq_left h]; omega
    · rw [Nat.min_eq_right h]; omega

/-- `x` lies in the left arm of `m`. -/
theorem inLeft_iff {N m x : Nat} (hx : 1 ≤ x) (hm : 1 ≤ m) (hmN : m ≤ N) :
    (m - reach N m ≤ x ∧ x < m) ↔ (x < m ∧ 2 * m ≤ N + x) := by
  unfold reach
  constructor
  · rintro ⟨h1, h2⟩; refine ⟨h2, ?_⟩; rcases Nat.le_total (m - 1) (N - m) with h | h
    · rw [Nat.min_eq_left h] at h1; omega
    · rw [Nat.min_eq_right h] at h1; omega
  · rintro ⟨h1, h2⟩; refine ⟨?_, h1⟩; rcases Nat.le_total (m - 1) (N - m) with h | h
    · rw [Nat.min_eq_left h]; omega
    · rw [Nat.min_eq_right h]; omega

theorem leftCount_cons {N m x : Nat} {S : List Nat} (hnd : S.Nodup) (hx : x ∉ S) :
    leftCount N (x :: S) m =
      leftCount N S m + (if m - reach N m ≤ x ∧ x < m then 1 else 0) := by
  have hnd' : (x :: S).Nodup := List.nodup_cons.2 ⟨hx, hnd⟩
  rw [leftCount_eq hnd', leftCount_eq hnd, List.countP_cons]
  by_cases h : m - reach N m ≤ x ∧ x < m <;> simp [h]

theorem rightCount_cons {N m x : Nat} {S : List Nat} (hnd : S.Nodup) (hx : x ∉ S) :
    rightCount N (x :: S) m =
      rightCount N S m + (if m < x ∧ x ≤ m + reach N m then 1 else 0) := by
  have hnd' : (x :: S).Nodup := List.nodup_cons.2 ⟨hx, hnd⟩
  rw [rightCount_eq hnd', rightCount_eq hnd, List.countP_cons]
  by_cases h : m < x ∧ x ≤ m + reach N m <;> simp [h]

/-- **Dipole lemma.** Adding panel `x` changes the imbalance of panel `m` by `+1` if `x`
is in the right arm of `m` (`m < x ≤ 2m - 1`), by `-1` if `x` is in the left arm
(`2m - N ≤ x < m`), and leaves it unchanged otherwise. -/
theorem imb_cons {N m x : Nat} {S : List Nat} (hnd : S.Nodup) (hx : x ∉ S)
    (hx1 : 1 ≤ x) (hm : 1 ≤ m) (hmN : m ≤ N) (hxN : x ≤ N) :
    imb N (x :: S) m = imb N S m
      + (if m < x ∧ x + 1 ≤ 2 * m then 1 else 0)
      - (if x < m ∧ 2 * m ≤ N + x then 1 else 0) := by
  unfold imb
  rw [leftCount_cons hnd hx, rightCount_cons hnd hx]
  simp only [inRight_iff (N := N) (m := m) hxN, inLeft_iff (N := N) (x := x) hx1 hm hmN]
  split_ifs <;> push_cast <;> omega

/-- A panel whose window does not contain `x` is unaffected by adding `x`. -/
theorem imb_cons_of_not_mem_window {N m x : Nat} {S : List Nat} (hnd : S.Nodup)
    (hx : x ∉ S) (hx1 : 1 ≤ x) (hm : 1 ≤ m) (hmN : m ≤ N) (hxN : x ≤ N)
    (hw : ¬ (m < x ∧ x + 1 ≤ 2 * m)) (hw' : ¬ (x < m ∧ 2 * m ≤ N + x)) :
    imb N (x :: S) m = imb N S m := by
  rw [imb_cons hnd hx hx1 hm hmN hxN]; simp [hw, hw']

/-- Validity of `m` is unaffected by adding `x` outside its window. -/
theorem semiStep_cons_iff {N m x : Nat} {S : List Nat} (hnd : S.Nodup)
    (hx : x ∉ S) (hx1 : 1 ≤ x) (hm : 1 ≤ m) (hmN : m ≤ N) (hxN : x ≤ N)
    (hw : ¬ (m < x ∧ x + 1 ≤ 2 * m)) (hw' : ¬ (x < m ∧ 2 * m ≤ N + x)) :
    SemiStep N (x :: S) m ↔ SemiStep N S m := by
  rw [semiStep_iff_imb, semiStep_iff_imb, imb_cons_of_not_mem_window hnd hx hx1 hm hmN hxN hw hw']

/-- The `+1` support of the dipole of `x`: panels `m` with `m < x ≤ 2m - 1`.  It is the
interval `[x/2 + 1, x - 1]` and has `(x - 1) / 2` elements. -/
theorem plus_support_eq (x : Nat) :
    (Finset.Icc 1 x).filter (fun m => m < x ∧ x + 1 ≤ 2 * m) = Finset.Icc (x / 2 + 1) (x - 1) := by
  ext m; simp only [Finset.mem_filter, Finset.mem_Icc]; omega

theorem card_plus_support (x : Nat) :
    ((Finset.Icc 1 x).filter (fun m => m < x ∧ x + 1 ≤ 2 * m)).card = (x - 1) / 2 := by
  rw [plus_support_eq, Nat.card_Icc]; omega

/-- The `-1` support of the dipole of `x`: panels `m` with `x < m`, `2m ≤ N + x`.  It is the
interval `[x + 1, (N + x)/2]` and has `(N - x) / 2` elements (for `x ≤ N`). -/
theorem minus_support_eq (N x : Nat) :
    (Finset.Icc 1 N).filter (fun m => x < m ∧ 2 * m ≤ N + x) = Finset.Icc (x + 1) ((N + x) / 2) := by
  ext m; simp only [Finset.mem_filter, Finset.mem_Icc]; omega

theorem card_minus_support {N x : Nat} (hx : x ≤ N) :
    ((Finset.Icc 1 N).filter (fun m => x < m ∧ 2 * m ≤ N + x)).card = (N - x) / 2 := by
  rw [minus_support_eq, Nat.card_Icc]; omega

/-! ## Binary-digit (dyadic) decomposition of the doubling defect

`cnt A a l` counts the positions `a, a+1, …, a+l-1` in `A`.  For any two sets `A, B ⊆ ℕ`
and any `x < 2^L`,
  `#A∩[0, 2x+1) - 2·#B∩[0, x) = Σ_{j<L, bit j of x = 1} (#A∩2I_j - 2·#B∩I_j) + [2x ∈ A]`,
where `I_j = [h_j, h_j + 2^j)` with `h_j = ⌊x / 2^(j+1)⌋·2^(j+1)` (the dyadic interval of
length `2^j` just below the `j`-th one-bit of `x`) and `2I_j = [2h_j, 2h_j + 2^(j+1))` its image
under doubling (`dyadic_defect`).  With `N = 2^L`, `B = S - 1` and `A` the periodic
extension of `B`, the left side is `P̃(2m-1) - 2P(m-1)` (`x = m - 1`), whose vanishing is the
cyclic form of a semi-symmetric step (`semiStep_iff_cyclicStep`), and `#A∩2I_j` is the count
in the image of `I_j` under the doubling map `y ↦ 2y mod N`: the validity defect is a sum of
one "doubling balance" term per scale along the binary digits of the panel.
-/

/-- Number of `y ∈ [a, a + l)` with `A y`. -/
def cnt (A : Nat → Bool) (a l : Nat) : Nat := (List.range' a l).countP A

theorem cnt_add (A : Nat → Bool) (a l₁ l₂ : Nat) :
    cnt A a (l₁ + l₂) = cnt A a l₁ + cnt A (a + l₁) l₂ := by
  unfold cnt; rw [← List.range'_append_1, List.countP_append]

theorem cnt_shift (A : Nat → Bool) (a c l : Nat) :
    cnt A (c + a) l = cnt (fun y => A (c + y)) a l := by
  unfold cnt; rw [← List.map_add_range', List.countP_map]; rfl

theorem cnt_one (A : Nat → Bool) (a : Nat) : cnt A a 1 = if A a then 1 else 0 := by
  unfold cnt; simp [List.range']

/-- The term of scale `j` in the dyadic decomposition. -/
def dyTerm (A B : Nat → Bool) (x j : Nat) : Int :=
  if x / 2 ^ j % 2 = 1 then
    (cnt A (2 * (x / 2 ^ (j + 1) * 2 ^ (j + 1))) (2 ^ (j + 1)) : Int)
      - 2 * (cnt B (x / 2 ^ (j + 1) * 2 ^ (j + 1)) (2 ^ j) : Int)
  else 0

theorem bit_add_high {L j x : Nat} (hj : j < L) :
    (2 ^ L + x) / 2 ^ j % 2 = x / 2 ^ j % 2 := by
  have h : 2 ^ L = 2 ^ j * (2 * 2 ^ (L - j - 1)) := by
    rw [← Nat.pow_succ', ← Nat.pow_add]; congr 1; omega
  rw [h, Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  omega

theorem high_add_high {L j x : Nat} (hj : j < L) :
    (2 ^ L + x) / 2 ^ (j + 1) * 2 ^ (j + 1) = 2 ^ L + x / 2 ^ (j + 1) * 2 ^ (j + 1) := by
  have h : 2 ^ L = 2 ^ (j + 1) * 2 ^ (L - j - 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [h, Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  rw [Nat.add_mul, Nat.add_comm, Nat.mul_comm (2 ^ (L - j - 1))]

theorem dyTerm_add_high (A B : Nat → Bool) {L j x : Nat} (hj : j < L) :
    dyTerm A B (2 ^ L + x) j =
      dyTerm (fun y => A (2 ^ (L + 1) + y)) (fun y => B (2 ^ L + y)) x j := by
  unfold dyTerm
  rw [bit_add_high hj, high_add_high hj]
  have e : 2 * (2 ^ L + x / 2 ^ (j + 1) * 2 ^ (j + 1))
      = 2 ^ (L + 1) + 2 * (x / 2 ^ (j + 1) * 2 ^ (j + 1)) := by rw [Nat.pow_succ]; ring
  rw [e, cnt_shift, cnt_shift]

/-- **Dyadic decomposition of the doubling defect.** -/
theorem dyadic_defect (L : Nat) : ∀ (A B : Nat → Bool) (x : Nat), x < 2 ^ L →
    (cnt A 0 (2 * x + 1) : Int) - 2 * (cnt B 0 x : Int)
      = (∑ j ∈ Finset.range L, dyTerm A B x j) + (if A (2 * x) then 1 else 0) := by
  induction L with
  | zero =>
    intro A B x hx
    have : x = 0 := by simpa using hx
    subst this; simp [cnt]
  | succ L ih =>
    intro A B x hx
    rw [Finset.sum_range_succ]
    by_cases hlo : x < 2 ^ L
    · -- top bit 0: the new term vanishes
      have hb : x / 2 ^ L % 2 = 0 := by rw [Nat.div_eq_of_lt hlo]
      have ht : dyTerm A B x L = 0 := by unfold dyTerm; rw [hb]; simp
      rw [ht, ih A B x hlo]; ring
    · -- top bit 1: x = 2^L + x'
      obtain ⟨x', rfl⟩ : ∃ x', x = 2 ^ L + x' := ⟨x - 2 ^ L, by omega⟩
      have hx' : x' < 2 ^ L := by rw [Nat.pow_succ] at hx; omega
      have hsum : ∑ j ∈ Finset.range L, dyTerm A B (2 ^ L + x') j
          = ∑ j ∈ Finset.range L,
              dyTerm (fun y => A (2 ^ (L + 1) + y)) (fun y => B (2 ^ L + y)) x' j := by
        apply Finset.sum_congr rfl
        intro j hj; exact dyTerm_add_high A B (Finset.mem_range.1 hj)
      have hq : (2 ^ L + x') / 2 ^ L = 1 := by
        rw [Nat.add_comm, Nat.add_div_right _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt hx']
      have hq2 : (2 ^ L + x') / 2 ^ (L + 1) = 0 := by
        apply Nat.div_eq_of_lt; rw [Nat.pow_succ]; omega
      have ht : dyTerm A B (2 ^ L + x') L
          = (cnt A 0 (2 ^ (L + 1)) : Int) - 2 * (cnt B 0 (2 ^ L) : Int) := by
        unfold dyTerm; rw [hq, hq2]; simp
      rw [hsum, ht]
      have h := ih (fun y => A (2 ^ (L + 1) + y)) (fun y => B (2 ^ L + y)) x' hx'
      beta_reduce at h
      have e1 : 2 * (2 ^ L + x') + 1 = 2 ^ (L + 1) + (2 * x' + 1) := by rw [Nat.pow_succ]; ring
      have e2 : 2 * (2 ^ L + x') = 2 ^ (L + 1) + 2 * x' := by rw [Nat.pow_succ]; ring
      have c1 : cnt A 0 (2 ^ (L + 1) + (2 * x' + 1))
          = cnt A 0 (2 ^ (L + 1)) + cnt (fun y => A (2 ^ (L + 1) + y)) 0 (2 * x' + 1) := by
        rw [cnt_add, Nat.zero_add, ← cnt_shift]; simp only [Nat.add_zero]
      have c2 : cnt B 0 (2 ^ L + x')
          = cnt B 0 (2 ^ L) + cnt (fun y => B (2 ^ L + y)) 0 x' := by
        rw [cnt_add, Nat.zero_add, ← cnt_shift]; simp only [Nat.add_zero]
      rw [e1, e2, c1, c2]
      push_cast; linarith

/-! ### Application to fold sequences (`N = 2^L`) -/

theorem cnt_succ (A : Nat → Bool) (a l : Nat) :
    cnt A a (l + 1) = cnt A a l + (if A (a + l) then 1 else 0) := by
  rw [cnt_add, cnt_one]

theorem below_succ {S : List Nat} (hnd : S.Nodup) (j : Nat) :
    below S (j + 1) = below S j + (if j + 1 ∈ S then 1 else 0) := by
  rw [below_split S (Nat.le_succ j), ← countP_eq_nodup hnd]
  congr 1; apply List.countP_congr; intro x _; simp; omega

/-- `P(j)` as a count of positions: `below S j = #{y < j : y + 1 ∈ S}`. -/
theorem below_eq_cnt {S : List Nat} (hnd : S.Nodup) (hpos : ∀ x ∈ S, 1 ≤ x) (j : Nat) :
    below S j = cnt (fun y => decide (y + 1 ∈ S)) 0 j := by
  induction j with
  | zero => rw [below_zero hpos]; rfl
  | succ j ih => rw [below_succ hnd, cnt_succ, ih, Nat.zero_add]; simp

/-- `P̃(j)` as a count of positions of the periodic extension of `S - 1`. -/
theorem cycBelow_eq_cnt {N : Nat} {S : List Nat} (hnd : S.Nodup)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (hN : 0 < N) (j : Nat) :
    cycBelow N S j = cnt (fun y => decide (y % N + 1 ∈ S)) 0 j := by
  have hpos : ∀ x ∈ S, 1 ≤ x := fun x hx => (hS x hx).1
  induction j with
  | zero => unfold cycBelow; simp [below_zero hpos]; rfl
  | succ j ih =>
    rw [cnt_succ, ← ih, Nat.zero_add]
    unfold cycBelow
    by_cases h : (j + 1) % N = 0
    · have hj : j % N = N - 1 := by
        have := Nat.mod_add_mod j N 1
        rw [h] at this
        have hlt := Nat.mod_lt j hN
        rcases Nat.lt_or_ge (j % N + 1) N with h2 | h2
        · rw [Nat.mod_eq_of_lt h2] at this; omega
        · omega
      have hd : (j + 1) / N = j / N + 1 := by
        have e1 := Nat.div_add_mod (j + 1) N
        have e2 := Nat.div_add_mod j N
        rw [h] at e1
        have : N * ((j + 1) / N) = N * (j / N + 1) := by rw [Nat.mul_add]; omega
        exact Nat.eq_of_mul_eq_mul_left hN this
      rw [h, hd, hj, below_zero hpos]
      have hlen := below_eq_length (S := S) (N := N) (fun x hx => (hS x hx).2)
      have hsplit := below_succ hnd (N - 1)
      rw [show N - 1 + 1 = N by omega, hlen] at hsplit
      rw [show N - 1 + 1 = N by omega]
      simp only [Nat.zero_add, Nat.add_mul, Nat.one_mul, decide_eq_true_eq]
      generalize j / N * S.length = q
      split_ifs at hsplit ⊢ <;> omega
    · have hm : (j + 1) % N = j % N + 1 := by
        have := Nat.mod_add_mod j N 1
        have hlt := Nat.mod_lt j hN
        rcases Nat.lt_or_ge (j % N + 1) N with h2 | h2
        · rw [Nat.mod_eq_of_lt h2] at this; omega
        · have : j % N + 1 = N := by omega
          have h3 : (j + 1) % N = 0 := by
            rw [← Nat.mod_add_mod, this, Nat.mod_self]
          exact absurd h3 h
      have hd : (j + 1) / N = j / N := by
        have e1 := Nat.div_add_mod (j + 1) N
        have e2 := Nat.div_add_mod j N
        rw [hm] at e1
        have : N * ((j + 1) / N) = N * (j / N) := by omega
        exact Nat.eq_of_mul_eq_mul_left hN this
      rw [hm, hd, below_succ hnd]
      split_ifs <;> simp_all <;> omega

/-- **Dyadic form of a semi-symmetric step** for `N = 2^L`.  With `x = m - 1`,
`B y = [y + 1 ∈ S]` and `A y = [y mod N + 1 ∈ S]`, the step `(S, m)` is semi-symmetric iff
`Σ_{j<L} dyTerm A B x j + [A (2x)] = 0`: one doubling-balance term per binary digit of `x`. -/
theorem semiStep_iff_dyadic {L N m : Nat} {S : List Nat} (hNL : N = 2 ^ L) (hnd : S.Nodup)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (hm1 : 1 ≤ m) (hmN : m ≤ N) (hmS : m ∉ S) :
    SemiStep N S m ↔
      (∑ j ∈ Finset.range L,
          dyTerm (fun y => decide (y % N + 1 ∈ S)) (fun y => decide (y + 1 ∈ S)) (m - 1) j)
        + (if decide ((2 * (m - 1)) % N + 1 ∈ S) then 1 else 0) = 0 := by
  have hN : 0 < N := by omega
  have hpos : ∀ x ∈ S, 1 ≤ x := fun x hx => (hS x hx).1
  rw [semiStep_iff_cyclicStep hnd hS hm1 hmN hmS]
  unfold CyclicStep
  have hx : m - 1 < 2 ^ L := by omega
  have key := dyadic_defect L (fun y => decide (y % N + 1 ∈ S)) (fun y => decide (y + 1 ∈ S))
    (m - 1) hx
  have e : 2 * (m - 1) + 1 = 2 * m - 1 := by omega
  rw [e, ← cycBelow_eq_cnt hnd hS hN, ← below_eq_cnt hnd hpos] at key
  rw [← key]
  constructor
  · intro h; rw [h]; push_cast; ring
  · intro h; have : ((cycBelow N S (2 * m - 1) : Nat) : Int) = 2 * (below S (m - 1) : Int) := by
      linarith
    exact_mod_cast this

/-! ## Antipodal pairs: the top-scale balance

For `N = 2h` the panels `m` and `m + h` have doubled positions `2m - 1` and `2m - 1 + N`, which
coincide on the circle, so their cyclic conditions differ only by the count of `S` in the half
circle `[m, m + h - 1]`.  If both are valid, that half circle holds exactly half of `S`
(`half_balance`).  For `|S|` odd this is the parity lemma `not_both_valid` of `Growth.lean`;
in general it gives `V(S) ≤ h + #{m ≤ h : the half circle [m, m+h-1] holds |S|/2 points}`. -/

theorem cycBelow_add_N {N : Nat} (S : List Nat) (hN : 0 < N) (j : Nat) :
    cycBelow N S (j + N) = cycBelow N S j + S.length := by
  unfold cycBelow
  rw [Nat.add_mod_right, Nat.add_div_right _ hN, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

/-- **Half-circle balance.**  For `N = 2h`, if `m` and `m + h` (`1 ≤ m ≤ h`) are both valid
next panels, then exactly half of `S` lies in `[m, m + h - 1]`. -/
theorem half_balance {h m : Nat} {S : List Nat} (hnd : S.Nodup)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ 2 * h) (hm1 : 1 ≤ m) (hmh : m ≤ h)
    (h1 : m ∉ S ∧ SemiStep (2 * h) S m) (h2 : m + h ∉ S ∧ SemiStep (2 * h) S (m + h)) :
    S.length = 2 * (below S (m - 1 + h) - below S (m - 1)) := by
  have c1 := (semiStep_iff_cyclicStep hnd hS hm1 (by omega) h1.1).1 h1.2
  have c2 := (semiStep_iff_cyclicStep hnd hS (by omega) (by omega) h2.1).1 h2.2
  unfold CyclicStep at c1 c2
  have e : 2 * (m + h) - 1 = (2 * m - 1) + 2 * h := by omega
  have e2 : m + h - 1 = m - 1 + h := by omega
  rw [e, cycBelow_add_N S (by omega), e2] at c2
  have mono : below S (m - 1) ≤ below S (m - 1 + h) := by
    rw [below_split S (Nat.le_add_right (m - 1) h)]; omega
  omega

end Folds
