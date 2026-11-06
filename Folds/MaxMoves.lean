import Folds.PathLemma

/-!
# At most `2N/3` valid moves when `|S| ≡ 2 (mod 4)`

See `experiments/maxmoves/PROOFS.txt`.

Let `S ⊆ [1, N]` with `s = |S|`, `P(j) = #{x ∈ S | x ≤ j}` and `P̃` its quasi-periodic extension.
A free panel `m` is valid iff `P̃(2m - 1) = 2 P(m - 1)` (`semiStep_iff_cyclicStep`).

**Gap decomposition.**  Sort the panels by `k = P(m - 1) ∈ [0, s]` (the *gap* of `m`);
`W_k = {m ∈ [1, N] | P(m - 1) = k}` is an interval (`gapSet`), and `∑_k |W_k| = N`.
A valid panel of gap `k` has `P̃(2m - 1) = 2k`, so its *doubled position* lies in gap `2k`
(read cyclically: `2m ∈ W_{2k}` if `2m ≤ N`, and `2m - N ∈ W_{2k - s}` if `2m > N`).  Since the
doubled positions of distinct panels differ by at least 2, at most `(|W_j| + 1)/2` panels have
their doubled position in a given gap `j` (`two_mul_card_le`).  Hence, with `z_k` the number of
valid panels of gap `k` and `w_k = |W_k|`:

* `z_k ≤ w_k - 1` for `k < s` (the gap contains one panel of `S`);
* `2 z_k ≤ w_{2k mod s} + 1` (and `2 z_0 ≤ w_0`, `2 z_{s/2} ≤ w_s + w_0 + 2`).

**Charging.**  For `s = 2u` with `u` odd, the gaps `k` and `k + u` have the same doubled gap
`2k mod s` and opposite parities.  Bounding `3 z_k ≤ 2(w_k - 1) + z_k` for odd `k` and
`3 z_k ≤ 3 z_k` for even `k`, and then each `z_k` by the doubled gap, every gap is charged at
most `2/3` of its size (`arith_two_mod_four`):

  `card_moves_two_mod_four : |S| ≡ 2 (mod 4) → 3 · V(S) ≤ 2N`   (any `N`).

The bound is attained for every `N ≤ 24` (e.g. `S = {N/3, 2N/3}`, `V = ⌊2N/3⌋`).  For
`|S| ≡ 0 (mod 4)` it is false: `N = 60`, `S = {8, 17, 34, 35}` has `V = 41 > 40`
(`moves_sixty`), and this set is reachable.  The same charging along the doubling map gives
`(a + 2) V ≤ (a + 1) N` for `v₂(|S|) = a` (paper, PROOFS.txt).

**Tree bound.**  `semiCount_even_le_prod_two_mod_four` and
`semiCount_odd_le_prod_two_mod_four`: at a level `i ≡ 2 (mod 4)` at most `⌊2N/3⌋` panels are
valid.  Together with the parity bounds this gives
`a(N) ≤ N! · exp(-(0.1146… + o(1)) N)` for even `N` (was `0.0966`) and
`a(N) ≤ N! · exp(-(0.0769… + o(1)) N)` for odd `N` (was `0.0589`).
-/

namespace Folds

open Finset

/-! ## Arithmetic: the charging scheme -/

theorem sum_range_two_mul_add_one (u : Nat) (f : Nat → Nat) :
    ∑ k ∈ range (2 * u + 1), f k = ∑ k ∈ range u, (f k + f (k + u)) + f (2 * u) := by
  rw [Finset.sum_range_succ, two_mul, Finset.sum_range_add, Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.add_comm]

theorem sum_range_two_mul (f : Nat → Nat) :
    ∀ n, ∑ k ∈ range (2 * n), f k = ∑ k ∈ range n, (f (2 * k) + f (2 * k + 1))
  | 0 => by simp
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, sum_range_two_mul f n]
    ring

/-- **The charging inequality** (`s = 2u`, `u` odd).  `z k` is the number of valid panels of
gap `k`, `w k` the size of gap `k`. -/
theorem arith_two_mod_four (u : Nat) (hu : u % 2 = 1) (z w : Nat → Nat)
    (h0 : 2 * z 0 ≤ w 0)
    (h1 : ∀ k, 1 ≤ k → k < u → 2 * z k ≤ w (2 * k) + 1)
    (hu' : 2 * z u ≤ w (2 * u) + w 0 + 2)
    (h2 : ∀ k, u < k → k < 2 * u → 2 * z k ≤ w (2 * k - 2 * u) + 1)
    (hs : 2 * z (2 * u) ≤ w (2 * u) + 1)
    (hodd : ∀ k, k < 2 * u → k % 2 = 1 → z k + 1 ≤ w k) :
    3 * ∑ k ∈ range (2 * u + 1), z k ≤ 2 * ∑ k ∈ range (2 * u + 1), w k := by
  -- the odd member of the pair `{k, k + u}` (`u` itself for `k = 0`)
  let o : Nat → Nat := fun k => if k = 0 then u else if k % 2 = 1 then k else k + u
  have hbij : ∑ k ∈ range u, w (o k) = ∑ k ∈ range u, w (2 * k + 1) := by
    apply Finset.sum_nbij' (fun k => (o k - 1) / 2)
      (fun i => if 2 * i + 1 = u then 0 else if 2 * i + 1 < u then 2 * i + 1 else 2 * i + 1 - u)
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      simp only [o]
      split_ifs <;> omega
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      split_ifs <;> omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [o]
      split_ifs <;> omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      by_cases h1 : 2 * i + 1 = u
      · simp only [h1, ite_true, o]; omega
      · by_cases h2 : 2 * i + 1 < u
        · have h3 : 2 * i + 1 ≠ 0 := by omega
          have h4 : (2 * i + 1) % 2 = 1 := by omega
          simp only [h1, h2, ite_false, ite_true, o, h3, h4]; omega
        · have h3 : 2 * i + 1 - u ≠ 0 := by omega
          have h4 : ¬ (2 * i + 1 - u) % 2 = 1 := by omega
          simp only [h1, h2, ite_false, o, h3, h4]; omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      congr 1
      simp only [o]
      split_ifs <;> omega
  have hk : ∀ k ∈ range u,
      6 * (z k + z (k + u)) + (if k = 0 then 6 * z (2 * u) else 0) ≤
        4 * w (o k) + 4 * w (2 * k) + (if k = 0 then 4 * w (2 * u) + 1 else 0) := by
    intro k hk
    rw [Finset.mem_range] at hk
    simp only [o]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [ite_true, Nat.zero_add, Nat.mul_zero]
      have := hodd u (by omega) hu
      omega
    · simp only [hk0, ite_false]
      have e : 2 * (k + u) - 2 * u = 2 * k := by omega
      have a1 := h1 k (by omega) hk
      have a2 := h2 (k + u) (by omega) (by omega)
      rw [e] at a2
      by_cases hpar : k % 2 = 1
      · simp only [hpar, ite_true]
        have := hodd k (by omega) hpar
        omega
      · simp only [hpar, ite_false]
        have := hodd (k + u) (by omega) (by omega)
        omega
  have hsum := Finset.sum_le_sum hk
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hbij] at hsum
  have hu0 : 0 ∈ range u := Finset.mem_range.2 (by omega)
  simp only [Finset.sum_ite_eq', hu0, ite_true] at hsum
  have ez := sum_range_two_mul_add_one u z
  have ew : ∑ k ∈ range (2 * u + 1), w k =
      ∑ k ∈ range u, w (2 * k + 1) + ∑ k ∈ range u, w (2 * k) + w (2 * u) := by
    rw [Finset.sum_range_succ, sum_range_two_mul w u, Finset.sum_add_distrib]; ring
  rw [ez, ew]
  omega

/-! ## Gaps and doubled positions -/

section Gaps

variable {N : Nat} {S : List Nat}

/-- The panels of gap `k`: `W_k = {m ∈ [1, N] | P(m - 1) = k}`. -/
def gapSet (N : Nat) (S : List Nat) (k : Nat) : Finset Nat :=
  (Finset.Icc 1 N).filter fun m => below S (m - 1) = k

/-- The valid panels of gap `k`. -/
def validIn (N : Nat) (S : List Nat) (k : Nat) : Finset Nat :=
  (moves N S).filter fun m => below S (m - 1) = k

theorem below_mono (S : List Nat) {j k : Nat} (h : j ≤ k) : below S j ≤ below S k := by
  rw [below_split S h]; omega

theorem below_le_length (S : List Nat) (j : Nat) : below S j ≤ S.length :=
  List.countP_le_length

theorem gapSet_convex (k : Nat) :
    ∀ x ∈ gapSet N S k, ∀ y ∈ gapSet N S k, ∀ c, x ≤ c → c ≤ y → c ∈ gapSet N S k := by
  intro x hx y hy c hxc hcy
  simp only [gapSet, Finset.mem_filter, Finset.mem_Icc] at hx hy ⊢
  have := below_mono S (show x - 1 ≤ c - 1 by omega)
  have := below_mono S (show c - 1 ≤ y - 1 by omega)
  refine ⟨⟨by omega, by omega⟩, by omega⟩

/-- At most `(|W| + 1)/2` panels have their doubled position `2m - c` in an interval `W`. -/
theorem two_mul_card_le (D W : Finset Nat) (c : Nat)
    (hconv : ∀ x ∈ W, ∀ y ∈ W, ∀ t, x ≤ t → t ≤ y → t ∈ W)
    (hD : ∀ m ∈ D, c < 2 * m ∧ 2 * m - c ∈ W) : 2 * D.card ≤ W.card + 1 := by
  rcases D.eq_empty_or_nonempty with h | h
  · simp [h]
  set a := D.min' h
  set b := D.max' h
  have ha := hD a (D.min'_mem h)
  have hb := hD b (D.max'_mem h)
  have hab : a ≤ b := D.min'_le_max' h
  have h1 : D ⊆ Finset.Icc a b := fun m hm =>
    Finset.mem_Icc.2 ⟨D.min'_le m hm, D.le_max' m hm⟩
  have h2 : Finset.Icc (2 * a - c) (2 * b - c) ⊆ W := fun t ht => by
    rw [Finset.mem_Icc] at ht
    exact hconv _ ha.2 _ hb.2 t ht.1 ht.2
  have c1 := Finset.card_le_card h1
  have c2 := Finset.card_le_card h2
  rw [Nat.card_Icc] at c1 c2
  omega

/-- Sharper count for the first gap: there both `2m` and `2m - 1` lie in `W`. -/
theorem two_mul_card_le_of_pairs (D W : Finset Nat)
    (hD : ∀ m ∈ D, 1 ≤ m ∧ 2 * m ∈ W ∧ 2 * m - 1 ∈ W) : 2 * D.card ≤ W.card := by
  have hdisj : Disjoint (D.image (2 * ·)) (D.image (2 * · - 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image] at hx hx'
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨m', hm', e⟩ := hx'
    have := (hD m' hm').1
    omega
  have hsub : D.image (2 * ·) ∪ D.image (2 * · - 1) ⊆ W := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_image] at hx
    rcases hx with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
    · exact (hD m hm).2.1
    · exact (hD m hm).2.2
  have c := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun x y e => by simpa using e),
    Finset.card_image_of_injOn (fun x hx y hy e => by
      have := (hD x hx).1; have := (hD y hy).1; omega)] at c
  omega

theorem cycBelow_two_mul_lo {m : Nat} (hm : 1 ≤ m) (h : 2 * m ≤ N) :
    cycBelow N S (2 * m - 1) = below S (2 * m - 1) := by
  unfold cycBelow
  rw [Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  simp

theorem cycBelow_two_mul_hi {m : Nat} (hmN : m ≤ N) (h : N < 2 * m) :
    cycBelow N S (2 * m - 1) = below S (2 * m - N - 1) + S.length := by
  unfold cycBelow
  have hN : 0 < N := by omega
  have h' : N ≤ 2 * m - 1 := by omega
  have hlt : 2 * m - 1 - N < N := by omega
  rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt hlt, Nat.div_eq_sub_div hN h',
    Nat.div_eq_of_lt hlt, show 2 * m - 1 - N = 2 * m - N - 1 by omega]
  simp

theorem validIn_card_le (k : Nat) : (validIn N S k).card ≤ (gapSet N S k).card := by
  apply Finset.card_le_card
  intro m hm
  simp only [validIn, gapSet, Finset.mem_filter, moves, Finset.mem_Icc] at hm ⊢
  exact ⟨hm.1.1, hm.2⟩

theorem validIn_card_split (k : Nat) :
    (validIn N S k).card = ((validIn N S k).filter (fun m => 2 * m ≤ N)).card +
      ((validIn N S k).filter (fun m => ¬ 2 * m ≤ N)).card :=
  (Finset.card_filter_add_card_filter_not _).symm

theorem card_moves_eq_sum :
    (moves N S).card = ∑ k ∈ range (S.length + 1), (validIn N S k).card := by
  apply Finset.card_eq_sum_card_fiberwise
  intro m _
  exact Finset.mem_range.2 (Nat.lt_succ_of_le (below_le_length S _))

theorem sum_gapSet :
    N = ∑ k ∈ range (S.length + 1), (gapSet N S k).card := by
  have := Finset.card_eq_sum_card_fiberwise (s := Finset.Icc 1 N) (t := range (S.length + 1))
    (f := fun m => below S (m - 1))
    (fun m _ => Finset.mem_range.2 (Nat.lt_succ_of_le (below_le_length S _)))
  rw [Nat.card_Icc, Nat.add_sub_cancel] at this
  exact this

variable (hnd : S.Nodup) (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N)
include hnd hS

theorem cyc_of_mem_moves {m : Nat} (hm : m ∈ moves N S) :
    cycBelow N S (2 * m - 1) = 2 * below S (m - 1) ∧ 1 ≤ m ∧ m ≤ N ∧ m ∉ S := by
  rw [mem_moves] at hm
  obtain ⟨⟨h1, h2⟩, hmS, hv⟩ := hm
  exact ⟨(semiStep_iff_cyclicStep hnd hS h1 h2 hmS).1 hv, h1, h2, hmS⟩

/-- Every gap `k < s` contains a panel of `S` (namely the `(k+1)`-st one). -/
theorem exists_mem_gapSet {k : Nat} (hk : k < S.length) : ∃ x ∈ S, x ∈ gapSet N S k := by
  have hpos : ∀ x ∈ S, 1 ≤ x := fun x hx => (hS x hx).1
  have hex : ∃ j, k < below S j :=
    ⟨N, by rw [below_eq_length (fun x hx => (hS x hx).2)]; exact hk⟩
  set j := Nat.find hex with hj
  have hjk : k < below S j := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h0; rw [h0, below_zero hpos] at hjk; omega
  have hmin : ¬ k < below S (j - 1) := Nat.find_min hex (by omega)
  have hsucc := below_succ hnd (j - 1)
  rw [show j - 1 + 1 = j by omega] at hsucc
  by_cases hjS : j ∈ S
  · refine ⟨j, hjS, ?_⟩
    simp only [hjS, ite_true] at hsucc
    simp only [gapSet, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, (hS j hjS).2⟩, by omega⟩
  · simp only [hjS, ite_false] at hsucc
    omega

theorem validIn_card_lt {k : Nat} (hk : k < S.length) :
    (validIn N S k).card + 1 ≤ (gapSet N S k).card := by
  obtain ⟨x, hxS, hx⟩ := exists_mem_gapSet hnd hS hk
  have hxZ : x ∉ validIn N S k := by
    intro h
    simp only [validIn, moves, Finset.mem_filter] at h
    exact h.1.2.1 hxS
  have hsub : insert x (validIn N S k) ⊆ gapSet N S k := by
    intro m hm
    rw [Finset.mem_insert] at hm
    rcases hm with rfl | hm
    · exact hx
    · simp only [validIn, gapSet, Finset.mem_filter, moves, Finset.mem_Icc] at hm ⊢
      exact ⟨hm.1.1, hm.2⟩
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem hxZ] at this

/-- Valid panels of gap `k` whose doubled position `2m` is at most `N`: their doubled
positions lie in gap `2k`. -/
theorem validIn_lo_card (k : Nat) :
    2 * ((validIn N S k).filter (fun m => 2 * m ≤ N)).card ≤ (gapSet N S (2 * k)).card + 1 := by
  apply two_mul_card_le _ _ 0 (gapSet_convex (2 * k))
  intro m hm
  simp only [validIn, Finset.mem_filter] at hm
  obtain ⟨⟨hmv, hk⟩, hle⟩ := hm
  obtain ⟨hc, h1, h2, _⟩ := cyc_of_mem_moves hnd hS hmv
  rw [cycBelow_two_mul_lo h1 hle] at hc
  refine ⟨by omega, ?_⟩
  simp only [gapSet, Finset.mem_filter, Finset.mem_Icc, Nat.sub_zero]
  exact ⟨⟨by omega, hle⟩, by omega⟩

/-- Valid panels of gap `k` whose doubled position `2m` exceeds `N`: `2m - N` lies in gap
`2k - s`. -/
theorem validIn_hi_card (k : Nat) :
    2 * ((validIn N S k).filter (fun m => ¬ 2 * m ≤ N)).card ≤
      (gapSet N S (2 * k - S.length)).card + 1 := by
  apply two_mul_card_le _ _ N (gapSet_convex _)
  intro m hm
  simp only [validIn, Finset.mem_filter] at hm
  obtain ⟨⟨hmv, hk⟩, hgt⟩ := hm
  obtain ⟨hc, h1, h2, _⟩ := cyc_of_mem_moves hnd hS hmv
  rw [cycBelow_two_mul_hi h2 (by omega)] at hc
  refine ⟨by omega, ?_⟩
  simp only [gapSet, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem validIn_hi_empty {k : Nat} (hk : 2 * k < S.length) :
    ((validIn N S k).filter (fun m => ¬ 2 * m ≤ N)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m hm hgt
  simp only [validIn, Finset.mem_filter] at hm
  obtain ⟨hmv, hk'⟩ := hm
  obtain ⟨hc, h1, h2, _⟩ := cyc_of_mem_moves hnd hS hmv
  rw [cycBelow_two_mul_hi h2 (by omega)] at hc
  omega

theorem validIn_zero_card (hs : 0 < S.length) :
    2 * (validIn N S 0).card ≤ (gapSet N S 0).card := by
  apply two_mul_card_le_of_pairs
  intro m hm
  simp only [validIn, Finset.mem_filter] at hm
  obtain ⟨hmv, hk⟩ := hm
  obtain ⟨hc, h1, h2, _⟩ := cyc_of_mem_moves hnd hS hmv
  have hle : 2 * m ≤ N := by
    by_contra hgt
    rw [cycBelow_two_mul_hi h2 (by omega)] at hc
    omega
  rw [cycBelow_two_mul_lo h1 hle, hk] at hc
  have := below_mono S (show 2 * m - 1 - 1 ≤ 2 * m - 1 by omega)
  simp only [gapSet, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨h1, ⟨⟨by omega, hle⟩, by omega⟩, ⟨by omega, by omega⟩, by omega⟩

/-- **Max-moves bound.**  If `|S| ≡ 2 (mod 4)`, at most `2N/3` panels are valid:
`3 · V(S) ≤ 2N`. -/
theorem card_moves_two_mod_four (hs : S.length % 4 = 2) : 3 * (moves N S).card ≤ 2 * N := by
  set u := S.length / 2 with hu
  have hsu : S.length = 2 * u := by omega
  have huodd : u % 2 = 1 := by omega
  set z : Nat → Nat := fun k => (validIn N S k).card with hz
  set w : Nat → Nat := fun k => (gapSet N S k).card with hw
  have hV := card_moves_eq_sum (N := N) (S := S)
  have hN := sum_gapSet (N := N) (S := S)
  rw [hsu] at hV hN
  rw [hV]
  conv_rhs => rw [hN]
  have lo := validIn_lo_card hnd hS
  have hi := validIn_hi_card hnd hS
  have hi0 : ∀ k, 2 * k < S.length →
      ((validIn N S k).filter (fun m => ¬ 2 * m ≤ N)).card = 0 :=
    fun k hk => validIn_hi_empty hnd hS hk
  have spl := validIn_card_split (N := N) (S := S)
  rw [hsu] at hi hi0
  -- gaps beyond `s` are empty
  have wbig : ∀ j, 2 * u < j → w j = 0 := by
    intro j hj
    simp only [hw, Finset.card_eq_zero, gapSet, Finset.filter_eq_empty_iff]
    intro m _
    have := below_le_length S (m - 1)
    omega
  apply arith_two_mod_four u huodd z w
  · exact validIn_zero_card hnd hS (by omega)
  · intro k hk1 hku
    have a := lo k; have b := hi0 (k := k) (by omega); have c := spl k
    simp only [hz, hw] at a b c ⊢
    omega
  · have a := lo u; have b := hi u; have c := spl u
    simp only [hz, hw] at a b c ⊢
    rw [show 2 * u - 2 * u = 0 by omega] at b
    omega
  · intro k hk1 hk2
    have a := lo k; have b := hi k; have c := spl k
    have d := wbig (2 * k) (by omega)
    simp only [hz, hw] at a b c d ⊢
    omega
  · have a := lo (2 * u); have b := hi (2 * u); have c := spl (2 * u)
    have d := wbig (2 * (2 * u)) (by omega)
    simp only [hz, hw] at a b c d ⊢
    rw [show 2 * (2 * u) - 2 * u = 2 * u by omega] at b
    omega
  · intro k hk hodd
    have := validIn_card_lt hnd hS (k := k) (by omega)
    simpa [hz, hw] using this

end Gaps

/-! ## The tree bound -/

/-- **Improved upper bound, even `N`.**  At odd levels at most `h` panels are valid (parity),
at levels `i ≡ 2 (mod 4)` at most `⌊4h/3⌋`:
`a(2h) ≤ ∏_{i < 2h} B_i` with `B_i = min(2h - i, h)` (`i` odd), `min(2h - i, ⌊4h/3⌋)`
(`i ≡ 2 mod 4`), `2h - i` otherwise.  This is `(2h)! · exp(-(0.1146… + o(1)) · 2h)`. -/
theorem semiCount_even_le_prod_two_mod_four (h : Nat) :
    semiCount (2 * h) ≤
      ∏ i ∈ Finset.range (2 * h),
        (if i % 2 = 1 then min (2 * h - i) h
         else if i % 4 = 2 then min (2 * h - i) (2 * (2 * h) / 3) else 2 * h - i) := by
  apply semiCount_le_prod
  intro p _ hnd hb _
  have c1 := card_moves_le hnd hb
  split
  · next hodd => exact le_min c1 (card_moves_odd_le hnd hb hodd)
  · split
    · next h4 =>
      have := card_moves_two_mod_four hnd hb h4
      exact le_min c1 (by omega)
    · exact c1

/-- **Improved upper bound, odd `N`.**  At odd levels `i` at most `h + 1 + ⌊i/2⌋` panels are
valid (`card_moves_odd_odd_le`), at levels `i ≡ 2 (mod 4)` at most `⌊2N/3⌋`.  This is
`(2h+1)! · exp(-(0.0769… + o(1)) N)`. -/
theorem semiCount_odd_le_prod_two_mod_four (h : Nat) :
    semiCount (2 * h + 1) ≤
      ∏ i ∈ Finset.range (2 * h + 1),
        (if i % 2 = 1 then min (2 * h + 1 - i) (h + 1 + i / 2)
         else if i % 4 = 2 then min (2 * h + 1 - i) (2 * (2 * h + 1) / 3)
         else 2 * h + 1 - i) := by
  apply semiCount_le_prod
  intro p _ hnd hb _
  have c1 := card_moves_le hnd hb
  split
  · next hodd => exact le_min c1 (card_moves_odd_odd_le hnd hb hodd)
  · split
    · next h4 =>
      have := card_moves_two_mod_four hnd hb h4
      exact le_min c1 (by omega)
    · exact c1

/-! ## `|S| ≡ 0 (mod 4)`: the `2N/3` bound fails

For `N = 60` the reachable set `{8, 17, 34, 35}` (valid order `35, 17, 34, 8`) leaves
`41 > 40 = 2N/3` valid panels. -/
theorem moves_sixty :
    SemiSymmetric 60 [35, 17, 34, 8] ∧ (moves 60 [35, 17, 34, 8]).card = 41 := by
  decide

end Folds
