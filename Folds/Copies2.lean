import Folds.Neutral
import Folds.Prefix

/-!
# Large window copies are neutral

Paper proofs: `experiments/jseq/NOTES.txt` (section "Large copies").  Notation as in
`Folds/Neutral.lean`: `X ⊆ [1, N]` is a *copy* if it is balanced around each of its own
elements, *neutral* if it is balanced around every panel.

* `copy_dbl`: for a copy, the doubling relation `P(2k+1) = P(k) + P(k+1)` holds whenever the
  panel `k + 1` (read mod `N`) lies in `X`.
* `hd_bounds_copy`: for a copy, `|N P(t) - |X| t| ≤ N - |X|` (one half of the neutral bound).
* `copy_size`: a copy with `N < 2|X| < 2N` has `2|X| d = (d + 1) N` for an odd `d ∣ N`,
  `d ≥ 3`.
* `copy_unique`: two copies of the same size `s` with `N < 2s` coincide.
* `copy_large_neutral`: **every copy with `N < 2|X|` is neutral**; with
  `neutral_classification` (`copy_large_mem`) the copies of size `> N/2` other than `[1, N]`
  are exactly the odd panels (odd `N`) and the sets `E_dᶜ`.
* `CN_large`: hence `C_N(k) = #{X ∈ NFam N : |X| = k} · a(N - k)` for `N < 2k`, `k < N`: the
  part `k > N/2` of identity (B) is explicit.

# Copies of size 2 and of size N/2
* `isCopy_pair`, `card_copies_two`: `{x < y}` is a copy iff `2x ≤ y` and `x + N + 1 ≤ 2y`;
  there are `⌊N²/2⌋ - ⌊N²/3⌋ = ⌊(N² + 2)/6⌋` copies of size 2 (OEIS A156040, shifted).
* `copy_half_P`, `copy_half_iff`: a copy of size `N/2` has exactly one panel in each pair
  `{2i + 1, 2i + 2}`, and such a set is a copy iff (panels mod `N`) `2i + 1 ∈ X ⇒ 4i + 1 ∈ X`
  and `2i + 2 ∈ X ⇒ 4i + 4 ∈ X`.  So the copies of size `N/2` correspond to the subsets of
  `Z/(N/2)` closed under `i ↦ 2i` and `2i + 1 ↦ i`.
-/

namespace Folds
namespace Copies2

open Neutral

variable {N : Nat} {X : Finset Nat}

/-- For a copy, `Dbl k` holds whenever panel `k + 1` (mod `N`) belongs to `X`. -/
theorem copy_dbl (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hc : IsCopy N X) :
    ∀ k, xi N X (k + 1) = 1 → Dbl N X k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.lt_or_ge k N with hlt | hge
    · have hm : k + 1 ∈ X := (mem_iff_xi hN (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).2 hk
      have := (balF_iff_P hN hX (by omega) (by omega)).1 (hc _ hm)
      unfold Dbl
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, Nat.add_sub_cancel] at this
      exact this
    · have h' : xi N X (k - N + 1) = 1 := by
        rw [← xi_add hN, show k - N + 1 + N = k + 1 by omega]; exact hk
      have := ih (k - N) (by omega) h'
      rw [← dbl_add_iff hN hX, Nat.sub_add_cancel hge] at this
      exact this

theorem hd_empty (t : Nat) : hd N ∅ t = 0 := by
  have h : ∀ k, xi N ∅ k = 0 := fun k => by unfold xi; simp
  unfold hd P; simp [h]

/-- **Discrepancy bound for copies.**  `|N · P t - |X| · t| ≤ N - |X|`. -/
theorem hd_bounds_copy (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hc : IsCopy N X) (t : Nat) :
    hd N X t ≤ (N : Int) - X.card ∧ -((N : Int) - X.card) ≤ hd N X t := by
  have hsN : X.card ≤ N := by
    have := Finset.card_le_card hX; rw [Nat.card_Icc] at this; omega
  have hsN' : (X.card : Int) ≤ N := by exact_mod_cast hsN
  rcases Nat.eq_zero_or_pos X.card with h0 | hpos
  · rw [Finset.card_eq_zero.1 h0, hd_empty]; simp
  have hs : (0 : Int) < X.card := by exact_mod_cast hpos
  have hdb := copy_dbl hN hX hc
  have hne : (Finset.range N).Nonempty := ⟨0, Finset.mem_range.2 hN⟩
  have x01 : ∀ k, xi N X k = 0 ∨ xi N X k = 1 := fun k => by
    have := xi_le_one (N := N) (X := X) k; omega
  obtain ⟨t0, -, hmax⟩ := Finset.exists_max_image (Finset.range N) (hd N X) hne
  obtain ⟨t1, -, hmin⟩ := Finset.exists_min_image (Finset.range N) (hd N X) hne
  have hall : ∀ t, hd N X t ≤ hd N X t0 := fun t => by
    rw [hd_mod hN hX t]; exact hmax _ (Finset.mem_range.2 (Nat.mod_lt _ hN))
  have hall' : ∀ t, hd N X t1 ≤ hd N X t := fun t => by
    rw [hd_mod hN hX t]; exact hmin _ (Finset.mem_range.2 (Nat.mod_lt _ hN))
  -- the maximum
  have u2 : hd N X t0 ≤ (N : Int) - X.card := by
    have e := hd_add hN hX t0
    have b := hd_succ (N := N) (X := X) (t0 + N - 1)
    rw [show t0 + N - 1 + 1 = t0 + N by omega, e] at b
    rcases x01 (t0 + N) with hx | hx
    · rw [hx] at b; have := hall (t0 + N - 1); push_cast at b; linarith
    · have hk : xi N X (t0 + N - 1 + 1) = 1 := by
        rw [show t0 + N - 1 + 1 = t0 + N by omega]; exact hx
      have a := hall (2 * (t0 + N - 1) + 1); rw [hd_dbl (hdb _ hk)] at a
      rw [show t0 + N - 1 + 1 = t0 + N by omega, e] at a
      rw [hx] at b; push_cast at b; linarith
  -- the minimum
  have l1 : -((N : Int) - X.card) ≤ hd N X t1 := by
    have b := hd_succ (N := N) (X := X) t1
    rcases x01 (t1 + 1) with hx | hx
    · rw [hx] at b; have := hall' (t1 + 1); push_cast at b; linarith
    · have a := hall' (2 * t1 + 1); rw [hd_dbl (hdb t1 hx)] at a
      rw [hx] at b; push_cast at b; linarith
  have := hall t; have := hall' t
  exact ⟨by linarith, by linarith⟩

/-- **Size bound from a discrepancy bound.**  If `|N · P t - |X| · t| ≤ μ` for all `t`, then
`g ⌊N/(2g)⌋ ≤ μ` with `g = gcd(|X|, N)`. -/
theorem size_bound_gen (hN : 0 < N) (μ : Int) (hb : ∀ t, hd N X t ≤ μ ∧ -μ ≤ hd N X t) :
    ((Nat.gcd X.card N * (N / Nat.gcd X.card N / 2) : Nat) : Int) ≤ μ := by
  have hgN : Nat.gcd X.card N * (N / Nat.gcd X.card N) = N :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ N)
  generalize hq : N / Nat.gcd X.card N / 2 = q
  have h2q : 2 * (Nat.gcd X.card N * q) ≤ N := by
    have : q * 2 ≤ N / Nat.gcd X.card N := by rw [← hq]; exact Nat.div_mul_le_self _ _
    calc 2 * (Nat.gcd X.card N * q) = Nat.gcd X.card N * (q * 2) := by ring
      _ ≤ Nat.gcd X.card N * (N / Nat.gcd X.card N) := Nat.mul_le_mul_left _ this
      _ = N := hgN
  have bez : (Nat.gcd X.card N : Int) =
      X.card * Nat.gcdA X.card N + N * Nat.gcdB X.card N := Nat.gcd_eq_gcd_ab _ _
  have hNpos : (0 : Int) < N := by exact_mod_cast hN
  have htz : (((-Nat.gcdA X.card N * q) % N).toNat : Int) =
      -Nat.gcdA X.card N * q - N * ((-Nat.gcdA X.card N * q) / N) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hNpos.ne'), Int.emod_def]
  generalize ((-Nat.gcdA X.card N * q) % N).toNat = t at htz
  have key : hd N X t - Nat.gcd X.card N * q = N * ((P N X t : Int) +
      X.card * ((-Nat.gcdA X.card N * q) / N) - Nat.gcdB X.card N * q) := by
    unfold hd; rw [htz, bez]; ring
  generalize ((P N X t : Int) + X.card * ((-Nat.gcdA X.card N * q) / N) -
      Nat.gcdB X.card N * q) = w at key
  obtain ⟨b1, b2⟩ := hb t
  have h2q' : 2 * ((Nat.gcd X.card N : Int) * q) ≤ N := by exact_mod_cast h2q
  push_cast
  by_contra hc
  push Not at hc
  have h1 : (N : Int) * w < 0 := by linarith
  have hw0 : w < 0 := by
    by_contra hw0; push Not at hw0; nlinarith
  have : (N : Int) * w ≤ N * (-1) := mul_le_mul_of_nonneg_left (by omega) hNpos.le
  linarith

/-- **Sizes of large copies.**  A copy with `N < 2|X|` and `|X| < N` has
`2 |X| d = (d + 1) N` for some odd `d ∣ N` with `d ≥ 3`. -/
theorem copy_size (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hc : IsCopy N X)
    (hbig : N < 2 * X.card) (hlt : X.card < N) :
    ∃ d, d ∣ N ∧ d % 2 = 1 ∧ 3 ≤ d ∧ 2 * X.card * d = (d + 1) * N := by
  have hsN : X.card ≤ N := hlt.le
  have b := size_bound_gen hN ((N : Int) - X.card) (hd_bounds_copy hN hX hc)
  have b' : Nat.gcd X.card N * (N / Nat.gcd X.card N / 2) ≤ N - X.card := by
    have : ((Nat.gcd X.card N * (N / Nat.gcd X.card N / 2) : Nat) : Int) ≤
        ((N - X.card : Nat) : Int) := by push_cast [hsN]; exact b
    exact_mod_cast this
  have hg : 0 < Nat.gcd X.card N := Nat.gcd_pos_of_pos_right _ hN
  have hs := (Nat.mul_div_cancel' (Nat.gcd_dvd_left X.card N)).symm
  have hNd := (Nat.mul_div_cancel' (Nat.gcd_dvd_right X.card N)).symm
  generalize Nat.gcd X.card N = g at hg hs hNd b'
  generalize X.card / g = a at hs
  generalize N / g = d at hNd b'
  rw [hs] at hbig hlt b' ⊢
  rw [hNd] at hbig hlt b' ⊢
  have l2 : d / 2 ≤ d - a := by
    apply Nat.le_of_mul_le_mul_left _ hg
    rw [Nat.mul_sub]; exact b'
  have l3 : d < 2 * a := by
    apply Nat.lt_of_mul_lt_mul_left (a := g)
    calc g * d < 2 * (g * a) := hbig
      _ = g * (2 * a) := by ring
  have l4 : a < d := Nat.lt_of_mul_lt_mul_left hlt
  have hodd : d % 2 = 1 := by omega
  have ha : 2 * a = d + 1 := by omega
  refine ⟨d, ⟨g, by ring⟩, hodd, by omega, ?_⟩
  calc 2 * (g * a) * d = g * (2 * a) * d := by ring
    _ = (d + 1) * (g * d) := by rw [ha]; ring

/-- **Uniqueness.**  Two copies of the same size `s` with `N < 2s` coincide. -/
theorem copy_unique {X' : Finset Nat} (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N)
    (hX' : X' ⊆ Finset.Icc 1 N) (c1 : IsCopy N X) (c2 : IsCopy N X')
    (hc : X.card = X'.card) (hbig : N < 2 * X.card) : X = X' := by
  apply eq_of_P_eq hN hX hX'
  intro t
  have b1 := hd_bounds_copy hN hX c1 t
  have b2 := hd_bounds_copy hN hX' c2 t
  rw [← hc] at b2
  have hND : (N : Int) * ((P N X t : Int) - P N X' t) = hd N X t - hd N X' t := by
    unfold hd; rw [← hc]; ring
  have hNpos : (0 : Int) < N := by exact_mod_cast hN
  have hbig' : (N : Int) < 2 * X.card := by exact_mod_cast hbig
  have lt1 : (N : Int) * ((P N X t : Int) - P N X' t) < N * 1 := by linarith
  have lt2 : (N : Int) * (-1) < N * ((P N X t : Int) - P N X' t) := by linarith
  have := lt_of_mul_lt_mul_left lt1 hNpos.le
  have := lt_of_mul_lt_mul_left lt2 hNpos.le
  omega

theorem isCopy_of_neutral (hX : X ⊆ Finset.Icc 1 N) (hn : IsNeutral N X) : IsCopy N X :=
  fun m hm => hn m (hX hm)

/-- **Large copies are neutral.**  A copy `X ⊆ [1, N]` with `N < 2|X|` is neutral. -/
theorem copy_large_neutral (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hc : IsCopy N X)
    (hbig : N < 2 * X.card) : IsNeutral N X := by
  have hsN : X.card ≤ N := by
    have := Finset.card_le_card hX; rw [Nat.card_Icc] at this; omega
  rcases Nat.lt_or_ge X.card N with hlt | hge
  · obtain ⟨d, hdN, hodd, hd3, he⟩ := copy_size hN hX hc hbig hlt
    have hdle : d ≤ N := Nat.le_of_dvd hN hdN
    rcases Nat.lt_or_ge d N with hdlt | hdge
    · have hd : d ∈ oddDivs N := by
        simp only [oddDivs, Finset.mem_filter, Finset.mem_Ico]; exact ⟨⟨hd3, hdlt⟩, hdN, hodd⟩
      obtain ⟨hj, hn2, hjn⟩ := oddDivs_facts hd
      have hdj : d = 2 * ((d - 1) / 2) + 1 := by omega
      generalize (d - 1) / 2 = j at hj hjn hdj
      generalize N / d = n at hn2 hjn
      subst hdj
      have hcard : X.card = (Finset.Icc 1 N \ resE j n).card := by
        rw [card_compl_resE hj hjn]
        rw [← hjn] at he
        have : (2 * (2 * j + 1)) * X.card = (2 * (2 * j + 1)) * ((j + 1) * n) := by
          have e2 : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
          rw [e2] at he; nlinarith
        exact Nat.eq_of_mul_eq_mul_left (by omega) this
      have hcp := isCopy_of_neutral Finset.sdiff_subset (neutral_compl_resE hj hjn)
      rw [copy_unique hN hX Finset.sdiff_subset hc hcp hcard hbig]
      exact neutral_compl_resE hj hjn
    · have hdN' : d = N := by omega
      subst hdN'
      have h2 : 2 * X.card = d + 1 := Nat.eq_of_mul_eq_mul_right hN (by rw [he])
      have hcp := isCopy_of_neutral (parCls_sub d 1 le_rfl (by omega))
        (neutral_parCls1 (N := d) (by omega))
      have hcard : X.card = (parCls d 1).card := by rw [card_parCls1 (by omega)]; omega
      rw [copy_unique hN hX (parCls_sub d 1 le_rfl (by omega)) hc hcp hcard hbig]
      exact neutral_parCls1 (by omega)
  · have : X = Finset.Icc 1 N :=
      Finset.eq_of_subset_of_card_le hX (by rw [Nat.card_Icc]; omega)
    rw [this]; exact neutral_full N

/-- The copies of size `> N/2`, other than `[1, N]`, are members of `NFam N`: the odd panels
(odd `N`) and the sets `E_dᶜ`. -/
theorem copy_large_mem (hN : 2 ≤ N) (hX : X ⊆ Finset.Icc 1 N) (hc : IsCopy N X)
    (hbig : N < 2 * X.card) (hlt : X.card < N) : X ∈ NFam N :=
  (neutral_classification hN hX).1 ⟨copy_large_neutral (by omega) hX hc hbig, by omega, hlt⟩

/-- A copy has `g(X) = a(|X|)`. -/
theorem g_copy (hX : X ⊆ Finset.Icc 1 N) (hc : IsCopy N X) : g N X = semiCount X.card := by
  obtain ⟨φ, hφ, e⟩ := (isCopy_iff_winEmb hX).1 hc
  conv_lhs => rw [← e]
  rw [g_winEmb hφ]

/-- **The large part of identity (B) is explicit.**  For `N < 2k`, `k < N`:
`C_N(k) = #{X ∈ NFam N : |X| = k} · a(N - k)` (and the count is `0` or `1`). -/
theorem CN_large {k : Nat} (hN : 2 ≤ N) (hk : N < 2 * k) (hkN : k < N) :
    CN N k = ((NFam N).filter (fun X => X.card = k)).card * semiCount (N - k) := by
  have heq : copies N k = (NFam N).filter (fun X => X.card = k) := by
    ext X
    simp only [copies, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hX, hcard⟩, hc⟩
      exact ⟨copy_large_mem hN hX hc (by omega) (by omega), hcard⟩
    · rintro ⟨hX, hcard⟩
      have hsub := nfam_sub hX
      obtain ⟨hn, -⟩ := (neutral_classification hN hsub).2 hX
      exact ⟨⟨hsub, hcard⟩, isCopy_of_neutral hsub hn⟩
  unfold CN
  rw [heq, Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
  apply Finset.sum_congr rfl
  intro X hX
  rw [Finset.mem_filter] at hX
  have hsub := nfam_sub hX.1
  obtain ⟨hn, -⟩ := (neutral_classification hN hsub).2 hX.1
  have hcs : Finset.Icc 1 N \ X ⊆ Finset.Icc 1 N := Finset.sdiff_subset
  have hcc : IsCopy N (Finset.Icc 1 N \ X) :=
    ((neutral_iff_copy_compl hsub).1 hn).2
  rw [g_copy hcs hcc, Finset.card_sdiff_of_subset hsub, Nat.card_Icc, Nat.add_sub_cancel, hX.2]

/-! ## Copies of size 2 -/

/-- A 2-set `{x < y}` is a copy iff `2x ≤ y` and `x + N + 1 ≤ 2y`. -/
theorem balF_pair {x y : Nat} (hne : x ≠ y) (m : Nat) :
    BalF N {x, y} m ↔
      (if m - reach N m ≤ x ∧ x < m then 1 else 0) + (if m - reach N m ≤ y ∧ y < m then 1 else 0)
        = (if m < x ∧ x ≤ m + reach N m then 1 else 0) +
          (if m < y ∧ y ≤ m + reach N m then 1 else 0) := by
  unfold BalF
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_pair hne, Finset.sum_pair hne]

theorem isCopy_pair {x y : Nat} (h1 : 1 ≤ x) (hxy : x < y) (hyN : y ≤ N) :
    IsCopy N {x, y} ↔ 2 * x ≤ y ∧ x + N + 1 ≤ 2 * y := by
  have hne : x ≠ y := by omega
  have hx : BalF N {x, y} x ↔ 2 * x ≤ y := by
    rw [balF_pair hne]; unfold reach
    split_ifs <;> omega
  have hy : BalF N {x, y} y ↔ x + N + 1 ≤ 2 * y := by
    rw [balF_pair hne]; unfold reach
    split_ifs <;> omega
  unfold IsCopy
  simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
  rw [hx, hy]

/-- Sorted pairs `(x, y)` with `2x ≤ y`. -/
def lowS (N : Nat) : Finset (Nat × Nat) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter fun p => 2 * p.1 ≤ p.2

/-- Sorted pairs `(x, y)` forming a copy. -/
def copyTwoArith (N : Nat) : Finset (Nat × Nat) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter fun p => 2 * p.1 ≤ p.2 ∧ p.1 + N + 1 ≤ 2 * p.2

theorem card_copyTwoArith (N : Nat) : (copyTwoArith N).card = N * N / 2 - N * N / 3 := by
  have hl : (lowS N).card = (pairsLow N).card := by
    apply Finset.card_nbij' Prod.swap Prod.swap
    · intro p hp; simp only [lowS, pairsLow, Finset.coe_filter, Finset.mem_product,
        Finset.mem_Icc, Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap] at hp ⊢; omega
    · intro p hp; simp only [lowS, pairsLow, Finset.coe_filter, Finset.mem_product,
        Finset.mem_Icc, Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap] at hp ⊢; omega
    · intro p _; simp
    · intro p _; simp
  have hu : lowS N ∪ pairsHigh N = reachTwoArith N := by
    ext ⟨x, y⟩
    simp only [lowS, pairsHigh, reachTwoArith, Finset.mem_union, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Icc]
    constructor <;> intro h <;> omega
  have hi : lowS N ∩ pairsHigh N = copyTwoArith N := by
    ext ⟨x, y⟩
    simp only [lowS, pairsHigh, copyTwoArith, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Icc]
    constructor <;> intro h <;> omega
  have := Finset.card_union_add_card_inter (lowS N) (pairsHigh N)
  rw [hu, hi, hl, card_pairsHigh, card_pairsLow, card_reachTwoArith] at this
  have := two_mul_sq_div_four N
  omega

/-- **Copies of size 2.**  There are `⌊N²/2⌋ - ⌊N²/3⌋ = ⌊(N² + 2)/6⌋` of them: the valid
2-prefixes minus the reachable 2-sets. -/
theorem card_copies_two (N : Nat) : (copies N 2).card = N * N / 2 - N * N / 3 := by
  rw [← card_copyTwoArith N]
  symm
  apply Finset.card_bij (fun p _ => ({p.1, p.2} : Finset Nat))
  · intro ⟨x, y⟩ hp
    simp only [copyTwoArith, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    simp only [copies, Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨?_, ?_⟩, (isCopy_pair hp.1.1.1 (by omega) hp.1.2.2).2 hp.2⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [Finset.mem_Icc]; omega
    · rw [Finset.card_pair (by omega)]
  · intro ⟨x, y⟩ hp ⟨x', y'⟩ hp' e
    simp only [copyTwoArith, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp hp'
    have a1 : x ∈ ({x', y'} : Finset Nat) := by rw [← e]; simp
    have a2 : y ∈ ({x', y'} : Finset Nat) := by rw [← e]; simp
    have a3 : x' ∈ ({x, y} : Finset Nat) := by rw [e]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at a1 a2 a3
    simp only [Prod.mk.injEq]
    omega
  · intro X hX
    simp only [copies, Finset.mem_filter, Finset.mem_powersetCard] at hX
    obtain ⟨⟨hsub, hc2⟩, hcp⟩ := hX
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hc2
    have ha := Finset.mem_Icc.1 (hsub (by simp : a ∈ ({a, b} : Finset Nat)))
    have hb := Finset.mem_Icc.1 (hsub (by simp : b ∈ ({a, b} : Finset Nat)))
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · refine ⟨(a, b), ?_, rfl⟩
      have := (isCopy_pair ha.1 h hb.2).1 hcp
      simp only [copyTwoArith, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      omega
    · rw [Finset.pair_comm] at hcp
      refine ⟨(b, a), ?_, Finset.pair_comm _ _⟩
      have := (isCopy_pair hb.1 h ha.2).1 hcp
      simp only [copyTwoArith, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      omega

/-! ## Copies of size N/2 -/

/-- A copy of size `N/2` has `P(2u) = u`: it contains exactly one panel of each pair
`{2i - 1, 2i}`. -/
theorem copy_half_P (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hc : IsCopy N X)
    (h2 : 2 * X.card = N) (u : Nat) : P N X (2 * u) = u := by
  have b := hd_bounds_copy hN hX hc (2 * u)
  unfold hd at b
  have hs : (0 : Int) < X.card := by
    have : 0 < X.card := by omega
    exact_mod_cast this
  have h2' : (N : Int) = 2 * X.card := by exact_mod_cast h2.symm
  rw [h2'] at b
  have e1 : (X.card : Int) * (2 * ((P N X (2 * u) : Int) - u)) ≤ X.card * 1 := by
    push_cast at b; nlinarith
  have e2 : (X.card : Int) * (-1) ≤ X.card * (2 * ((P N X (2 * u) : Int) - u)) := by
    push_cast at b; nlinarith
  have := le_of_mul_le_mul_left e1 hs
  have := le_of_mul_le_mul_left e2 hs
  omega

theorem P_s1 (t : Nat) : P N X (t + 1) = P N X t + xi N X (t + 1) := P_succ t

/-- Under `P(2u) = u`: one panel of each pair, and `P(2u + 1) = u + xi(2u + 1)`. -/
theorem pair_of_P (hP : ∀ u, P N X (2 * u) = u) (u : Nat) :
    xi N X (2 * u + 1) + xi N X (2 * u + 2) = 1 ∧ P N X (2 * u + 1) = u + xi N X (2 * u + 1) := by
  have a := hP u
  have b : P N X (2 * u + 2) = u + 1 := by rw [show 2 * u + 2 = 2 * (u + 1) by ring]; exact hP _
  have c := P_s1 (N := N) (X := X) (2 * u)
  have d := P_s1 (N := N) (X := X) (2 * u + 1)
  rw [show 2 * u + 1 + 1 = 2 * u + 2 by ring] at d
  omega

/-- **Copies of size `N/2`.**  For `2|X| = N`, `X` is a copy iff it has one panel in each pair
`{2i + 1, 2i + 2}` (`P(2u) = u`) and, reading panels mod `N`, an odd panel `2i + 1 ∈ X` forces
`4i + 1 ∈ X` and an even panel `2i + 2 ∈ X` forces `4i + 4 ∈ X`.  (Equivalently: with
`U = {i : 2i + 1 ∈ X} ⊆ Z/(N/2)`, `U` is closed under `i ↦ 2i` and `2i + 1 ↦ i`.) -/
theorem copy_half_iff (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (h2 : 2 * X.card = N) :
    IsCopy N X ↔ (∀ u, P N X (2 * u) = u) ∧
      (∀ i, xi N X (2 * i + 1) = 1 → xi N X (4 * i + 1) = 1) ∧
      (∀ i, xi N X (2 * i + 2) = 1 → xi N X (4 * i + 4) = 1) := by
  -- the facts used in both directions, for a given `i`, assuming `P(2u) = u`
  have facts : (∀ u, P N X (2 * u) = u) → ∀ i,
      P N X (4 * i + 1) = 2 * i + xi N X (4 * i + 1) ∧
      P N X (4 * i + 3) = 2 * i + 1 + xi N X (4 * i + 3) ∧
      xi N X (4 * i + 3) + xi N X (4 * i + 4) = 1 ∧
      xi N X (2 * i + 1) + xi N X (2 * i + 2) = 1 ∧
      P N X (2 * i + 1) = i + xi N X (2 * i + 1) ∧
      P N X (2 * i) = i ∧ P N X (2 * i + 2) = i + 1 := by
    intro hP i
    have p1 := pair_of_P hP (2 * i)
    have p2 := pair_of_P hP (2 * i + 1)
    have p3 := pair_of_P hP i
    rw [show 2 * (2 * i) + 1 = 4 * i + 1 by ring] at p1
    rw [show 2 * (2 * i + 1) + 1 = 4 * i + 3 by ring,
      show 2 * (2 * i + 1) + 2 = 4 * i + 4 by ring] at p2
    have b : P N X (2 * i + 2) = i + 1 := by
      rw [show 2 * i + 2 = 2 * (i + 1) by ring]; exact hP _
    exact ⟨p1.2, p2.2, p2.1, p3.1, p3.2, hP i, b⟩
  constructor
  · intro hc
    have hP := copy_half_P hN hX hc h2
    have hdb := copy_dbl hN hX hc
    refine ⟨hP, fun i hi => ?_, fun i hi => ?_⟩
    · have d := hdb (2 * i) hi
      unfold Dbl at d
      rw [show 2 * (2 * i) + 1 = 4 * i + 1 by ring] at d
      obtain ⟨f1, -, -, -, f5, f6, -⟩ := facts hP i
      omega
    · have d := hdb (2 * i + 1) (by rw [show 2 * i + 1 + 1 = 2 * i + 2 by ring]; exact hi)
      unfold Dbl at d
      rw [show 2 * (2 * i + 1) + 1 = 4 * i + 3 by ring,
        show 2 * i + 1 + 1 = 2 * i + 2 by ring] at d
      obtain ⟨-, f2, f3, f4, f5, -, f7⟩ := facts hP i
      omega
  · rintro ⟨hP, h1, h3⟩ m hm
    have hmI := Finset.mem_Icc.1 (hX hm)
    rw [balF_iff_P hN hX hmI.1 hmI.2]
    have hx : xi N X m = 1 := (mem_iff_xi hN (hX hm)).1 hm
    rcases Nat.even_or_odd' (m - 1) with ⟨i, hi | hi⟩
    · have hm' : m = 2 * i + 1 := by omega
      subst hm'
      have h4 := h1 i hx
      rw [show 2 * (2 * i + 1) - 1 = 4 * i + 1 by omega, Nat.add_sub_cancel]
      obtain ⟨f1, -, -, -, f5, f6, -⟩ := facts hP i
      omega
    · have hm' : m = 2 * i + 2 := by omega
      subst hm'
      have h4 := h3 i hx
      rw [show 2 * (2 * i + 2) - 1 = 4 * i + 3 by omega,
        show 2 * i + 2 - 1 = 2 * i + 1 by omega]
      obtain ⟨-, f2, f3, f4, f5, -, f7⟩ := facts hP i
      omega

end Copies2
end Folds

