import Folds.Neutral
import Folds.Generate
import Folds.Adjacent
import Folds.Asymptotics
import Mathlib.Data.Nat.ModEq

/-!
# Words, the doubling map, and discrepancy (cross-domain campaign: combinatorics on words)

Paper version and data: `experiments/xd_words/NOTES.txt`.

Notation (from `Folds/Neutral.lean`): for `X ⊆ [1, N]`, `P N X t` is the `N`-periodic counting
function (extended with slope `|X|` per period) and `hd N X t = N · P t - |X| · t` the
discrepancy.

## A. The imbalance field and a discrepancy bound for every set
* `jm N X k = P(2k+1) - P(k) - P(k+1)` is the imbalance of panel `k + 1` (right arm minus left
  arm, `jm_eq_arms`; `imb_eq_jm` for lists); `dfc N X k = P(2k+1) - 2 P(k)` its cyclic defect.
* `hd_bounds_of_jm`: if `-A ≤ jm ≤ B` everywhere then
  `-(min(|X|, N - |X|) + N B) ≤ hd t ≤ min(|X|, N - |X|) + N A`.
  For a neutral set (`A = B = 0`) this is `Neutral.hd_bounds`.

## B. The functional graph `b ↦ 2b + 1` on `ℤ/N`
* `phi N b = (2b + 1) mod N` sends boundary `m - 1` to boundary `2m - 1`.
  `phi_iter_modEq`: `phi^k(b) + 1 ≡ 2^k (b + 1)`, so `phi` is the doubling map in panel
  coordinates.  `phi_injOn` (odd `N`: a permutation), `phi_iter_pow_two` (`N = 2^L`: a tree of
  depth `L` rooted at the fixed point `N - 1`), `phi_iter_dvd`, `phi_inj_periodic`
  (`N = 2^a q`: after `a` steps every point is in the periodic part, where `phi` is injective).
* `hd_orbit` (**orbit formula**): `2^n hd(k) = hd(phi^n k) + (2^n - 1)|X| - N ∑_{i<n}
  2^(n-1-i) dfc(phi^i k)`: the discrepancy at a boundary is the binary expansion whose digits
  are the defects along its orbit.  `hd_cycle`: on a cycle of length `n`,
  `(2^n - 1)(|X| - hd k) = N ∑ 2^(n-1-i) dfc(phi^i k)`; for neutral sets the digits are the
  membership bits (`hd_cycle_neutral`).

## C. Reachable sets
* `imb_le_of_semiSymmetric`: along a valid sequence, the panel placed at step `k` has final
  imbalance at most `(length - 1 - k)` in absolute value.
* `parking`, `reachable_parking`: in a reachable set, for every `i < |S|` at least `i + 1`
  elements have imbalance `≤ i` in absolute value (a parking-function condition).
* `reachable_Icc`, `hd_Icc`: the intervals `[1, k]` are reachable and have the largest possible
  discrepancy `k (N - k)`; so no sup-norm discrepancy bound separates reachable sets.

## D. The canonical word is a Toeplitz word
* `tword ρ j`: the one-hole Toeplitz word with hole `ρ`: compare `j` and `ρ` at their lowest
  differing binary digit.  `tword_add_pow`: every position `j ≢ ρ (mod 2^i)` is
  `2^i`-periodic (the Toeplitz property).
* `canon_prefix_word`: the set of the first `k + 1` panels of the truncated bit-reversal order
  `gen canon N` is `{m : tword (c - 1) (m - 1)}`, `c` its `(k+1)`-st panel.
-/

namespace Folds
namespace XdWords

open Neutral
open scoped Nat

variable {N : Nat} {X : Finset Nat}

/-! ## A. The imbalance field in periodic form -/

/-- The imbalance of panel `k + 1` (right arm minus left arm) in counting form. -/
def jm (N : Nat) (X : Finset Nat) (k : Nat) : Int :=
  (P N X (2 * k + 1) : Int) - P N X k - P N X (k + 1)

/-- The cyclic defect of panel `k + 1`: `P̃(2m - 1) - 2 P(m - 1)` with `m = k + 1`. -/
def dfc (N : Nat) (X : Finset Nat) (k : Nat) : Int :=
  (P N X (2 * k + 1) : Int) - 2 * P N X k

theorem dfc_eq_jm (k : Nat) : dfc N X k = jm N X k + xi N X (k + 1) := by
  unfold dfc jm; rw [P_succ k]; push_cast; ring

theorem hd_jm (k : Nat) :
    hd N X (2 * k + 1) = hd N X k + hd N X (k + 1) + N * jm N X k := by
  unfold hd jm; push_cast; ring

theorem hd_dfc (k : Nat) :
    hd N X (2 * k + 1) = 2 * hd N X k - X.card + N * dfc N X k := by
  unfold hd dfc; push_cast; ring

theorem jm_add (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (k : Nat) :
    jm N X (k + N) = jm N X k := by
  unfold jm
  have a := P_add hN hX (2 * k + 1 + N)
  have b := P_add hN hX (2 * k + 1)
  have c := P_add hN hX k
  have d := P_add hN hX (k + 1)
  rw [show 2 * k + 1 + N + N = 2 * (k + N) + 1 by ring] at a
  rw [show k + 1 + N = k + N + 1 by ring] at d
  rw [a, b, c, d]; push_cast; ring

theorem jm_add_mul (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (k : Nat) :
    ∀ q, jm N X (k + N * q) = jm N X k
  | 0 => by simp
  | q + 1 => by rw [Nat.mul_succ, ← Nat.add_assoc, jm_add hN hX, jm_add_mul hN hX k q]

theorem jm_mod (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (k : Nat) :
    jm N X k = jm N X (k % N) := by
  conv_lhs => rw [← Nat.mod_add_div k N]
  exact jm_add_mul hN hX _ _

theorem jm_eq_zero_iff (k : Nat) : jm N X k = 0 ↔ Dbl N X k := by
  unfold jm Dbl; omega

/-- `jm N X (m - 1)` is the number of elements in the right arm of `m` minus the number in its
left arm. -/
theorem jm_eq_arms (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) {m : Nat} (hm1 : 1 ≤ m)
    (hmN : m ≤ N) :
    jm N X (m - 1) = ((X.filter (fun x => m < x ∧ x ≤ m + reach N m)).card : Int) -
      (X.filter (fun x => m - reach N m ≤ x ∧ x < m)).card := by
  unfold jm
  rw [show 2 * (m - 1) + 1 = 2 * m - 1 by omega, Nat.sub_add_cancel hm1]
  set r := reach N m with hr
  have hr1 : r ≤ m - 1 ∧ m + r ≤ N := by rw [hr]; unfold reach; omega
  have eL : X.filter (fun x => m - r ≤ x ∧ x < m) =
      X.filter (fun x => m - r - 1 < x ∧ x ≤ m - 1) := by
    apply Finset.filter_congr; intro x hx; have := Finset.mem_Icc.1 (hX hx); omega
  rw [eL]
  have i1 := P_interval hN hX (a := m - r - 1) (b := m - 1) (by omega) (by omega)
  have i2 := P_interval hN hX (a := m) (b := m + r) (by omega) (by omega)
  rcases Nat.le_total (2 * m - 1) N with h | h
  · have hr' : r = m - 1 := by rw [hr]; unfold reach; omega
    have e1 : P N X (m - r - 1) = 0 := by rw [show m - r - 1 = 0 by omega, P_zero]
    have e2 : P N X (m + r) = P N X (2 * m - 1) := by rw [show m + r = 2 * m - 1 by omega]
    omega
  · have hr' : r = N - m := by rw [hr]; unfold reach; omega
    have e2 : P N X (m + r) = X.card := by rw [show m + r = N by omega, P_N hN hX]
    have := P_add hN hX (2 * m - 1 - N)
    rw [show 2 * m - 1 - N + N = 2 * m - 1 by omega] at this
    have e1 : P N X (m - r - 1) = P N X (2 * m - 1 - N) := by
      rw [show m - r - 1 = 2 * m - 1 - N by omega]
    omega

/-- The list imbalance `imb` of `Folds/Asymptotics.lean` is `jm` of the underlying set. -/
theorem imb_eq_jm (hN : 0 < N) {l : List Nat} (hnd : l.Nodup)
    (hb : ∀ x ∈ l, 1 ≤ x ∧ x ≤ N) {m : Nat} (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    imb N l m = jm N l.toFinset (m - 1) := by
  have hX : l.toFinset ⊆ Finset.Icc 1 N := by
    intro x hx; rw [List.mem_toFinset] at hx; exact Finset.mem_Icc.2 (hb x hx)
  rw [jm_eq_arms hN hX hm1 hmN]
  unfold imb
  rw [leftCount_eq hnd, rightCount_eq hnd, countP_eq_card hnd, countP_eq_card hnd]

/-- **Discrepancy bound for an arbitrary set**, generalising `Neutral.hd_bounds`: if the
imbalance field satisfies `-A ≤ jm ≤ B` at every panel, then
`-(min(|X|, N - |X|) + N B) ≤ N P(t) - |X| t ≤ min(|X|, N - |X|) + N A`. -/
theorem hd_bounds_of_jm (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (A B : Int)
    (hJ : ∀ k, k < N → -A ≤ jm N X k ∧ jm N X k ≤ B) (t : Nat) :
    hd N X t ≤ X.card + N * A ∧ hd N X t ≤ (N : Int) - X.card + N * A ∧
      -(X.card : Int) - N * B ≤ hd N X t ∧ -((N : Int) - X.card) - N * B ≤ hd N X t := by
  have hne : (Finset.range N).Nonempty := ⟨0, Finset.mem_range.2 hN⟩
  have hN' : (0 : Int) ≤ N := by positivity
  have hJ' : ∀ k, -((N : Int) * A) ≤ N * jm N X k ∧ (N : Int) * jm N X k ≤ N * B := by
    intro k
    have h := hJ (k % N) (Nat.mod_lt _ hN)
    rw [← jm_mod hN hX] at h
    constructor
    · have := mul_le_mul_of_nonneg_left h.1 hN'; linarith
    · exact mul_le_mul_of_nonneg_left h.2 hN'
  have x01 : ∀ k, (0 : Int) ≤ (N : Int) * (xi N X k : Int) ∧
      (N : Int) * (xi N X k : Int) ≤ N := by
    intro k
    have := xi_le_one (N := N) (X := X) k
    constructor
    · positivity
    · have : (xi N X k : Int) ≤ 1 := by exact_mod_cast this
      nlinarith
  obtain ⟨t0, -, hmax⟩ := Finset.exists_max_image (Finset.range N) (hd N X) hne
  obtain ⟨t1, -, hmin⟩ := Finset.exists_min_image (Finset.range N) (hd N X) hne
  have hall : ∀ t, hd N X t ≤ hd N X t0 := fun t => by
    rw [hd_mod hN hX t]; exact hmax _ (Finset.mem_range.2 (Nat.mod_lt _ hN))
  have hall' : ∀ t, hd N X t1 ≤ hd N X t := fun t => by
    rw [hd_mod hN hX t]; exact hmin _ (Finset.mem_range.2 (Nat.mod_lt _ hN))
  have u1 : hd N X t0 ≤ X.card + N * A := by
    have a := hall (2 * t0 + 1); rw [hd_jm] at a
    have b := hd_succ (N := N) (X := X) t0
    have := x01 (t0 + 1); have := hJ' t0; linarith
  have u2 : hd N X t0 ≤ (N : Int) - X.card + N * A := by
    have e := hd_add hN hX t0
    have a := hall (2 * (t0 + N - 1) + 1); rw [hd_jm] at a
    rw [show t0 + N - 1 + 1 = t0 + N by omega, e] at a
    have b := hd_succ (N := N) (X := X) (t0 + N - 1)
    rw [show t0 + N - 1 + 1 = t0 + N by omega, e] at b
    have := x01 (t0 + N); have := hJ' (t0 + N - 1); linarith
  have l1 : -((N : Int) - X.card) - N * B ≤ hd N X t1 := by
    have a := hall' (2 * t1 + 1); rw [hd_jm] at a
    have b := hd_succ (N := N) (X := X) t1
    have := x01 (t1 + 1); have := hJ' t1; linarith
  have l2 : -(X.card : Int) - N * B ≤ hd N X t1 := by
    have e := hd_add hN hX t1
    have a := hall' (2 * (t1 + N - 1) + 1); rw [hd_jm] at a
    rw [show t1 + N - 1 + 1 = t1 + N by omega, e] at a
    have b := hd_succ (N := N) (X := X) (t1 + N - 1)
    rw [show t1 + N - 1 + 1 = t1 + N by omega, e] at b
    have := x01 (t1 + N); have := hJ' (t1 + N - 1); linarith
  have := hall t; have := hall' t
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The symmetric form: `|N P(t) - |X| t| ≤ min(|X|, N - |X|) + N B` when `|jm| ≤ B`. -/
theorem abs_hd_le_of_jm (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (B : Int)
    (hJ : ∀ k, k < N → |jm N X k| ≤ B) (t : Nat) :
    |hd N X t| ≤ min (X.card : Int) ((N : Int) - X.card) + N * B := by
  have h := hd_bounds_of_jm hN hX B B (fun k hk => by
    have := abs_le.1 (hJ k hk); exact ⟨this.1, this.2⟩) t
  rw [abs_le]
  rcases min_cases (X.card : Int) ((N : Int) - X.card) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;>
    constructor <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- `Neutral.hd_bounds` is the case `A = B = 0`. -/
theorem jm_neutral (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hn : IsNeutral N X) (k : Nat) :
    jm N X k = 0 :=
  (jm_eq_zero_iff k).2 ((neutral_iff_dbl hN hX).1 hn k)

/-! ## B. The functional graph `b ↦ 2b + 1` on `ℤ/N` -/

/-- The boundary map: panel `m = b + 1` links boundary `b = m - 1` to boundary `2m - 1`. -/
def phi (N b : Nat) : Nat := (2 * b + 1) % N

theorem phi_lt (hN : 0 < N) (b : Nat) : phi N b < N := Nat.mod_lt _ hN

theorem phi_iter_lt (hN : 0 < N) {b : Nat} (hb : b < N) : ∀ k, (phi N)^[k] b < N
  | 0 => hb
  | k + 1 => by rw [Function.iterate_succ_apply']; exact phi_lt hN _

/-- In panel coordinates `m = b + 1` the map `phi` is the doubling map:
`phi^k(b) + 1 ≡ 2^k (b + 1) (mod N)`. -/
theorem phi_iter_modEq (N b : Nat) : ∀ k, (phi N)^[k] b + 1 ≡ 2 ^ k * (b + 1) [MOD N]
  | 0 => by simp [Nat.ModEq]
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    have ih := phi_iter_modEq N b k
    have h1 : phi N ((phi N)^[k] b) + 1 ≡ 2 * ((phi N)^[k] b) + 1 + 1 [MOD N] :=
      Nat.ModEq.add_right 1 (Nat.mod_modEq _ _)
    have h2 : 2 * ((phi N)^[k] b + 1) ≡ 2 * (2 ^ k * (b + 1)) [MOD N] := ih.mul_left 2
    have e1 : 2 * ((phi N)^[k] b) + 1 + 1 = 2 * ((phi N)^[k] b + 1) := by ring
    have e2 : 2 ^ (k + 1) * (b + 1) = 2 * (2 ^ k * (b + 1)) := by ring
    rw [e2]; rw [e1] at h1; exact h1.trans h2

/-- The fixed point: boundary `N - 1`, i.e. panel `N` (whose window is empty). -/
theorem phi_fixed (hN : 0 < N) : phi N (N - 1) = N - 1 := by
  unfold phi
  rw [show 2 * (N - 1) + 1 = (N - 1) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- **Odd `N`: `phi` is a permutation of `ℤ/N`** (its cycles are the cyclotomic cosets of `2`
modulo `N`, shifted by one). -/
theorem phi_injOn (hodd : N % 2 = 1) {b b' : Nat} (hb : b < N) (hb' : b' < N)
    (h : phi N b = phi N b') : b = b' := by
  unfold phi at h
  have h1 : 2 * b + 1 ≡ 2 * b' + 1 [MOD N] := h
  have h2 : 2 * b ≡ 2 * b' [MOD N] := Nat.ModEq.add_right_cancel' 1 h1
  have hc : Nat.gcd N 2 = 1 := by
    rw [Nat.gcd_comm]; exact (Nat.coprime_two_left).2 (Nat.odd_iff.2 hodd)
  have h3 : b ≡ b' [MOD N] := Nat.ModEq.cancel_left_of_coprime hc h2
  exact Nat.ModEq.eq_of_lt_of_lt h3 hb hb'

/-- **`N = 2^L`: the graph of `phi` is a tree of depth `L`**: every boundary reaches the fixed
point `N - 1` after `L` steps. -/
theorem phi_iter_pow_two (L : Nat) {b : Nat} (hb : b < 2 ^ L) :
    (phi (2 ^ L))^[L] b = 2 ^ L - 1 := by
  have hN : 0 < 2 ^ L := by positivity
  have h := phi_iter_modEq (2 ^ L) b L
  have hlt := phi_iter_lt hN hb L
  have hdvd : 2 ^ L ∣ (phi (2 ^ L))^[L] b + 1 :=
    Nat.dvd_of_mod_eq_zero (h.trans (Nat.mul_mod_right _ _))
  have := Nat.le_of_dvd (Nat.succ_pos _) hdvd
  omega

end XdWords
end Folds
