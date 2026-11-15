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

theorem gcd_two_of_odd {q : Nat} (h : q % 2 = 1) : Nat.gcd q 2 = 1 := by
  rw [Nat.gcd_comm, Nat.gcd_rec, h]; rfl

/-- **Odd `N`: `phi` is a permutation of `ℤ/N`** (its cycles are the cyclotomic cosets of `2`
modulo `N`, shifted by one). -/
theorem phi_injOn (hodd : N % 2 = 1) {b b' : Nat} (hb : b < N) (hb' : b' < N)
    (h : phi N b = phi N b') : b = b' := by
  unfold phi at h
  have h1 : 2 * b + 1 ≡ 2 * b' + 1 [MOD N] := h
  have h2 : 2 * b ≡ 2 * b' [MOD N] := Nat.ModEq.add_right_cancel' 1 h1
  have h3 : b ≡ b' [MOD N] := Nat.ModEq.cancel_left_of_coprime (gcd_two_of_odd hodd) h2
  exact Nat.ModEq.eq_of_lt_of_lt h3 hb hb'

/-- **`N = 2^L`: the graph of `phi` is a tree of depth `L`**: every boundary reaches the fixed
point `N - 1` after `L` steps. -/
theorem phi_iter_pow_two (L : Nat) {b : Nat} (hb : b < 2 ^ L) :
    (phi (2 ^ L))^[L] b = 2 ^ L - 1 := by
  have hN : 0 < 2 ^ L := by positivity
  have h := phi_iter_modEq (2 ^ L) b L
  have hlt := phi_iter_lt hN hb L
  have hdvd : 2 ^ L ∣ (phi (2 ^ L))^[L] b + 1 :=
    Nat.dvd_of_mod_eq_zero ((show ((phi (2 ^ L))^[L] b + 1) % 2 ^ L =
      (2 ^ L * (b + 1)) % 2 ^ L from h).trans (Nat.mul_mod_right _ _))
  have := Nat.le_of_dvd (Nat.succ_pos _) hdvd
  omega

/-- **General `N`, the tree part**: if `2^a ∣ N`, after `a` steps every boundary `b` satisfies
`2^a ∣ b + 1` (it is in the periodic part when `N / 2^a` is odd). -/
theorem phi_iter_dvd {a : Nat} (ha : 2 ^ a ∣ N) (b : Nat) : 2 ^ a ∣ (phi N)^[a] b + 1 := by
  have h := (phi_iter_modEq N b a).of_dvd ha
  exact Nat.dvd_of_mod_eq_zero ((show ((phi N)^[a] b + 1) % 2 ^ a =
      (2 ^ a * (b + 1)) % 2 ^ a from h).trans (Nat.mul_mod_right _ _))

/-- **General `N = 2^a q`, `q` odd, the periodic part**: `phi` is injective on
`{b < N : 2^a ∣ b + 1}` (which it maps into itself, a copy of the doubling map on `ℤ/q`). -/
theorem phi_inj_periodic {a q : Nat} (hq : q % 2 = 1) {b b' : Nat} (hb : b < 2 ^ a * q)
    (hb' : b' < 2 ^ a * q) (hd : 2 ^ a ∣ b + 1) (hd' : 2 ^ a ∣ b' + 1)
    (h : phi (2 ^ a * q) b = phi (2 ^ a * q) b') : b = b' := by
  unfold phi at h
  obtain ⟨u, hu⟩ := hd
  obtain ⟨u', hu'⟩ := hd'
  have h1 : 2 * b + 1 + 1 ≡ 2 * b' + 1 + 1 [MOD 2 ^ a * q] := Nat.ModEq.add_right 1 h
  have e1 : 2 * b + 1 + 1 = 2 ^ a * (2 * u) := by
    rw [show 2 * b + 1 + 1 = 2 * (b + 1) by ring, hu]; ring
  have e2 : 2 * b' + 1 + 1 = 2 ^ a * (2 * u') := by
    rw [show 2 * b' + 1 + 1 = 2 * (b' + 1) by ring, hu']; ring
  rw [e1, e2] at h1
  have h2 : 2 * u ≡ 2 * u' [MOD q] := Nat.ModEq.mul_left_cancel' (by positivity) h1
  have h3 : u ≡ u' [MOD q] := Nat.ModEq.cancel_left_of_coprime (gcd_two_of_odd hq) h2
  have h4 : 2 ^ a * u ≡ 2 ^ a * u' [MOD 2 ^ a * q] := Nat.ModEq.mul_left' (2 ^ a) h3
  rw [← hu, ← hu'] at h4
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' 1 h4) hb hb'

/-! ### The orbit formula -/

/-- The binary-weighted sum `∑_{i<n} 2^(n-1-i) f i` (Horner form). -/
def osum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => 2 * osum f n + f n

theorem osum_eq_sum (f : Nat → Int) :
    ∀ n, osum f n = ∑ i ∈ Finset.range n, 2 ^ (n - 1 - i) * f i
  | 0 => by simp [osum]
  | n + 1 => by
    rw [osum, osum_eq_sum f n, Finset.sum_range_succ, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show n + 1 - 1 - i = (n - 1 - i) + 1 by omega, pow_succ]; ring
    · simp

/-- One step along the graph: `hd(phi k) = 2 hd(k) - |X| + N dfc(k)`. -/
theorem hd_phi (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (k : Nat) :
    hd N X (phi N k) = 2 * hd N X k - X.card + N * dfc N X k := by
  unfold phi; rw [← hd_mod hN hX, hd_dfc]

/-- **Orbit formula.**  Along the orbit `k, phi k, phi² k, …` of a boundary,
`2^n hd(k) = hd(phi^n k) + (2^n - 1) |X| - N ∑_{i<n} 2^(n-1-i) dfc(phi^i k)`.
Dividing by `2^n`: `hd(k)/N = |X|/N - ∑_{i ≥ 0} dfc(phi^i k) / 2^(i+1)`, a binary expansion
whose digits are the cyclic defects along the orbit. -/
theorem hd_orbit (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (k : Nat) :
    ∀ n, 2 ^ n * hd N X k = hd N X ((phi N)^[n] k) + (2 ^ n - 1) * X.card
      - N * osum (fun i => dfc N X ((phi N)^[i] k)) n
  | 0 => by simp [osum]
  | n + 1 => by
    have ih := hd_orbit hN hX k n
    rw [Function.iterate_succ_apply', hd_phi hN hX, osum, pow_succ]
    linear_combination 2 * ih

/-- **Cycle formula.**  If the boundary `k` lies on a cycle of length `n` of `phi`, then
`(2^n - 1) (|X| - hd k) = N ∑_{i<n} 2^(n-1-i) dfc(phi^i k)`. -/
theorem hd_cycle (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) {k n : Nat}
    (hc : (phi N)^[n] k = k) :
    (2 ^ n - 1) * ((X.card : Int) - hd N X k) =
      N * osum (fun i => dfc N X ((phi N)^[i] k)) n := by
  have h := hd_orbit hN hX k n
  rw [hc] at h
  linear_combination -h

theorem dfc_neutral (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hn : IsNeutral N X) (k : Nat) :
    dfc N X k = xi N X (k + 1) := by
  rw [dfc_eq_jm, jm_neutral hN hX hn]; ring

/-- For a neutral set the digits are the membership bits along the doubling orbit: the set is
the itinerary coding of the rotation by `|X|/N`. -/
theorem hd_cycle_neutral (hN : 0 < N) (hX : X ⊆ Finset.Icc 1 N) (hn : IsNeutral N X)
    {k n : Nat} (hc : (phi N)^[n] k = k) :
    (2 ^ n - 1) * ((X.card : Int) - hd N X k) =
      N * osum (fun i => (xi N X ((phi N)^[i] k + 1) : Int)) n := by
  rw [hd_cycle hN hX hc]
  have e : (fun i => dfc N X ((phi N)^[i] k)) = fun i => (xi N X ((phi N)^[i] k + 1) : Int) :=
    funext fun i => dfc_neutral hN hX hn _
  rw [e]

/-! ## C. Reachable sets -/

theorem imb_congr {N m : Nat} {S T : List Nat} (h : ∀ x, x ∈ S ↔ x ∈ T) :
    imb N S m = imb N T m := by
  unfold imb leftCount rightCount; simp only [h]

/-- Adding the panels of `T` changes the imbalance of `m` by at most `|T|`. -/
theorem imb_append_le {N m : Nat} (hm : 1 ≤ m) (hmN : m ≤ N) :
    ∀ (T S : List Nat), (T ++ S).Nodup → (∀ x ∈ T, 1 ≤ x ∧ x ≤ N) →
      |imb N (T ++ S) m - imb N S m| ≤ (T.length : Int)
  | [], S, _, _ => by simp
  | x :: T, S, hnd, hb => by
    have hnd' : (T ++ S).Nodup := (List.nodup_cons.1 hnd).2
    have hx : x ∉ T ++ S := (List.nodup_cons.1 hnd).1
    have ih := imb_append_le hm hmN T S hnd' (fun y hy => hb y (List.mem_cons_of_mem _ hy))
    have hbx := hb x List.mem_cons_self
    have e := imb_cons (N := N) (m := m) hnd' hx hbx.1 hm hmN hbx.2
    rw [List.cons_append, e, List.length_cons]
    push_cast
    rw [abs_le] at ih ⊢
    split_ifs <;> constructor <;> linarith [ih.1, ih.2]

theorem imb_mid_le {N : Nat} (A B : List Nat) (m : Nat) (hnd : (A ++ m :: B).Nodup)
    (hb : ∀ x ∈ A ++ m :: B, 1 ≤ x ∧ x ≤ N) (h0 : imb N A m = 0) :
    |imb N (A ++ m :: B) m| ≤ (B.length : Int) := by
  have hm := hb m (by simp)
  have hp : (B ++ m :: A).Perm (A ++ m :: B) :=
    List.perm_middle.trans ((List.perm_append_comm.cons m).trans List.perm_middle.symm)
  have hnd2 : (B ++ m :: A).Nodup := hp.nodup_iff.2 hnd
  have hmA : (m :: A).Nodup := hnd2.of_append_right
  have e1 : imb N (A ++ m :: B) m = imb N (B ++ m :: A) m :=
    imb_congr fun x => hp.mem_iff.symm
  have e2 : imb N (m :: A) m = imb N A m := by
    rw [imb_cons (List.nodup_cons.1 hmA).2 (List.nodup_cons.1 hmA).1 hm.1 hm.1 hm.2 hm.2]
    simp
  have h := imb_append_le hm.1 hm.2 B (m :: A) hnd2
    (fun x hx => hb x (by simp only [List.mem_append, List.mem_cons]; tauto))
  rw [e1]; rw [e2, h0, sub_zero] at h; exact h

/-- **Along a valid sequence**, the panel placed at step `k` ends with imbalance at most
`length - 1 - k` in absolute value: it was balanced when placed, and each later panel changes
its imbalance by at most one. -/
theorem imb_le_of_semiSymmetric {N : Nat} {l : List Nat} (hnd : l.Nodup)
    (hb : ∀ x ∈ l, 1 ≤ x ∧ x ≤ N) (h : SemiSymmetric N l) (k : Nat) (hk : k < l.length) :
    |imb N l l[k]| ≤ ((l.length - 1 - k : Nat) : Int) := by
  have hsplit : l.take k ++ l[k] :: l.drop (k + 1) = l := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have h0 : imb N (l.take k) l[k] = 0 := (semiStep_iff_imb N _ _).1 (h k hk)
  have key := imb_mid_le (N := N) (l.take k) (l.drop (k + 1)) l[k]
    (by rw [hsplit]; exact hnd) (by rw [hsplit]; exact hb) h0
  rw [hsplit, List.length_drop] at key
  have e : l.length - (k + 1) = l.length - 1 - k := by omega
  rw [e] at key; exact key

/-- **Parking condition.**  In the set of a valid sequence, for every `i` at least `i + 1`
panels have imbalance at most `i` in absolute value. -/
theorem parking {N : Nat} {l : List Nat} (hnd : l.Nodup) (hb : ∀ x ∈ l, 1 ≤ x ∧ x ≤ N)
    (h : SemiSymmetric N l) (i : Nat) (hi : i < l.length) :
    i + 1 ≤ (l.toFinset.filter (fun m => |imb N l m| ≤ (i : Int))).card := by
  have hsub : (l.drop (l.length - 1 - i)).toFinset ⊆
      l.toFinset.filter (fun m => |imb N l m| ≤ (i : Int)) := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
    rw [List.length_drop] at ht
    rw [List.getElem_drop, Finset.mem_filter, List.mem_toFinset]
    refine ⟨List.getElem_mem _, ?_⟩
    refine (imb_le_of_semiSymmetric hnd hb h (l.length - 1 - i + t) (by omega)).trans ?_
    exact_mod_cast (by omega : l.length - 1 - (l.length - 1 - i + t) ≤ i)
  have hc : (l.drop (l.length - 1 - i)).toFinset.card = i + 1 := by
    rw [List.toFinset_card_of_nodup (hnd.sublist (List.drop_sublist _ _)), List.length_drop]
    omega
  rw [← hc]; exact Finset.card_le_card hsub

/-- **Parking condition for reachable sets** (`0 < g N S`: `S` is the set of a valid prefix):
for every `i < |S|`, at least `i + 1` elements `m` of `S` have `|jm(m - 1)| ≤ i`. -/
theorem reachable_parking (hN : 0 < N) {S : Finset Nat} (hS : S ⊆ Finset.Icc 1 N)
    (hr : 0 < g N S) (i : Nat) (hi : i < S.card) :
    i + 1 ≤ (S.filter (fun m => |jm N S (m - 1)| ≤ (i : Int))).card := by
  obtain ⟨l, hl⟩ := Finset.card_pos.1 (show 0 < (semiOrders N S).card from hr)
  obtain ⟨⟨hnd, rfl⟩, hsemi⟩ := mem_semiOrders.1 hl
  have hb : ∀ x ∈ l, 1 ≤ x ∧ x ≤ N := fun x hx =>
    Finset.mem_Icc.1 (hS (List.mem_toFinset.2 hx))
  have hp := parking hnd hb hsemi i (by rwa [List.toFinset_card_of_nodup hnd] at hi)
  refine hp.trans (Finset.card_le_card ?_)
  intro m hm
  rw [Finset.mem_filter] at hm ⊢
  have hm' := hb m (List.mem_toFinset.1 hm.1)
  refine ⟨hm.1, ?_⟩
  rw [← imb_eq_jm hN hnd hb hm'.1 hm'.2]; exact hm.2

/-- A removable element: a nonempty reachable set contains a balanced panel. -/
theorem reachable_exists_balanced (hN : 0 < N) {S : Finset Nat} (hS : S ⊆ Finset.Icc 1 N)
    (hr : 0 < g N S) (hne : S.Nonempty) : ∃ m ∈ S, jm N S (m - 1) = 0 := by
  have h := reachable_parking hN hS hr 0 (Finset.card_pos.2 hne)
  obtain ⟨m, hm⟩ := Finset.card_pos.1 (show 0 < _ from h)
  rw [Finset.mem_filter] at hm
  exact ⟨m, hm.1, by simpa using hm.2⟩

/-- The initial intervals `[1, k]` are reachable. -/
theorem reachable_Icc {k : Nat} (hk : k < N) : 0 < g N (Finset.Icc 1 k) := by
  have h := coReach_interval (N := N) (a := k + 1) (b := N) (by omega) (by omega) le_rfl
  unfold CoReach at h
  have e : Finset.Icc 1 N \ Finset.Icc (k + 1) N = Finset.Icc 1 k := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega
  rwa [e] at h

/-- The interval `[1, k]` has discrepancy `k (N - k)` at `t = k`, the largest value possible for
a `k`-set.  With `reachable_Icc`: no bound on `max_t |hd t|` in terms of `|S|` and `N` alone
separates reachable sets from arbitrary sets. -/
theorem hd_Icc (hN : 0 < N) {k : Nat} (hk : k ≤ N) :
    hd N (Finset.Icc 1 k) k = (k : Int) * ((N : Int) - k) := by
  have hX : Finset.Icc 1 k ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc le_rfl hk
  have h := P_interval hN hX (a := 0) (b := k) (Nat.zero_le _) hk
  have e : (Finset.Icc 1 k).filter (fun x => 0 < x ∧ x ≤ k) = Finset.Icc 1 k := by
    apply Finset.filter_true_of_mem; intro x hx; rw [Finset.mem_Icc] at hx; omega
  rw [e, P_zero, Nat.card_Icc] at h
  have h' : P N (Finset.Icc 1 k) k = k := by omega
  unfold hd; rw [h', Nat.card_Icc, Nat.add_sub_cancel]; ring

/-! ## D. The canonical word is a Toeplitz word -/

/-- The one-hole Toeplitz word with hole `ρ`: `tword ρ j` is `true` at `j = ρ`; otherwise look
at the lowest binary digit where `j` and `ρ` differ, and return that digit of `ρ`. -/
def tword (ρ j : Nat) : Bool :=
  if ρ = j then true
  else if ρ % 2 = j % 2 then tword (ρ / 2) (j / 2)
  else decide (ρ % 2 = 1)
termination_by ρ + j
decreasing_by omega

theorem tword_unfold (ρ j : Nat) : tword ρ j =
    if ρ = j then true else if ρ % 2 = j % 2 then tword (ρ / 2) (j / 2)
      else decide (ρ % 2 = 1) := by
  rw [tword]

theorem tword_self (ρ : Nat) : tword ρ ρ = true := by rw [tword_unfold, if_pos rfl]

theorem tword_even_even (a b : Nat) : tword (2 * a) (2 * b) = tword a b := by
  rw [tword_unfold]
  by_cases h : a = b
  · subst h; rw [if_pos rfl, tword_self]
  · rw [if_neg (by omega), if_pos (by omega), Nat.mul_div_cancel_left _ (by norm_num),
      Nat.mul_div_cancel_left _ (by norm_num)]

theorem tword_odd_odd (a b : Nat) : tword (2 * a + 1) (2 * b + 1) = tword a b := by
  rw [tword_unfold]
  by_cases h : a = b
  · subst h; rw [if_pos rfl, tword_self]
  · rw [if_neg (by omega), if_pos (by omega), show (2 * a + 1) / 2 = a by omega,
      show (2 * b + 1) / 2 = b by omega]

theorem tword_even_odd (a b : Nat) : tword (2 * a) (2 * b + 1) = false := by
  rw [tword_unfold, if_neg (by omega), if_neg (by omega)]; simp

theorem tword_odd_even (a b : Nat) : tword (2 * a + 1) (2 * b) = true := by
  rw [tword_unfold, if_neg (by omega), if_neg (by omega)]; simp

/-- **Toeplitz property.**  Every position `j ≢ ρ (mod 2^i)` lies in a `2^i`-periodic part of
the word: after stage `i` of the construction only the residue class of `ρ` mod `2^i` is
undetermined. -/
theorem tword_add_pow : ∀ (i ρ j : Nat), j % 2 ^ i ≠ ρ % 2 ^ i →
    tword ρ (j + 2 ^ i) = tword ρ j
  | 0, ρ, j, h => by simp [Nat.mod_one] at h
  | i + 1, ρ, j, h => by
    have hp : 2 ^ (i + 1) = 2 * 2 ^ i := pow_succ' 2 i
    have hj := Nat.mod_mul (x := j) (a := 2) (b := 2 ^ i)
    have hr := Nat.mod_mul (x := ρ) (a := 2) (b := 2 ^ i)
    rw [hp] at h
    have h1 : ρ ≠ j := fun e => h (by rw [e])
    have h2 : ρ ≠ j + 2 * 2 ^ i := fun e => h (by rw [e, Nat.add_mod_right])
    have hpar : (j + 2 * 2 ^ i) % 2 = j % 2 := by omega
    have hhalf : (j + 2 * 2 ^ i) / 2 = j / 2 + 2 ^ i := by omega
    rw [tword_unfold ρ (j + 2 ^ (i + 1)), tword_unfold ρ j, hp, if_neg h2, if_neg h1, hpar,
      hhalf]
    by_cases hq : ρ % 2 = j % 2
    · rw [if_pos hq, if_pos hq]
      exact tword_add_pow i (ρ / 2) (j / 2) (by omega)
    · rw [if_neg hq, if_neg hq]

open Gen in
theorem canon_word_aux : ∀ (N k c m : Nat), (gen canon N)[k]? = some c → 1 ≤ m → m ≤ N →
    (m ∈ (gen canon N).take (k + 1) ↔ tword (c - 1) (m - 1) = true) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k c m hc hm1 hmN
    rcases Nat.lt_or_ge N 2 with hN | hN
    · have hN1 : N = 1 := by omega
      subst hN1
      have hm : m = 1 := by omega
      subst hm
      have e : gen canon 1 = [1] := by rw [gen_small (by omega)]; rfl
      rw [e] at hc ⊢
      rcases k with _ | k
      · simp at hc; subst hc; simp [tword_self]
      · simp at hc
    · have hA := length_gen canon ((N + 1) / 2)
      have hmemA : ∀ y, y ∈ gen canon ((N + 1) / 2) ↔ 1 ≤ y ∧ y ≤ (N + 1) / 2 := fun y =>
        mem_range'_of_perm (gen_valid canon ((N + 1) / 2)).1
      have hmemB : ∀ y, y ∈ gen canon (N / 2) ↔ 1 ≤ y ∧ y ≤ N / 2 := fun y =>
        mem_range'_of_perm (gen_valid canon (N / 2)).1
      rw [gen_canon_unfold] at hc ⊢
      rcases Nat.lt_or_ge k ((N + 1) / 2) with hk | hk
      · -- the `(k+1)`-st panel is in the odd block
        rw [List.getElem?_append_left (by rw [List.length_map, hA]; exact hk),
          List.getElem?_map, Option.map_eq_some_iff] at hc
        obtain ⟨c', hc', rfl⟩ := hc
        have hcb := (hmemA c').1 (List.mem_of_getElem? hc')
        rw [List.take_append_of_le_length (by rw [List.length_map, hA]; omega),
          ← List.map_take, List.mem_map]
        rcases Nat.even_or_odd' m with ⟨m', rfl | rfl⟩
        · -- `m` even: not in the odd block
          have e1 : scale 1 c' - 1 = 2 * (c' - 1) := by unfold scale; omega
          have e2 : 2 * m' - 1 = 2 * (m' - 1) + 1 := by omega
          rw [e1, e2, tword_even_odd]
          constructor
          · rintro ⟨y, hy, hy2⟩
            have := (hmemA y).1 (List.mem_of_mem_take hy)
            unfold scale at hy2; omega
          · intro h; exact absurd h (by simp)
        · -- `m = 2m' + 1` odd
          have e1 : scale 1 c' - 1 = 2 * (c' - 1) := by unfold scale; omega
          have e2 : 2 * m' + 1 - 1 = 2 * (m' + 1 - 1) := by omega
          rw [e1, e2, tword_even_even,
            ← ih ((N + 1) / 2) (by omega) k c' (m' + 1) hc' (by omega) (by omega)]
          constructor
          · rintro ⟨y, hy, hy2⟩
            have := (hmemA y).1 (List.mem_of_mem_take hy)
            have : y = m' + 1 := by unfold scale at hy2; omega
            rw [← this]; exact hy
          · intro h; exact ⟨m' + 1, h, by unfold scale; omega⟩
      · -- the `(k+1)`-st panel is in the even block
        rw [List.getElem?_append_right (by rw [List.length_map, hA]; exact hk),
          List.getElem?_map, Option.map_eq_some_iff, List.length_map, hA] at hc
        obtain ⟨c', hc', rfl⟩ := hc
        have hcb := (hmemB c').1 (List.mem_of_getElem? hc')
        rw [List.take_append, List.mem_append, List.length_map, hA,
          List.take_of_length_le (by rw [List.length_map, hA]; omega), ← List.map_take,
          List.mem_map, List.mem_map]
        rcases Nat.even_or_odd' m with ⟨m', rfl | rfl⟩
        · -- `m = 2m'` even
          have e1 : scale 0 c' - 1 = 2 * (c' - 1) + 1 := by unfold scale; omega
          have e2 : 2 * m' - 1 = 2 * (m' - 1) + 1 := by omega
          have e3 : k + 1 - (N + 1) / 2 = k - (N + 1) / 2 + 1 := by omega
          rw [e1, e2, tword_odd_odd, e3,
            ← ih (N / 2) (by omega) (k - (N + 1) / 2) c' m' hc' (by omega) (by omega)]
          constructor
          · rintro (⟨y, hy, hy2⟩ | ⟨y, hy, hy2⟩)
            · have := (hmemA y).1 hy
              unfold scale at hy2; omega
            · have : y = m' := by unfold scale at hy2; omega
              rw [← this]; exact hy
          · intro h; exact Or.inr ⟨m', h, by unfold scale; omega⟩
        · -- `m = 2m' + 1` odd: in the odd block, which is complete
          have e1 : scale 0 c' - 1 = 2 * (c' - 1) + 1 := by unfold scale; omega
          have e2 : 2 * m' + 1 - 1 = 2 * m' := by omega
          rw [e1, e2, tword_odd_even]
          exact iff_of_true
            (Or.inl ⟨m' + 1, (hmemA _).2 (by omega), by unfold scale; omega⟩) rfl

open Gen in
/-- **The canonical word is a Toeplitz word.**  Let `c` be the `(k+1)`-st panel of the truncated
bit-reversal order `gen canon N`.  The set of the first `k + 1` panels is
`{m ∈ [1, N] : tword (c - 1) (m - 1)}`: its indicator word is the length-`N` prefix of the
one-hole Toeplitz word with hole `c - 1`. -/
theorem canon_prefix_word (N k : Nat) (hk : k < (gen canon N).length) {m : Nat} (hm1 : 1 ≤ m)
    (hmN : m ≤ N) :
    m ∈ (gen canon N).take (k + 1) ↔ tword ((gen canon N)[k] - 1) (m - 1) = true :=
  canon_word_aux N k _ m (List.getElem?_eq_getElem hk) hm1 hmN

end XdWords
end Folds
