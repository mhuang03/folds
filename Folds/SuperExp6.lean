import Mathlib.Algebra.BigOperators.Fin
import Folds.Growth

/-!
# Generalised composition: residue classes of an arbitrary strip

`semiCount_comp` (Growth.lean) places the residue classes mod `q` of the `nq`-strip as
blocks.  Here `q` need not divide `N`: for `N = n q + ρ` (`ρ < q`) the class `t` has
`sz n ρ t = n + [t ≤ ρ]` panels, every class is a window-embedded copy of its own strip,
and the mirror `x ↦ N + 1 - x` maps class `t` to class `mst q ρ t`.  A set `R` of complete
classes is balanced around the left-half panels of class `s` iff `(R, s)` is a valid step of
the `q`-strip, and around the right-half panels iff `(mst R, mst s)` is.  Hence
(`semiCount_gcomp`): if `π` and `π.map (mst q ρ)` are both valid `q`-sequences, then
`∏ₛ a(sz n ρ s) ≤ a(nq + ρ)`.

Instances: `a(n+1) a(n)² ≤ a(3n+1)` and `a(n+1)² a(n) ≤ a(3n+2)` (`semiCount_three_one`,
`semiCount_three_two`).

See `experiments/superexp6/PROOFS.txt`.
-/

namespace Folds
namespace GComp

/-- Number of panels of class `t` (mod `q`) in `[1..n q + ρ]`. -/
def sz (n ρ t : Nat) : Nat := if t ≤ ρ then n + 1 else n

/-- The class of the mirror images of the panels of class `t`. -/
def mst (q ρ t : Nat) : Nat := if t ≤ ρ then ρ + 1 - t else q + ρ + 1 - t

theorem mst_bounds {q ρ t : Nat} (hρ : ρ < q) (ht1 : 1 ≤ t) (htq : t ≤ q) :
    1 ≤ mst q ρ t ∧ mst q ρ t ≤ q := by unfold mst; split <;> omega

theorem mst_mst {q ρ t : Nat} (hρ : ρ < q) (ht1 : 1 ≤ t) (htq : t ≤ q) :
    mst q ρ (mst q ρ t) = t := by unfold mst; split <;> split <;> omega

theorem sz_mst {q n ρ t : Nat} (_hρ : ρ < q) (ht1 : 1 ≤ t) (htq : t ≤ q) :
    sz n ρ (mst q ρ t) = sz n ρ t := by unfold sz mst; split <;> split <;> omega

/-- The panels of class `t`, in increasing order. -/
def cpanels (q n ρ t : Nat) : List Nat := (List.range' 1 (sz n ρ t)).map (cls q t)

theorem ccount_top' {q n ρ t : Nat} (hq : 0 < q) (hρ : ρ < q) (ht1 : 1 ≤ t) (htq : t ≤ q) :
    ccount q t (n * q + ρ) = sz n ρ t := by
  unfold ccount sz
  rw [show n * q + ρ + q - t = (ρ + q - t) + n * q by omega, Nat.add_mul_div_right _ _ hq]
  split
  · rw [div_small (k := 1) (by omega) (by omega)]; omega
  · rw [Nat.div_eq_of_lt (by omega)]; omega

theorem ccount_le_sz {q n ρ t z : Nat} (hq : 0 < q) (hρ : ρ < q) (ht1 : 1 ≤ t) (htq : t ≤ q)
    (hz : z ≤ n * q + ρ) : ccount q t z ≤ sz n ρ t :=
  ccount_top' (n := n) hq hρ ht1 htq ▸ ccount_mono hz

theorem countP_cpanels {q n ρ t z : Nat} (hq : 0 < q) (hρ : ρ < q) (ht1 : 1 ≤ t) (htq : t ≤ q)
    (hz : z ≤ n * q + ρ) :
    (cpanels q n ρ t).countP (fun u => decide (u ≤ z)) = ccount q t z := by
  unfold cpanels
  rw [List.countP_map]
  have e : (List.range' 1 (sz n ρ t)).countP ((fun u => decide (u ≤ z)) ∘ cls q t) =
      (List.range' 1 (sz n ρ t)).countP (fun y => decide (1 ≤ y ∧ y ≤ ccount q t z)) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    rw [cls_le_iff hq htq hy.1]; omega
  rw [e, countP_range'_interval]
  have := ccount_le_sz (n := n) hq hρ ht1 htq hz
  omega

theorem cls_mirror' {q n ρ s j : Nat} (_hρ : ρ < q) (_hs1 : 1 ≤ s) (hsq : s ≤ q) (hj1 : 1 ≤ j)
    (hjn : j ≤ sz n ρ s) :
    cls q (mst q ρ s) (sz n ρ s + 1 - j) + cls q s j = n * q + ρ + 1 := by
  unfold cls
  by_cases h : s ≤ ρ
  · simp only [mst, sz, h, ite_true] at hjn ⊢
    have e : (n + 1 + 1 - j - 1) * q + (j - 1) * q = n * q := by
      rw [← Nat.add_mul]; congr 1; omega
    omega
  · simp only [mst, sz, h, ite_false] at hjn ⊢
    have e : (n + 1 - j - 1) * q + (j - 1) * q + q = n * q := by
      rw [← Nat.add_mul, ← Nat.succ_mul]; congr 1; omega
    omega

/-- Mirror identity for the class counts. -/
theorem ccount_mirror' {q n ρ t z : Nat} (hq : 0 < q) (hρ : ρ < q) (ht1 : 1 ≤ t) (htq : t ≤ q)
    (hz : z ≤ n * q + ρ) :
    ccount q t z + ccount q (mst q ρ t) (n * q + ρ - z) = sz n ρ t := by
  have hle := ccount_le_sz (n := n) hq hρ ht1 htq hz
  have hdm := Nat.div_add_mod (z + q - t) q
  have hb : (z + q - t) % q < q := Nat.mod_lt _ hq
  unfold ccount at hle ⊢
  generalize (z + q - t) / q = a at hdm hle ⊢
  generalize (z + q - t) % q = b at hdm hb
  rw [Nat.mul_comm] at hdm
  by_cases h : t ≤ ρ
  · simp only [mst, sz, h, ite_true] at hle ⊢
    have hsub : (n + 1 - a) * q + a * q = n * q + q := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hle, Nat.succ_mul]
    rw [show n * q + ρ - z + q - (ρ + 1 - t) = (q - 1 - b) + (n + 1 - a) * q by omega,
      Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt (by omega)]
    omega
  · simp only [mst, sz, h, ite_false] at hle ⊢
    have hsub : (n - a) * q + a * q = n * q := by rw [← Nat.add_mul, Nat.sub_add_cancel hle]
    rw [show n * q + ρ - z + q - (q + ρ + 1 - t) = (q - 1 - b) + (n - a) * q by omega,
      Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt (by omega)]
    omega

theorem cls_bounds' {q n ρ s j : Nat} (hq : 0 < q) (hρ : ρ < q) (hs1 : 1 ≤ s) (hsq : s ≤ q)
    (hj1 : 1 ≤ j) (hjn : j ≤ sz n ρ s) : 1 ≤ cls q s j ∧ cls q s j ≤ n * q + ρ := by
  refine ⟨by unfold cls; omega, ?_⟩
  rw [cls_le_iff hq hsq hj1, ccount_top' hq hρ hs1 hsq]; exact hjn

/-- The two window arms of `x` in the `N`-strip, counted on a list `U`. -/
abbrev armL (N x : Nat) (U : List Nat) : Nat :=
  U.countP (fun u => decide (x - reach N x ≤ u ∧ u < x))
abbrev armR (N x : Nat) (U : List Nat) : Nat :=
  U.countP (fun u => decide (x < u ∧ u ≤ x + reach N x))

/-- Arm counts of a class in terms of `ccount`. -/
theorem arms_ccount {q n ρ t x : Nat} (hq : 0 < q) (hρ : ρ < q) (ht1 : 1 ≤ t) (htq : t ≤ q)
    (hx1 : 1 ≤ x) (hxN : x ≤ n * q + ρ) :
    armL (n * q + ρ) x (cpanels q n ρ t) + ccount q t (x - reach (n * q + ρ) x - 1) =
      ccount q t (x - 1) ∧
    armR (n * q + ρ) x (cpanels q n ρ t) + ccount q t x =
      ccount q t (x + reach (n * q + ρ) x) := by
  have hr : reach (n * q + ρ) x ≤ x - 1 ∧ reach (n * q + ρ) x ≤ n * q + ρ - x := by
    unfold reach; omega
  have i1 := countP_interval_add (cpanels q n ρ t) (lo := x - reach (n * q + ρ) x)
    (hi := x - 1) (by omega)
  rw [countP_succ_le (by omega), countP_cpanels hq hρ ht1 htq (by omega),
    countP_cpanels hq hρ ht1 htq (by omega)] at i1
  have i2 := countP_interval_add (cpanels q n ρ t) (lo := x + 1)
    (hi := x + reach (n * q + ρ) x) (by omega)
  rw [countP_succ_le (by omega), countP_cpanels hq hρ ht1 htq (by omega),
    countP_cpanels hq hρ ht1 htq (by omega), show x + 1 - 1 = x by omega] at i2
  have e1 : armL (n * q + ρ) x (cpanels q n ρ t) = (cpanels q n ρ t).countP
      (fun u => decide (x - reach (n * q + ρ) x ≤ u ∧ u ≤ x - 1)) := by
    apply List.countP_congr; intro u _; simp; omega
  have e2 : armR (n * q + ρ) x (cpanels q n ρ t) = (cpanels q n ρ t).countP
      (fun u => decide (x + 1 ≤ u ∧ u ≤ x + reach (n * q + ρ) x)) := by
    apply List.countP_congr; intro u _; simp; omega
  constructor <;> omega

/-- **Class identity, left half.**  For `x = cls q s j` with `x - 1 ≤ N - x` the imbalance
of class `t` around `x` is the indicator imbalance of `t` around `s` in the `q`-strip. -/
theorem class_identity_left {q n ρ s t j : Nat} (hq : 0 < q) (hρ : ρ < q) (hs1 : 1 ≤ s)
    (hsq : s ≤ q) (ht1 : 1 ≤ t) (htq : t ≤ q) (hj1 : 1 ≤ j) (hjn : j ≤ sz n ρ s)
    (hle : cls q s j - 1 ≤ n * q + ρ - cls q s j) :
    armL (n * q + ρ) (cls q s j) (cpanels q n ρ t) + (if s < t ∧ t ≤ s + reach q s then 1 else 0) =
    armR (n * q + ρ) (cls q s j) (cpanels q n ρ t) +
      (if s - reach q s ≤ t ∧ t < s then 1 else 0) := by
  obtain ⟨hx1, hxN⟩ := cls_bounds' hq hρ hs1 hsq hj1 hjn
  obtain ⟨v1, v2, v3⟩ := ccount_vals (j := j) hq hs1 hsq ht1 htq
  obtain ⟨a1, a2⟩ := arms_ccount (n := n) (t := t) hq hρ ht1 htq hx1 hxN
  generalize cls q s j = x at *
  have hr' : reach (n * q + ρ) x = x - 1 := by unfold reach; omega
  rw [hr'] at a1 a2
  rw [show x - (x - 1) - 1 = 0 by omega, ccount_zero ht1 htq] at a1
  rw [show x + (x - 1) = 2 * x - 1 by omega] at a2
  have rq : reach q s = min (s - 1) (q - s) := rfl
  rw [rq]; split_ifs at v1 v2 v3 ⊢ <;> omega

/-- **Class identity, right half.**  For `N - x ≤ x - 1` the imbalance of class `t` around
`x = cls q s j` is the indicator imbalance of `mst t` around `mst s` in the `q`-strip
(with the arms exchanged): the mirror `x ↦ N + 1 - x` maps class `t` to class `mst t`. -/
theorem class_identity_right {q n ρ s t j : Nat} (hq : 0 < q) (hρ : ρ < q) (hs1 : 1 ≤ s)
    (hsq : s ≤ q) (ht1 : 1 ≤ t) (htq : t ≤ q) (hj1 : 1 ≤ j) (hjn : j ≤ sz n ρ s)
    (hge : n * q + ρ - cls q s j ≤ cls q s j - 1) :
    armL (n * q + ρ) (cls q s j) (cpanels q n ρ t) +
      (if mst q ρ s - reach q (mst q ρ s) ≤ mst q ρ t ∧ mst q ρ t < mst q ρ s then 1 else 0) =
    armR (n * q + ρ) (cls q s j) (cpanels q n ρ t) +
      (if mst q ρ s < mst q ρ t ∧ mst q ρ t ≤ mst q ρ s + reach q (mst q ρ s) then 1 else 0) := by
  obtain ⟨hx1, hxN⟩ := cls_bounds' hq hρ hs1 hsq hj1 hjn
  obtain ⟨a1, a2⟩ := arms_ccount (n := n) (t := t) hq hρ ht1 htq hx1 hxN
  have hmir := cls_mirror' (n := n) hρ hs1 hsq hj1 hjn
  obtain ⟨s1, s2⟩ := mst_bounds hρ hs1 hsq
  obtain ⟨t1, t2⟩ := mst_bounds hρ ht1 htq
  obtain ⟨w1, w2, w3⟩ := ccount_vals (j := sz n ρ s + 1 - j) (s := mst q ρ s) (t := mst q ρ t)
    hq s1 s2 t1 t2
  have top := ccount_top' (n := n) hq hρ ht1 htq
  generalize cls q s j = x at *
  generalize cls q (mst q ρ s) (sz n ρ s + 1 - j) = x' at *
  have hr' : reach (n * q + ρ) x = n * q + ρ - x := by unfold reach; omega
  rw [hr'] at a1 a2
  rw [show x + (n * q + ρ - x) = n * q + ρ by omega, top] at a2
  rw [show x - (n * q + ρ - x) - 1 = 2 * x - (n * q + ρ) - 1 by omega] at a1
  have m1 := ccount_mirror' (n := n) (z := x - 1) hq hρ ht1 htq (by omega)
  have m2 := ccount_mirror' (n := n) (z := 2 * x - (n * q + ρ) - 1) hq hρ ht1 htq (by omega)
  have m3 := ccount_mirror' (n := n) (z := x) hq hρ ht1 htq (by omega)
  rw [show n * q + ρ - (x - 1) = x' by omega] at m1
  rw [show n * q + ρ - (2 * x - (n * q + ρ) - 1) = 2 * x' - 1 by omega] at m2
  rw [show n * q + ρ - x = x' - 1 by omega] at m3
  have rq : reach q (mst q ρ s) = min (mst q ρ s - 1) (q - mst q ρ s) := rfl
  rw [rq]
  generalize mst q ρ s = s' at *
  generalize mst q ρ t = t' at *
  split_ifs at w1 w2 w3 ⊢ <;> omega

/-- The union of the classes in `R`, class by class. -/
def cunion (q n ρ : Nat) (R : List Nat) : List Nat := (R.map (cpanels q n ρ)).flatten

theorem cunion_identity_left {q n ρ s j : Nat} (hq : 0 < q) (hρ : ρ < q) (hs1 : 1 ≤ s)
    (hsq : s ≤ q) (hj1 : 1 ≤ j) (hjn : j ≤ sz n ρ s)
    (hle : cls q s j - 1 ≤ n * q + ρ - cls q s j) : ∀ R : List Nat, (∀ t ∈ R, 1 ≤ t ∧ t ≤ q) →
    armL (n * q + ρ) (cls q s j) (cunion q n ρ R) +
      R.countP (fun t => decide (s < t ∧ t ≤ s + reach q s)) =
    armR (n * q + ρ) (cls q s j) (cunion q n ρ R) +
      R.countP (fun t => decide (s - reach q s ≤ t ∧ t < s))
  | [], _ => by simp [cunion]
  | t :: R, hR => by
    have ih := cunion_identity_left hq hρ hs1 hsq hj1 hjn hle R (fun t ht => hR t (by simp [ht]))
    have ht := hR t (by simp)
    have ci := class_identity_left (t := t) hq hρ hs1 hsq ht.1 ht.2 hj1 hjn hle
    simp only [cunion, armL, armR, List.map_cons, List.flatten_cons, List.countP_append,
      List.countP_cons] at ih ci ⊢
    split_ifs at ci ⊢ <;> simp_all <;> omega

theorem cunion_identity_right {q n ρ s j : Nat} (hq : 0 < q) (hρ : ρ < q) (hs1 : 1 ≤ s)
    (hsq : s ≤ q) (hj1 : 1 ≤ j) (hjn : j ≤ sz n ρ s)
    (hge : n * q + ρ - cls q s j ≤ cls q s j - 1) : ∀ R : List Nat, (∀ t ∈ R, 1 ≤ t ∧ t ≤ q) →
    armL (n * q + ρ) (cls q s j) (cunion q n ρ R) +
      (R.map (mst q ρ)).countP (fun t => decide (mst q ρ s - reach q (mst q ρ s) ≤ t ∧
        t < mst q ρ s)) =
    armR (n * q + ρ) (cls q s j) (cunion q n ρ R) +
      (R.map (mst q ρ)).countP (fun t => decide (mst q ρ s < t ∧
        t ≤ mst q ρ s + reach q (mst q ρ s)))
  | [], _ => by simp [cunion]
  | t :: R, hR => by
    have ih := cunion_identity_right hq hρ hs1 hsq hj1 hjn hge R (fun t ht => hR t (by simp [ht]))
    have ht := hR t (by simp)
    have ci := class_identity_right (t := t) hq hρ hs1 hsq ht.1 ht.2 hj1 hjn hge
    simp only [cunion, armL, armR, List.map_cons, List.flatten_cons, List.countP_append,
      List.countP_cons] at ih ci ⊢
    split_ifs at ci ⊢ <;> simp_all <;> omega

theorem mst_nodup {q ρ : Nat} (hρ : ρ < q) {R : List Nat} (hR : ∀ t ∈ R, 1 ≤ t ∧ t ≤ q)
    (hnd : R.Nodup) : (R.map (mst q ρ)).Nodup :=
  nodup_map_of_injOn hnd fun x hx y hy e => by
    have a := mst_mst hρ (hR x hx).1 (hR x hx).2
    have b := mst_mst hρ (hR y hy).1 (hR y hy).2
    rw [e] at a; omega

/-- **Class balance.**  If `(R, s)` and `(mst R, mst s)` are valid steps of the `q`-strip,
the complete classes `R` are balanced around every panel of class `s`. -/
theorem cunion_balanced {q n ρ s j : Nat} {R : List Nat} (hq : 0 < q) (hρ : ρ < q)
    (hs1 : 1 ≤ s) (hsq : s ≤ q) (hj1 : 1 ≤ j) (hjn : j ≤ sz n ρ s)
    (hR : ∀ t ∈ R, 1 ≤ t ∧ t ≤ q) (hnd : R.Nodup) (hstep : SemiStep q R s)
    (hstep' : SemiStep q (R.map (mst q ρ)) (mst q ρ s)) :
    Balanced (n * q + ρ) (cunion q n ρ R) (cls q s j) := by
  unfold Balanced
  rcases Nat.le_total (cls q s j - 1) (n * q + ρ - cls q s j) with hle | hge
  · have := cunion_identity_left hq hρ hs1 hsq hj1 hjn hle R hR
    unfold SemiStep at hstep
    rw [leftCount_eq hnd, rightCount_eq hnd] at hstep
    simp only [armL, armR] at this
    omega
  · have := cunion_identity_right hq hρ hs1 hsq hj1 hjn hge R hR
    unfold SemiStep at hstep'
    rw [leftCount_eq (mst_nodup hρ hR hnd), rightCount_eq (mst_nodup hρ hR hnd)] at hstep'
    simp only [armL, armR] at this
    omega

/-- Each class is a window-embedded copy of its own strip. -/
theorem winEmb_cls' {q n ρ s : Nat} (hq : 0 < q) (hρ : ρ < q) (hs1 : 1 ≤ s) (hsq : s ≤ q) :
    WinEmb (n * q + ρ) (sz n ρ s) (cls q s) := by
  have self : ∀ j, 1 ≤ j → ccount q s (cls q s j) = j := fun j _ => by
    have := (ccount_vals (j := j) hq hs1 hsq hs1 hsq).2.1; simp at this; omega
  have dbl : ∀ j, 1 ≤ j → ccount q s (2 * cls q s j - 1) = 2 * j - 1 := fun j hj => by
    have := (ccount_vals (j := j) hq hs1 hsq hs1 hsq).2.2
    rw [this]; split_ifs <;> omega
  obtain ⟨s1, s2⟩ := mst_bounds hρ hs1 hsq
  have dbl' : ∀ j, 1 ≤ j → ccount q (mst q ρ s) (2 * cls q (mst q ρ s) j - 1) = 2 * j - 1 :=
    fun j hj => by
      have := (ccount_vals (j := j) hq s1 s2 s1 s2).2.2
      rw [this]; split_ifs <;> omega
  have top := ccount_top' (n := n) hq hρ hs1 hsq
  have tops := ccount_top' (n := n) hq hρ s1 s2
  rw [sz_mst hρ hs1 hsq] at tops
  refine ⟨fun y h1 h2 => cls_bounds' hq hρ hs1 hsq h1 h2, fun x y hx1 _ hy1 _ e => ?_, ?_, ?_⟩
  · have a := self x hx1; have b := self y hy1; rw [e] at a; omega
  all_goals
    intro j y hj1 hjn hy1 hyn
    obtain ⟨hx1, hxN⟩ := cls_bounds' hq hρ hs1 hsq hj1 hjn
    have hmir := cls_mirror' (n := n) hρ hs1 hsq hj1 hjn
    have d1 := dbl j hj1
    have d2 := dbl' (sz n ρ s + 1 - j) (by omega)
    have sj := self j hj1
    have sj' : ccount q s (cls q s j - 1) = j - 1 := by
      have := (ccount_vals (j := j) hq hs1 hsq hs1 hsq).1; simp at this; omega
    have c1 := cls_le_iff (z := cls q s j - 1) hq hsq hy1
    have c2 := cls_le_iff (z := cls q s j) hq hsq hy1
    have mn : ∀ z, z ≤ n * q + ρ → ccount q s z ≤ sz n ρ s := fun z hz => top ▸ ccount_mono hz
    have mn' : ∀ z, z ≤ n * q + ρ → ccount q (mst q ρ s) z ≤ sz n ρ s :=
      fun z hz => tops ▸ ccount_mono hz
    generalize cls q s j = x at *
    generalize cls q (mst q ρ s) (sz n ρ s + 1 - j) = x' at *
    rcases Nat.le_total (x - 1) (n * q + ρ - x) with hle | hle
    · have hr : reach (n * q + ρ) x = x - 1 := by unfold reach; omega
      have := mn (2 * x - 1) (by omega)
      have hrn : reach (sz n ρ s) j = j - 1 := by unfold reach; omega
      rw [hr, hrn]
      first
      | (have c3 := cls_le_iff (z := x - (x - 1) - 1) hq hsq hy1
         rw [show x - (x - 1) - 1 = 0 by omega, ccount_zero hs1 hsq] at c3
         omega)
      | (have c3 := cls_le_iff (z := x + (x - 1)) hq hsq hy1
         rw [show x + (x - 1) = 2 * x - 1 by omega, d1] at c3
         omega)
    · have hr : reach (n * q + ρ) x = n * q + ρ - x := by unfold reach; omega
      have := mn' (2 * x' - 1) (by omega)
      have m2 := ccount_mirror' (n := n) (z := 2 * x - (n * q + ρ) - 1) hq hρ hs1 hsq (by omega)
      rw [show n * q + ρ - (2 * x - (n * q + ρ) - 1) = 2 * x' - 1 by omega, d2] at m2
      have hrn : reach (sz n ρ s) j = sz n ρ s - j := by unfold reach; omega
      rw [hr, hrn]
      first
      | (have c3 := cls_le_iff (z := x - (n * q + ρ - x) - 1) hq hsq hy1
         rw [show x - (n * q + ρ - x) - 1 = 2 * x - (n * q + ρ) - 1 by omega] at c3
         omega)
      | (have c3 := cls_le_iff (z := x + (n * q + ρ - x)) hq hsq hy1
         rw [show x + (n * q + ρ - x) = n * q + ρ by omega, top] at c3
         omega)

/-! ## The composed sequences -/

theorem blocks_perm' {q n ρ : Nat} {σ : Nat → List Nat} : ∀ π : List Nat,
    (∀ s ∈ π, IsFoldSeq (sz n ρ s) (σ s)) → (blocks q π σ).Perm (cunion q n ρ π)
  | [], _ => by simp [blocks, cunion]
  | s :: π, h => by
    simp only [blocks, cunion, List.map_cons, List.flatten_cons] at *
    exact ((h s (by simp)).map _).append (blocks_perm' π fun t ht => h t (by simp [ht]))

theorem length_cunion {q n ρ : Nat} : ∀ R : List Nat,
    (cunion q n ρ R).length = (R.map (sz n ρ)).sum
  | [] => by simp [cunion]
  | t :: R => by
    have := length_cunion (q := q) (n := n) (ρ := ρ) R
    simp only [cunion, List.map_cons, List.flatten_cons, List.length_append,
      List.sum_cons] at *
    rw [this]; simp [cpanels]

theorem sum_sz (n ρ : Nat) : ∀ k, ((List.range' 1 k).map (sz n ρ)).sum = k * n + min k ρ
  | 0 => by simp
  | k + 1 => by
    rw [List.range'_concat, List.map_append, List.sum_append, sum_sz n ρ k]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sz]
    split <;> rw [Nat.succ_mul] <;> omega

theorem cunion_cover {q n ρ : Nat} (hq : 0 < q) (hρ : ρ < q) :
    (cunion q n ρ (List.range' 1 q)).Perm (List.range' 1 (n * q + ρ)) := by
  have sub : List.range' 1 (n * q + ρ) ⊆ cunion q n ρ (List.range' 1 q) := by
    intro u hu
    rw [List.mem_range'_1] at hu
    simp only [cunion, List.mem_flatten, List.mem_map]
    refine ⟨cpanels q n ρ ((u - 1) % q + 1), ⟨(u - 1) % q + 1, List.mem_range'_1.2
      ⟨by omega, by have := Nat.mod_lt (u - 1) hq; omega⟩, rfl⟩, ?_⟩
    have hd := Nat.div_add_mod' (u - 1) q
    have hmod := Nat.mod_lt (u - 1) hq
    generalize (u - 1) / q = d at hd ⊢
    generalize (u - 1) % q = r at hd hmod ⊢
    have hsz : d + 1 ≤ sz n ρ (r + 1) := by
      have h1 := cls_le_iff (t := r + 1) (y := d + 1) (z := n * q + ρ) hq (by omega) (by omega)
      rw [ccount_top' hq hρ (by omega) (by omega)] at h1
      apply h1.1; unfold cls; rw [Nat.add_sub_cancel]; omega
    simp only [cpanels, List.mem_map, List.mem_range'_1]
    exact ⟨d + 1, ⟨by omega, by omega⟩, by unfold cls; rw [Nat.add_sub_cancel]; omega⟩
  refine ((List.subperm_of_subset (List.nodup_range' ..) sub).perm_of_length_le ?_).symm
  rw [length_cunion, sum_sz, Nat.min_eq_right hρ.le, Nat.mul_comm]; simp

theorem isFoldSeq_blocks' {q n ρ : Nat} (hq : 0 < q) (hρ : ρ < q) {π : List Nat}
    {σ : Nat → List Nat} (hπ : IsFoldSeq q π)
    (hσ : ∀ s, 1 ≤ s → s ≤ q → IsFoldSeq (sz n ρ s) (σ s)) :
    IsFoldSeq (n * q + ρ) (blocks q π σ) :=
  (blocks_perm' π fun s hs => hσ s ((mem_range'_of_perm hπ).1 hs).1
    ((mem_range'_of_perm hπ).1 hs).2).trans
    ((List.Perm.flatten (hπ.map _)).trans (cunion_cover hq hρ))

/-- **Generalised composition.**  If `π` and `π.map (mst q ρ)` are valid for `q` and every
`σ s` is valid for `sz n ρ s`, the composed sequence is valid for `n q + ρ`. -/
theorem semiSymmetric_blocks' {q n ρ : Nat} (hq : 0 < q) (hρ : ρ < q) {π : List Nat}
    {σ : Nat → List Nat} (hπ : IsFoldSeq q π) (hπs : SemiSymmetric q π)
    (hπm : SemiSymmetric q (π.map (mst q ρ)))
    (hσ : ∀ s, 1 ≤ s → s ≤ q → IsFoldSeq (sz n ρ s) (σ s) ∧ SemiSymmetric (sz n ρ s) (σ s)) :
    SemiSymmetric (n * q + ρ) (blocks q π σ) := by
  have hall := nodup_of_foldSeq (isFoldSeq_blocks' hq hρ hπ fun s h1 h2 => (hσ s h1 h2).1)
  have bπ : ∀ s ∈ π, 1 ≤ s ∧ s ≤ q := fun s hs => (mem_range'_of_perm hπ).1 hs
  have hndπ := nodup_of_foldSeq hπ
  suffices H : ∀ k, k ≤ π.length → SemiSymmetric (n * q + ρ) (blocks q (π.take k) σ) by
    simpa using H π.length le_rfl
  intro k
  induction k with
  | zero => intro _ i hi; simp [blocks] at hi
  | succ k ih =>
    intro hk
    have hkl : k < π.length := by omega
    rw [List.take_succ_eq_append_getElem hkl, blocks_append, semiSymmetric_append_iff]
    refine ⟨ih (by omega), ?_⟩
    have hs := bπ _ (List.getElem_mem hkl)
    obtain ⟨hσf, hσs⟩ := hσ π[k] hs.1 hs.2
    have bσ : ∀ y ∈ σ π[k], 1 ≤ y ∧ y ≤ sz n ρ π[k] := fun y hy => (mem_range'_of_perm hσf).1 hy
    have hpre : (blocks q (π.take (k + 1)) σ).Nodup := by
      have e : blocks q π σ = blocks q (π.take (k + 1)) σ ++ blocks q (π.drop (k + 1)) σ := by
        rw [← blocks_append, List.take_append_drop]
      rw [e] at hall; exact (List.nodup_append.1 hall).1
    rw [List.take_succ_eq_append_getElem hkl, blocks_append] at hpre
    have hstep' : SemiStep q ((π.take k).map (mst q ρ)) (mst q ρ π[k]) := by
      have := hπm k (by simpa using hkl)
      simpa [List.map_take] using this
    intro i hi
    simp only [blocks, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.length_map] at hi ⊢
    rw [List.getElem_map, ← List.map_take]
    have hj := bσ _ (List.getElem_mem hi)
    refine ((winEmb_cls' (n := n) hq hρ hs.1 hs.2).semiStep_iff ?_
      (fun y hy => bσ y (List.mem_of_mem_take hy)) hj.1 hj.2 ?_).2 (hσs i hi)
    · simp only [blocks, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil] at hpre
      exact hpre.sublist (List.Sublist.append_left (List.map_take ▸
        (List.take_sublist _ _)) _)
    · refine (cunion_balanced (R := π.take k) hq hρ hs.1 hs.2 hj.1 hj.2
        (fun t ht => bπ t (List.mem_of_mem_take ht)) (take_nodup hndπ k) (hπs k hkl)
        hstep').perm ?_
      exact (blocks_perm' _ fun t ht => (hσ t (bπ t (List.mem_of_mem_take ht)).1
        (bπ t (List.mem_of_mem_take ht)).2).1).symm

theorem flatten_map_eq {f g : Nat → List Nat} : ∀ L : List Nat,
    (∀ s ∈ L, (f s).length = (g s).length) → (L.map f).flatten = (L.map g).flatten →
      ∀ s ∈ L, f s = g s
  | [], _, _ => by simp
  | a :: L, h, e => by
    simp only [List.map_cons, List.flatten_cons] at e
    obtain ⟨e1, e2⟩ := List.append_inj e (h a (by simp))
    intro s hs
    rcases List.mem_cons.1 hs with rfl | hs
    · exact e1
    · exact flatten_map_eq L (fun t ht => h t (by simp [ht])) e2 s hs

/-- The composition map for a fixed class order `π`. -/
def gcompMap (q : Nat) (π : List Nat) (σ : Fin q → List Nat) : List Nat :=
  blocks q π (extFam σ)

theorem extFam_mem {q n ρ : Nat} {σ : Fin q → List Nat}
    (hσ : σ ∈ Fintype.piFinset (fun i : Fin q => semiSeqs (sz n ρ (i.val + 1))))
    {s : Nat} (h1 : 1 ≤ s) (h2 : s ≤ q) :
    IsFoldSeq (sz n ρ s) (extFam σ s) ∧ SemiSymmetric (sz n ρ s) (extFam σ s) := by
  rw [Fintype.mem_piFinset] at hσ
  unfold extFam; rw [dite_eq_left_of_eq_true (eq_true (by omega))]
  have := mem_semiSeqs.1 (hσ ⟨s - 1, by omega⟩)
  simpa [show s - 1 + 1 = s by omega] using this

/-- **Generalised composition lower bound.**  For `N = n q + ρ` with `ρ < q`: if both `π`
and `π.map (mst q ρ)` are valid sequences of the `q`-strip, then
`∏ₛ a(|class s|) ≤ a(N)`. -/
theorem semiCount_gcomp {q n ρ : Nat} (hq : 0 < q) (hρ : ρ < q) {π : List Nat}
    (hπ : π ∈ semiSeqs q) (hπm : SemiSymmetric q (π.map (mst q ρ))) :
    ∏ i : Fin q, semiCount (sz n ρ (i.val + 1)) ≤ semiCount (n * q + ρ) := by
  rw [mem_semiSeqs] at hπ
  set P := Fintype.piFinset (fun i : Fin q => semiSeqs (sz n ρ (i.val + 1)))
  have hsub : P.image (gcompMap q π) ⊆ semiSeqs (n * q + ρ) := by
    intro x hx
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hx
    rw [mem_semiSeqs]
    exact ⟨isFoldSeq_blocks' hq hρ hπ.1 fun s h1 h2 => (extFam_mem hσ h1 h2).1,
      semiSymmetric_blocks' hq hρ hπ.1 hπ.2 hπm fun s h1 h2 => extFam_mem hσ h1 h2⟩
  have hinj : Set.InjOn (gcompMap q π) (P : Set (Fin q → List Nat)) := by
    intro σ hσ σ' hσ' e
    have bπ : ∀ s ∈ π, 1 ≤ s ∧ s ≤ q := fun s hs => (mem_range'_of_perm hπ.1).1 hs
    have hl : ∀ s ∈ π, ((extFam σ s).map (cls q s)).length =
        ((extFam σ' s).map (cls q s)).length := by
      intro s hs
      rw [List.length_map, List.length_map, (extFam_mem hσ (bπ s hs).1 (bπ s hs).2).1.length_eq,
        (extFam_mem hσ' (bπ s hs).1 (bπ s hs).2).1.length_eq]
    have hpt := flatten_map_eq (f := fun s => (extFam σ s).map (cls q s))
      (g := fun s => (extFam σ' s).map (cls q s)) π hl e
    funext i
    have hi : i.val + 1 ∈ π := (mem_range'_of_perm hπ.1).2 (by omega)
    have h1 := hpt _ hi
    have f1 := (extFam_mem hσ (s := i.val + 1) (by omega) (by omega)).1
    have f2 := (extFam_mem hσ' (s := i.val + 1) (by omega) (by omega)).1
    have := (winEmb_cls' (n := n) (ρ := ρ) hq hρ (s := i.val + 1) (by omega) (by omega)).map_inj
      (fun y hy => (mem_range'_of_perm f1).1 hy) (fun y hy => (mem_range'_of_perm f2).1 hy) h1
    unfold extFam at this
    rw [dite_eq_left_of_eq_true (eq_true (by omega)),
      dite_eq_left_of_eq_true (eq_true (by omega))] at this
    simpa using this
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Fintype.card_piFinset] at this
  exact this

/-! ## Instances: `q = 3` -/

/-- `a(n+1) · a(n)² ≤ a(3n+1)`: classes mod 3 in the order `2, 1, 3`. -/
theorem semiCount_three_one (n : Nat) :
    semiCount (n + 1) * semiCount n * semiCount n ≤ semiCount (3 * n + 1) := by
  have h := semiCount_gcomp (q := 3) (n := n) (ρ := 1) (π := [2, 1, 3]) (by omega) (by omega)
    (by rw [mem_semiSeqs]; decide) (by decide)
  rw [Fin.prod_univ_three] at h
  simp only [sz] at h
  rw [show n * 3 + 1 = 3 * n + 1 by omega] at h
  simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h

/-- `a(n+1)² · a(n) ≤ a(3n+2)`: classes mod 3 in the order `1, 3, 2`. -/
theorem semiCount_three_two (n : Nat) :
    semiCount (n + 1) * semiCount (n + 1) * semiCount n ≤ semiCount (3 * n + 2) := by
  have h := semiCount_gcomp (q := 3) (n := n) (ρ := 2) (π := [1, 3, 2]) (by omega) (by omega)
    (by rw [mem_semiSeqs]; decide) (by decide)
  rw [Fin.prod_univ_three] at h
  simp only [sz] at h
  rw [show n * 3 + 2 = 3 * n + 2 by omega] at h
  simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using h

end GComp
end Folds
