import Folds.Copies

/-!
# Live pairs, part 2: residue chains

`experiments/live2/PROOFS.txt`.

* `CoReach N D`: the panels outside `D` can be bisected (in some order) with every step
  semi-symmetric.  A valid prefix is live iff its set is co-reachable
  (`extends_iff_coReach`).
* `winEmb_res`: **every residue class is a window copy, for every `N`**: the class
  `{s, s + q, s + 2q, …} ⊆ [1, N]` (`cls q s`) is a copy of the strip of its size
  `ccount q s N` (arithmetic progressions through `x` are symmetric about `x` inside every
  window).
* `coReach_winEmb`: co-reachability transfers through any window copy whose complement is
  reachable (the weak split, for arbitrary sets).
* Residue chains (`res_chain`): placing complete residue classes one after the other, in an
  order `π` in which every class is balanced by the classes before it, is valid.  The
  balance of a union of classes around a panel `x` only depends on `x mod q` and on
  `reach N x mod q` (`balanced_rUnion_iff`, `reach_cls_mod`), so the chain condition is a
  finite condition `ChainOK q ν π` on `(q, N mod q, π)`, decidable for each concrete `q`.
* `coReach_res`, `extends_res`: if the classes other than `s` form a chain, then
  co-reachable sets of the class strip of `s` stay co-reachable in `[1, N]`; in particular
  pairs `u ≡ v (mod q)` reduce to the class strip (also for mixed parity, `q` odd).
* `chainFor_ok`, `coReach_mod`: for every `2 ≤ q ≤ 12`, every `N ≥ q` and every class `s`
  except the exceptional ones (`s = 1`, `N ≡ 1`; `s = q`, `N ≡ -1 (mod q)`; none for
  `q = 2, 4, 8`), a chain exists (checked by `decide` on explicit orders).
* `coReach_mirror`, `coReach_small`, `coReach_base` (Conjecture C for `N ≤ 12`, by explicit
  witnesses), and the closure `Cov` of these base cases under residue transfers and the
  mirror: `Cov.coReach`, `Cov.extends`.  `experiments/live2/covlean.py` computes the family:
  e.g. 523 of the 779 non-dead 2-sets at `N = 40`, 2400 of 4949 at `N = 100`.
-/

namespace Folds
namespace Live2

/-! ## Co-reachability -/

/-- `D` is co-reachable: the panels of `[1, N]` outside `D` have a semi-symmetric ordering
from scratch. -/
def CoReach (N : Nat) (D : Finset Nat) : Prop := 0 < g N (Finset.Icc 1 N \ D)

theorem extends_iff_coReach {N : Nat} {p : List Nat} (hnd : p.Nodup)
    (hp : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N) (hv : SemiSymmetric N p) :
    Extends N p ↔ CoReach N p.toFinset :=
  extends_iff_g_pos hnd hp hv

/-! ## Residue classes are window copies for every `N` -/

theorem min_div (a b q : Nat) : min a b / q = min (a / q) (b / q) := by
  rcases Nat.le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (Nat.div_le_div_right h)]
  · rw [min_eq_right h, min_eq_right (Nat.div_le_div_right h)]

theorem cls_pos {q s y : Nat} (hs1 : 1 ≤ s) : 1 ≤ cls q s y := by unfold cls; omega

theorem cls_sub {q s j y : Nat} (hy : 1 ≤ y) (h : y ≤ j) :
    cls q s j = cls q s y + (j - y) * q := by
  unfold cls
  have : (j - 1) * q = (y - 1) * q + (j - y) * q := by rw [← Nat.add_mul]; congr 1; omega
  omega

theorem ccount_eq {q s N : Nat} (hq : 0 < q) (hsN : s ≤ N) :
    ccount q s N = (N - s) / q + 1 := by
  unfold ccount
  rw [show N + q - s = (N - s) + q by omega, Nat.add_div_right _ hq]

/-- The reach of a class panel, divided by `q`, is the reach in the class strip. -/
theorem reach_cls_div {q s N j : Nat} (hq : 0 < q) (hs1 : 1 ≤ s) (hsq : s ≤ q) (hj1 : 1 ≤ j)
    (hx : cls q s j ≤ N) : reach N (cls q s j) / q = reach (ccount q s N) j := by
  have hsN : s ≤ N := by unfold cls at hx; omega
  have e1 : (cls q s j - 1) / q = j - 1 := by
    unfold cls
    rw [show (j - 1) * q + s - 1 = (s - 1) + (j - 1) * q by omega, Nat.add_mul_div_right _ _ hq,
      Nat.div_eq_of_lt (by omega)]
    simp
  have e2 : (N - cls q s j) / q = ccount q s N - j := by
    rw [ccount_eq hq hsN]
    have hle : q * (j - 1) ≤ N - s := by
      unfold cls at hx; rw [Nat.mul_comm]; omega
    have : N - cls q s j = (N - s) - q * (j - 1) := by unfold cls; rw [Nat.mul_comm q]; omega
    rw [this, Nat.sub_mul_div]
    have : j - 1 ≤ (N - s) / q := (Nat.le_div_iff_mul_le hq).2 (by rw [Nat.mul_comm]; exact hle)
    omega
  unfold reach
  rw [min_div, e1, e2]

/-- **Residue classes are window copies**, for every `N`: the class of `s` (`1 ≤ s ≤ q`,
`s ≤ N`) is a copy of the strip `[1, ccount q s N]`. -/
theorem winEmb_res {q s N : Nat} (hq : 0 < q) (hs1 : 1 ≤ s) (hsq : s ≤ q) (hsN : s ≤ N) :
    WinEmb N (ccount q s N) (cls q s) := by
  have hb : ∀ y, 1 ≤ y → y ≤ ccount q s N → cls q s y ≤ N := fun y hy1 hy =>
    (cls_le_iff hq hsq hy1).2 hy
  refine ⟨fun y h1 h2 => ⟨cls_pos hs1, hb y h1 h2⟩, fun x y hx1 _ hy1 _ e => ?_, ?_, ?_⟩
  · unfold cls at e
    have : (x - 1) * q = (y - 1) * q := by omega
    have := Nat.eq_of_mul_eq_mul_right hq this
    omega
  · intro j y hj1 hjn hy1 hyn
    have hr := reach_cls_div hq hs1 hsq hj1 (hb j hj1 hjn)
    have hrx : reach N (cls q s j) ≤ cls q s j - 1 := by unfold reach; omega
    constructor
    · rintro ⟨h1, h2⟩
      have hyj : y < j := by
        by_contra hc
        have := cls_sub (q := q) (s := s) hj1 (show j ≤ y by omega); omega
      have e := cls_sub (q := q) (s := s) hy1 hyj.le
      have : (j - y) * q ≤ reach N (cls q s j) := by omega
      have := (Nat.le_div_iff_mul_le hq).2 this
      omega
    · rintro ⟨h1, h2⟩
      have e := cls_sub (q := q) (s := s) hy1 h2.le
      have : j - y ≤ reach N (cls q s j) / q := by omega
      have := (Nat.le_div_iff_mul_le hq).1 this
      have : 0 < (j - y) * q := Nat.mul_pos (by omega) hq
      omega
  · intro j y hj1 hjn hy1 hyn
    have hr := reach_cls_div hq hs1 hsq hj1 (hb j hj1 hjn)
    constructor
    · rintro ⟨h1, h2⟩
      have hyj : j < y := by
        by_contra hc
        have := cls_sub (q := q) (s := s) hy1 (show y ≤ j by omega); omega
      have e := cls_sub (q := q) (s := s) hj1 hyj.le
      have : (y - j) * q ≤ reach N (cls q s j) := by omega
      have := (Nat.le_div_iff_mul_le hq).2 this
      omega
    · rintro ⟨h1, h2⟩
      have e := cls_sub (q := q) (s := s) hj1 h1.le
      have : y - j ≤ reach N (cls q s j) / q := by omega
      have := (Nat.le_div_iff_mul_le hq).1 this
      have : 0 < (y - j) * q := Nat.mul_pos (by omega) hq
      omega

/-! ## The weak split for arbitrary sets -/

/-- The full strip is balanced around each of its panels. -/
theorem balanced_full {N m : Nat} : Balanced N (List.range' 1 N) m := by
  unfold Balanced
  have L : (List.range' 1 N).countP (fun x => decide (m - reach N m ≤ x ∧ x < m)) =
      (List.range' 1 N).countP (fun y => decide (m - reach N m ≤ y ∧ y ≤ m - 1)) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [decide_eq_true_eq]; omega
  have R : (List.range' 1 N).countP (fun x => decide (m < x ∧ x ≤ m + reach N m)) =
      (List.range' 1 N).countP (fun y => decide (m + 1 ≤ y ∧ y ≤ m + reach N m)) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [decide_eq_true_eq]; omega
  rw [L, R, countP_range'_interval, countP_range'_interval]
  unfold reach; omega

theorem Balanced.of_append {N m : Nat} {A B : List Nat} (h : Balanced N (A ++ B) m)
    (hB : Balanced N B m) : Balanced N A m := by
  unfold Balanced at *; rw [List.countP_append, List.countP_append] at h; omega

theorem Balanced.append {N m : Nat} {A B : List Nat} (hA : Balanced N A m)
    (hB : Balanced N B m) : Balanced N (A ++ B) m := by
  unfold Balanced at *; rw [List.countP_append, List.countP_append]; omega

/-- Two nodup lists with the same elements are permutations of each other. -/
theorem perm_of_mem_iff {l l' : List Nat} (hl : l.Nodup) (hl' : l'.Nodup)
    (h : ∀ x, x ∈ l ↔ x ∈ l') : l.Perm l' :=
  (List.perm_ext_iff_of_nodup hl hl').2 h

/-- A list ordering exactly the complement of a window copy is balanced around every
panel of the copy. -/
theorem WinEmb.balanced_compl {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ)
    {l : List Nat} (hnd : l.Nodup)
    (hl : l.toFinset = Finset.Icc 1 N \ (Finset.Icc 1 p).image φ) {j : Nat} (hj1 : 1 ≤ j)
    (hjp : j ≤ p) : Balanced N l (φ j) := by
  have hX : ((List.range' 1 p).map φ).Nodup := hφ.nodup_map (List.nodup_range' ..)
    fun y hy => by rw [List.mem_range'_1] at hy; omega
  have hmem : ∀ x, x ∈ l ↔ (1 ≤ x ∧ x ≤ N) ∧ ¬ ∃ y, (1 ≤ y ∧ y ≤ p) ∧ φ y = x := by
    intro x
    rw [← List.mem_toFinset, hl]
    simp
  have hp : (l ++ (List.range' 1 p).map φ).Perm (List.range' 1 N) := by
    refine perm_of_mem_iff (List.nodup_append.2 ⟨hnd, hX, ?_⟩) (List.nodup_range' ..) ?_
    · intro a ha b hb e
      subst e
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
      rw [List.mem_range'_1] at hy
      exact ((hmem _).1 ha).2 ⟨y, by omega, rfl⟩
    · intro x
      rw [List.mem_append, hmem, List.mem_map, List.mem_range'_1]
      constructor
      · rintro (⟨h, -⟩ | ⟨y, hy, rfl⟩)
        · omega
        · rw [List.mem_range'_1] at hy
          have := hφ.bound y hy.1 (by omega); omega
      · intro hx
        by_cases h : ∃ y, (1 ≤ y ∧ y ≤ p) ∧ φ y = x
        · obtain ⟨y, hy, rfl⟩ := h
          exact Or.inr ⟨y, List.mem_range'_1.2 ⟨hy.1, by omega⟩, rfl⟩
        · exact Or.inl ⟨by omega, h⟩
  exact Balanced.of_append (Balanced.perm balanced_full hp.symm) (hφ.balanced_self hj1 hjp)

/-- **Weak split for sets.**  If `φ` is a window copy of the `p`-strip whose complement is
reachable from scratch, co-reachable sets of the `p`-strip map to co-reachable sets. -/
theorem coReach_winEmb {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ)
    (hY : 0 < g N (Finset.Icc 1 N \ (Finset.Icc 1 p).image φ)) {D : Finset Nat}
    (hDs : D ⊆ Finset.Icc 1 p) (hD : CoReach p D) : CoReach N (D.image φ) := by
  unfold CoReach g at *
  rw [Finset.card_pos] at hY hD ⊢
  obtain ⟨l1, h1⟩ := hY
  obtain ⟨l2, h2⟩ := hD
  rw [mem_semiOrders] at h1 h2
  obtain ⟨⟨hnd1, hs1⟩, hv1⟩ := h1
  obtain ⟨⟨hnd2, hs2⟩, hv2⟩ := h2
  have m2 : ∀ y, y ∈ l2 ↔ (1 ≤ y ∧ y ≤ p) ∧ y ∉ D := by
    intro y; rw [← List.mem_toFinset, hs2]; simp
  have m1 : ∀ x, x ∈ l1 ↔ (1 ≤ x ∧ x ≤ N) ∧ ¬ ∃ y, (1 ≤ y ∧ y ≤ p) ∧ φ y = x := by
    intro x; rw [← List.mem_toFinset, hs1]; simp
  have b2 : ∀ y ∈ l2, 1 ≤ y ∧ y ≤ p := fun y hy => ((m2 y).1 hy).1
  have hnd2' := hφ.nodup_map hnd2 b2
  have hnd : (l1 ++ l2.map φ).Nodup := by
    refine List.nodup_append.2 ⟨hnd1, hnd2', fun a ha b hb e => ?_⟩
    subst e
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact ((m1 _).1 ha).2 ⟨y, b2 y hy, rfl⟩
  refine ⟨l1 ++ l2.map φ, mem_semiOrders.2 ⟨⟨hnd, ?_⟩, ?_⟩⟩
  · ext x
    simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset, Finset.mem_sdiff,
      Finset.mem_Icc, Finset.mem_image, List.mem_map]
    constructor
    · rintro (hx | ⟨y, hy, rfl⟩)
      · obtain ⟨hx1, hx2⟩ := (m1 x).1 hx
        refine ⟨hx1, fun ⟨d, hd, e⟩ => hx2 ⟨d, ?_, e⟩⟩
        have := hDs hd; simpa using this
      · obtain ⟨hy1, hy2⟩ := (m2 y).1 hy
        refine ⟨hφ.bound y hy1.1 hy1.2, fun ⟨d, hd, e⟩ => hy2 ?_⟩
        have hd' : 1 ≤ d ∧ d ≤ p := by have := hDs hd; simpa using this
        rwa [← hφ.inj d y hd'.1 hd'.2 hy1.1 hy1.2 e]
    · rintro ⟨hx, hxD⟩
      by_cases h : ∃ y, (1 ≤ y ∧ y ≤ p) ∧ φ y = x
      · obtain ⟨y, hy, rfl⟩ := h
        exact Or.inr ⟨y, (m2 y).2 ⟨hy, fun hyD => hxD ⟨y, hyD, rfl⟩⟩, rfl⟩
      · exact Or.inl ((m1 x).2 ⟨hx, h⟩)
  · rw [semiSymmetric_append_iff]
    refine ⟨hv1, fun k hk => ?_⟩
    simp only [List.length_map] at hk
    rw [List.getElem_map, ← List.map_take]
    have hj := b2 _ (List.getElem_mem hk)
    have hbal : Balanced N l1 (φ l2[k]) := WinEmb.balanced_compl hφ hnd1 hs1 hj.1 hj.2
    refine (hφ.semiStep_iff ?_ (fun y hy => b2 y (List.mem_of_mem_take hy)) hj.1 hj.2
      hbal).2 (hv2 k hk)
    refine hnd.sublist (List.Sublist.append_left ?_ _)
    rw [List.map_take]; exact List.take_sublist _ _

/-- A valid prefix whose set lies in a window copy with reachable complement is live as
soon as its preimage set is co-reachable in the copy's strip. -/
theorem extends_of_coReach_winEmb {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ)
    (hY : 0 < g N (Finset.Icc 1 N \ (Finset.Icc 1 p).image φ)) {r : List Nat}
    (hr : ∀ y ∈ r, 1 ≤ y ∧ y ≤ p) (hnd : r.Nodup) (hv : SemiSymmetric N (r.map φ))
    (hD : CoReach p r.toFinset) : Extends N (r.map φ) := by
  have hnd' := hφ.nodup_map hnd hr
  rw [extends_iff_coReach hnd' (fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact hφ.bound y (hr y hy).1 (hr y hy).2) hv]
  have := coReach_winEmb hφ hY (D := r.toFinset) (fun y hy => by
    have := hr y (List.mem_toFinset.1 hy); simpa using this) hD
  convert this using 2
  ext x; simp

/-! ## Window counts of residue classes -/

/-- The panels of class `t` inside `[1, N]`. -/
def rPanels (q N t : Nat) : List Nat := classPanels q (ccount q t N) t

theorem countP_le_rPanels {q N t z : Nat} (hq : 0 < q) (ht1 : 1 ≤ t) (htq : t ≤ q)
    (hz : z ≤ N) : (rPanels q N t).countP (fun u => decide (u ≤ z)) = ccount q t z := by
  unfold rPanels classPanels
  rw [List.countP_map]
  have e : (List.range' 1 (ccount q t N)).countP ((fun u => decide (u ≤ z)) ∘ cls q t) =
      (List.range' 1 (ccount q t N)).countP (fun y => decide (1 ≤ y ∧ y ≤ ccount q t z)) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    rw [cls_le_iff hq htq hy.1]; omega
  rw [e, countP_range'_interval]
  have : ccount q t z ≤ ccount q t N := ccount_mono hz
  omega

/-- Counting multiples in a shifted interval. -/
theorem div_add_sub_div (y r q : Nat) (hq : 0 < q) : (y + r) / q - y / q = (y % q + r) / q := by
  have h := Nat.div_add_mod y q
  have : (y + r) / q = (y % q + r) / q + y / q := by
    rw [show y + r = (y % q + r) + q * (y / q) by omega, Nat.add_mul_div_left _ _ hq]
  rw [this, Nat.add_sub_cancel]

theorem countP_interval_rPanels {q N t lo hi : Nat} (hq : 0 < q) (ht1 : 1 ≤ t) (htq : t ≤ q)
    (hlo : 1 ≤ lo) (hle : lo ≤ hi + 1) (hhi : hi ≤ N) :
    (rPanels q N t).countP (fun u => decide (lo ≤ u ∧ u ≤ hi)) =
      ((lo - 1 + q - t) % q + (hi + 1 - lo)) / q := by
  have i1 := countP_interval_add (rPanels q N t) hle
  rw [countP_succ_le hlo, countP_le_rPanels hq ht1 htq hhi,
    countP_le_rPanels hq ht1 htq (by omega)] at i1
  unfold ccount at i1
  have := div_add_sub_div (lo - 1 + q - t) (hi + 1 - lo) q hq
  rw [show lo - 1 + q - t + (hi + 1 - lo) = hi + q - t by omega] at this
  omega

/-- Right arm count of class `t` around `x`, with radius `r`. -/
theorem countP_right_rPanels {q N t x r : Nat} (hq : 0 < q) (ht1 : 1 ≤ t) (htq : t ≤ q)
    (hx : 1 ≤ x) (hr : x + r ≤ N) :
    (rPanels q N t).countP (fun u => decide (x < u ∧ u ≤ x + r)) =
      ((x + q - t) % q + r) / q := by
  have := countP_interval_rPanels (N := N) (lo := x + 1) (hi := x + r) hq ht1 htq (by omega) (by omega) hr
  rw [show x + 1 - 1 + q - t = x + q - t by omega, show x + r + 1 - (x + 1) = r by omega] at this
  rw [← this]
  apply List.countP_congr; intro u _; simp only [decide_eq_true_eq]; omega

/-- Left arm count of class `t` around `x`, with radius `r`. -/
theorem countP_left_rPanels {q N t x r : Nat} (hq : 0 < q) (ht1 : 1 ≤ t) (htq : t ≤ q)
    (hr : r + 1 ≤ x) (hx : x ≤ N) :
    (rPanels q N t).countP (fun u => decide (x - r ≤ u ∧ u < x)) =
      ((x - r - 1 + q - t) % q + r) / q := by
  have := countP_interval_rPanels (N := N) (lo := x - r) (hi := x - 1) hq ht1 htq (by omega) (by omega)
    (by omega)
  rw [show x - 1 + 1 - (x - r) = r by omega] at this
  rw [← this]
  apply List.countP_congr; intro u _; simp only [decide_eq_true_eq]; omega

/-- The union of the classes listed in `A`. -/
def rUnion (q N : Nat) (A : List Nat) : List Nat := (A.map (rPanels q N)).flatten

theorem countP_rUnion (q N : Nat) (P : Nat → Bool) :
    ∀ A : List Nat, (rUnion q N A).countP P = (A.map fun t => (rPanels q N t).countP P).sum
  | [] => by simp [rUnion]
  | t :: A => by
    have := countP_rUnion q N P A
    simp only [rUnion, List.map_cons, List.flatten_cons, List.countP_append, List.sum_cons] at *
    rw [this]

/-- The cyclic balance condition: the classes `A` are balanced, on the cycle `ℤ/q`, around
`s` within radius `ρ` (as computed by the window counts). -/
def CycBal (q : Nat) (A : List Nat) (s ρ : Nat) : Prop :=
  (A.map fun t => ((s + 2 * q - ρ - 1 - t) % q + ρ) / q).sum =
    (A.map fun t => ((s + q - t) % q + ρ) / q).sum

instance (q : Nat) (A : List Nat) (s ρ : Nat) : Decidable (CycBal q A s ρ) :=
  inferInstanceAs (Decidable (_ = _))

theorem sum_map_add_const (A : List Nat) (f : Nat → Nat) (c : Nat) :
    (A.map fun t => f t + c).sum = (A.map f).sum + A.length * c := by
  induction A with
  | nil => simp
  | cons a A ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- **Balance of a union of classes** around a class panel `x = cls q s j`: it depends only
on `s` and on `ρ = reach N x mod q`. -/
theorem balanced_rUnion_iff {q N s j : Nat} {A : List Nat} (hq : 0 < q) (hs1 : 1 ≤ s)
    (hsq : s ≤ q) (hj1 : 1 ≤ j) (hx : cls q s j ≤ N) (hA : ∀ t ∈ A, 1 ≤ t ∧ t ≤ q) :
    Balanced N (rUnion q N A) (cls q s j) ↔
      CycBal q A s (reach N (cls q s j) % q) := by
  set x := cls q s j with hxdef
  set r := reach N x with hrdef
  have hr1 : r + 1 ≤ x := by
    have : 1 ≤ x := cls_pos hs1
    rw [hrdef]; unfold reach; omega
  have hr2 : x + r ≤ N := by rw [hrdef]; unfold reach; omega
  unfold Balanced
  rw [countP_rUnion, countP_rUnion]
  have eL : (A.map fun t => (rPanels q N t).countP (fun u => decide (x - r ≤ u ∧ u < x))) =
      A.map fun t => ((x - r - 1 + q - t) % q + r) / q := by
    apply List.map_congr_left; intro t ht
    exact countP_left_rPanels hq (hA t ht).1 (hA t ht).2 hr1 (by omega)
  have eR : (A.map fun t => (rPanels q N t).countP (fun u => decide (x < u ∧ u ≤ x + r))) =
      A.map fun t => ((x + q - t) % q + r) / q := by
    apply List.map_congr_left; intro t ht
    exact countP_right_rPanels hq (hA t ht).1 (hA t ht).2 (cls_pos hs1) hr2
  rw [eL, eR]
  -- reduce both sides modulo `q`
  obtain ⟨R, ρ, hρ, hrR⟩ : ∃ R ρ, ρ < q ∧ r = q * R + ρ :=
    ⟨r / q, r % q, Nat.mod_lt _ hq, (Nat.div_add_mod r q).symm⟩
  have hρr : r % q = ρ := by rw [hrR, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hρ
  rw [hρr]
  have hxs : x = q * (j - 1) + s := by rw [hxdef]; unfold cls; rw [Nat.mul_comm]
  have eL' : ∀ t ∈ A, ((x - r - 1 + q - t) % q + r) / q =
      ((s + 2 * q - ρ - 1 - t) % q + ρ) / q + R := by
    intro t ht
    have ht' := hA t ht
    have hm : (x - r - 1 + q - t) % q = (s + 2 * q - ρ - 1 - t) % q := by
      -- `x - r - 1 + q - t + q * (R + 1) = q * (j - 1) + (s + 2q - ρ - 1 - t)`
      have e : x - r - 1 + q - t + q * (R + 1) = (s + 2 * q - ρ - 1 - t) + q * (j - 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      have := congrArg (· % q) e
      simp only [Nat.add_mul_mod_self_left] at this
      exact this
    rw [hm, hrR, show (s + 2 * q - ρ - 1 - t) % q + (q * R + ρ) =
      ((s + 2 * q - ρ - 1 - t) % q + ρ) + q * R by ring, Nat.add_mul_div_left _ _ hq]
  have eR' : ∀ t ∈ A, ((x + q - t) % q + r) / q = ((s + q - t) % q + ρ) / q + R := by
    intro t ht
    have ht' := hA t ht
    have hm : (x + q - t) % q = (s + q - t) % q := by
      rw [hxs, show q * (j - 1) + s + q - t = (s + q - t) + q * (j - 1) by omega,
        Nat.add_mul_mod_self_left]
    rw [hm, hrR, show (s + q - t) % q + (q * R + ρ) = ((s + q - t) % q + ρ) + q * R by ring,
      Nat.add_mul_div_left _ _ hq]
  rw [List.map_congr_left eL', List.map_congr_left eR', sum_map_add_const, sum_map_add_const]
  unfold CycBal
  omega

/-- The two possible radii modulo `q`: `s - 1` in the left half, `(ν + q - s) mod q` in the
right half (`ν = N mod q`). -/
theorem reach_cls_mod {q N s j : Nat} (hq : 0 < q) (hs1 : 1 ≤ s) (hsq : s ≤ q) (hj1 : 1 ≤ j)
    (hx : cls q s j ≤ N) :
    reach N (cls q s j) % q = s - 1 ∨ reach N (cls q s j) % q = (N % q + q - s) % q := by
  have hxs : cls q s j = q * (j - 1) + s := by unfold cls; rw [Nat.mul_comm]
  unfold reach
  rcases Nat.le_total (cls q s j - 1) (N - cls q s j) with h | h
  · left
    rw [min_eq_left h, hxs, show q * (j - 1) + s - 1 = (s - 1) + q * (j - 1) by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · right
    rw [min_eq_right h]
    have hqj : q * j = q * (j - 1) + q := by rw [← Nat.mul_succ]; congr 1; omega
    have e : (N - cls q s j) + q * j = (N % q + q - s) + q * (N / q) := by
      have := Nat.div_add_mod N q
      have := Nat.mod_lt N hq
      rw [hxs] at hx ⊢; omega
    have := congrArg (· % q) e
    simpa only [Nat.add_mul_mod_self_left] using this

/-! ## Residue chains -/

/-- **The chain condition** for an order `π` of residue classes (labels `1..q`), for strips
`N ≡ ν (mod q)`: every class is balanced by the earlier ones, at both possible radii. -/
def ChainOK (q ν : Nat) (π : List Nat) : Prop :=
  ∀ i (h : i < π.length), CycBal q (π.take i) π[i] (π[i] - 1) ∧
    CycBal q (π.take i) π[i] ((ν + q - π[i]) % q)

instance (q ν : Nat) (π : List Nat) : Decidable (ChainOK q ν π) := by
  unfold ChainOK; infer_instance

theorem mem_rPanels_iff {q N t x : Nat} (hq : 0 < q) (ht1 : 1 ≤ t) (htq : t ≤ q) :
    x ∈ rPanels q N t ↔ 1 ≤ x ∧ x ≤ N ∧ (x - 1) % q + 1 = t := by
  unfold rPanels classPanels
  rw [List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [List.mem_range'_1] at hy
    exact ⟨cls_pos ht1, (cls_le_iff hq htq hy.1).2 (by omega), by rw [cls_class ht1 htq]; omega⟩
  · rintro ⟨hx1, hxN, hres⟩
    have hd := Nat.div_add_mod (x - 1) q
    have hx : cls q t ((x - 1) / q + 1) = x := by
      show ((x - 1) / q + 1 - 1) * q + t = x
      rw [Nat.add_sub_cancel, Nat.mul_comm]; omega
    refine ⟨(x - 1) / q + 1, List.mem_range'_1.2 ⟨Nat.le_add_left 1 _, ?_⟩, hx⟩
    have := (cls_le_iff hq htq (Nat.le_add_left 1 ((x - 1) / q)) (z := N)).1 (by rw [hx]; exact hxN)
    omega

theorem mem_blocks {q : Nat} {σ : Nat → List Nat} {x : Nat} :
    ∀ π : List Nat, x ∈ blocks q π σ ↔ ∃ t ∈ π, ∃ y ∈ σ t, cls q t y = x
  | [] => by simp [blocks]
  | t :: π => by
    have ih := mem_blocks (q := q) (σ := σ) (x := x) π
    simp only [blocks, List.map_cons, List.flatten_cons, List.mem_append, List.mem_map,
      List.mem_cons] at *
    rw [ih]
    constructor
    · rintro (⟨y, hy, e⟩ | ⟨t', ht', y, hy, e⟩)
      · exact ⟨t, Or.inl rfl, y, hy, e⟩
      · exact ⟨t', Or.inr ht', y, hy, e⟩
    · rintro ⟨t', ht' | ht', y, hy, e⟩
      · subst ht'; exact Or.inl ⟨y, hy, e⟩
      · exact Or.inr ⟨t', ht', y, hy, e⟩

theorem blocks_perm_rUnion {q N : Nat} {σ : Nat → List Nat} :
    ∀ π : List Nat, (∀ t ∈ π, IsFoldSeq (ccount q t N) (σ t)) →
      (blocks q π σ).Perm (rUnion q N π)
  | [], _ => by simp [blocks, rUnion]
  | t :: π, h => by
    simp only [blocks, rUnion, List.map_cons, List.flatten_cons] at *
    exact ((h t (by simp)).map _).append (blocks_perm_rUnion π fun t' ht' => h t' (by simp [ht']))

theorem blocks_nodup {q N : Nat} (hq : 0 < q) {σ : Nat → List Nat} :
    ∀ π : List Nat, π.Nodup → (∀ t ∈ π, 1 ≤ t ∧ t ≤ q) →
      (∀ t ∈ π, IsFoldSeq (ccount q t N) (σ t)) → (blocks q π σ).Nodup
  | [], _, _, _ => by simp [blocks]
  | t :: π, hnd, hb, hσ => by
    have ih := blocks_nodup hq π (List.nodup_cons.1 hnd).2 (fun t' ht' => hb t' (by simp [ht']))
      (fun t' ht' => hσ t' (by simp [ht']))
    have ht := hb t (by simp)
    have hσt := hσ t (by simp)
    have bσ : ∀ y ∈ σ t, 1 ≤ y ∧ y ≤ ccount q t N := fun y hy => (mem_range'_of_perm hσt).1 hy
    have hm : ((σ t).map (cls q t)).Nodup :=
      nodup_map_of_injOn (nodup_of_foldSeq hσt) fun a _ b _ e => by
        unfold cls at e
        have := Nat.eq_of_mul_eq_mul_right hq (show (a - 1) * q = (b - 1) * q by omega)
        have := bσ a ‹_›; have := bσ b ‹_›; omega
    simp only [blocks, List.map_cons, List.flatten_cons]
    refine List.nodup_append.2 ⟨hm, ih, fun a ha b hbm e => ?_⟩
    subst e
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    obtain ⟨t', ht', y', _, e⟩ := (mem_blocks π).1 hbm
    have hb' := hb t' (by simp [ht'])
    have c1 := cls_class (q := q) (y := y) ht.1 ht.2
    have c2 := cls_class (q := q) (y := y') hb'.1 hb'.2
    rw [e] at c2
    have : t = t' := by omega
    subst this
    exact (List.nodup_cons.1 hnd).1 ht'

/-- **Residue chains are valid.**  If the classes are placed as complete blocks in an order
`π` satisfying `ChainOK q (N mod q) π`, each in a valid order of its class strip, the result
is valid. -/
theorem res_chain {q N : Nat} (hq : 0 < q) (hqN : q ≤ N) {π : List Nat}
    (hπ : ∀ t ∈ π, 1 ≤ t ∧ t ≤ q) (hnd : π.Nodup) (hc : ChainOK q (N % q) π)
    {σ : Nat → List Nat}
    (hσ : ∀ t, 1 ≤ t → t ≤ q → IsFoldSeq (ccount q t N) (σ t) ∧
      SemiSymmetric (ccount q t N) (σ t)) :
    SemiSymmetric N (blocks q π σ) := by
  have hσf : ∀ t ∈ π, IsFoldSeq (ccount q t N) (σ t) := fun t ht =>
    (hσ t (hπ t ht).1 (hπ t ht).2).1
  have hall := blocks_nodup hq π hnd hπ hσf
  suffices H : ∀ k, k ≤ π.length → SemiSymmetric N (blocks q (π.take k) σ) by
    simpa using H π.length le_rfl
  intro k
  induction k with
  | zero => intro _ i hi; simp [blocks] at hi
  | succ k ih =>
    intro hk
    have hkl : k < π.length := by omega
    rw [List.take_succ_eq_append_getElem hkl, blocks_append, semiSymmetric_append_iff]
    refine ⟨ih (by omega), ?_⟩
    have hs := hπ _ (List.getElem_mem hkl)
    obtain ⟨hσf', hσs⟩ := hσ π[k] hs.1 hs.2
    have bσ : ∀ y ∈ σ π[k], 1 ≤ y ∧ y ≤ ccount q π[k] N := fun y hy =>
      (mem_range'_of_perm hσf').1 hy
    have hsN : π[k] ≤ N := by omega
    have hpre : (blocks q (π.take (k + 1)) σ).Nodup := by
      have e : blocks q π σ = blocks q (π.take (k + 1)) σ ++ blocks q (π.drop (k + 1)) σ := by
        rw [← blocks_append, List.take_append_drop]
      rw [e] at hall; exact (List.nodup_append.1 hall).1
    rw [List.take_succ_eq_append_getElem hkl, blocks_append] at hpre
    intro i hi
    simp only [blocks, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.length_map] at hi ⊢
    rw [List.getElem_map, ← List.map_take]
    have hj := bσ _ (List.getElem_mem hi)
    have hxN : cls q π[k] (σ π[k])[i] ≤ N := (cls_le_iff hq hs.2 hj.1).2 hj.2
    refine ((winEmb_res hq hs.1 hs.2 hsN).semiStep_iff ?_
      (fun y hy => bσ y (List.mem_of_mem_take hy)) hj.1 hj.2 ?_).2 (hσs i hi)
    · simp only [blocks, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil] at hpre
      exact hpre.sublist (List.Sublist.append_left (List.map_take ▸
        (List.take_sublist _ _)) _)
    · have hA : ∀ t ∈ π.take k, 1 ≤ t ∧ t ≤ q := fun t ht => hπ t (List.mem_of_mem_take ht)
      refine (Balanced.perm ?_ (blocks_perm_rUnion (N := N) (π.take k)
        fun t ht => hσf t (List.mem_of_mem_take ht)).symm)
      rw [balanced_rUnion_iff hq hs.1 hs.2 hj.1 hxN hA]
      obtain ⟨c1, c2⟩ := hc k hkl
      rcases reach_cls_mod hq hs.1 hs.2 hj.1 hxN with h | h
      · rw [h]; exact c1
      · rw [h]; exact c2

/-- **Residue transfer.**  Let `π` list the residue classes other than `s` in an order
satisfying the chain condition.  Then the complement of the class of `s` is reachable, so
co-reachable sets of the class strip stay co-reachable in `[1, N]`. -/
theorem coReach_res {q N s : Nat} (hq : 0 < q) (hqN : q ≤ N) (hs1 : 1 ≤ s) (hsq : s ≤ q)
    {π : List Nat} (hπ : ∀ t, t ∈ π ↔ 1 ≤ t ∧ t ≤ q ∧ t ≠ s) (hnd : π.Nodup)
    (hc : ChainOK q (N % q) π) {D : Finset Nat} (hDs : D ⊆ Finset.Icc 1 (ccount q s N))
    (hD : CoReach (ccount q s N) D) : CoReach N (D.image (cls q s)) := by
  have hsN : s ≤ N := by omega
  refine coReach_winEmb (winEmb_res hq hs1 hsq hsN) ?_ hDs hD
  have hex : ∀ t, ∃ σt, IsFoldSeq (ccount q t N) σt ∧ SemiSymmetric (ccount q t N) σt :=
    fun t => exists_semiSymmetric _
  choose σ hσ using hex
  have hb : ∀ t ∈ π, 1 ≤ t ∧ t ≤ q := fun t ht => by
    have := (hπ t).1 ht; omega
  have hval := res_chain hq hqN hb hnd hc (σ := σ) fun t _ _ => hσ t
  have hnd' := blocks_nodup hq π hnd hb fun t _ => (hσ t).1
  rw [g, Finset.card_pos]
  refine ⟨blocks q π σ, mem_semiOrders.2 ⟨⟨hnd', ?_⟩, hval⟩⟩
  ext x
  rw [List.mem_toFinset, mem_blocks, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, y, hy, rfl⟩
    have htq := (hπ t).1 ht
    have hy' := (mem_range'_of_perm (hσ t).1).1 hy
    have hx : cls q t y ∈ rPanels q N t := List.mem_map.2 ⟨y, List.mem_range'_1.2 ⟨hy'.1, by omega⟩, rfl⟩
    rw [mem_rPanels_iff hq htq.1 htq.2.1] at hx
    refine ⟨⟨hx.1, hx.2.1⟩, ?_⟩
    rintro ⟨y', -, e⟩
    have := cls_class (q := q) (y := y') hs1 hsq
    rw [e] at this
    omega
  · rintro ⟨⟨hx1, hxN⟩, hnot⟩
    set t := (x - 1) % q + 1 with ht
    have htq : 1 ≤ t ∧ t ≤ q := by have := Nat.mod_lt (x - 1) hq; omega
    have hx : x ∈ rPanels q N t := (mem_rPanels_iff hq htq.1 htq.2).2 ⟨hx1, hxN, rfl⟩
    obtain ⟨y, hy, e⟩ := List.mem_map.1 hx
    rw [List.mem_range'_1] at hy
    have hts : t ≠ s := by
      intro h
      apply hnot
      refine ⟨y, Finset.mem_Icc.2 ⟨hy.1, by rw [← h]; omega⟩, ?_⟩
      rw [← h]; exact e
    exact ⟨t, (hπ t).2 ⟨htq.1, htq.2, hts⟩, y,
      (mem_range'_of_perm (hσ t).1).2 ⟨hy.1, by omega⟩, e⟩

/-- **Live pairs through residue classes.**  Under the chain condition for the classes
other than `s`, a valid 2-prefix `[cls q s a, cls q s b]` is live as soon as `{a, b}` is
co-reachable in the class strip. -/
theorem extends_res {q N s : Nat} (hq : 0 < q) (hqN : q ≤ N) (hs1 : 1 ≤ s) (hsq : s ≤ q)
    {π : List Nat} (hπ : ∀ t, t ∈ π ↔ 1 ≤ t ∧ t ≤ q ∧ t ≠ s) (hnd : π.Nodup)
    (hc : ChainOK q (N % q) π) {a b : Nat} (ha : 1 ≤ a ∧ a ≤ ccount q s N)
    (hb : 1 ≤ b ∧ b ≤ ccount q s N) (hab : a ≠ b)
    (hv : SemiSymmetric N [cls q s a, cls q s b]) (hD : CoReach (ccount q s N) {a, b}) :
    Extends N [cls q s a, cls q s b] := by
  have hφ := winEmb_res hq hs1 hsq (show s ≤ N by omega)
  have hnd2 : [cls q s a, cls q s b].Nodup := by
    simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    intro e; exact hab (hφ.inj a b ha.1 ha.2 hb.1 hb.2 e)
  rw [extends_iff_coReach hnd2 (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hφ.bound a ha.1 ha.2
    · exact hφ.bound b hb.1 hb.2) hv]
  have := coReach_res hq hqN hs1 hsq hπ hnd hc (D := {a, b}) (by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> simp [ha.1, ha.2, hb.1, hb.2]) hD
  convert this using 1
  simp [Finset.image_insert]

/-! ## Concrete residue chains, `q ≤ 12`

Orders found by `experiments/live2/chainok.py`; `chainFor_ok` checks them by `decide`. -/

set_option maxRecDepth 100000 in
/-- `chainTbl[q][ν][s-1]`: an order of the classes other than `s` satisfying
`ChainOK q ν` (empty when `s` is exceptional). -/
noncomputable def chainTbl : List (List (List (List Nat))) :=
  [[],[],[[[2],[1]],[[2],[1]]],[[[2,3],[1,3],[2,1]],[[],[3,1],[2,1]],[[2,3],[1,3],[]]],[[[2,4,3],[1,3,4],[2,1,4],[1,3,2]],[[2,4,3],[1,3,4],[2,4,1],[1,3,2]],[[2,4,3],[1,3,4],[2,4,1],[1,3,2]],[[2,4,3],[1,3,4],[2,4,1],[1,3,2]]],[[[2,4,3,5],[1,4,3,5],[2,1,4,5],[1,5,3,2],[1,4,3,2]],[[],[3,5,4,1],[2,1,4,5],[3,5,1,2],[4,2,3,1]],[[5,2,3,4],[3,1,5,4],[2,4,5,1],[3,1,5,2],[1,4,3,2]],[[2,5,3,4],[1,4,3,5],[2,4,1,5],[3,5,1,2],[1,4,3,2]],[[2,4,3,5],[1,5,3,4],[2,4,5,1],[3,1,2,5],[]]],[[[2,5,3,6,4],[1,4,3,6,5],[2,1,5,4,6],[1,5,3,2,6],[1,4,3,2,6],[1,5,3,4,2]],[[],[3,1,5,4,6],[2,5,1,4,6],[3,1,2,5,6],[2,6,4,3,1],[2,5,1,4,3]],[[2,5,3,6,4],[1,4,3,6,5],[4,2,6,5,1],[2,5,3,6,1],[1,4,3,6,2],[3,1,5,4,2]],[[2,5,3,6,4],[1,4,3,6,5],[2,5,1,4,6],[1,5,3,6,2],[1,4,3,6,2],[1,5,3,4,2]],[[2,6,4,3,5],[1,5,3,4,6],[2,5,1,4,6],[1,5,3,2,6],[3,6,1,4,2],[2,5,1,4,3]],[[2,5,3,6,4],[1,4,3,6,5],[2,6,1,4,5],[1,5,3,2,6],[1,4,3,6,2],[]]],[[[2,5,3,7,4,6],[1,5,3,7,4,6],[2,1,5,7,4,6],[1,5,3,2,7,6],[1,6,4,3,2,7],[1,5,3,7,4,2],[2,6,4,1,5,3]],[[],[3,7,5,1,4,6],[2,6,4,1,5,7],[3,6,1,2,5,7],[2,6,4,3,1,7],[3,7,5,1,4,2],[2,6,4,1,5,3]],[[4,2,6,3,7,5],[4,1,6,3,7,5],[4,7,2,5,6,1],[1,5,3,7,6,2],[4,1,6,3,7,2],[1,5,3,7,4,2],[3,1,6,5,4,2]],[[2,6,4,3,7,5],[1,5,7,3,4,6],[2,5,7,1,4,6],[2,5,7,3,6,1],[2,6,4,3,7,1],[1,5,7,3,4,2],[2,6,4,1,5,3]],[[2,6,4,3,7,5],[1,5,3,7,4,6],[2,5,4,7,1,6],[3,6,1,2,5,7],[3,6,1,7,4,2],[1,5,3,7,4,2],[2,6,4,5,1,3]],[[2,5,3,7,4,6],[1,6,4,3,7,5],[2,6,4,1,5,7],[2,5,3,7,6,1],[1,6,4,3,2,7],[2,7,4,1,5,3],[2,6,4,1,5,3]],[[2,6,4,7,3,5],[1,5,3,7,4,6],[2,5,4,7,1,6],[1,5,3,2,7,6],[2,6,4,7,3,1],[1,5,3,7,4,2],[]]],[[[2,6,4,3,8,7,5],[1,5,3,7,4,8,6],[2,1,6,5,4,8,7],[1,5,3,2,7,6,8],[1,6,4,3,2,8,7],[1,5,3,7,4,2,8],[1,5,3,8,6,4,2],[1,5,3,2,7,6,4]],[[2,6,4,3,8,7,5],[1,5,3,7,4,8,6],[2,6,4,8,1,5,7],[1,5,3,2,7,6,8],[2,6,4,3,8,7,1],[1,5,3,7,4,2,8],[2,6,4,8,1,5,3],[1,5,3,2,7,6,4]],[[2,6,4,3,8,7,5],[1,5,3,7,4,8,6],[2,6,4,8,1,5,7],[1,5,3,7,2,6,8],[2,6,4,3,8,7,1],[1,5,3,7,4,8,2],[2,6,4,8,1,5,3],[1,5,3,7,2,6,4]],[[2,6,4,8,3,7,5],[1,5,3,7,4,8,6],[2,6,4,8,1,5,7],[1,5,3,7,2,6,8],[1,6,4,8,3,7,2],[1,5,3,7,4,8,2],[1,5,8,3,6,4,2],[1,5,3,7,2,6,4]],[[2,6,4,8,3,7,5],[1,5,3,7,4,8,6],[2,6,1,5,4,8,7],[1,5,3,2,7,6,8],[2,6,4,8,3,7,1],[1,5,3,7,4,8,2],[2,6,1,5,4,8,3],[1,5,3,2,7,6,4]],[[2,6,4,3,8,7,5],[1,5,3,7,4,8,6],[2,6,4,8,1,5,7],[1,5,3,7,2,6,8],[1,6,4,3,8,2,7],[1,5,3,7,4,8,2],[2,6,4,8,1,5,3],[1,5,3,7,2,6,4]],[[2,6,4,8,3,7,5],[1,5,3,7,4,8,6],[2,6,4,8,1,5,7],[1,5,3,7,2,6,8],[1,7,4,3,2,6,8],[1,5,3,7,4,8,2],[2,6,4,8,1,5,3],[1,5,3,7,2,6,4]],[[2,6,4,8,3,7,5],[1,5,3,7,4,8,6],[2,6,4,8,1,5,7],[1,5,3,2,7,6,8],[1,6,4,8,3,2,7],[1,5,3,7,4,8,2],[2,6,4,8,1,5,3],[1,5,3,2,7,6,4]]],[[[2,6,4,3,8,7,5,9],[1,6,4,3,8,7,5,9],[2,1,6,8,5,4,9,7],[1,6,5,3,2,8,9,7],[1,6,4,3,2,8,7,9],[1,7,4,3,9,8,5,2],[1,6,4,3,8,9,5,2],[1,6,4,3,9,7,5,2],[1,6,4,3,8,7,5,2]],[[],[3,7,6,9,1,4,5,8],[2,7,5,9,1,4,6,8],[3,7,5,9,1,2,6,8],[3,7,6,9,1,4,2,8],[2,7,5,9,8,1,4,3],[2,8,5,4,1,9,6,3],[2,7,5,9,1,4,6,3],[2,8,5,4,1,7,6,3]],[[5,9,2,3,7,4,8,6],[3,1,7,9,5,4,8,6],[2,6,4,8,5,9,7,1],[3,1,7,9,5,2,6,8],[1,6,4,3,8,2,7,9],[3,1,7,9,5,4,8,2],[2,6,4,8,5,9,1,3],[3,1,7,9,5,2,6,4],[1,6,4,8,7,3,5,2]],[[2,7,5,9,3,4,8,6],[1,6,4,3,8,9,5,7],[2,6,8,4,1,9,5,7],[2,7,5,6,3,9,8,1],[1,6,4,3,8,2,7,9],[2,7,5,9,1,4,8,3],[1,6,4,3,8,9,5,2],[1,6,4,9,3,7,5,2],[1,6,4,3,8,7,5,2]],[[2,6,4,8,9,3,5,7],[1,7,5,3,9,4,8,6],[2,6,4,8,9,1,5,7],[1,6,5,3,2,8,9,7],[2,6,4,3,8,7,9,1],[1,7,5,3,9,4,8,2],[2,6,4,8,9,1,5,3],[1,7,5,6,3,2,9,4],[2,6,4,8,7,1,5,3]],[[2,7,4,9,3,8,5,6],[1,6,4,3,8,9,5,7],[2,7,4,6,1,9,5,8],[1,7,5,6,3,9,2,8],[1,6,4,3,8,2,7,9],[2,7,4,9,5,8,1,3],[1,6,4,3,8,9,5,2],[1,7,5,6,3,9,2,4],[2,6,1,8,7,4,5,3]],[[2,6,4,8,9,3,5,7],[1,7,4,3,9,6,5,8],[2,6,4,8,5,9,1,7],[1,7,5,3,9,6,2,8],[1,7,4,3,9,6,2,8],[1,7,5,3,4,9,2,8],[2,6,4,8,5,9,1,3],[1,7,5,3,9,6,2,4],[1,8,5,3,2,7,6,4]],[[2,6,4,9,3,7,5,8],[1,6,4,8,3,7,5,9],[2,6,4,8,1,9,5,7],[1,8,5,7,3,2,6,9],[1,6,4,8,3,2,7,9],[1,8,5,7,3,4,9,2],[2,6,4,8,5,1,3,9],[3,7,5,9,1,2,6,4],[1,8,5,7,3,2,6,4]],[[2,6,5,8,9,3,4,7],[1,6,4,8,9,3,5,7],[2,6,4,8,5,9,1,7],[2,6,5,8,9,3,1,7],[1,6,4,8,7,9,3,2],[1,7,4,3,9,8,5,2],[1,6,4,8,9,3,5,2],[1,7,4,3,9,6,5,2],[]]],[[[2,7,4,3,9,8,5,10,6],[1,6,4,3,9,8,5,10,7],[2,1,7,6,4,9,5,10,8],[1,6,5,3,2,9,8,7,10],[1,6,4,3,2,9,8,7,10],[1,7,4,3,9,8,5,2,10],[1,6,4,3,9,8,5,2,10],[1,6,4,3,9,10,7,5,2],[1,6,4,3,10,8,7,5,2],[1,6,4,3,2,9,8,7,5]],[[],[3,1,7,6,4,9,5,10,8],[2,7,1,6,4,9,5,10,8],[3,1,2,7,9,6,5,10,8],[2,8,6,4,3,10,1,7,9],[2,7,1,9,5,4,3,8,10],[2,8,5,4,10,9,1,6,3],[2,7,1,6,4,9,5,3,10],[2,7,5,10,1,4,8,6,3],[2,7,1,9,5,4,8,6,3]],[[5,2,8,7,3,4,10,9,6],[3,8,1,6,5,4,10,9,7],[2,7,4,9,5,10,1,6,8],[3,1,7,9,5,6,10,8,2],[1,6,4,3,9,8,2,7,10],[3,1,7,9,5,4,2,8,10],[3,8,1,6,5,4,10,9,2],[1,6,4,3,9,10,7,5,2],[3,8,1,6,5,10,2,7,4],[1,6,4,3,9,8,2,7,5]],[[2,7,5,10,3,8,4,9,6],[1,6,4,9,3,8,5,10,7],[2,7,4,9,1,6,5,10,8],[1,7,5,3,9,6,10,8,2],[1,6,4,9,3,8,2,7,10],[1,7,5,3,4,9,2,8,10],[1,6,4,9,3,8,5,10,2],[1,6,4,9,10,3,7,5,2],[1,7,5,10,3,8,4,6,2],[1,6,4,9,3,8,2,7,5]],[[2,7,4,9,3,8,5,10,6],[1,6,5,3,4,9,8,10,7],[2,7,4,9,5,10,1,6,8],[1,7,5,3,9,6,2,10,8],[2,8,6,4,10,3,7,9,1],[1,7,5,3,4,9,8,10,2],[1,6,5,3,4,9,8,10,2],[1,7,5,3,9,6,2,10,4],[1,7,5,10,3,4,8,6,2],[1,6,5,3,9,2,8,7,4]],[[2,7,4,3,9,8,5,10,6],[1,6,4,3,9,8,5,10,7],[2,7,1,6,4,9,5,10,8],[1,6,5,10,3,2,8,7,9],[1,6,4,3,9,2,8,7,10],[1,7,4,3,9,8,5,10,2],[1,6,4,3,9,8,5,10,2],[1,7,4,3,9,6,5,10,2],[1,6,5,10,3,2,8,7,4],[1,6,4,3,9,2,8,7,5]],[[2,8,5,10,6,3,4,9,7],[1,7,4,3,9,6,5,10,8],[2,7,1,6,4,9,5,10,8],[1,7,5,3,9,2,8,6,10],[1,7,4,3,9,2,8,6,10],[1,7,5,3,4,9,8,2,10],[2,8,5,4,10,9,1,6,3],[1,7,5,3,9,6,10,2,4],[1,8,5,3,7,6,10,2,4],[1,7,4,3,9,2,8,6,5]],[[2,8,5,3,7,4,10,9,6],[1,6,4,9,3,10,7,5,8],[2,7,4,9,5,8,1,6,10],[1,8,5,3,7,6,10,2,9],[1,6,4,9,3,8,2,7,10],[1,8,5,3,7,4,10,2,9],[2,8,6,4,5,10,1,3,9],[1,9,5,7,3,6,10,2,4],[1,8,5,3,7,6,10,2,4],[1,6,4,9,3,8,2,7,5]],[[2,7,5,10,3,8,4,9,6],[1,6,4,9,3,8,5,10,7],[2,7,4,9,1,6,5,10,8],[1,9,5,7,3,2,10,6,8],[1,6,4,9,3,2,8,7,10],[1,7,4,9,3,8,5,10,2],[1,6,4,9,3,8,5,10,2],[1,7,4,6,9,10,3,5,2],[3,8,5,10,1,6,2,7,4],[1,6,4,9,3,2,8,7,5]],[[2,7,4,3,9,8,5,10,6],[1,6,4,9,10,3,7,5,8],[2,7,4,9,5,10,1,6,8],[1,7,5,3,2,9,10,6,8],[1,6,4,9,10,3,2,7,8],[1,7,4,3,9,8,5,10,2],[1,6,4,10,3,8,9,5,2],[1,6,4,9,10,3,7,5,2],[1,6,4,10,3,8,7,5,2],[]]],[[[2,7,4,3,10,8,6,5,11,9],[1,7,4,3,10,8,6,5,11,9],[2,1,7,10,6,4,9,5,11,8],[1,7,5,3,2,10,9,8,6,11],[1,7,4,3,2,10,8,11,6,9],[1,7,4,3,10,8,11,9,5,2],[1,8,5,3,10,9,6,4,2,11],[1,7,4,3,10,9,6,5,2,11],[1,7,4,3,10,8,6,5,2,11],[1,7,4,3,11,9,6,2,8,5],[1,7,4,3,10,9,6,2,8,5]],[[],[3,8,5,4,11,9,7,1,6,10],[2,8,5,1,7,4,10,11,6,9],[3,8,5,1,2,10,7,11,6,9],[2,8,6,4,3,1,10,9,7,11],[2,8,5,4,11,9,1,3,7,10],[2,8,5,4,11,9,1,10,6,3],[2,10,6,1,7,4,9,5,3,11],[2,8,5,1,7,4,10,11,6,3],[2,8,6,4,3,11,1,9,7,5],[2,8,6,4,1,10,9,5,7,3]],[[5,2,3,9,8,11,6,4,10,7],[3,9,1,11,6,5,8,4,10,7],[2,7,4,10,8,5,6,11,1,9],[3,1,8,10,6,5,2,9,7,11],[1,7,4,10,6,3,9,2,8,11],[2,7,4,10,8,5,11,9,1,3],[3,1,8,10,6,5,4,2,9,11],[1,7,4,10,6,3,9,5,2,11],[1,7,4,10,6,11,8,3,5,2],[3,9,1,7,5,11,8,4,6,2],[1,7,4,10,6,3,9,2,8,5]],[[2,8,5,11,6,3,9,4,10,7],[1,7,4,10,6,3,9,5,11,8],[2,7,4,10,6,1,9,5,11,8],[2,7,5,10,6,3,9,11,8,1],[1,7,4,10,6,3,9,2,8,11],[1,7,5,10,3,4,9,2,8,11],[2,8,5,10,6,1,4,3,9,11],[1,7,4,10,6,3,9,5,11,2],[1,7,4,10,6,11,3,8,5,2],[3,8,5,4,11,1,9,7,6,2],[1,7,4,10,6,3,9,2,8,5]],[[2,8,6,4,10,3,9,5,11,7],[1,7,5,3,10,4,9,11,6,8],[2,7,10,1,8,5,4,11,6,9],[1,7,5,3,10,9,2,11,6,8],[2,8,6,4,10,7,3,11,9,1],[1,7,5,3,10,11,4,8,9,2],[2,8,6,4,10,3,9,5,11,1],[1,7,5,3,10,4,9,11,6,2],[1,7,5,3,10,11,4,8,6,2],[1,7,5,11,3,4,9,8,6,2],[1,7,5,3,10,9,2,8,6,4]],[[2,7,4,10,3,9,6,5,11,8],[1,7,4,10,3,8,6,5,11,9],[2,7,4,10,8,1,6,5,11,9],[1,7,5,10,6,3,2,9,11,8],[1,7,4,10,3,8,6,2,11,9],[2,7,4,10,3,8,11,9,5,1],[1,8,5,10,6,3,4,9,11,2],[1,7,4,10,6,3,9,5,11,2],[1,7,4,10,3,8,6,5,11,2],[1,8,6,4,11,3,2,9,7,5],[1,7,4,10,6,3,2,9,8,5]],[[2,8,5,3,10,9,6,4,11,7],[1,7,4,3,10,9,6,5,11,8],[2,7,5,10,1,4,9,11,6,8],[1,7,5,3,10,2,9,11,6,8],[1,7,4,3,10,9,6,2,8,11],[1,7,5,3,4,10,9,2,8,11],[2,8,5,4,10,9,1,11,6,3],[1,7,4,3,10,9,6,5,11,2],[1,8,5,3,10,2,7,11,6,4],[1,7,11,4,6,3,9,2,8,5],[1,7,4,3,10,9,6,2,8,5]],[[2,9,5,7,11,3,4,10,6,8],[1,8,5,3,10,7,4,11,6,9],[2,9,5,4,11,7,6,10,1,8],[1,8,5,3,10,7,6,11,2,9],[1,8,6,4,10,3,2,9,7,11],[1,8,5,3,10,7,4,11,2,9],[2,9,6,4,5,11,8,1,3,10],[2,9,5,4,11,7,6,10,1,3],[1,8,5,3,10,7,6,11,2,4],[1,9,5,3,8,7,6,11,2,4],[1,8,6,4,10,3,2,9,7,5]],[[2,7,4,10,3,11,6,8,5,9],[1,9,5,7,3,4,11,8,6,10],[2,7,4,10,6,5,9,1,11,8],[1,9,5,7,3,11,6,2,10,8],[1,7,4,10,3,9,6,2,8,11],[1,9,5,7,3,4,11,2,8,10],[1,9,5,8,3,11,6,4,10,2],[2,7,4,10,6,5,9,1,3,11],[2,8,5,10,3,11,6,1,7,4],[1,9,5,8,3,11,6,2,7,4],[1,7,4,10,3,9,6,2,8,5]],[[2,7,4,11,3,9,6,5,10,8],[1,7,4,10,3,9,6,5,11,8],[2,7,4,10,6,1,9,5,11,8],[1,7,5,10,3,2,9,11,6,8],[1,7,4,10,3,9,6,2,8,11],[1,7,5,10,3,9,4,8,11,2],[1,8,5,3,10,9,6,11,4,2],[1,7,4,10,3,9,6,5,11,2],[1,8,5,3,10,7,6,2,4,11],[3,9,6,11,1,7,4,2,8,5],[1,7,4,10,3,9,6,2,8,5]],[[2,7,4,3,10,8,6,11,5,9],[1,7,4,3,11,9,6,10,5,8],[2,7,4,10,8,11,5,1,6,9],[1,7,5,3,2,10,11,8,6,9],[1,7,4,3,10,8,11,2,6,9],[1,7,4,3,10,8,11,9,5,2],[1,9,5,11,6,3,8,4,2,10],[1,7,4,3,11,9,6,10,5,2],[1,7,5,3,2,10,11,8,6,4],[1,7,5,3,2,11,9,8,6,4],[]]],[[[2,8,5,3,11,9,6,4,12,10,7],[1,7,4,3,10,9,6,5,12,11,8],[2,1,8,7,5,4,11,10,6,12,9],[1,7,5,3,2,10,9,8,6,12,11],[1,7,4,3,2,10,9,8,6,12,11],[1,7,4,3,10,9,8,5,2,12,11],[1,8,5,3,11,9,6,4,2,12,10],[1,7,4,3,10,9,6,5,2,12,11],[1,7,4,3,10,12,8,6,5,2,11],[1,7,4,3,2,11,9,8,6,5,12],[1,7,4,3,2,10,9,8,6,5,12],[1,7,4,3,2,11,9,10,6,8,5]],[[],[3,9,1,7,5,4,11,10,6,12,8],[2,8,5,4,11,1,9,7,6,12,10],[3,9,1,2,11,7,6,5,10,8,12],[2,8,6,4,3,11,10,9,1,7,12],[2,8,5,4,11,1,3,9,12,7,10],[2,8,6,4,5,11,10,1,3,9,12],[2,9,1,7,5,4,11,10,6,3,12],[2,8,5,4,11,10,1,7,6,3,12],[2,8,5,4,11,1,9,7,6,3,12],[2,8,6,4,3,12,10,9,1,7,5],[2,8,5,4,11,10,1,7,3,9,6]],[[2,8,5,3,11,9,6,4,12,10,7],[1,7,4,3,10,9,6,5,12,11,8],[4,2,9,11,6,5,12,8,1,7,10],[2,8,5,3,11,9,6,12,1,7,10],[1,7,4,3,10,9,6,12,2,8,11],[2,8,5,3,11,12,7,9,4,10,1],[2,8,5,3,11,9,6,4,12,10,1],[1,7,4,3,10,9,6,5,12,11,2],[1,7,4,3,10,12,8,6,5,11,2],[2,8,5,3,11,9,6,12,1,7,4],[1,7,4,3,10,9,6,12,2,8,5],[3,1,8,7,5,4,11,10,2,9,6]],[[2,8,5,11,3,9,6,4,12,10,7],[1,7,4,10,3,9,6,5,12,11,8],[2,8,5,4,11,10,1,7,6,12,9],[1,7,5,3,10,9,6,12,2,8,11],[1,7,4,10,3,9,6,12,2,8,11],[1,7,5,3,10,9,4,12,2,8,11],[1,8,5,11,3,9,6,4,12,10,2],[1,7,4,10,3,9,6,5,12,11,2],[1,7,4,10,6,12,11,3,8,5,2],[1,7,4,11,3,9,6,12,2,8,5],[1,7,4,10,3,9,6,12,2,8,5],[1,7,4,11,3,9,6,10,2,8,5]],[[2,8,6,4,11,12,3,9,5,10,7],[1,7,5,3,10,9,12,11,4,6,8],[2,8,5,11,1,7,4,10,6,12,9],[1,7,5,11,3,2,9,8,6,12,10],[2,8,6,4,11,10,3,12,7,9,1],[1,7,5,3,10,9,8,4,12,11,2],[2,8,6,4,5,11,12,1,9,10,3],[1,7,5,3,10,9,12,11,4,6,2],[1,7,10,5,12,11,3,4,8,6,2],[1,7,5,11,3,2,9,8,6,12,4],[1,7,5,3,10,2,9,8,6,12,4],[1,7,5,11,3,9,6,2,10,8,4]],[[2,8,5,11,3,9,6,12,4,10,7],[1,7,4,3,10,9,6,12,5,11,8],[2,8,6,4,5,11,10,12,1,7,9],[1,7,5,10,12,3,8,6,2,11,9],[1,7,4,3,10,9,6,12,2,8,11],[1,7,4,10,12,3,8,9,5,11,2],[1,8,5,11,3,9,6,12,4,10,2],[1,7,4,3,10,9,6,12,5,11,2],[1,7,4,10,12,3,8,6,5,11,2],[1,7,5,11,3,2,9,8,6,12,4],[1,7,4,3,10,9,6,12,2,8,5],[1,7,5,11,3,9,6,2,10,8,4]],[[2,8,5,11,3,9,6,12,4,10,7],[1,7,4,3,10,9,6,12,5,11,8],[2,8,1,7,5,4,11,10,6,12,9],[1,7,5,3,10,2,9,8,6,12,11],[1,7,4,3,10,2,9,8,6,12,11],[1,7,5,3,10,9,8,4,12,2,11],[2,8,5,11,3,9,6,12,4,10,1],[1,7,4,3,10,9,6,12,5,11,2],[1,8,5,7,3,4,11,10,6,12,2],[1,7,4,11,3,2,9,8,6,12,5],[1,7,4,3,10,2,9,8,6,12,5],[1,7,4,11,3,2,9,10,6,8,5]],[[2,8,5,3,11,10,7,4,6,12,9],[1,8,5,3,11,7,4,10,6,12,9],[2,8,5,4,11,10,1,7,6,12,9],[1,8,5,3,11,2,10,7,6,12,9],[1,8,6,4,11,3,10,2,9,7,12],[1,8,5,3,11,7,4,10,9,2,12],[2,8,6,4,5,11,10,9,1,3,12],[1,9,5,3,11,7,2,10,6,12,4],[1,8,5,3,11,2,10,7,6,12,4],[1,9,5,3,2,8,11,7,6,12,4],[1,8,5,7,12,3,10,2,9,6,4],[1,8,5,3,11,7,4,10,9,2,6]],[[2,8,5,11,3,9,6,12,4,10,7],[1,7,4,10,3,9,6,5,12,11,8],[2,8,5,11,6,12,1,4,9,7,10],[1,9,5,3,2,11,10,7,6,8,12],[1,7,4,10,3,9,6,12,2,8,11],[1,7,4,10,3,9,8,5,12,2,11],[1,9,5,3,8,11,6,12,4,2,10],[1,7,4,10,3,9,6,5,12,11,2],[2,10,6,4,12,8,5,11,1,7,3],[1,9,5,3,8,11,6,7,12,2,4],[1,7,4,10,3,9,6,12,2,8,5],[1,9,5,3,11,7,4,10,2,8,6]],[[2,8,5,11,3,9,6,12,4,10,7],[1,7,4,10,3,9,6,5,12,11,8],[2,8,5,11,1,7,4,10,6,12,9],[1,7,5,10,3,9,6,12,2,8,11],[1,7,4,10,3,9,6,12,2,8,11],[1,7,4,10,3,9,8,5,12,2,11],[1,8,5,11,3,9,6,12,4,10,2],[1,7,4,10,3,9,6,5,12,11,2],[1,8,5,11,3,2,10,7,6,4,12],[1,7,4,11,3,9,6,12,2,8,5],[1,7,4,10,3,9,6,12,2,8,5],[1,7,4,11,3,2,9,10,6,8,5]],[[2,8,5,12,7,3,4,10,9,6,11],[1,7,4,11,3,9,6,5,10,12,8],[2,8,5,11,1,7,4,10,6,12,9],[1,7,5,11,3,2,9,8,6,12,10],[1,7,4,11,3,2,9,8,6,12,10],[1,7,4,11,3,9,8,5,12,2,10],[1,8,5,3,11,10,6,4,9,12,2],[1,7,4,11,3,9,6,5,10,12,2],[1,8,5,3,11,7,2,10,6,4,12],[1,7,4,11,3,2,9,8,6,5,12],[3,9,6,12,1,7,4,2,10,8,5],[2,8,5,11,1,7,4,3,10,9,6]],[[2,8,5,3,11,9,6,12,4,10,7],[1,7,4,3,10,9,6,12,5,11,8],[2,8,5,11,6,12,1,4,9,7,10],[1,7,5,3,2,10,9,8,6,12,11],[1,7,4,3,10,9,6,12,2,8,11],[1,7,5,3,4,10,9,12,2,8,11],[1,8,5,3,11,9,6,12,4,2,10],[1,7,4,3,10,9,6,12,5,2,11],[1,7,4,3,10,12,8,6,5,2,11],[1,7,5,3,2,11,9,8,6,12,4],[1,7,4,3,10,9,6,12,2,8,5],[]]]]

noncomputable def chainFor (q ν s : Nat) : List Nat := ((chainTbl.getD q []).getD ν []).getD (s - 1) []

/-- The exceptional classes (Conjecture RS): `s = 1` for `N ≡ 1`, `s = q` for `N ≡ -1`,
unless `q` is a power of `2`. -/
def excB (q ν s : Nat) : Bool :=
  !(q == 2 || q == 4 || q == 8) && ((ν == 1 && s == 1) || (ν + 1 == q && s == q))

def chainOKB (q ν s : Nat) (π : List Nat) : Bool :=
  decide (π.Perm ((List.range' 1 q).filter (fun t => t != s))) && decide (ChainOK q ν π)

noncomputable def chainQOK (q : Nat) : Bool :=
  (List.range q).all fun ν => (List.range' 1 q).all fun s =>
    excB q ν s || chainOKB q ν s (chainFor q ν s)

theorem chainQOK_2 : chainQOK 2 = true := by decide +kernel
theorem chainQOK_3 : chainQOK 3 = true := by decide +kernel
theorem chainQOK_4 : chainQOK 4 = true := by decide +kernel
theorem chainQOK_5 : chainQOK 5 = true := by decide +kernel
theorem chainQOK_6 : chainQOK 6 = true := by decide +kernel
theorem chainQOK_7 : chainQOK 7 = true := by decide +kernel
theorem chainQOK_8 : chainQOK 8 = true := by decide +kernel
theorem chainQOK_9 : chainQOK 9 = true := by decide +kernel
theorem chainQOK_10 : chainQOK 10 = true := by decide +kernel
theorem chainQOK_11 : chainQOK 11 = true := by decide +kernel
theorem chainQOK_12 : chainQOK 12 = true := by decide +kernel

theorem chainQOK_all : ∀ q, 2 ≤ q → q < 13 → chainQOK q = true := by
  intro q h2 h17
  interval_cases q
  · exact chainQOK_2
  · exact chainQOK_3
  · exact chainQOK_4
  · exact chainQOK_5
  · exact chainQOK_6
  · exact chainQOK_7
  · exact chainQOK_8
  · exact chainQOK_9
  · exact chainQOK_10
  · exact chainQOK_11
  · exact chainQOK_12

theorem chainFor_ok {q ν s : Nat} (h2 : 2 ≤ q) (hq : q < 13) (hν : ν < q) (hs1 : 1 ≤ s)
    (hsq : s ≤ q) (he : excB q ν s = false) : chainOKB q ν s (chainFor q ν s) = true := by
  have h := chainQOK_all q h2 hq
  unfold chainQOK at h
  have h' := (List.all_eq_true.1 h) ν (List.mem_range.2 hν)
  have h'' := (List.all_eq_true.1 h') s (List.mem_range'_1.2 ⟨hs1, by omega⟩)
  rw [he, Bool.false_or] at h''
  exact h''

/-- **Residue transfer for `q ≤ 12`**, every non-exceptional class: co-reachable sets of the
class strip stay co-reachable. -/
theorem coReach_mod {q N s : Nat} (hq2 : 2 ≤ q) (hq12 : q ≤ 12) (hqN : q ≤ N) (hs1 : 1 ≤ s)
    (hsq : s ≤ q) (hexc : excB q (N % q) s = false) {D : Finset Nat}
    (hDs : D ⊆ Finset.Icc 1 (ccount q s N)) (hD : CoReach (ccount q s N) D) :
    CoReach N (D.image (cls q s)) := by
  have hok := chainFor_ok hq2 (by omega) (Nat.mod_lt N (by omega)) hs1 hsq hexc
  unfold chainOKB at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hperm, hc⟩ := hok
  refine coReach_res (by omega) hqN hs1 hsq (π := chainFor q (N % q) s) ?_ ?_ hc hDs hD
  · intro t
    rw [hperm.mem_iff, List.mem_filter, List.mem_range'_1]
    simp only [bne_iff_ne, ne_eq]
    omega
  · exact hperm.nodup_iff.2 ((List.nodup_range' ..).filter _)

/-! ## Mirror, small strips, and the closure -/

theorem coReach_mirror {N : Nat} {D : Finset Nat} (hD : CoReach N D) :
    CoReach N (D.image (N + 1 - ·)) := by
  unfold CoReach g at *
  rw [Finset.card_pos] at hD ⊢
  obtain ⟨l, hl⟩ := hD
  rw [mem_semiOrders] at hl
  obtain ⟨⟨hnd, hs⟩, hv⟩ := hl
  have m : ∀ x, x ∈ l ↔ (1 ≤ x ∧ x ≤ N) ∧ x ∉ D := by
    intro x; rw [← List.mem_toFinset, hs]; simp
  refine ⟨l.map (N + 1 - ·), mem_semiOrders.2 ⟨⟨?_, ?_⟩, ?_⟩⟩
  · exact nodup_map_of_injOn hnd fun a ha b hb e => by
      have := ((m a).1 ha).1; have := ((m b).1 hb).1; omega
  · ext x
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_sdiff, Finset.mem_Icc,
      Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hy1, hyD⟩ := (m y).1 hy
      refine ⟨by omega, fun ⟨d, hd, e⟩ => hyD ?_⟩
      by_cases hdN : d ≤ N
      · rwa [show y = d by omega]
      · omega
    · rintro ⟨hx, hxD⟩
      refine ⟨N + 1 - x, (m _).2 ⟨by omega, fun h => hxD ⟨N + 1 - x, h, by omega⟩⟩, by omega⟩
  · intro k hk
    simp only [List.length_map] at hk
    rw [List.getElem_map, ← List.map_take]
    have hb := ((m _).1 (List.getElem_mem hk)).1
    exact (semiStep_mirror_iff (fun x hx => ((m x).1 (List.mem_of_mem_take hx)).1.2)
      hb.1 hb.2).2 (hv k hk)

/-- At most one panel left: trivially co-reachable. -/
theorem coReach_small {N : Nat} {D : Finset Nat} (h : (Finset.Icc 1 N \ D).card ≤ 1) :
    CoReach N D := by
  unfold CoReach g
  rw [Finset.card_pos]
  refine ⟨(Finset.Icc 1 N \ D).toList, mem_semiOrders.2 ⟨⟨Finset.nodup_toList _, by simp⟩, ?_⟩⟩
  intro k hk
  have hl : (Finset.Icc 1 N \ D).toList.length ≤ 1 := by rwa [Finset.length_toList]
  obtain rfl : k = 0 := by omega
  simp [SemiStep, leftCount, rightCount]

set_option maxRecDepth 100000 in
/-- Witnesses for every non-dead 2-set of the strips `N ≤ 12`
(`experiments/live2/orderset.py`): `(u, v, ordering of [N] \ {u, v})`. -/
noncomputable def witTbl : List (List (Nat × Nat × List Nat)) :=
  [[],
  [],
  [(1,2,[])],
  [(1,2,[3]),(1,3,[2]),(2,3,[1])],
  [(1,2,[3,4]),(1,3,[2,4]),(2,3,[1,4]),(2,4,[1,3]),(3,4,[2,1])],
  [(1,2,[3,5,4]),(1,3,[2,4,5]),(1,4,[2,5,3]),(1,5,[2,4,3]),(2,3,[1,4,5]),(2,4,[3,1,5]),(2,5,[1,4,3]),(3,4,[2,1,5]),(3,5,[2,1,4]),(4,5,[3,1,2])],
  [(1,2,[3,5,4,6]),(1,3,[2,5,4,6]),(1,4,[2,5,3,6]),(1,5,[4,2,3,6]),(2,3,[1,4,6,5]),(2,4,[3,1,5,6]),(2,5,[1,4,3,6]),(2,6,[3,1,5,4]),(3,4,[2,1,5,6]),(3,5,[4,2,1,6]),(3,6,[2,1,5,4]),(4,5,[3,1,2,6]),(4,6,[3,1,2,5]),(5,6,[1,4,3,2])],
  [(1,2,[3,6,4,7,5]),(1,3,[4,2,6,5,7]),(1,4,[2,5,3,7,6]),(1,5,[4,2,3,6,7]),(1,6,[2,5,3,7,4]),(2,3,[4,1,6,5,7]),(2,4,[3,1,6,5,7]),(2,5,[4,1,3,6,7]),(2,6,[1,5,3,7,4]),(2,7,[3,1,6,5,4]),(3,4,[2,1,5,7,6]),(3,5,[4,2,1,6,7]),(3,6,[2,5,4,1,7]),(3,7,[4,2,1,6,5]),(4,5,[3,1,2,6,7]),(4,6,[1,5,3,2,7]),(4,7,[3,1,2,6,5]),(5,6,[4,1,3,2,7]),(5,7,[4,1,3,2,6]),(6,7,[2,5,4,1,3])],
  [(1,2,[3,7,4,6,5,8]),(1,3,[4,2,7,6,5,8]),(1,4,[5,2,3,7,6,8]),(1,5,[4,2,3,7,6,8]),(1,6,[5,2,3,7,4,8]),(1,7,[2,6,5,3,4,8]),(2,3,[1,6,4,5,8,7]),(2,4,[1,5,3,7,6,8]),(2,5,[4,1,3,7,6,8]),(2,6,[1,5,3,7,4,8]),(2,7,[3,1,6,5,4,8]),(2,8,[4,1,3,7,6,5]),(3,4,[5,2,1,7,6,8]),(3,5,[4,2,1,7,6,8]),(3,6,[5,2,4,1,7,8]),(3,7,[2,1,6,5,4,8]),(3,8,[4,2,1,7,6,5]),(4,5,[3,1,2,6,8,7]),(4,6,[1,5,3,2,7,8]),(4,7,[3,1,6,5,2,8]),(4,8,[1,5,3,2,7,6]),(5,6,[4,1,3,2,7,8]),(5,7,[1,6,4,3,2,8]),(5,8,[4,1,3,2,7,6]),(6,7,[5,2,4,1,3,8]),(6,8,[5,2,4,1,3,7]),(7,8,[2,1,6,5,4,3])],
  [(1,2,[6,3,4,8,5,9,7]),(1,3,[5,2,4,8,7,6,9]),(1,4,[5,2,3,8,7,6,9]),(1,5,[2,6,4,3,8,7,9]),(1,6,[5,2,3,8,7,4,9]),(1,7,[2,6,5,3,4,8,9]),(1,8,[4,2,7,6,3,9,5]),(1,9,[2,6,4,3,8,7,5]),(2,3,[5,1,4,8,7,6,9]),(2,4,[5,1,3,8,7,6,9]),(2,5,[1,6,4,3,8,7,9]),(2,6,[3,8,5,4,1,7,9]),(2,7,[1,6,5,3,4,8,9]),(2,8,[3,1,7,6,4,9,5]),(2,9,[1,6,4,3,8,7,5]),(3,4,[2,7,5,1,6,9,8]),(3,5,[2,6,4,1,8,7,9]),(3,6,[5,2,4,1,8,7,9]),(3,7,[2,6,5,1,4,8,9]),(3,8,[4,2,7,6,5,1,9]),(3,9,[5,2,4,1,8,7,6]),(4,5,[6,3,1,2,8,7,9]),(4,6,[5,1,3,2,8,7,9]),(4,7,[1,6,5,3,2,8,9]),(4,8,[3,1,7,6,5,2,9]),(4,9,[5,1,3,2,8,7,6]),(5,6,[4,1,3,2,7,9,8]),(5,7,[1,6,4,3,2,8,9]),(5,8,[3,1,7,6,4,2,9]),(5,9,[1,6,4,3,2,8,7]),(6,7,[5,2,4,1,3,8,9]),(6,8,[2,7,5,1,4,3,9]),(6,9,[5,2,4,1,3,8,7]),(7,8,[2,6,5,1,4,3,9]),(7,9,[2,6,5,1,4,3,8]),(8,9,[3,1,7,6,5,2,4])],
  [(1,2,[3,7,4,9,5,8,6,10]),(1,3,[2,7,4,9,5,8,6,10]),(1,4,[6,2,5,3,9,8,7,10]),(1,5,[6,2,4,3,9,8,7,10]),(1,6,[2,7,5,3,4,9,8,10]),(1,7,[6,2,5,3,4,9,8,10]),(1,8,[2,7,4,9,6,3,5,10]),(1,9,[4,2,8,7,6,3,5,10]),(2,3,[4,1,8,7,5,6,10,9]),(2,4,[1,6,5,3,9,8,7,10]),(2,5,[1,6,4,3,9,8,7,10]),(2,6,[1,7,5,3,4,9,8,10]),(2,7,[1,6,5,3,4,9,8,10]),(2,8,[3,1,7,6,4,9,5,10]),(2,9,[4,1,3,8,7,6,5,10]),(2,10,[1,7,5,3,4,9,8,6]),(3,4,[6,2,5,1,9,8,7,10]),(3,5,[6,2,4,1,9,8,7,10]),(3,6,[2,7,5,1,4,9,8,10]),(3,7,[6,2,5,1,4,9,8,10]),(3,8,[2,1,7,6,4,9,5,10]),(3,9,[4,2,1,8,7,6,5,10]),(3,10,[2,7,5,1,4,9,8,6]),(4,5,[3,1,8,6,2,7,10,9]),(4,6,[1,7,5,3,2,9,8,10]),(4,7,[1,6,5,3,2,9,8,10]),(4,8,[3,1,7,6,5,2,9,10]),(4,9,[3,1,8,6,2,7,5,10]),(4,10,[1,6,5,3,2,9,8,7]),(5,6,[1,7,4,3,2,9,8,10]),(5,7,[1,6,4,3,2,9,8,10]),(5,8,[3,1,7,6,4,2,9,10]),(5,9,[4,1,3,8,7,6,2,10]),(5,10,[1,6,4,3,2,9,8,7]),(6,7,[5,2,4,1,3,8,10,9]),(6,8,[2,7,5,1,4,3,9,10]),(6,9,[5,2,1,8,7,4,3,10]),(6,10,[2,7,5,1,4,3,9,8]),(7,8,[6,2,5,1,4,3,9,10]),(7,9,[2,1,8,6,5,4,3,10]),(7,10,[6,2,5,1,4,3,9,8]),(8,9,[3,1,7,6,5,2,4,10]),(8,10,[3,1,7,6,5,2,4,9]),(9,10,[3,1,8,6,2,7,5,4])],
  [(1,2,[3,8,7,4,5,10,6,11,9]),(1,3,[2,8,6,4,5,10,9,7,11]),(1,4,[2,8,5,10,6,3,9,7,11]),(1,5,[2,7,4,10,6,3,9,8,11]),(1,6,[2,7,5,3,4,10,9,8,11]),(1,7,[2,8,5,10,6,3,4,9,11]),(1,8,[2,7,4,10,6,3,9,5,11]),(1,9,[4,2,8,7,6,3,5,10,11]),(1,10,[4,2,9,7,3,8,5,11,6]),(1,11,[2,7,5,3,4,10,9,8,6]),(2,3,[1,8,6,4,5,10,9,7,11]),(2,4,[3,8,6,1,5,10,9,7,11]),(2,5,[7,3,6,1,4,10,9,8,11]),(2,6,[1,7,5,3,4,10,9,8,11]),(2,7,[3,8,6,1,5,4,10,9,11]),(2,8,[7,3,4,10,6,5,1,9,11]),(2,9,[3,1,8,7,6,4,5,10,11]),(2,10,[4,1,9,7,3,8,5,11,6]),(2,11,[1,7,5,3,4,10,9,8,6]),(3,4,[5,2,9,8,6,1,7,11,10]),(3,5,[2,7,6,1,4,10,9,8,11]),(3,6,[2,7,5,1,4,10,9,8,11]),(3,7,[2,8,6,1,5,4,10,9,11]),(3,8,[2,7,4,10,6,5,1,9,11]),(3,9,[2,8,6,1,7,4,5,10,11]),(3,10,[5,2,4,9,8,7,6,1,11]),(3,11,[2,8,6,1,5,4,10,9,7]),(4,5,[7,3,6,1,2,10,9,8,11]),(4,6,[1,7,5,3,2,10,9,8,11]),(4,7,[3,8,6,1,5,2,10,9,11]),(4,8,[7,3,6,1,5,2,10,9,11]),(4,9,[3,1,8,7,6,2,5,10,11]),(4,10,[5,1,3,9,8,7,6,2,11]),(4,11,[3,8,6,1,5,2,10,9,7]),(5,6,[4,1,9,7,3,2,8,11,10]),(5,7,[1,8,6,4,3,2,10,9,11]),(5,8,[7,3,6,1,4,2,10,9,11]),(5,9,[3,1,8,7,6,4,2,10,11]),(5,10,[4,1,9,7,3,8,6,2,11]),(5,11,[7,3,6,1,4,2,10,9,8]),(6,7,[2,8,5,4,1,3,10,9,11]),(6,8,[2,7,5,1,4,3,10,9,11]),(6,9,[2,8,5,1,7,4,3,10,11]),(6,10,[5,2,4,1,9,8,7,3,11]),(6,11,[2,7,5,1,4,3,10,9,8]),(7,8,[6,2,5,1,4,3,9,11,10]),(7,9,[2,8,6,1,5,4,3,10,11]),(7,10,[6,2,4,1,9,8,5,3,11]),(7,11,[2,8,6,1,5,4,3,10,9]),(8,9,[7,3,6,1,5,2,4,10,11]),(8,10,[3,1,9,7,6,2,5,4,11]),(8,11,[7,3,6,1,5,2,4,10,9]),(9,10,[3,1,8,7,6,2,5,4,11]),(9,11,[3,1,8,7,6,2,5,4,10]),(10,11,[4,1,9,7,3,8,6,2,5])],
  [(1,2,[3,8,6,4,5,11,10,9,7,12]),(1,3,[2,8,6,4,5,11,10,9,7,12]),(1,4,[5,9,7,2,6,3,11,10,8,12]),(1,5,[2,9,7,4,6,3,11,10,8,12]),(1,6,[2,8,5,11,7,3,4,10,9,12]),(1,7,[2,8,5,11,6,3,4,10,9,12]),(1,8,[2,9,7,4,6,3,5,11,10,12]),(1,9,[2,8,7,4,6,3,5,11,10,12]),(1,10,[4,2,9,8,7,3,5,11,6,12]),(1,11,[7,2,4,3,10,9,8,5,6,12]),(2,3,[5,1,10,8,4,9,6,7,12,11]),(2,4,[5,1,9,7,6,3,11,10,8,12]),(2,5,[3,1,9,7,6,4,11,10,8,12]),(2,6,[3,1,8,7,5,4,11,10,9,12]),(2,7,[3,8,6,1,5,4,11,10,9,12]),(2,8,[3,1,9,7,6,4,5,11,10,12]),(2,9,[3,1,8,7,6,4,5,11,10,12]),(2,10,[4,1,3,9,8,7,5,11,6,12]),(2,11,[1,7,4,3,10,9,8,5,6,12]),(2,12,[3,8,6,1,5,4,11,10,9,7]),(3,4,[5,9,7,2,6,1,11,10,8,12]),(3,5,[2,1,9,7,6,4,11,10,8,12]),(3,6,[2,1,8,7,5,4,11,10,9,12]),(3,7,[2,8,6,1,5,4,11,10,9,12]),(3,8,[2,1,9,7,6,4,5,11,10,12]),(3,9,[2,1,8,7,6,4,5,11,10,12]),(3,10,[4,2,1,9,8,7,5,11,6,12]),(3,11,[5,2,10,8,4,1,9,7,6,12]),(3,12,[2,8,6,1,5,4,11,10,9,7]),(4,5,[7,3,1,2,10,9,6,8,12,11]),(4,6,[3,1,8,7,5,2,11,10,9,12]),(4,7,[3,8,6,1,5,2,11,10,9,12]),(4,8,[3,1,9,7,6,2,5,11,10,12]),(4,9,[3,1,8,7,6,2,5,11,10,12]),(4,10,[5,1,3,9,8,7,6,2,11,12]),(4,11,[1,7,5,3,2,10,9,8,6,12]),(4,12,[3,1,9,7,6,2,5,11,10,8]),(5,6,[8,4,1,7,3,2,11,10,9,12]),(5,7,[1,8,6,4,3,2,11,10,9,12]),(5,8,[3,1,9,7,6,4,2,11,10,12]),(5,9,[3,1,8,7,6,4,2,11,10,12]),(5,10,[4,1,3,9,8,7,6,2,11,12]),(5,11,[1,7,4,3,2,10,9,8,6,12]),(5,12,[3,1,9,7,6,4,2,11,10,8]),(6,7,[5,2,10,8,4,1,3,9,12,11]),(6,8,[2,1,9,7,5,4,3,11,10,12]),(6,9,[2,1,8,7,5,4,3,11,10,12]),(6,10,[4,2,1,9,8,7,5,3,11,12]),(6,11,[5,2,10,8,4,1,9,7,3,12]),(6,12,[2,1,8,7,5,4,3,11,10,9]),(7,8,[2,9,6,1,5,4,3,11,10,12]),(7,9,[2,8,6,1,5,4,3,11,10,12]),(7,10,[4,2,9,8,6,1,5,3,11,12]),(7,11,[6,2,4,1,10,9,8,5,3,12]),(7,12,[2,8,6,1,5,4,3,11,10,9]),(8,9,[7,3,6,1,5,2,4,10,12,11]),(8,10,[3,1,9,7,6,2,5,4,11,12]),(8,11,[7,3,1,2,10,9,6,5,4,12]),(8,12,[3,1,9,7,6,2,5,4,11,10]),(9,10,[3,1,8,7,6,2,5,4,11,12]),(9,11,[7,3,1,2,10,8,6,5,4,12]),(9,12,[3,1,8,7,6,2,5,4,11,10]),(10,11,[4,1,3,9,8,7,6,2,5,12]),(10,12,[4,1,3,9,8,7,6,2,5,11]),(11,12,[1,7,4,3,2,10,9,8,6,5])]]

def deadB (N u v : Nat) : Bool := u == 1 && v == N && ((N % 2 == 0 && 4 ≤ N) || N == 7)

def witOK (N : Nat) (e : Nat × Nat × List Nat) : Bool :=
  decide e.2.2.Nodup && decide (e.2.2.toFinset = Finset.Icc 1 N \ {e.1, e.2.1}) &&
    decide (SemiSymmetric N e.2.2)

noncomputable def witNOK (N : Nat) : Bool := (witTbl.getD N []).all (witOK N)

theorem witNOK_0 : witNOK 0 = true := by decide +kernel
theorem witNOK_1 : witNOK 1 = true := by decide +kernel
theorem witNOK_2 : witNOK 2 = true := by decide +kernel
theorem witNOK_3 : witNOK 3 = true := by decide +kernel
theorem witNOK_4 : witNOK 4 = true := by decide +kernel
theorem witNOK_5 : witNOK 5 = true := by decide +kernel
theorem witNOK_6 : witNOK 6 = true := by decide +kernel
theorem witNOK_7 : witNOK 7 = true := by decide +kernel
theorem witNOK_8 : witNOK 8 = true := by decide +kernel
theorem witNOK_9 : witNOK 9 = true := by decide +kernel
theorem witNOK_10 : witNOK 10 = true := by decide +kernel
theorem witNOK_11 : witNOK 11 = true := by decide +kernel
theorem witNOK_12 : witNOK 12 = true := by decide +kernel

theorem witTbl_ok : ∀ N, N < 13 → ∀ e ∈ witTbl.getD N [], witOK N e = true := by
  intro N hN e he
  have h : witNOK N = true := by
    interval_cases N
    · exact witNOK_0
    · exact witNOK_1
    · exact witNOK_2
    · exact witNOK_3
    · exact witNOK_4
    · exact witNOK_5
    · exact witNOK_6
    · exact witNOK_7
    · exact witNOK_8
    · exact witNOK_9
    · exact witNOK_10
    · exact witNOK_11
    · exact witNOK_12
  unfold witNOK at h
  exact (List.all_eq_true.1 h) e he

theorem witTbl_complete : ∀ N, N < 13 → ∀ u, u < N + 1 → ∀ v, v < N + 1 →
    (1 ≤ u ∧ u < v ∧ deadB N u v = false) →
      ((witTbl.getD N []).any fun e => e.1 == u && e.2.1 == v) = true := by decide +kernel

/-- **Conjecture C for `N ≤ 12`**: every 2-set except `{1, N}` (`N` even `≥ 4`) and
`{1, 7}` (`N = 7`) is co-reachable. -/
theorem coReach_base {N u v : Nat} (hN : N ≤ 12) (hu : 1 ≤ u) (huv : u < v) (hv : v ≤ N)
    (hd : deadB N u v = false) : CoReach N {u, v} := by
  have := witTbl_complete N (by omega) u (by omega) v (by omega) ⟨hu, huv, hd⟩
  rw [List.any_eq_true] at this
  obtain ⟨e, he, hb⟩ := this
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  have hok := witTbl_ok N (by omega) e he
  unfold witOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hnd, hs⟩, hv'⟩ := hok
  unfold CoReach g
  rw [Finset.card_pos]
  refine ⟨e.2.2, mem_semiOrders.2 ⟨⟨hnd, ?_⟩, hv'⟩⟩
  rw [hs, hb.1, hb.2]

/-- **The proven family.**  The closure of the base cases under residue transfers mod
`q ≤ 12` (non-exceptional classes) and the mirror. -/
inductive Cov : Nat → Finset Nat → Prop
  | small {N : Nat} {D : Finset Nat} : (Finset.Icc 1 N \ D).card ≤ 1 → Cov N D
  | table {N u v : Nat} : N ≤ 12 → 1 ≤ u → u < v → v ≤ N → deadB N u v = false →
      Cov N {u, v}
  | res {q N s : Nat} {D : Finset Nat} : 2 ≤ q → q ≤ 12 → q ≤ N → 1 ≤ s → s ≤ q →
      excB q (N % q) s = false → D ⊆ Finset.Icc 1 (ccount q s N) →
      Cov (ccount q s N) D → Cov N (D.image (cls q s))
  | mirror {N : Nat} {D : Finset Nat} : Cov N D → Cov N (D.image (N + 1 - ·))

theorem Cov.coReach {N : Nat} {D : Finset Nat} (h : Cov N D) : CoReach N D := by
  induction h with
  | small h => exact coReach_small h
  | table hN hu huv hv hd => exact coReach_base hN hu huv hv hd
  | res hq2 hq12 hqN hs1 hsq hexc hDs _ ih => exact coReach_mod hq2 hq12 hqN hs1 hsq hexc hDs ih
  | mirror _ ih => exact coReach_mirror ih

/-- Every valid 2-prefix whose set is in the family is live. -/
theorem Cov.extends {N u v : Nat} (h : Cov N {u, v}) (hu : 1 ≤ u ∧ u ≤ N)
    (hv : 1 ≤ v ∧ v ≤ N) (huv : u ≠ v) (hval : SemiSymmetric N [u, v]) :
    Extends N [u, v] := by
  rw [extends_iff_coReach (by simp [huv]) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption) hval]
  convert h.coReach using 2
  ext x; simp

end Live2
end Folds
