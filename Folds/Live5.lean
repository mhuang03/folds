import Folds.Adjacent

/-!
# Live pairs, part 5: Beatty transfers and the pairs `{1, N}`

`experiments/live5/PROOFS.txt`.
-/

namespace Folds

/-! ## Arm counts of a copy given by a counting function -/

theorem CountEmb.countP_left {N p : Nat} {φ c : Nat → Nat} (h : CountEmb N p φ c) {m : Nat}
    (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    ((List.range' 1 p).map φ).countP (fun x => decide (m - reach N m ≤ x ∧ x < m)) =
      c (m - 1) - c (m - reach N m - 1) := by
  rw [List.countP_map]
  have hr : reach N m ≤ m - 1 := by unfold reach; omega
  have L : (List.range' 1 p).countP ((fun x => decide (m - reach N m ≤ x ∧ x < m)) ∘ φ) =
      (List.range' 1 p).countP
        (fun y => decide (c (m - reach N m - 1) + 1 ≤ y ∧ y ≤ c (m - 1))) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    have a := h.gal y (m - 1) hy.1
    have b := h.gal y (m - reach N m - 1) hy.1
    omega
  rw [L, countP_range'_interval]
  have := h.c_mono (show m - 1 ≤ N by omega); rw [h.top] at this
  have := h.c_mono (show m - reach N m - 1 ≤ m - 1 by omega)
  omega

theorem CountEmb.countP_right {N p : Nat} {φ c : Nat → Nat} (h : CountEmb N p φ c) {m : Nat}
    (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    ((List.range' 1 p).map φ).countP (fun x => decide (m < x ∧ x ≤ m + reach N m)) =
      c (m + reach N m) - c m := by
  rw [List.countP_map]
  have hr : m + reach N m ≤ N := by unfold reach; omega
  have R : (List.range' 1 p).countP ((fun x => decide (m < x ∧ x ≤ m + reach N m)) ∘ φ) =
      (List.range' 1 p).countP (fun y => decide (c m + 1 ≤ y ∧ y ≤ c (m + reach N m))) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    have a := h.gal y m hy.1
    have b := h.gal y (m + reach N m) hy.1
    omega
  rw [R, countP_range'_interval]
  have := h.c_mono hr; rw [h.top] at this
  have := h.c_mono (show m ≤ m + reach N m by omega)
  omega

/-- A panel outside the image does not raise the counting function. -/
theorem CountEmb.c_pred_of_not_mem {N p : Nat} {φ c : Nat → Nat} (h : CountEmb N p φ c)
    {m : Nat} (hm1 : 1 ≤ m) (hmN : m ≤ N) (hm : ∀ y, 1 ≤ y → y ≤ p → φ y ≠ m) :
    c m = c (m - 1) := by
  have hle := h.c_mono (show m - 1 ≤ m by omega)
  by_contra hne
  have hpos : 1 ≤ c m := by omega
  have hcp : c m ≤ p := by have := h.c_mono hmN; rw [h.top] at this; exact this
  have a := (h.gal (c m) m hpos).2 le_rfl
  have b := h.gal (c m) (m - 1) hpos
  have : ¬ φ (c m) ≤ m - 1 := fun h' => by have := b.1 h'; omega
  exact hm (c m) hpos hcp (by omega)

namespace Live5

open Live2 Live4 Adjacent

/-- The image list of an injective map on `[1, p]` is a permutation of its `toList`. -/
theorem image_toList_perm {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ) :
    ((Finset.Icc 1 p).image φ).toList.Perm ((List.range' 1 p).map φ) := by
  refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _)
    (hφ.nodup_map (List.nodup_range' ..) fun y hy => by
      rw [List.mem_range'_1] at hy; omega)).2 fun x => ?_
  simp only [Finset.mem_toList, Finset.mem_image, Finset.mem_Icc, List.mem_map,
    List.mem_range'_1]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, ⟨hy.1, by omega⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, ⟨hy.1, by omega⟩, rfl⟩

/-! ## Right-aligned Beatty copies are co-reachable -/

/-- The key inequality: for `h ≤ 1` and `k = c(m - 1)`, `2 k N ≤ 2 p m + h - 1`. -/
theorem beatty_key {N p h m : Nat} (hN : 0 < N) (hp : 1 ≤ p) (hm : 1 ≤ m) (h1 : h ≤ 1) :
    2 * (beattyCnt N p h (m - 1)) ≤ (2 * (p * m) + h - 1) / N := by
  unfold beattyCnt
  have e : p * (m - 1) + p + h - 1 = p * m + h - 1 := by
    rw [Nat.mul_sub_one]; have : p ≤ p * m := Nat.le_mul_of_pos_right p hm; omega
  rw [e, Nat.le_div_iff_mul_le hN]
  have := Nat.div_mul_le_self (p * m + h - 1) N
  have : p ≤ p * m := Nat.le_mul_of_pos_right p hm
  rw [Nat.mul_assoc]
  omega

/-- **Right-aligned Beatty copies pull every other panel to the right**: for `h ≤ 1` the
Beatty set `{⌊(rN - h)/p⌋}` satisfies the criterion of Theorem G with the centre right of
the strip. -/
theorem inward_beatty {N p h : Nat} (hp : 1 ≤ p) (hh : h + 2 * p ≤ N + 1) (h1 : h ≤ 1) :
    Inward N (2 * N + 1) ((Finset.Icc 1 p).image (beatty N p h)) := by
  have hN : 0 < N := by omega
  have hc := countEmb_beatty hp hh
  have hφ := winEmb_beatty hp hh
  have hperm := image_toList_perm hφ
  have hnd := Finset.nodup_toList ((Finset.Icc 1 p).image (beatty N p h))
  intro m hm1 hmN hmB
  refine ⟨by omega, fun _ => ?_, fun h' => by omega⟩
  have hnot : ∀ y, 1 ≤ y → y ≤ p → beatty N p h y ≠ m := fun y hy1 hyp e =>
    hmB (Finset.mem_image.2 ⟨y, Finset.mem_Icc.2 ⟨hy1, hyp⟩, e⟩)
  have hcm := hc.c_pred_of_not_mem hm1 hmN hnot
  rw [leftCount_eq hnd, rightCount_eq hnd, hperm.countP_eq, hperm.countP_eq,
    hc.countP_left hm1 hmN, hc.countP_right hm1 hmN, hcm]
  have key := beatty_key (h := h) hN hp hm1 h1
  rcases Nat.le_total (m - 1) (N - m) with hle | hle
  · have hr : reach N m = m - 1 := by unfold reach; omega
    rw [hr, show m - (m - 1) - 1 = 0 by omega, hc.zero,
      show m + (m - 1) = 2 * m - 1 by omega]
    have e : beattyCnt N p h (2 * m - 1) = (2 * (p * m) + h - 1) / N := by
      unfold beattyCnt
      congr 1
      rw [Nat.mul_sub_one, Nat.mul_left_comm]
      have : p ≤ 2 * (p * m) := by
        have := Nat.le_mul_of_pos_right p hm1; omega
      omega
    rw [e]; omega
  · have hr : reach N m = N - m := by unfold reach; omega
    rw [hr, show m + (N - m) = N by omega, hc.top,
      show m - (N - m) - 1 = 2 * m - N - 1 by omega]
    have e : beattyCnt N p h (2 * m - N - 1) + p = (2 * (p * m) + h - 1) / N := by
      unfold beattyCnt
      obtain ⟨t, ht⟩ : ∃ t, 2 * m = N + 1 + t := ⟨2 * m - N - 1, by omega⟩
      have et : 2 * m - N - 1 = t := by omega
      have e2 : 2 * (p * m) = p * N + p + p * t := by
        rw [show 2 * (p * m) = p * (2 * m) by ring, ht, Nat.mul_add, Nat.mul_add, Nat.mul_one]
      have e1 : p * (2 * m - N - 1) + p + h - 1 = (2 * (p * m) + h - 1) - p * N := by
        rw [et]; omega
      rw [e1]
      conv_rhs => rw [show 2 * (p * m) + h - 1 = (2 * (p * m) + h - 1 - p * N) + p * N by
        omega]
      rw [Nat.add_mul_div_right _ _ hN]
    have := hc.c_mono (show m - 1 ≤ N by omega); rw [hc.top] at this
    omega

/-- Right-aligned Beatty copies are co-reachable. -/
theorem coReach_beatty {N p h : Nat} (hp : 1 ≤ p) (hh : h + 2 * p ≤ N + 1) (h1 : h ≤ 1) :
    CoReach N ((Finset.Icc 1 p).image (beatty N p h)) := by
  refine coReach_of_inward (fun x hx => ?_) (inward_beatty hp hh h1)
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
  rw [Finset.mem_Icc] at hy ⊢
  exact (winEmb_beatty hp hh).bound y hy.1 hy.2

/-- **Beatty transfer**: co-reachable sets of the `p`-strip stay co-reachable through a
right-aligned Beatty copy (`h ≤ 1`). -/
theorem coReach_beatty_transfer {N p h : Nat} (hp : 1 ≤ p) (hh : h + 2 * p ≤ N + 1)
    (h1 : h ≤ 1) {D : Finset Nat} (hDs : D ⊆ Finset.Icc 1 p) (hD : CoReach p D) :
    CoReach N (D.image (beatty N p h)) :=
  coReach_winEmb (winEmb_beatty hp hh) (coReach_beatty hp hh h1) hDs hD

end Live5
end Folds
