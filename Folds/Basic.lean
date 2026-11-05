import Folds.Defs

namespace Folds

/-! ## Symmetric ⇒ semi-symmetric -/

theorem SymStep.semiStep {N : Nat} {S : List Nat} {m : Nat} (h : SymStep N S m) :
    SemiStep N S m := by
  unfold SemiStep leftCount rightCount
  apply List.countP_congr
  intro d hd
  rw [List.mem_range'_1] at hd
  simpa using h d (by omega) (by omega)

theorem Symmetric.semiSymmetric {N : Nat} {a : List Nat} (h : Symmetric N a) :
    SemiSymmetric N a :=
  fun k hk => (h k hk).semiStep

/-! ## Complementing the set of already-bisected panels -/

theorem semiStep_iff_of_compl {N m : Nat} {S T : List Nat}
    (hST : ∀ d, 1 ≤ d → d ≤ reach N m →
      ((m - d ∈ T ↔ m - d ∉ S) ∧ (m + d ∈ T ↔ m + d ∉ S))) :
    SemiStep N S m ↔ SemiStep N T m := by
  have hl : leftCount N T m = reach N m - leftCount N S m := by
    have h1 := List.length_eq_countP_add_countP (fun d => decide (m - d ∈ S))
      (l := List.range' 1 (reach N m))
    have h2 : leftCount N T m = (List.range' 1 (reach N m)).countP
        (fun d => decide ¬decide (m - d ∈ S) = true) := by
      unfold leftCount; apply List.countP_congr
      intro d hd; rw [List.mem_range'_1] at hd
      simp [(hST d (by omega) (by omega)).1]
    simp only [List.length_range'] at h1
    unfold leftCount at *; omega
  have hr : rightCount N T m = reach N m - rightCount N S m := by
    have h1 := List.length_eq_countP_add_countP (fun d => decide (m + d ∈ S))
      (l := List.range' 1 (reach N m))
    have h2 : rightCount N T m = (List.range' 1 (reach N m)).countP
        (fun d => decide ¬decide (m + d ∈ S) = true) := by
      unfold rightCount; apply List.countP_congr
      intro d hd; rw [List.mem_range'_1] at hd
      simp [(hST d (by omega) (by omega)).2]
    simp only [List.length_range'] at h1
    unfold rightCount at *; omega
  have bl : leftCount N S m ≤ reach N m := by
    have := List.countP_le_length (p := fun d => decide (m - d ∈ S)) (l := List.range' 1 (reach N m))
    simpa [leftCount] using this
  have br : rightCount N S m ≤ reach N m := by
    have := List.countP_le_length (p := fun d => decide (m + d ∈ S)) (l := List.range' 1 (reach N m))
    simpa [rightCount] using this
  unfold SemiStep; omega

theorem getElem_mem_take_iff {a : List Nat} (hnd : a.Nodup) {p j : Nat} (hp : p < a.length) :
    a[p] ∈ a.take j ↔ p < j := by
  constructor
  · intro h
    obtain ⟨q, hq, hqe⟩ := List.mem_iff_getElem.1 h
    rw [List.getElem_take] at hqe
    have : q = p := (List.Nodup.getElem_inj hnd).1 hqe
    simp at hq; omega
  · intro h
    have : (a.take j)[p]'(by simp; omega) = a[p] := List.getElem_take ..
    rw [← this]; exact List.getElem_mem _

theorem getElem_mem_drop_iff {a : List Nat} (hnd : a.Nodup) {p j : Nat} (hp : p < a.length) :
    a[p] ∈ a.drop j ↔ j ≤ p := by
  constructor
  · intro h
    obtain ⟨q, hq, hqe⟩ := List.mem_iff_getElem.1 h
    rw [List.getElem_drop] at hqe
    have : j + q = p := (List.Nodup.getElem_inj hnd).1 hqe
    omega
  · intro h
    have : (a.drop j)[p - j]'(by simp; omega) = a[p] := by
      rw [List.getElem_drop]; congr 1; omega
    rw [← this]; exact List.getElem_mem _

theorem mem_range'_of_perm {N : Nat} {a : List Nat} (h : IsFoldSeq N a) {x : Nat} :
    x ∈ a ↔ 1 ≤ x ∧ x ≤ N := by
  rw [h.mem_iff, List.mem_range'_1]; omega

theorem reversal_compl {a : List Nat} (hnd : a.Nodup) {j : Nat} (hj : j < a.length)
    {x : Nat} (hx : x ∈ a) (hne : x ≠ a[j]) :
    x ∈ a.drop (j + 1) ↔ x ∉ a.take j := by
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hx
  rw [getElem_mem_drop_iff hnd hp, getElem_mem_take_iff hnd hp]
  have : p ≠ j := fun h => hne (by subst h; rfl)
  omega

theorem window_mem {N m d : Nat} {a : List Nat} (h : IsFoldSeq N a) (hm : m ∈ a)
    (hd : d ≤ reach N m) : m - d ∈ a ∧ m + d ∈ a := by
  simp only [mem_range'_of_perm h] at *; unfold reach at hd; omega

/-- Reversing a semi-symmetric fold sequence gives a semi-symmetric fold sequence. -/
theorem SemiSymmetric.reverse {N : Nat} {a : List Nat} (hf : IsFoldSeq N a)
    (h : SemiSymmetric N a) : SemiSymmetric N a.reverse := by
  have hnd : a.Nodup := hf.nodup_iff.2 (List.nodup_range' ..)
  intro k hk
  simp only [List.length_reverse] at hk
  have hj : a.length - 1 - k < a.length := by omega
  have e1 : a.reverse[k]'(by simpa using hk) = a[a.length - 1 - k] := by
    rw [List.getElem_reverse]
  have e2 : a.reverse.take k = (a.drop (a.length - 1 - k + 1)).reverse := by
    rw [List.take_reverse]; congr 2; omega
  rw [e1, e2]
  have hs := h _ hj
  refine (semiStep_iff_of_compl ?_).1 hs
  intro d hd1 hd2
  have hm := List.getElem_mem hj
  obtain ⟨h1, h2⟩ := window_mem hf hm hd2
  have hr : 1 ≤ a[a.length - 1 - k] := ((mem_range'_of_perm hf).1 hm).1
  simp only [List.mem_reverse]
  constructor
  · exact reversal_compl hnd hj h1 (by unfold reach at hd2; omega)
  · exact reversal_compl hnd hj h2 (by omega)


/-! ## Symmetric ⇔ no 3-term arithmetic progression -/

theorem symmetric_iff_apFree {N : Nat} {a : List Nat} (hf : IsFoldSeq N a) :
    Symmetric N a ↔ APFree a := by
  have hnd : a.Nodup := hf.nodup_iff.2 (List.nodup_range' ..)
  have bnd : ∀ (p : Nat) (hp : p < a.length), 1 ≤ a[p] ∧ a[p] ≤ N :=
    fun p hp => (mem_range'_of_perm hf).1 (List.getElem_mem hp)
  constructor
  · intro h i j k hij hjk hk hap
    have hi : i < a.length := by omega
    have hj : j < a.length := by omega
    have hik : a[i] ≠ a[k] := fun e => by
      have := (List.Nodup.getElem_inj hnd).1 e; omega
    have bi := bnd i hi; have bk := bnd k hk
    have sj := h j hj
    have ti : a[i] ∈ a.take j := (getElem_mem_take_iff hnd hi).2 hij
    have tk : a[k] ∉ a.take j := fun hh => by
      have := (getElem_mem_take_iff hnd hk).1 hh; omega
    by_cases hlt : a[i] < a[j]
    · have := sj (a[j] - a[i]) (by omega) (by unfold reach; omega)
      have e1 : a[j] - (a[j] - a[i]) = a[i] := by omega
      have e2 : a[j] + (a[j] - a[i]) = a[k] := by omega
      rw [e1, e2] at this; exact tk (this.1 ti)
    · have := sj (a[i] - a[j]) (by omega) (by unfold reach; omega)
      have e1 : a[j] - (a[i] - a[j]) = a[k] := by omega
      have e2 : a[j] + (a[i] - a[j]) = a[i] := by omega
      rw [e1, e2] at this; exact tk (this.2 ti)
  · intro h j hj d hd1 hd2
    have hm := List.getElem_mem hj
    obtain ⟨h1, h2⟩ := window_mem hf hm hd2
    obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.1 h1
    obtain ⟨q, hq, hqe⟩ := List.mem_iff_getElem.1 h2
    have bm := bnd j hj
    rw [← hpe, ← hqe, getElem_mem_take_iff hnd hp, getElem_mem_take_iff hnd hq]
    have hpj : p ≠ j := fun e => by subst e; unfold reach at hd2; omega
    have hqj : q ≠ j := fun e => by subst e; omega
    constructor
    · intro hpj'
      refine Decidable.byContradiction fun hc => ?_
      exact h p j q (by omega) (by omega) hq (by unfold reach at hd2; omega)
    · intro hqj'
      refine Decidable.byContradiction fun hc => ?_
      exact h q j p (by omega) (by omega) hp (by unfold reach at hd2; omega)

/-! ## Mirror symmetry `m ↦ N + 1 - m` -/

theorem mem_map_mirror {N y : Nat} {S : List Nat} (hS : ∀ x ∈ S, x ≤ N) (hy : y ≤ N) :
    N + 1 - y ∈ S.map (N + 1 - ·) ↔ y ∈ S := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨x, hx, e⟩
    have := hS x hx
    have : x = y := by omega
    exact this ▸ hx
  · intro hy'; exact ⟨y, hy', rfl⟩

theorem SemiSymmetric.mirror {N : Nat} {a : List Nat} (hf : IsFoldSeq N a)
    (h : SemiSymmetric N a) : SemiSymmetric N (a.map (N + 1 - ·)) := by
  intro k hk
  simp only [List.length_map] at hk
  rw [List.getElem_map, ← List.map_take]
  have hm := List.getElem_mem hk
  have bm := (mem_range'_of_perm hf).1 hm
  have hS : ∀ x ∈ a.take k, x ≤ N := fun x hx =>
    ((mem_range'_of_perm hf).1 (List.mem_of_mem_take hx)).2
  have hr : reach N (N + 1 - a[k]) = reach N a[k] := by unfold reach; omega
  have hs := h k hk
  unfold SemiStep leftCount rightCount at *
  rw [hr]
  have L : (List.range' 1 (reach N a[k])).countP
      (fun d => decide (N + 1 - a[k] - d ∈ (a.take k).map (N + 1 - ·))) =
      (List.range' 1 (reach N a[k])).countP (fun d => decide (a[k] + d ∈ a.take k)) := by
    apply List.countP_congr; intro d hd; rw [List.mem_range'_1] at hd
    have e : N + 1 - a[k] - d = N + 1 - (a[k] + d) := by omega
    rw [e]; simp only [decide_eq_true_eq]
    exact mem_map_mirror hS (by unfold reach at hd; omega)
  have R : (List.range' 1 (reach N a[k])).countP
      (fun d => decide (N + 1 - a[k] + d ∈ (a.take k).map (N + 1 - ·))) =
      (List.range' 1 (reach N a[k])).countP (fun d => decide (a[k] - d ∈ a.take k)) := by
    apply List.countP_congr; intro d hd; rw [List.mem_range'_1] at hd
    have e : N + 1 - a[k] + d = N + 1 - (a[k] - d) := by unfold reach at hd; omega
    rw [e]; simp only [decide_eq_true_eq]
    exact mem_map_mirror hS (by omega)
  rw [L, R]; exact hs.symm

end Folds
