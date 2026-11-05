import Folds.Cyclic

/-!
# Parity facts

* `even_length_of_semiStep_cover`: if the window of `m` covers every already-bisected
  panel, a semi-symmetric step at `m` forces `|S|` to be even.
* `middle_index_even`: for `N = 2n+1` the middle panel `n+1` of a semi-symmetric fold
  sequence sits at an even 0-based index (an odd step, 1-based).
-/

namespace Folds

theorem nodup_of_foldSeq {N : Nat} {a : List Nat} (hf : IsFoldSeq N a) : a.Nodup :=
  hf.nodup_iff.2 (List.nodup_range' ..)

theorem nodup_map_of_injOn {f : Nat → Nat} {l : List Nat} (hl : l.Nodup)
    (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih hl.2 fun x hx y hy => hf x (by simp [hx]) y (by simp [hy])⟩
    rintro ⟨x, hx, e⟩
    have := hf x (by simp [hx]) a (by simp) e
    exact hl.1 (this ▸ hx)

theorem take_nodup {a : List Nat} (h : a.Nodup) (k : Nat) : (a.take k).Nodup :=
  h.sublist (List.take_sublist _ _)

/-- If every already-bisected panel lies in the window of `m` (and `m` itself has not
been bisected), a semi-symmetric step at `m` forces an even number of bisected panels. -/
theorem even_length_of_semiStep_cover {N m : Nat} {S : List Nat} (hnd : S.Nodup)
    (hmS : m ∉ S) (hcov : ∀ x ∈ S, m - reach N m ≤ x ∧ x ≤ m + reach N m)
    (h : SemiStep N S m) : S.length % 2 = 0 := by
  unfold SemiStep at h
  rw [leftCount_eq hnd, rightCount_eq hnd] at h
  have hsplit := countP_split S (fun _ => true) (fun x => decide (x < m))
  rw [List.countP_true] at hsplit
  have e1 : S.countP (fun x => true && decide (x < m)) =
      S.countP (fun x => decide (m - reach N m ≤ x ∧ x < m)) := by
    apply List.countP_congr; intro x hx; have := hcov x hx; simp; omega
  have e2 : S.countP (fun x => true && !decide (x < m)) =
      S.countP (fun x => decide (m < x ∧ x ≤ m + reach N m)) := by
    apply List.countP_congr; intro x hx; have := hcov x hx
    have : x ≠ m := fun e => hmS (e ▸ hx)
    simp; omega
  omega

/-- For odd `N = 2n + 1`, the middle panel `n + 1` of a semi-symmetric fold sequence is
bisected at an even 0-based index `k` (i.e. at an odd step, counting from 1). -/
theorem middle_index_even {n : Nat} {a : List Nat} (hf : IsFoldSeq (2 * n + 1) a)
    (h : SemiSymmetric (2 * n + 1) a) {k : Nat} (hk : k < a.length) (hm : a[k] = n + 1) :
    k % 2 = 0 := by
  have hnd := nodup_of_foldSeq hf
  have hS := h k hk
  rw [hm] at hS
  have hmS : n + 1 ∉ a.take k := by
    rw [← hm, getElem_mem_take_iff hnd hk]; omega
  have hlen : (a.take k).length = k := by simp; omega
  rw [← hlen]
  refine even_length_of_semiStep_cover (take_nodup hnd k) hmS ?_ hS
  intro x hx
  have := (mem_range'_of_perm hf).1 (List.mem_of_mem_take hx)
  unfold reach; omega

end Folds
