import Folds.Congruence

/-!
# Self-dual sequences as a half-size problem

A fold sequence is *self-dual* if it is fixed by reversal ∘ mirror (`revMirror N a = a`),
i.e. `a[N-1-k] = N + 1 - a[k]`.  `c(N) = (revMirrorFixed N).card` counts the semi-symmetric
ones.

* `semiStep_mirror_iff`: mirroring `x ↦ N + 1 - x` preserves the validity of a single step.
* `semiStep_selfDual_iff`: in a self-dual fold sequence, step `k` is semi-symmetric iff step
  `N - 1 - k` is (0-based).
* `semiSymmetric_iff_take_of_selfDual`: a self-dual fold sequence is semi-symmetric iff its
  first `⌈N/2⌉` steps are.
* `eq_expand_of_selfDual`, `expand_isFoldSeq`, `revMirror_expand`: self-dual fold sequences are
  exactly `expand N t = t ++ mid N ++ revMirror N t` for *half sequences* `t`: lists of
  length `⌊N/2⌋` choosing one panel from each pair `{j, N + 1 - j}`, `j ≤ N/2` (`mid N` is
  `[(N+1)/2]` for odd `N` and empty for even `N`).
* `card_revMirrorFixed`: **`c(N)` = the number of half sequences `t` such that
  `t ++ mid N` is semi-symmetric** (`validHalf N`).  This is the `3^{N/2}`-state reformulation
  used by `experiments/arith/selfdual*.c`: a half sequence fills the folded positions
  `1..⌊N/2⌋`, each with "left" (`j`) or "right" (`N + 1 - j`).
-/

namespace Folds

open Finset

/-! ## Mirror, step by step -/

theorem semiStep_mirror_iff {N m : ℕ} {S : List ℕ} (hS : ∀ x ∈ S, x ≤ N) (hm1 : 1 ≤ m)
    (hmN : m ≤ N) :
    SemiStep N (S.map (N + 1 - ·)) (N + 1 - m) ↔ SemiStep N S m := by
  have hr : reach N (N + 1 - m) = reach N m := by unfold reach; omega
  unfold SemiStep leftCount rightCount
  rw [hr]
  have L : (List.range' 1 (reach N m)).countP
      (fun d => decide (N + 1 - m - d ∈ S.map (N + 1 - ·))) =
      (List.range' 1 (reach N m)).countP (fun d => decide (m + d ∈ S)) := by
    apply List.countP_congr; intro d hd; rw [List.mem_range'_1] at hd
    have e : N + 1 - m - d = N + 1 - (m + d) := by omega
    rw [e]; simp only [decide_eq_true_eq]
    exact mem_map_mirror hS (by unfold reach at hd; omega)
  have R : (List.range' 1 (reach N m)).countP
      (fun d => decide (N + 1 - m + d ∈ S.map (N + 1 - ·))) =
      (List.range' 1 (reach N m)).countP (fun d => decide (m - d ∈ S)) := by
    apply List.countP_congr; intro d hd; rw [List.mem_range'_1] at hd
    have e : N + 1 - m + d = N + 1 - (m - d) := by unfold reach at hd; omega
    rw [e]; simp only [decide_eq_true_eq]
    exact mem_map_mirror hS (by omega)
  rw [L, R]; exact eq_comm

/-- Step `j` of a list `b = mirror a` is valid iff step `j` of `a` is. -/
theorem semiStep_of_eq_mirror {N : ℕ} {a b : List ℕ} (hf : IsFoldSeq N a)
    (hb : b = a.map (N + 1 - ·)) {j : ℕ} (hj : j < b.length) :
    SemiStep N (b.take j) b[j] ↔ SemiStep N (a.take j) (a[j]'(by simpa [hb] using hj)) := by
  subst hb
  rw [List.getElem_map, ← List.map_take]
  have hm := (mem_range'_of_perm hf).1 (List.getElem_mem (by simpa using hj))
  exact semiStep_mirror_iff (fun x hx => ((mem_range'_of_perm hf).1 (List.mem_of_mem_take hx)).2)
    hm.1 hm.2

theorem reverse_eq_mirror_of_fixed {N : ℕ} {a : List ℕ} (hfix : revMirror N a = a) :
    a.reverse = a.map (N + 1 - ·) := by
  nth_rw 1 [← hfix]; unfold revMirror; rw [List.reverse_reverse]

/-! ## Self-dual sequences: step `k` ⇔ step `N - 1 - k` -/

/-- **Step duality.**  In a fold sequence fixed by reversal ∘ mirror, the step at (0-based)
index `k` is semi-symmetric iff the step at index `N - 1 - k` is. -/
theorem semiStep_selfDual_iff {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a)
    (hfix : revMirror N a = a) {k : ℕ} (hk : k < a.length) :
    SemiStep N (a.take k) a[k] ↔
      SemiStep N (a.take (a.length - 1 - k)) (a[a.length - 1 - k]'(by omega)) := by
  rw [semiStep_reverse_iff hf hk]
  exact semiStep_of_eq_mirror hf (reverse_eq_mirror_of_fixed hfix) _

/-- **Half-size test.**  A self-dual fold sequence is semi-symmetric iff its first `⌈N/2⌉`
steps are. -/
theorem semiSymmetric_iff_take_of_selfDual {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a)
    (hfix : revMirror N a = a) :
    SemiSymmetric N a ↔ SemiSymmetric N (a.take ((N + 1) / 2)) := by
  have hlen : a.length = N := by rw [hf.length_eq]; simp
  rw [semiSymmetric_take_iff]
  constructor
  · intro h j hj _; exact h j hj
  · intro h j hj
    by_cases hjk : j < (N + 1) / 2
    · exact h j hj hjk
    · exact (semiStep_selfDual_iff hf hfix hj).2 (h _ (by omega) (by omega))

/-! ## Half sequences -/

/-- The middle panel, as a list: `[(N+1)/2]` for odd `N`, `[]` for even `N`. -/
def mid (N : ℕ) : List ℕ := if N % 2 = 1 then [(N + 1) / 2] else []

/-- The self-dual sequence with first half `t`. -/
def expand (N : ℕ) (t : List ℕ) : List ℕ := t ++ mid N ++ revMirror N t

/-- Half sequences: orderings of a transversal of the pairs `{j, N + 1 - j}`. -/
def halfSeqs (N : ℕ) : Finset (List ℕ) :=
  (((Icc 1 N).powersetCard (N / 2)).biUnion orderings).filter fun t => ∀ x ∈ t, N + 1 - x ∉ t

theorem mem_halfSeqs {N : ℕ} {t : List ℕ} :
    t ∈ halfSeqs N ↔ t.Nodup ∧ t.length = N / 2 ∧ (∀ x ∈ t, 1 ≤ x ∧ x ≤ N) ∧
      ∀ x ∈ t, N + 1 - x ∉ t := by
  simp only [halfSeqs, mem_filter, mem_biUnion, mem_powersetCard, mem_orderings]
  constructor
  · rintro ⟨⟨S, ⟨hS, hc⟩, hnd, rfl⟩, ht⟩
    refine ⟨hnd, ?_, ?_, ht⟩
    · rw [← hc, List.toFinset_card_of_nodup hnd]
    · intro x hx
      have := hS (List.mem_toFinset.2 hx)
      simpa using this
  · rintro ⟨hnd, hl, hb, ht⟩
    refine ⟨⟨t.toFinset, ⟨?_, ?_⟩, hnd, rfl⟩, ht⟩
    · intro x hx; rw [List.mem_toFinset] at hx; simpa using hb x hx
    · rw [List.toFinset_card_of_nodup hnd, hl]

/-- Valid half sequences: `t ++ mid N` is semi-symmetric. -/
def validHalf (N : ℕ) : Finset (List ℕ) :=
  (halfSeqs N).filter fun t => SemiSymmetric N (t ++ mid N)

theorem revMirror_append (N : ℕ) (x y : List ℕ) :
    revMirror N (x ++ y) = revMirror N y ++ revMirror N x := by
  simp [revMirror]

theorem length_revMirror (N : ℕ) (x : List ℕ) : (revMirror N x).length = x.length := by
  simp [revMirror]

theorem mem_revMirror {N : ℕ} {x : List ℕ} {y : ℕ} :
    y ∈ revMirror N x ↔ ∃ z ∈ x, N + 1 - z = y := by
  simp [revMirror]

theorem length_mid (N : ℕ) : (mid N).length = N % 2 := by
  unfold mid; split <;> simp <;> omega

theorem revMirror_mid (N : ℕ) : revMirror N (mid N) = mid N := by
  unfold mid revMirror; split
  · simp; omega
  · simp

theorem mem_mid {N y : ℕ} : y ∈ mid N ↔ N % 2 = 1 ∧ y = (N + 1) / 2 := by
  unfold mid; split <;> simp_all

theorem length_expand {N : ℕ} {t : List ℕ} (ht : t.length = N / 2) :
    (expand N t).length = N := by
  simp only [expand, List.length_append, length_mid, length_revMirror, ht]; omega

theorem take_expand {N : ℕ} {t : List ℕ} (ht : t.length = N / 2) :
    (expand N t).take ((N + 1) / 2) = t ++ mid N := by
  rw [expand, List.take_left' (by simp [length_mid, ht]; omega)]

theorem take_half_expand {N : ℕ} {t : List ℕ} (ht : t.length = N / 2) :
    (expand N t).take (N / 2) = t := by
  rw [expand, List.append_assoc, List.take_left' ht]

theorem revMirror_expand {N : ℕ} {t : List ℕ} (hb : ∀ x ∈ t, x ≤ N) :
    revMirror N (expand N t) = expand N t := by
  rw [expand, revMirror_append, revMirror_append, revMirror_revMirror hb, revMirror_mid,
    List.append_assoc]

theorem expand_isFoldSeq {N : ℕ} {t : List ℕ} (ht : t ∈ halfSeqs N) :
    IsFoldSeq N (expand N t) := by
  obtain ⟨hnd, hl, hb, htr⟩ := mem_halfSeqs.1 ht
  have hmid : (N + 1) / 2 ∉ t ∨ N % 2 = 0 := by
    by_cases hN : N % 2 = 0
    · right; exact hN
    · left; intro h; exact htr _ h (by rw [show N + 1 - (N + 1) / 2 = (N + 1) / 2 by omega]; exact h)
  apply perm_range'_of_nodup_subset
  · rw [expand, List.nodup_append, List.nodup_append]
    refine ⟨⟨hnd, ?_, ?_⟩, ?_, ?_⟩
    · unfold mid; split <;> simp
    · intro x hx y hy e; subst e
      rw [mem_mid] at hy
      rcases hmid with h | h
      · exact h (hy.2 ▸ hx)
      · omega
    · unfold revMirror
      rw [List.nodup_reverse]
      exact nodup_map_of_injOn hnd fun x hx y hy e => by
        have := hb x hx; have := hb y hy; omega
    · intro x hx y hy e; subst e
      obtain ⟨z, hz, hzx⟩ := mem_revMirror.1 hy
      rcases List.mem_append.1 hx with hx | hx
      · exact htr z hz (hzx ▸ hx)
      · rw [mem_mid] at hx
        have := hb z hz
        rcases hmid with h | h
        · exact h (by rw [show z = (N + 1) / 2 by omega] at hz; exact hz)
        · omega
  · intro y hy
    rw [expand, List.mem_append, List.mem_append, mem_mid, mem_revMirror] at hy
    rcases hy with (hy | hy) | ⟨z, hz, rfl⟩
    · exact hb y hy
    · omega
    · have := hb z hz; omega
  · exact length_expand hl

/-- Every self-dual fold sequence is the expansion of its first `⌊N/2⌋` panels. -/
theorem eq_expand_of_selfDual {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a)
    (hfix : revMirror N a = a) : a = expand N (a.take (N / 2)) := by
  have hlen : a.length = N := by rw [hf.length_eq]; simp
  set u := a.take (N / 2) with hu
  set w := (a.drop (N / 2)).take (N % 2) with hw
  set v := (a.drop (N / 2)).drop (N % 2) with hv
  have ha : a = u ++ (w ++ v) := by
    rw [hu, hw, hv, List.take_append_drop, List.take_append_drop]
  have lu : u.length = N / 2 := by rw [hu, List.length_take]; omega
  have lw : w.length = N % 2 := by rw [hw, List.length_take, List.length_drop]; omega
  have lv : v.length = N / 2 := by rw [hv, List.length_drop, List.length_drop]; omega
  have h := hfix
  rw [ha, revMirror_append, revMirror_append, List.append_assoc] at h
  obtain ⟨e1, e2⟩ := List.append_inj h (by rw [length_revMirror, lu, lv])
  obtain ⟨e3, e4⟩ := List.append_inj e2 (by rw [length_revMirror])
  have hwm : w = mid N := by
    unfold mid
    split
    · obtain ⟨x, hx⟩ : ∃ x, w = [x] := List.length_eq_one_iff.1 (by rw [lw]; omega)
      have hxN : x ≤ N := by
        have : x ∈ a := by rw [ha]; simp [hx]
        exact ((mem_range'_of_perm hf).1 this).2
      rw [hx] at e3
      simp [revMirror] at e3
      rw [hx]; congr 1; omega
    · exact List.eq_nil_of_length_eq_zero (by rw [lw]; omega)
  rw [expand, e4, ← hwm, List.append_assoc, ← ha]

theorem take_mem_halfSeqs {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a)
    (hfix : revMirror N a = a) : a.take (N / 2) ∈ halfSeqs N := by
  have hlen : a.length = N := by rw [hf.length_eq]; simp
  have hnd := nodup_of_foldSeq hf
  have he := eq_expand_of_selfDual hf hfix
  rw [mem_halfSeqs]
  refine ⟨take_nodup hnd _, by rw [List.length_take]; omega,
    fun x hx => (mem_range'_of_perm hf).1 (List.mem_of_mem_take hx), ?_⟩
  intro x hx hx'
  have h2 := hnd
  rw [he, expand, List.nodup_append] at h2
  refine h2.2.2 (N + 1 - x) (List.mem_append_left _ hx') (N + 1 - x)
    (mem_revMirror.2 ⟨x, hx, rfl⟩) rfl

/-- **Half-size reformulation of `c(N)`.**  The number of semi-symmetric fold sequences
fixed by reversal ∘ mirror equals the number of half sequences `t` (one panel from each pair
`{j, N + 1 - j}`, in some order) such that `t ++ mid N` is semi-symmetric. -/
theorem card_revMirrorFixed (N : ℕ) : (revMirrorFixed N).card = (validHalf N).card := by
  apply card_nbij' (fun a => a.take (N / 2)) (expand N)
  · intro a ha
    simp only [revMirrorFixed, coe_filter, Set.mem_ofPred_eq, mem_semiSeqs] at ha
    obtain ⟨⟨hf, hs⟩, hfix⟩ := ha
    simp only [validHalf, coe_filter, Set.mem_ofPred_eq]
    have ht := take_mem_halfSeqs hf hfix
    refine ⟨ht, ?_⟩
    rw [semiSymmetric_iff_take_of_selfDual hf hfix, eq_expand_of_selfDual hf hfix,
      take_expand (mem_halfSeqs.1 ht).2.1] at hs
    exact hs
  · intro t ht
    simp only [validHalf, coe_filter, Set.mem_ofPred_eq] at ht
    obtain ⟨ht, hs⟩ := ht
    obtain ⟨-, hl, hb, -⟩ := mem_halfSeqs.1 ht
    have hf := expand_isFoldSeq ht
    have hfix := revMirror_expand (N := N) (fun x hx => (hb x hx).2)
    simp only [revMirrorFixed, coe_filter, Set.mem_ofPred_eq, mem_semiSeqs]
    refine ⟨⟨hf, ?_⟩, hfix⟩
    rw [semiSymmetric_iff_take_of_selfDual hf hfix, take_expand hl]
    exact hs
  · intro a ha
    simp only [revMirrorFixed, coe_filter, Set.mem_ofPred_eq, mem_semiSeqs] at ha
    exact (eq_expand_of_selfDual ha.1.1 ha.2).symm
  · intro t ht
    simp only [validHalf, coe_filter, Set.mem_ofPred_eq] at ht
    exact take_half_expand (mem_halfSeqs.1 ht.1).2.1

end Folds
