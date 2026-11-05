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
* `flip_outer`, `flip_inner` (the flip lemma, step level): if `S` holds one panel of every
  pair other than `{x, N + 1 - x}`, then for an outer pair (`3 · min(x, N+1-x) ≤ N + 1`)
  placing `x` and placing `N + 1 - x` after `S` are valid together, and for an inner pair at
  most one of them is valid.
* `flipLast_mem_validHalf`, `flipLast_not_mem_validHalf`: the same for the last panel of a
  valid half sequence (even `N`).
* `revMirrorFixed_mod_four_inner`: for even `N ≥ 4`,
  `c(N) ≡ #{valid half sequences whose last pair is inner} (mod 4)`.
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

/-! ## The flip lemma

Let `S` contain exactly one panel from each pair `{y, N + 1 - y}` other than the pair
`{x, N + 1 - x}` (and neither `x` nor `N + 1 - x`).  Write `σ y = N + 1 - y`.  Placing `σ x`
after `S` is valid iff placing `x` after `σ(S)` is, and inside the window of `x`, `σ(S)` is
the complement of `S`, except at `σ x` when `σ x` lies in the window.

* **outer pair** (`3 · min(x, N+1-x) ≤ N + 1`): `σ x` is outside the window of `x`, so `x`
  and `σ x` are valid together (`flip_outer`);
* **inner pair** (`3 · min(x, N+1-x) > N + 1`, `x ≠ σ x`): at most one of them is valid
  (`flip_inner`).
-/

theorem countP_add_three (l : List ℕ) (p q s : ℕ → Bool)
    (h : ∀ d ∈ l, (if p d then 1 else 0) + (if q d then 1 else 0) + (if s d then 1 else 0) = 1) :
    l.countP p + l.countP q + l.countP s = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have := ih (fun d hd => h d (by simp [hd]))
    simp only [List.countP_cons, List.length_cons]
    revert ha; cases p a <;> cases q a <;> cases s a <;> simp <;> omega

theorem mem_map_mirror' {N y : ℕ} {S : List ℕ} (hS : ∀ z ∈ S, z ≤ N) (hy1 : 1 ≤ y) (hy : y ≤ N) :
    y ∈ S.map (N + 1 - ·) ↔ N + 1 - y ∈ S := by
  have := mem_map_mirror (S := S) hS (y := N + 1 - y) (by omega)
  rwa [show N + 1 - (N + 1 - y) = y by omega] at this

section Flip

variable {N x : ℕ} {S : List ℕ}

/-- The counting identities behind the flip lemma. -/
theorem flip_counts (hS : ∀ y ∈ S, 1 ≤ y ∧ y ≤ N) (hx1 : 1 ≤ x) (hxN : x ≤ N)
    (htr : ∀ y, 1 ≤ y → y ≤ N → y ≠ x → y ≠ N + 1 - x → (y ∈ S ↔ N + 1 - y ∉ S))
    (hxS : x ∉ S) (hσS : N + 1 - x ∉ S) :
    leftCount N (S.map (N + 1 - ·)) x + leftCount N S x +
        (List.range' 1 (reach N x)).countP (fun d => decide (x - d = N + 1 - x)) = reach N x ∧
      rightCount N (S.map (N + 1 - ·)) x + rightCount N S x +
        (List.range' 1 (reach N x)).countP (fun d => decide (x + d = N + 1 - x)) =
          reach N x := by
  have hS' : ∀ z ∈ S, z ≤ N := fun z hz => (hS z hz).2
  have key : ∀ y, 1 ≤ y → y ≤ N → y ≠ x →
      (if decide (y ∈ S.map (N + 1 - ·)) then 1 else 0) + (if decide (y ∈ S) then 1 else 0) +
        (if decide (y = N + 1 - x) then 1 else 0) = 1 := by
    intro y hy1 hyN hyx
    simp only [mem_map_mirror' hS' hy1 hyN]
    by_cases hyσ : y = N + 1 - x
    · have : N + 1 - y = x := by omega
      rw [this]; simp [hxS, hyσ, hσS]
    · have := htr y hy1 hyN hyx hyσ
      by_cases hyS : y ∈ S
      · have : N + 1 - y ∉ S := this.1 hyS
        simp [hyS, this, hyσ]
      · have : N + 1 - y ∈ S := by
          by_contra hc; exact hyS (this.2 hc)
        simp [hyS, this, hyσ]
  unfold leftCount rightCount
  constructor
  · have := countP_add_three (List.range' 1 (reach N x))
      (fun d => decide (x - d ∈ S.map (N + 1 - ·))) (fun d => decide (x - d ∈ S))
      (fun d => decide (x - d = N + 1 - x)) (fun d hd => by
        rw [List.mem_range'_1] at hd
        exact key (x - d) (by unfold reach at hd; omega) (by omega) (by omega))
    simpa using this
  · have := countP_add_three (List.range' 1 (reach N x))
      (fun d => decide (x + d ∈ S.map (N + 1 - ·))) (fun d => decide (x + d ∈ S))
      (fun d => decide (x + d = N + 1 - x)) (fun d hd => by
        rw [List.mem_range'_1] at hd
        exact key (x + d) (by omega) (by unfold reach at hd; omega) (by omega))
    simpa using this

theorem semiStep_partner_iff (hS : ∀ y ∈ S, 1 ≤ y ∧ y ≤ N) (hx1 : 1 ≤ x) (hxN : x ≤ N) :
    SemiStep N S (N + 1 - x) ↔ SemiStep N (S.map (N + 1 - ·)) x := by
  have := semiStep_mirror_iff (S := S) (m := N + 1 - x) (fun z hz => (hS z hz).2)
    (by omega) (by omega)
  rw [show N + 1 - (N + 1 - x) = x by omega] at this
  exact this.symm

/-- **Flip lemma, outer pair.** -/
theorem flip_outer (hS : ∀ y ∈ S, 1 ≤ y ∧ y ≤ N) (hx1 : 1 ≤ x) (hxN : x ≤ N)
    (htr : ∀ y, 1 ≤ y → y ≤ N → y ≠ x → y ≠ N + 1 - x → (y ∈ S ↔ N + 1 - y ∉ S))
    (hxS : x ∉ S) (hσS : N + 1 - x ∉ S) (hout : 3 * min x (N + 1 - x) ≤ N + 1) :
    SemiStep N S x ↔ SemiStep N S (N + 1 - x) := by
  obtain ⟨h1, h2⟩ := flip_counts hS hx1 hxN htr hxS hσS
  have c1 : (List.range' 1 (reach N x)).countP (fun d => decide (x - d = N + 1 - x)) = 0 := by
    rw [List.countP_eq_zero]; intro d hd; rw [List.mem_range'_1] at hd
    unfold reach at hd; simp; omega
  have c2 : (List.range' 1 (reach N x)).countP (fun d => decide (x + d = N + 1 - x)) = 0 := by
    rw [List.countP_eq_zero]; intro d hd; rw [List.mem_range'_1] at hd
    unfold reach at hd; simp; omega
  rw [semiStep_partner_iff hS hx1 hxN]
  unfold SemiStep
  omega

theorem countP_range'_eq_one {r c : ℕ} (p : ℕ → Prop) [DecidablePred p] (h1 : 1 ≤ c)
    (h2 : c ≤ r) (hp : ∀ d, 1 ≤ d → d ≤ r → (p d ↔ d = c)) :
    (List.range' 1 r).countP (fun d => decide (p d)) = 1 := by
  have e : (List.range' 1 r).countP (fun d => decide (p d)) =
      (List.range' 1 r).countP (fun d => decide (d = c)) := by
    apply List.countP_congr; intro d hd; rw [List.mem_range'_1] at hd
    simp only [decide_eq_true_eq]; exact hp d (by omega) (by omega)
  rw [e, countP_eq_nodup (List.nodup_range' ..)]
  have : c ∈ List.range' 1 r := by rw [List.mem_range'_1]; omega
  simp [this]

/-- **Flip lemma, inner pair.** -/
theorem flip_inner (hS : ∀ y ∈ S, 1 ≤ y ∧ y ≤ N) (hx1 : 1 ≤ x) (hxN : x ≤ N)
    (htr : ∀ y, 1 ≤ y → y ≤ N → y ≠ x → y ≠ N + 1 - x → (y ∈ S ↔ N + 1 - y ∉ S))
    (hxS : x ∉ S) (hσS : N + 1 - x ∉ S) (hne : 2 * x ≠ N + 1)
    (hin : N + 1 < 3 * min x (N + 1 - x)) :
    ¬ (SemiStep N S x ∧ SemiStep N S (N + 1 - x)) := by
  obtain ⟨h1, h2⟩ := flip_counts hS hx1 hxN htr hxS hσS
  rw [semiStep_partner_iff hS hx1 hxN]
  unfold SemiStep
  rintro ⟨e1, e2⟩
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · -- `x` left of centre, `σ x` on the right of the window
    have c1 : (List.range' 1 (reach N x)).countP (fun d => decide (x - d = N + 1 - x)) = 0 := by
      rw [List.countP_eq_zero]; intro d hd; rw [List.mem_range'_1] at hd
      unfold reach at hd; simp; omega
    have c2 := countP_range'_eq_one (r := reach N x) (c := N + 1 - 2 * x)
      (fun d => x + d = N + 1 - x) (by omega) (by unfold reach; omega) (fun d _ _ => by omega)
    omega
  · have c2 : (List.range' 1 (reach N x)).countP (fun d => decide (x + d = N + 1 - x)) = 0 := by
      rw [List.countP_eq_zero]; intro d hd; rw [List.mem_range'_1] at hd
      unfold reach at hd; simp; omega
    have c1 := countP_range'_eq_one (r := reach N x) (c := 2 * x - (N + 1))
      (fun d => x - d = N + 1 - x) (by omega) (by unfold reach; omega)
      (fun d _ hd => by unfold reach at hd; omega)
    omega

end Flip

/-! ## The flip on half sequences, and `c(2n) mod 4`

For even `N`, flip the last panel `x` of a half sequence to its partner `N + 1 - x`
(`flipLast`).  On valid half sequences whose last pair is outer this is a fixed-point-free
involution commuting with the mirror `t ↦ t.map (N + 1 - ·)`; with `card_mod_four` this gives
`c(N) ≡ #{valid half sequences whose last pair is inner} (mod 4)` for even `N ≥ 4`. -/

/-- Replace the last entry `x` by `N + 1 - x`. -/
def flipLast (N : ℕ) (t : List ℕ) : List ℕ := (t.reverse.modifyHead (N + 1 - ·)).reverse

@[simp] theorem flipLast_concat (N : ℕ) (t : List ℕ) (x : ℕ) :
    flipLast N (t ++ [x]) = t ++ [N + 1 - x] := by
  simp [flipLast]

/-- The last panel `x` of `t` belongs to an outer pair: `3 · min(x, N + 1 - x) ≤ N + 1`. -/
def LastOuter (N : ℕ) (t : List ℕ) : Prop :=
  3 * min (t.getLastD 0) (N + 1 - t.getLastD 0) ≤ N + 1

instance (N : ℕ) : DecidablePred (LastOuter N) := fun _ => inferInstanceAs (Decidable (_ ≤ _))

theorem lastOuter_concat {N x : ℕ} {t : List ℕ} :
    LastOuter N (t ++ [x]) ↔ 3 * min x (N + 1 - x) ≤ N + 1 := by
  simp [LastOuter]

theorem exists_concat_of_mem_halfSeqs {N : ℕ} {t : List ℕ} (hN : 2 ≤ N) (ht : t ∈ halfSeqs N) :
    ∃ t' x, t = t' ++ [x] := by
  rcases List.eq_nil_or_concat t with rfl | ⟨L, b, rfl⟩
  · have := (mem_halfSeqs.1 ht).2.1; simp at this; omega
  · exact ⟨L, b, by simp⟩

/-- For even `N`, a half sequence meets every pair `{y, N + 1 - y}`. -/
theorem halfSeqs_cover {N : ℕ} {t : List ℕ} (hN : N % 2 = 0) (ht : t ∈ halfSeqs N) {y : ℕ}
    (hy1 : 1 ≤ y) (hyN : y ≤ N) : y ∈ t ∨ N + 1 - y ∈ t := by
  obtain ⟨hnd, hl, hb, htr⟩ := mem_halfSeqs.1 ht
  have hinj : Set.InjOn (fun z => min z (N + 1 - z)) (t.toFinset : Set ℕ) := by
    intro a ha b hb' e
    rw [mem_coe, List.mem_toFinset] at ha hb'
    have := hb a ha; have := hb b hb'
    simp only at e
    by_contra hne
    have hab : b = N + 1 - a := by omega
    exact htr a ha (hab ▸ hb')
  have himg : t.toFinset.image (fun z => min z (N + 1 - z)) = Icc 1 (N / 2) := by
    apply eq_of_subset_of_card_le
    · intro z hz
      rw [mem_image] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      have := hb a (List.mem_toFinset.1 ha)
      rw [mem_Icc]; omega
    · rw [card_image_of_injOn hinj, List.toFinset_card_of_nodup hnd, hl, Nat.card_Icc]; omega
  have hy : min y (N + 1 - y) ∈ t.toFinset.image (fun z => min z (N + 1 - z)) := by
    rw [himg, mem_Icc]; omega
  obtain ⟨z, hz, e⟩ := mem_image.1 hy
  rw [List.mem_toFinset] at hz
  have := hb z hz
  by_cases h : z = y
  · left; exact h ▸ hz
  · right
    have : z = N + 1 - y := by omega
    exact this ▸ hz

/-- The hypotheses of the flip lemma hold for the prefix `t'` of a half sequence `t' ++ [x]`. -/
theorem flip_setup {N x : ℕ} {t : List ℕ} (hN : N % 2 = 0) (ht : t ++ [x] ∈ halfSeqs N) :
    (∀ y ∈ t, 1 ≤ y ∧ y ≤ N) ∧ 1 ≤ x ∧ x ≤ N ∧
      (∀ y, 1 ≤ y → y ≤ N → y ≠ x → y ≠ N + 1 - x → (y ∈ t ↔ N + 1 - y ∉ t)) ∧
      x ∉ t ∧ N + 1 - x ∉ t ∧ 2 * x ≠ N + 1 ∧ t ++ [N + 1 - x] ∈ halfSeqs N := by
  obtain ⟨hnd, hl, hb, htr⟩ := mem_halfSeqs.1 ht
  have hx := hb x (by simp)
  have hxt : x ∉ t := by
    intro h; rw [List.nodup_append] at hnd; exact hnd.2.2 x h x (by simp) rfl
  have hσt : N + 1 - x ∉ t := fun h => htr x (by simp) (List.mem_append_left _ h)
  refine ⟨fun y hy => hb y (List.mem_append_left _ hy), hx.1, hx.2, ?_, hxt, hσt, by omega, ?_⟩
  · intro y hy1 hyN hyx hyσ
    constructor
    · intro hy hσ; exact htr y (List.mem_append_left _ hy) (List.mem_append_left _ hσ)
    · intro hσ
      rcases halfSeqs_cover hN ht hy1 hyN with h | h
      · rcases List.mem_append.1 h with h | h
        · exact h
        · simp at h; exact absurd h hyx
      · rcases List.mem_append.1 h with h | h
        · exact absurd h hσ
        · simp at h; omega
  · rw [mem_halfSeqs]
    refine ⟨?_, by simpa using hl, ?_, ?_⟩
    · rw [List.nodup_append] at hnd ⊢
      refine ⟨hnd.1, by simp, ?_⟩
      intro a ha b hb' e; simp at hb'; subst e; subst hb'; exact hσt ha
    · intro y hy
      rcases List.mem_append.1 hy with h | h
      · exact hb y (List.mem_append_left _ h)
      · simp at h; omega
    · intro y hy hσ
      rcases List.mem_append.1 hy with h | h
      · rcases List.mem_append.1 hσ with h' | h'
        · exact htr y (List.mem_append_left _ h) (List.mem_append_left _ h')
        · simp at h'
          have hyb := hb y (List.mem_append_left _ h)
          exact hxt (by rw [show x = y by omega]; exact h)
      · simp at h; subst h
        rcases List.mem_append.1 hσ with h' | h'
        · exact hxt (by rw [show N + 1 - (N + 1 - x) = x by omega] at h'; exact h')
        · simp at h'; omega

theorem mid_of_even {N : ℕ} (hN : N % 2 = 0) : mid N = [] := by
  unfold mid; split
  · omega
  · rfl

/-- **Flip on half sequences, outer pair.** -/
theorem flipLast_mem_validHalf {N : ℕ} {t : List ℕ} (hN : N % 2 = 0) (h2 : 2 ≤ N)
    (ht : t ∈ validHalf N) (hout : LastOuter N t) : flipLast N t ∈ validHalf N := by
  rw [validHalf, mem_filter] at ht ⊢
  obtain ⟨t', x, rfl⟩ := exists_concat_of_mem_halfSeqs h2 ht.1
  obtain ⟨hS, hx1, hxN, htr, hxS, hσS, -, hmem⟩ := flip_setup hN ht.1
  rw [lastOuter_concat] at hout
  rw [flipLast_concat]
  refine ⟨hmem, ?_⟩
  have hs := ht.2
  rw [mid_of_even hN, List.append_nil, semiSymmetric_concat_iff] at hs ⊢
  exact ⟨hs.1, (flip_outer hS hx1 hxN htr hxS hσS hout).1 hs.2⟩

/-- **Flip on half sequences, inner pair.** -/
theorem flipLast_not_mem_validHalf {N : ℕ} {t : List ℕ} (hN : N % 2 = 0) (h2 : 2 ≤ N)
    (ht : t ∈ validHalf N) (hin : ¬ LastOuter N t) : flipLast N t ∉ validHalf N := by
  rw [validHalf, mem_filter] at ht ⊢
  obtain ⟨t', x, rfl⟩ := exists_concat_of_mem_halfSeqs h2 ht.1
  obtain ⟨hS, hx1, hxN, htr, hxS, hσS, hne, -⟩ := flip_setup hN ht.1
  rw [lastOuter_concat] at hin
  rw [flipLast_concat]
  rintro ⟨-, hs'⟩
  have hs := ht.2
  rw [mid_of_even hN, List.append_nil, semiSymmetric_concat_iff] at hs hs'
  exact flip_inner hS hx1 hxN htr hxS hσS hne (by omega) ⟨hs.2, hs'.2⟩

theorem semiSymmetric_map_mirror_iff {N : ℕ} {t : List ℕ} (hb : ∀ x ∈ t, 1 ≤ x ∧ x ≤ N) :
    SemiSymmetric N (t.map (N + 1 - ·)) ↔ SemiSymmetric N t := by
  have key : ∀ k (hk : k < t.length),
      SemiStep N ((t.map (N + 1 - ·)).take k) ((t.map (N + 1 - ·))[k]'(by simpa using hk)) ↔
        SemiStep N (t.take k) t[k] := by
    intro k hk
    rw [List.getElem_map, ← List.map_take]
    have hm := hb _ (List.getElem_mem hk)
    exact semiStep_mirror_iff (fun z hz => (hb z (List.mem_of_mem_take hz)).2) hm.1 hm.2
  constructor
  · intro h k hk; exact (key k hk).1 (h k (by simpa using hk))
  · intro h k hk
    simp only [List.length_map] at hk
    exact (key k hk).2 (h k hk)

theorem map_mirror_mem_validHalf {N : ℕ} {t : List ℕ} (hN : N % 2 = 0)
    (ht : t ∈ validHalf N) : t.map (N + 1 - ·) ∈ validHalf N := by
  rw [validHalf, mem_filter] at ht ⊢
  obtain ⟨hnd, hl, hb, htr⟩ := mem_halfSeqs.1 ht.1
  refine ⟨mem_halfSeqs.2 ⟨?_, by simpa using hl, ?_, ?_⟩, ?_⟩
  · exact nodup_map_of_injOn hnd fun x hx y hy e => by
      have := hb x hx; have := hb y hy; omega
  · intro y hy; obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy; have := hb z hz; omega
  · intro y hy hσ
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    obtain ⟨w, hw, e⟩ := List.mem_map.1 hσ
    have := hb z hz; have := hb w hw
    exact htr z hz (by rw [show N + 1 - z = w by omega]; exact hw)
  · rw [mid_of_even hN, List.append_nil] at ht ⊢
    exact (semiSymmetric_map_mirror_iff hb).2 ht.2

/-- **`c(N) mod 4` from the inner pairs.**  For even `N ≥ 4`, the number `c(N)` of
semi-symmetric fold sequences fixed by reversal ∘ mirror is congruent mod 4 to the number of
valid half sequences whose last panel belongs to an inner pair. -/
theorem revMirrorFixed_mod_four_inner {N : ℕ} (hN : N % 2 = 0) (h4 : 4 ≤ N) :
    (revMirrorFixed N).card % 4 =
      ((validHalf N).filter fun t => ¬ LastOuter N t).card % 4 := by
  rw [card_revMirrorFixed, ← card_filter_add_card_filter_not (s := validHalf N) (LastOuter N)]
  set X := (validHalf N).filter (LastOuter N) with hX
  have memX : ∀ t ∈ X, t ∈ validHalf N ∧ LastOuter N t := fun t ht => mem_filter.1 ht
  have bnd : ∀ t ∈ X, ∀ y ∈ t, 1 ≤ y ∧ y ≤ N := fun t ht =>
    (mem_halfSeqs.1 (mem_filter.1 (memX t ht).1).1).2.2.1
  have split : ∀ t ∈ X, ∃ t' x, t = t' ++ [x] := fun t ht =>
    exists_concat_of_mem_halfSeqs (by omega) (mem_filter.1 (memX t ht).1).1
  have mirror_mirror' : ∀ t ∈ X, (t.map (N + 1 - ·)).map (N + 1 - ·) = t := by
    intro t ht
    rw [List.map_map]
    conv => rhs; rw [← List.map_id t]
    apply List.map_congr_left
    intro y hy; have := bnd t ht y hy; simp; omega
  have h := card_mod_four (flipLast N) (List.map (N + 1 - ·)) _ X rfl
    (fun t ht => by
      obtain ⟨hv, ho⟩ := memX t ht
      refine mem_filter.2 ⟨flipLast_mem_validHalf hN (by omega) hv ho, ?_⟩
      obtain ⟨t', x, rfl⟩ := split t ht
      rw [flipLast_concat, lastOuter_concat]; rw [lastOuter_concat] at ho
      have := bnd _ ht x (by simp); omega)
    (fun t ht => by
      obtain ⟨hv, ho⟩ := memX t ht
      refine mem_filter.2 ⟨map_mirror_mem_validHalf hN hv, ?_⟩
      obtain ⟨t', x, rfl⟩ := split t ht
      rw [List.map_append, List.map_singleton, lastOuter_concat]; rw [lastOuter_concat] at ho
      have := bnd _ ht x (by simp); omega)
    (fun t ht => by
      obtain ⟨t', x, rfl⟩ := split t ht
      have := bnd _ ht x (by simp)
      rw [flipLast_concat, flipLast_concat, show N + 1 - (N + 1 - x) = x by omega])
    mirror_mirror'
    (fun t ht => by
      obtain ⟨t', x, rfl⟩ := split t ht
      simp only [List.map_append, List.map_singleton, flipLast_concat])
    (fun t ht => by
      obtain ⟨t', x, rfl⟩ := split t ht
      have := bnd _ ht x (by simp)
      rw [flipLast_concat]; intro e
      have := List.append_inj_right' e rfl
      simp at this; omega)
    (fun t ht => by
      obtain ⟨t', x, rfl⟩ := split t ht
      have := bnd _ ht x (by simp)
      intro e
      have := congrArg List.getLast? e
      simp at this; omega)
  have hempty : (X.filter fun t => flipLast N (t.map (N + 1 - ·)) = t) = ∅ := by
    apply filter_false_of_mem
    intro t ht e
    obtain ⟨t', x, rfl⟩ := split t ht
    have hl := (mem_halfSeqs.1 (mem_filter.1 (memX _ ht).1).1).2.1
    simp only [List.length_append, List.length_singleton] at hl
    rw [List.map_append, List.map_singleton, flipLast_concat] at e
    have e' := List.append_inj_left' e rfl
    obtain ⟨y, ys, rfl⟩ : ∃ y ys, t' = y :: ys := by
      cases t' with
      | nil => simp at hl; omega
      | cons y ys => exact ⟨y, ys, rfl⟩
    simp only [List.map_cons, List.cons.injEq] at e'
    have := bnd _ ht y (by simp)
    omega
  rw [hempty, card_empty] at h
  omega

end Folds
