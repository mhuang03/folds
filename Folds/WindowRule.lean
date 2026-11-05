import Folds.Prefix
import Folds.Cyclic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# The window rule, suffixes, and dead 2-prefixes

Let `S` be a nodup list of panels in `[1, N]` and `c ∉ S` a panel.  Write
`A = #{x ∈ S | c < x}` (points above `c`) and `B = #{x ∈ S | x < c}` (points below).
The window of `c` is `[2c - N, 2c - 1] ∩ [1, N]`.

* `semiStep_iff_window` (**window rule**, an iff):
  - if `A < B`: the step is semi-symmetric iff `c` is in the right half (`N + 1 < 2c`) and
    exactly `A` points of `S` lie in `[2c - N, c)`.  Equivalently (`ys` the points below `c`
    in decreasing order) `y_A ≥ 2c - N > y_{A+1}`;
  - if `B < A`: mirror image, `2c < N + 1` and exactly `B` points of `S` lie in `(c, 2c - 1]`;
  - if `A = B`: every point of `S` lies in the window.
* `card_validSuffixes`: the numbers of valid length-`k` suffixes and of valid length-`k`
  prefixes are equal (reversal plus complementation).
* `not_semiSymmetric_one_N`, `not_semiSymmetric_N_one`: for even `N ≥ 3` no semi-symmetric
  fold sequence starts with `[1, N]` or `[N, 1]` (no valid third step exists).
-/

namespace Folds

/-! ## The window rule -/

/-- Number of points of `S` above `c`. -/
def numAbove (S : List Nat) (c : Nat) : Nat := S.countP (fun x => c < x)

/-- Number of points of `S` below `c`. -/
def numBelow (S : List Nat) (c : Nat) : Nat := S.countP (fun x => x < c)

theorem countP_le_of_imp {S : List Nat} {p q : Nat → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ x, p x → q x) :
    S.countP (fun x => decide (p x)) + S.countP (fun x => decide (q x ∧ ¬ p x)) =
      S.countP (fun x => decide (q x)) := by
  rw [countP_split S (fun x => decide (q x)) (fun x => decide (p x))]
  congr 1
  · apply List.countP_congr; intro x _; have := h x; simp; tauto

theorem countP_eq_zero_iff' {S : List Nat} {p : Nat → Prop} [DecidablePred p] :
    S.countP (fun x => decide (p x)) = 0 ↔ ∀ x ∈ S, ¬ p x := by
  rw [List.countP_eq_zero]; simp

/-- **The window rule.**  For a nodup list `S ⊆ [1, N]` and a panel `c ∉ S`, with
`A = numAbove S c` and `B = numBelow S c`, the step `(S, c)` is semi-symmetric iff
* `A < B`, `c` is in the right half and exactly `A` points lie in `[2c - N, c)`, or
* `B < A`, `c` is in the left half and exactly `B` points lie in `(c, 2c - 1]`, or
* `A = B` and the window `[2c - N, 2c - 1]` contains all of `S`. -/
theorem semiStep_iff_window {N c : Nat} {S : List Nat} (hnd : S.Nodup)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (hc1 : 1 ≤ c) (hcN : c ≤ N) (hcS : c ∉ S) :
    SemiStep N S c ↔
      (numAbove S c < numBelow S c ∧ N + 1 < 2 * c ∧
          S.countP (fun x => 2 * c - N ≤ x ∧ x < c) = numAbove S c) ∨
      (numBelow S c < numAbove S c ∧ 2 * c < N + 1 ∧
          S.countP (fun x => c < x ∧ x ≤ 2 * c - 1) = numBelow S c) ∨
      (numAbove S c = numBelow S c ∧ ∀ x ∈ S, 2 * c - N ≤ x ∧ x ≤ 2 * c - 1) := by
  have hne : ∀ x ∈ S, x ≠ c := fun x hx e => hcS (e ▸ hx)
  -- split the counts above/below into inside / outside the window
  have hB := countP_le_of_imp (S := S) (p := fun x => c - reach N c ≤ x ∧ x < c)
    (q := fun x => x < c) (fun x h => h.2)
  have hA := countP_le_of_imp (S := S) (p := fun x => c < x ∧ x ≤ c + reach N c)
    (q := fun x => c < x) (fun x h => h.1)
  rw [← leftCount_eq hnd] at hB
  rw [← rightCount_eq hnd] at hA
  set L := leftCount N S c
  set R := rightCount N S c
  set Lo := S.countP (fun x => decide (x < c ∧ ¬(c - reach N c ≤ x ∧ x < c)))
  set Ro := S.countP (fun x => decide (c < x ∧ ¬(c < x ∧ x ≤ c + reach N c)))
  change L + Lo = numBelow S c at hB
  change R + Ro = numAbove S c at hA
  have hwin : (∀ x ∈ S, 2 * c - N ≤ x ∧ x ≤ 2 * c - 1) ↔ Lo = 0 ∧ Ro = 0 := by
    rw [countP_eq_zero_iff', countP_eq_zero_iff']
    constructor
    · intro h
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> have := h x hx <;> have := hS x hx <;>
        unfold reach <;> omega
    · rintro ⟨h1, h2⟩ x hx
      have := h1 x hx; have := h2 x hx; have := hS x hx; have := hne x hx
      unfold reach at *; omega
  unfold SemiStep
  rcases Nat.lt_or_ge N (2 * c - 1) with hh | hh
  · -- right half: everything above `c` is in the window
    have hRo : Ro = 0 := by
      rw [countP_eq_zero_iff']; intro x hx; have := hS x hx; unfold reach; omega
    have hL : L = S.countP (fun x => 2 * c - N ≤ x ∧ x < c) := by
      show leftCount N S c = _
      rw [leftCount_eq hnd]; apply List.countP_congr; intro x _; unfold reach; simp; omega
    rw [hwin, ← hL]
    omega
  · -- left half: everything below `c` is in the window
    have hLo : Lo = 0 := by
      rw [countP_eq_zero_iff']; intro x hx; have := hS x hx; unfold reach; omega
    have hR : R = S.countP (fun x => c < x ∧ x ≤ 2 * c - 1) := by
      show rightCount N S c = _
      rw [rightCount_eq hnd]; apply List.countP_congr; intro x _; unfold reach; simp; omega
    have hmid : 2 * c - 1 = N → Ro = 0 := by
      intro e; rw [countP_eq_zero_iff']; intro x hx; have := hS x hx; unfold reach; omega
    rw [hwin, ← hR]
    omega

/-! ## Valid suffixes and valid prefixes are equinumerous -/

/-- The repetition-free lists of length `k` with entries in `[1, N]`. -/
def kLists (N k : Nat) : Finset (List Nat) :=
  ((Finset.Icc 1 N).powersetCard k).biUnion orderings

theorem mem_kLists {N k : Nat} {l : List Nat} :
    l ∈ kLists N k ↔ l.Nodup ∧ l.length = k ∧ ∀ x ∈ l, 1 ≤ x ∧ x ≤ N := by
  simp only [kLists, Finset.mem_biUnion, Finset.mem_powersetCard, mem_orderings]
  constructor
  · rintro ⟨S, ⟨hS, hk⟩, hnd, rfl⟩
    refine ⟨hnd, by rw [← hk, List.toFinset_card_of_nodup hnd], fun x hx => ?_⟩
    have := hS (List.mem_toFinset.2 hx)
    simpa using this
  · rintro ⟨hnd, hk, hx⟩
    refine ⟨l.toFinset, ⟨fun x h => ?_, by rw [List.toFinset_card_of_nodup hnd, hk]⟩, hnd, rfl⟩
    rw [List.mem_toFinset] at h
    simpa using hx x h

/-- The valid length-`k` prefixes: repetition-free lists of panels in which every step is
semi-symmetric.  Their number is `T(N, k)`. -/
def validPrefixes (N k : Nat) : Finset (List Nat) := (kLists N k).filter (SemiSymmetric N)

/-- `l = [b₁, …, b_k]` is valid as the *last* `k` steps of a bisection order of `[1..N]`:
when `bᵢ` is bisected, the panels bisected so far are exactly those not in `[bᵢ, …, b_k]`. -/
def SuffixValid (N : Nat) (l : List Nat) : Prop :=
  ∀ i (h : i < l.length), SemiStep N ((List.range' 1 N).filter (fun x => x ∉ l.drop i)) l[i]

instance (N : Nat) (l : List Nat) : Decidable (SuffixValid N l) := by
  unfold SuffixValid; infer_instance

/-- The valid length-`k` suffixes. -/
def validSuffixes (N k : Nat) : Finset (List Nat) := (kLists N k).filter (SuffixValid N)

/-- A list is a valid suffix iff its reversal is a valid prefix. -/
theorem suffixValid_iff {N : Nat} {l : List Nat} (hnd : l.Nodup)
    (hl : ∀ x ∈ l, 1 ≤ x ∧ x ≤ N) : SuffixValid N l ↔ SemiSymmetric N l.reverse := by
  have key : ∀ i (h : i < l.length),
      SemiStep N ((List.range' 1 N).filter (fun x => x ∉ l.drop i)) l[i] ↔
        SemiStep N (l.drop (i + 1)).reverse l[i] := by
    intro i h
    apply semiStep_iff_of_compl
    intro d hd1 hd2
    have hm := hl _ (List.getElem_mem h)
    have hdrop : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons h
    have hnot : l[i] ∉ l.drop (i + 1) := by
      have := hnd.sublist (List.drop_sublist i l)
      rw [hdrop, List.nodup_cons] at this; exact this.1
    unfold reach at hd2
    simp only [List.mem_reverse, List.mem_filter, List.mem_range'_1, hdrop, List.mem_cons,
      decide_eq_true_eq]
    constructor
    · constructor
      · intro hx; refine fun ⟨_, hn⟩ => hn (Or.inr hx)
      · intro hx; by_contra hc; exact hx ⟨by omega, fun h' => h'.elim (by omega) hc⟩
    · constructor
      · intro hx; refine fun ⟨_, hn⟩ => hn (Or.inr hx)
      · intro hx; by_contra hc; exact hx ⟨by omega, fun h' => h'.elim (by omega) hc⟩
  constructor
  · intro h k hk
    simp only [List.length_reverse] at hk
    have e1 : l.reverse[k]'(by simpa using hk) = l[l.length - 1 - k] := by
      rw [List.getElem_reverse]
    have e2 : l.reverse.take k = (l.drop (l.length - 1 - k + 1)).reverse := by
      rw [List.take_reverse]; congr 2; omega
    rw [e1, e2]
    exact (key _ (by omega)).1 (h _ (by omega))
  · intro h i hi
    have := h (l.length - 1 - i) (by simp; omega)
    have e1 : l.reverse[l.length - 1 - i]'(by simp; omega) = l[i] := by
      rw [List.getElem_reverse]; congr 1; omega
    have e2 : l.reverse.take (l.length - 1 - i) = (l.drop (i + 1)).reverse := by
      rw [List.take_reverse]; congr 2; omega
    rw [e1, e2] at this
    exact (key i hi).2 this

/-- **Suffix count = prefix count.**  The number of valid length-`k` suffixes equals the
number of valid length-`k` prefixes `T(N, k)`; the bijection is reversal. -/
theorem card_validSuffixes (N k : Nat) :
    (validSuffixes N k).card = (validPrefixes N k).card := by
  apply Finset.card_nbij' List.reverse List.reverse
  · intro l hl
    simp only [validSuffixes, validPrefixes, Finset.coe_filter, Set.mem_ofPred_eq,
      mem_kLists] at hl ⊢
    obtain ⟨⟨hnd, hk, hx⟩, hv⟩ := hl
    exact ⟨⟨List.nodup_reverse.2 hnd, by simpa using hk, fun x h => hx x (List.mem_reverse.1 h)⟩,
      (suffixValid_iff hnd hx).1 hv⟩
  · intro l hl
    simp only [validSuffixes, validPrefixes, Finset.coe_filter, Set.mem_ofPred_eq,
      mem_kLists] at hl ⊢
    obtain ⟨⟨hnd, hk, hx⟩, hv⟩ := hl
    have hnd' : l.reverse.Nodup := List.nodup_reverse.2 hnd
    have hx' : ∀ x ∈ l.reverse, 1 ≤ x ∧ x ≤ N := fun x h => hx x (List.mem_reverse.1 h)
    refine ⟨⟨hnd', by simpa using hk, hx'⟩, ?_⟩
    rw [suffixValid_iff hnd' hx', List.reverse_reverse]; exact hv
  · intro l _; simp
  · intro l _; simp

/-- The valid 2-prefixes counted here are those of `Folds.Prefix`: `T(N, 2) = ⌊N²/2⌋`. -/
theorem card_validPrefixes_two (N : Nat) : (validPrefixes N 2).card = N * N / 2 := by
  rw [← card_prefixTwo]
  apply Finset.card_nbij' (fun l => (l.headD 0, l.getLastD 0)) (fun p => [p.1, p.2])
  · intro l hl
    simp only [validPrefixes, Finset.coe_filter, Set.mem_ofPred_eq, mem_kLists] at hl
    obtain ⟨⟨hnd, hk, hx⟩, hv⟩ := hl
    match l, hk with
    | [a, b], _ =>
      simp only [Finset.mem_coe, prefixTwo_mem_iff]
      exact ⟨hx a (by simp), hx b (by simp), hnd, hv⟩
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_coe, prefixTwo_mem_iff] at hp
    simp only [validPrefixes, Finset.coe_filter, Set.mem_ofPred_eq, mem_kLists]
    refine ⟨⟨hp.2.2.1, rfl, ?_⟩, hp.2.2.2⟩
    intro x hx; simp at hx; rcases hx with rfl | rfl
    · exact hp.1
    · exact hp.2.1
  · intro l hl
    simp only [validPrefixes, Finset.coe_filter, Set.mem_ofPred_eq, mem_kLists] at hl
    match l, hl.1.2.1 with
    | [a, b], _ => rfl
  · intro p _; rfl

/-! ## Dead 2-prefixes: `(1, N)` and `(N, 1)` for even `N` -/

/-- For even `N`, after bisecting panels `1` and `N` no panel can be bisected: every window
contains exactly one of `1` and `N` (only the middle panel of an odd strip sees both). -/
theorem not_semiStep_one_N {N m : Nat} (hN : N % 2 = 0) (hm1 : 2 ≤ m) (hmN : m < N) :
    ¬ SemiStep N [1, N] m := by
  intro h
  unfold SemiStep at h
  rw [leftCount_eq (by simp; omega), rightCount_eq (by simp; omega)] at h
  simp only [List.countP_cons, List.countP_nil] at h
  unfold reach at h
  split_ifs at h <;> simp_all <;> omega

theorem not_semiStep_N_one {N m : Nat} (hN : N % 2 = 0) (hm1 : 2 ≤ m) (hmN : m < N) :
    ¬ SemiStep N [N, 1] m := by
  rw [semiStep_congr (T := [1, N]) (fun x => by simp; tauto)]
  exact not_semiStep_one_N hN hm1 hmN

/-- **Dead 2-prefix.**  For even `N ≥ 3`, no semi-symmetric fold sequence starts with
`[1, N]`. -/
theorem not_semiSymmetric_one_N {N : Nat} {a : List Nat} (hN : N % 2 = 0) (h3 : 3 ≤ N)
    (hf : IsFoldSeq N a) (ha : a.take 2 = [1, N]) : ¬ SemiSymmetric N a := by
  intro h
  have hlen : a.length = N := by rw [hf.length_eq]; simp
  have hs := h 2 (by omega)
  have h2 : 2 < a.length := by omega
  have hm := (mem_range'_of_perm hf).1 (List.getElem_mem h2)
  have hnt : a[2] ∉ a.take 2 := by
    rw [getElem_mem_take_iff (nodup_of_foldSeq hf) h2]; omega
  rw [ha] at hs hnt
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnt
  exact not_semiStep_one_N hN (by omega) (by omega) hs

/-- **Dead 2-prefix.**  For even `N ≥ 3`, no semi-symmetric fold sequence starts with
`[N, 1]`. -/
theorem not_semiSymmetric_N_one {N : Nat} {a : List Nat} (hN : N % 2 = 0) (h3 : 3 ≤ N)
    (hf : IsFoldSeq N a) (ha : a.take 2 = [N, 1]) : ¬ SemiSymmetric N a := by
  intro h
  have hlen : a.length = N := by rw [hf.length_eq]; simp
  have hs := h 2 (by omega)
  have h2 : 2 < a.length := by omega
  have hm := (mem_range'_of_perm hf).1 (List.getElem_mem h2)
  have hnt : a[2] ∉ a.take 2 := by
    rw [getElem_mem_take_iff (nodup_of_foldSeq hf) h2]; omega
  rw [ha] at hs hnt
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnt
  exact not_semiStep_N_one hN (by omega) (by omega) hs

/-- `[1, N]` and `[N, 1]` are valid 2-prefixes for every `N ≥ 2`, so they really are dead
ends, not invalid prefixes. -/
theorem semiSymmetric_one_N {N : Nat} (hN : 2 ≤ N) :
    SemiSymmetric N [1, N] ∧ SemiSymmetric N [N, 1] := by
  rw [semiSymmetric_pair_iff, semiSymmetric_pair_iff,
    semiStep_pair_iff le_rfl (by omega) (by omega) le_rfl (by omega),
    semiStep_pair_iff (by omega) le_rfl le_rfl (by omega) (by omega)]
  omega

/-! ## Extending a prefix -/

/-- The partial sequence `p` can be completed to a semi-symmetric fold sequence. -/
def Extends (N : Nat) (p : List Nat) : Prop :=
  ∃ a, IsFoldSeq N a ∧ SemiSymmetric N a ∧ p <+: a

/-- **Completability depends only on the complement.**  A valid prefix `p` extends to a
semi-symmetric fold sequence iff the set of remaining panels has a semi-symmetric
ordering *from scratch* (`g N ([1..N] \ p) > 0`): the rest of a completion, read backwards,
is such an ordering (reversal / complementation). -/
theorem extends_iff_g_pos {N : Nat} {p : List Nat} (hnd : p.Nodup)
    (hp : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N) (hv : SemiSymmetric N p) :
    Extends N p ↔ 0 < g N (Finset.Icc 1 N \ p.toFinset) := by
  rw [g, Finset.card_pos]
  constructor
  · rintro ⟨a, hf, ha, t, rfl⟩
    have hnda := nodup_of_foldSeq hf
    rw [semiSymmetric_split_iff hf (k := p.length) (by simp), List.drop_left] at ha
    refine ⟨t.reverse, mem_semiOrders.2 ⟨⟨?_, ?_⟩, ha.2⟩⟩
    · exact List.nodup_reverse.2 (List.nodup_append.1 hnda).2.1
    · ext x
      have hfs := (isFoldSeq_iff.1 hf).2
      rw [List.toFinset_append] at hfs
      have hdis := (List.nodup_append.1 hnda).2.2
      simp only [List.toFinset_reverse, Finset.mem_sdiff, List.mem_toFinset, ← hfs,
        Finset.mem_union]
      constructor
      · intro hx; exact ⟨Or.inr hx, fun hx' => hdis x hx' x hx rfl⟩
      · rintro ⟨hx | hx, hn⟩
        · exact absurd hx hn
        · exact hx
  · rintro ⟨q, hq⟩
    obtain ⟨⟨hndq, hq⟩, hsq⟩ := mem_semiOrders.1 hq
    have hf : IsFoldSeq N (p ++ q.reverse) := by
      rw [isFoldSeq_iff]
      refine ⟨List.nodup_append.2 ⟨hnd, List.nodup_reverse.2 hndq, ?_⟩, ?_⟩
      · intro x hx y hy e
        subst e
        have : x ∈ q.toFinset := List.mem_toFinset.2 (List.mem_reverse.1 hy)
        rw [hq, Finset.mem_sdiff, List.mem_toFinset] at this
        exact this.2 hx
      · rw [List.toFinset_append, List.toFinset_reverse, hq, Finset.union_sdiff_of_subset]
        intro x hx
        rw [List.mem_toFinset] at hx
        simpa using hp x hx
    refine ⟨p ++ q.reverse, hf, ?_, List.prefix_append _ _⟩
    rw [semiSymmetric_split_iff hf (k := p.length) (by simp), List.take_left, List.drop_left,
      List.reverse_reverse]
    exact ⟨hv, hsq⟩

/-- **Dead 2-prefixes.**  For even `N ≥ 3` the valid 2-prefixes `[1, N]` and `[N, 1]`
cannot be completed to a semi-symmetric fold sequence. -/
theorem not_extends_one_N {N : Nat} (hN : N % 2 = 0) (h3 : 3 ≤ N) :
    ¬ Extends N [1, N] ∧ ¬ Extends N [N, 1] := by
  constructor
  · rintro ⟨a, hf, ha, hpre⟩
    exact not_semiSymmetric_one_N hN h3 hf (List.prefix_iff_eq_take.1 hpre).symm ha
  · rintro ⟨a, hf, ha, hpre⟩
    exact not_semiSymmetric_N_one hN h3 hf (List.prefix_iff_eq_take.1 hpre).symm ha

/-! ## `T(N, 3)`: valid 3-prefixes

Reduction of `T(N, 3) = #validPrefixes N 3` to an explicit double sum. -/

/-- Mirroring a single step: `m ↦ N + 1 - m`. -/
theorem semiStep_mirror_iff {N m : Nat} {S : List Nat} (hS : ∀ x ∈ S, x ≤ N)
    (hm1 : 1 ≤ m) (hmN : m ≤ N) :
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

/-- The step `({a, b}, c)` in arithmetic form. -/
theorem semiStep_two_iff {N a b c : Nat} (hab : a ≠ b) :
    SemiStep N [a, b] c ↔
      (if c - reach N c ≤ a ∧ a < c then 1 else 0) + (if c - reach N c ≤ b ∧ b < c then 1 else 0) =
      (if c < a ∧ a ≤ c + reach N c then 1 else 0) + (if c < b ∧ b ≤ c + reach N c then 1 else 0) := by
  have hnd : [a, b].Nodup := by simp [hab]
  unfold SemiStep
  rw [leftCount_eq hnd, rightCount_eq hnd]
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split_ifs <;> simp

/-- The valid 3-prefixes as triples `(a, b, c)`. -/
def triples3 (N : Nat) : Finset (Nat × Nat × Nat) :=
  (Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter fun t =>
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ SemiStep N [t.1] t.2.1 ∧
      SemiStep N [t.1, t.2.1] t.2.2

theorem semiSymmetric_three_iff {N a b c : Nat} :
    SemiSymmetric N [a, b, c] ↔ SemiStep N [a] b ∧ SemiStep N [a, b] c := by
  have : [a, b, c] = [a, b] ++ [c] := rfl
  rw [this, semiSymmetric_concat_iff, semiSymmetric_pair_iff]

theorem card_validPrefixes_three (N : Nat) :
    (validPrefixes N 3).card = (triples3 N).card := by
  apply Finset.card_nbij' (fun l => (l.getD 0 0, l.getD 1 0, l.getD 2 0))
    (fun t => [t.1, t.2.1, t.2.2])
  · intro l hl
    simp only [validPrefixes, Finset.coe_filter, Set.mem_ofPred_eq, mem_kLists] at hl
    obtain ⟨⟨hnd, hk, hx⟩, hv⟩ := hl
    match l, hk with
    | [a, b, c], _ =>
      simp only [triples3, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
        Set.mem_ofPred_eq, List.getD_cons_zero, List.getD_cons_succ]
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        or_false, not_or] at hnd
      rw [semiSymmetric_three_iff] at hv
      have ha := hx a (by simp); have hb := hx b (by simp); have hc := hx c (by simp)
      exact ⟨⟨ha, hb, hc⟩, hnd.1.1, hnd.1.2, hnd.2.1, hv⟩
  · rintro ⟨a, b, c⟩ ht
    simp only [triples3, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      Set.mem_ofPred_eq] at ht
    simp only [validPrefixes, Finset.coe_filter, Set.mem_ofPred_eq, mem_kLists]
    obtain ⟨⟨ha, hb, hc⟩, h1, h2, h3, hv⟩ := ht
    refine ⟨⟨by simp [h1, h2, h3], rfl, ?_⟩, semiSymmetric_three_iff.2 hv⟩
    intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
  · intro l hl
    simp only [validPrefixes, Finset.coe_filter, Set.mem_ofPred_eq, mem_kLists] at hl
    match l, hl.1.2.1 with
    | [a, b, c], _ => rfl
  · intro t _; rfl

/-- Number of valid third panels `c` after a valid pair `(a, b)` with `2b ≤ a`:
`c` is a new maximum (`2c > N + a`), a new minimum (`2c ≤ b`), or lies between
(`a + 1 ≤ 2c ≤ N + b`, `c < a`). -/
def Zf (N a b : Nat) : Nat :=
  (N - (N + a) / 2) + b / 2 + (min (a - 1) ((N + b) / 2) + 1 - (a + 2) / 2)

theorem card_third {N a b : Nat} (hb : 1 ≤ b) (hab : 2 * b ≤ a) (haN : a ≤ N) :
    ((Finset.Icc 1 N).filter fun c => a ≠ c ∧ b ≠ c ∧ SemiStep N [a, b] c).card = Zf N a b := by
  have e : (Finset.Icc 1 N).filter (fun c => a ≠ c ∧ b ≠ c ∧ SemiStep N [a, b] c) =
      (Finset.Icc 1 (b / 2) ∪ Finset.Icc ((a + 2) / 2) (min (a - 1) ((N + b) / 2))) ∪
        Finset.Icc ((N + a) / 2 + 1) N := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union,
      semiStep_two_iff (show a ≠ b by omega)]
    unfold reach
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
      split_ifs at h5 <;> omega
    · intro h
      refine ⟨by omega, by omega, by omega, ?_⟩
      split_ifs <;> omega
  rw [e, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Nat.card_Icc,
    Nat.card_Icc, Nat.card_Icc]
  · unfold Zf; omega
  · rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
  · rw [Finset.disjoint_left]; intro x h1 h2
    simp only [Finset.mem_Icc, Finset.mem_union] at h1 h2; omega

/-- The double sum `W(N) = Σ_{a ≤ N} Σ_{1 ≤ b ≤ a/2} Z(N, a, b)`, half of `T(N, 3)`. -/
def Wf (N : Nat) : Nat := ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (a / 2), Zf N a b

/-- Triples whose pair `(a, b)` has `2b ≤ a`. -/
def triplesLow (N : Nat) : Finset (Nat × Nat × Nat) := (triples3 N).filter fun t => 2 * t.2.1 ≤ t.1

theorem card_triplesLow (N : Nat) : (triplesLow N).card = Wf N := by
  rw [triplesLow, triples3, Finset.filter_filter, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product, Wf]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_Icc] at ha
  rw [Finset.sum_product]
  rw [← Finset.sum_subset (s₁ := Finset.Icc 1 (a / 2)) (s₂ := Finset.Icc 1 N)]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_Icc] at hb
    rw [← card_third hb.1 (by omega) ha.2, Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    have h1 : SemiStep N [a] b := by
      rw [semiStep_pair_iff (by omega) hb.1 ha.2 (by omega) (by omega)]; omega
    dsimp only
    split_ifs with hx hy hy
    · rfl
    · exact absurd ⟨hx.1.2.1, hx.1.2.2.1, hx.1.2.2.2.2⟩ hy
    · exact absurd ⟨⟨by omega, hy.1, hy.2.1, h1, hy.2.2⟩, by omega⟩ hx
    · rfl
  · intro b hb; simp only [Finset.mem_Icc] at hb ⊢; omega
  · intro b hb0 hb
    simp only [Finset.mem_Icc, not_and, not_le] at hb hb0
    apply Finset.sum_eq_zero
    intro c _
    dsimp only
    split_ifs with hx
    · obtain ⟨-, h2⟩ := hx
      omega
    · rfl

/-- **`T(N, 3) = 2 W(N)`**, by mirror symmetry of valid pairs. -/
theorem card_triples3 (N : Nat) : (triples3 N).card = 2 * Wf N := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := triples3 N)
    (fun t : Nat × Nat × Nat => 2 * t.2.1 ≤ t.1)
  rw [← card_triplesLow]
  suffices h : ((triples3 N).filter (fun t : Nat × Nat × Nat => ¬ 2 * t.2.1 ≤ t.1)).card =
      (triplesLow N).card by
    rw [triplesLow] at h ⊢; omega
  apply Finset.card_nbij' (fun t => (N + 1 - t.1, N + 1 - t.2.1, N + 1 - t.2.2))
    (fun t => (N + 1 - t.1, N + 1 - t.2.1, N + 1 - t.2.2))
  · rintro ⟨a, b, c⟩ h
    simp only [triplesLow, triples3, Finset.coe_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Set.mem_ofPred_eq] at h ⊢
    obtain ⟨⟨⟨ha, hb, hc⟩, h1, h2, h3, hs1, hs2⟩, hlow⟩ := h
    refine ⟨⟨⟨by omega, by omega, by omega⟩, by omega, by omega, by omega, ?_, ?_⟩, ?_⟩
    · rw [semiStep_pair_iff (by omega) (by omega) (by omega) (by omega) (by omega)]
      rw [semiStep_pair_iff (by omega) (by omega) (by omega) (by omega) (by omega)] at hs1
      omega
    · have := (semiStep_mirror_iff (S := [a, b]) (N := N) (m := c)
        (by intro x hx; simp at hx; omega) hc.1 hc.2).2 hs2
      simpa using this
    · rw [semiStep_pair_iff (by omega) (by omega) (by omega) (by omega) (by omega)] at hs1
      omega
  · rintro ⟨a, b, c⟩ h
    simp only [triplesLow, triples3, Finset.coe_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Set.mem_ofPred_eq] at h ⊢
    obtain ⟨⟨⟨ha, hb, hc⟩, h1, h2, h3, hs1, hs2⟩, hlow⟩ := h
    refine ⟨⟨⟨by omega, by omega, by omega⟩, by omega, by omega, by omega, ?_, ?_⟩, ?_⟩
    · rw [semiStep_pair_iff (by omega) (by omega) (by omega) (by omega) (by omega)]
      rw [semiStep_pair_iff (by omega) (by omega) (by omega) (by omega) (by omega)] at hs1
      omega
    · have := (semiStep_mirror_iff (S := [a, b]) (N := N) (m := c)
        (by intro x hx; simp at hx; omega) hc.1 hc.2).2 hs2
      simpa using this
    · rw [semiStep_pair_iff (by omega) (by omega) (by omega) (by omega) (by omega)] at hs1
      omega
  · rintro ⟨a, b, c⟩ h
    simp only [triples3, Finset.coe_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Set.mem_ofPred_eq] at h
    dsimp only; simp only [Prod.mk.injEq]; omega
  · rintro ⟨a, b, c⟩ h
    simp only [triplesLow, triples3, Finset.coe_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc, Set.mem_ofPred_eq] at h
    dsimp only; simp only [Prod.mk.injEq]; omega

/-! ### Evaluating `W(N)` -/

theorem sum_half (N : Nat) : ∑ a ∈ Finset.Icc 1 N, a / 2 = N * N / 4 := by
  induction N with
  | zero => rfl
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, sq_div_four_succ]

/-- `hs e K = Σ_{1 ≤ b ≤ K} (b + e) / 2`. -/
def hs (e K : Nat) : Nat := ∑ b ∈ Finset.Icc 1 K, (b + e) / 2

theorem hs_zero (K : Nat) : hs 0 K = K * K / 4 := by
  simp only [hs, Nat.add_zero]; exact sum_half K

theorem hs_one (K : Nat) : hs 1 K = (K + 1) * (K + 1) / 4 := by
  induction K with
  | zero => rfl
  | succ n ih =>
    rw [hs, Finset.sum_Icc_succ_top (by omega)]
    rw [hs] at ih
    rw [ih, sq_div_four_succ (n + 1)]

theorem sq_div_four_mod (x : Nat) : 4 * (x * x / 4) + x % 2 = x * x := by
  rcases Nat.even_or_odd' x with ⟨k, rfl | rfl⟩
  · have e : 2 * k * (2 * k) = 4 * (k * k) := by ring
    rw [e]; omega
  · have e : (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 := by ring
    rw [e]; omega

/-- `C(N) = Σ_{a ≤ N} min(⌊a/2⌋, 2a - 3 - N)`: pairs `(a, b)` with `2b ≤ a` whose middle
range for `c` grows when `N` grows by `2`. -/
def Cf (N : Nat) : Nat := ∑ a ∈ Finset.Icc 1 N, min (a / 2) (2 * a - (3 + N))

theorem sum_ite_le (N a : Nat) :
    ∑ b ∈ Finset.Icc 1 (a / 2), (if N + b + 3 ≤ 2 * a then 1 else 0) =
      min (a / 2) (2 * a - (3 + N)) := by
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  have e : (Finset.Icc 1 (a / 2)).filter (fun b => N + b + 3 ≤ 2 * a) =
      Finset.Icc 1 (min (a / 2) (2 * a - (3 + N))) := by
    ext b; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [e, Nat.card_Icc]; omega

theorem Cf_succ (N : Nat) :
    Cf (N + 1) + (min N ((2 * N + 6) / 3) + 1 - (N + 5) / 2) =
      Cf N + min ((N + 1) / 2) (N - 2) := by
  have hcount : ∑ a ∈ Finset.Icc 1 N,
      (if N + 4 ≤ 2 * a ∧ 3 * a ≤ 2 * N + 6 then 1 else 0) =
      min N ((2 * N + 6) / 3) + 1 - (N + 5) / 2 := by
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    have e : (Finset.Icc 1 N).filter (fun a => N + 4 ≤ 2 * a ∧ 3 * a ≤ 2 * N + 6) =
        Finset.Icc ((N + 5) / 2) (min N ((2 * N + 6) / 3)) := by
      ext a; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [e, Nat.card_Icc]
  have hpt : ∑ a ∈ Finset.Icc 1 N, min (a / 2) (2 * a - (3 + (N + 1))) +
      ∑ a ∈ Finset.Icc 1 N, (if N + 4 ≤ 2 * a ∧ 3 * a ≤ 2 * N + 6 then 1 else 0) =
      ∑ a ∈ Finset.Icc 1 N, min (a / 2) (2 * a - (3 + N)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> omega
  have hm : min ((N + 1) / 2) (2 * (N + 1) - (3 + (N + 1))) = min ((N + 1) / 2) (N - 2) := by
    omega
  rw [Cf, Cf, Finset.sum_Icc_succ_top (by omega)]
  omega

/-- Closed form of `C(N)` for `N ≥ 2`: `6 C(N) = N² - 2N - d(N)`. -/
theorem Cf_closed (N : Nat) (hN : 2 ≤ N) :
    6 * Cf N + 2 * N + 3 * (N % 2) + 2 * (N % 3 % 2) = N * N := by
  induction N, hN using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hs := Cf_succ n
    have e : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
    rw [e]
    generalize n * n = X at ih ⊢
    rw [Nat.min_def, Nat.min_def] at hs
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 6 ∧ n = 6 * q + r :=
      ⟨n / 6, n % 6, Nat.mod_lt _ (by norm_num), by omega⟩
    interval_cases r <;> split_ifs at hs <;> omega

/-- One step `N → N + 2` of `W`. -/
theorem Wf_step {N : Nat} (hN : 2 ≤ N) :
    Wf (N + 2) = Wf N + N * N / 4 + Cf N +
      ((2 - N % 2) * ((N + 1) / 2) + hs 0 ((N + 1) / 2) + hs (N % 2) ((N + 1) / 2)) +
      (hs 0 ((N + 2) / 2) + hs (N % 2) ((N + 2) / 2)) := by
  rw [Wf, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
  have h1 : ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (a / 2), Zf (N + 2) a b =
      Wf N + N * N / 4 + Cf N := by
    rw [Wf, Cf, ← sum_half, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hpt : ∀ b ∈ Finset.Icc 1 (a / 2),
        Zf (N + 2) a b = Zf N a b + 1 + (if N + b + 3 ≤ 2 * a then 1 else 0) := by
      intro b hb
      rw [Finset.mem_Icc] at hb
      unfold Zf
      split_ifs <;> omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_le]
    simp
  have h2 : ∑ b ∈ Finset.Icc 1 ((N + 1) / 2), Zf (N + 2) (N + 1) b =
      (2 - N % 2) * ((N + 1) / 2) + hs 0 ((N + 1) / 2) + hs (N % 2) ((N + 1) / 2) := by
    have : (2 - N % 2) * ((N + 1) / 2) = ∑ b ∈ Finset.Icc 1 ((N + 1) / 2), (2 - N % 2) := by
      simp [mul_comm]
    rw [this, hs, hs, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_Icc] at hb
    unfold Zf; omega
  have h3 : ∑ b ∈ Finset.Icc 1 ((N + 2) / 2), Zf (N + 2) (N + 2) b =
      hs 0 ((N + 2) / 2) + hs (N % 2) ((N + 2) / 2) := by
    rw [hs, hs, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_Icc] at hb
    unfold Zf; omega
  rw [h1, h2, h3]

end Folds
