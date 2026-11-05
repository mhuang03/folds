import Folds.Prefix
import Folds.Cyclic

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

end Folds
