import Folds.Live7

/-!
# Live 3-prefixes

`experiments/live3p/PROOFS.txt`.

* `leftCount3`, `rightCount3`: the arm counts of a 3-set.
* `inward3`, `coReach3_of_F`: **Theorem G for 3-sets in closed form.**  For `a < b < c` with
  `2b ≤ N + 1`, the set `{a, b, c}` satisfies the criterion of Theorem G (for a suitable
  centre: `a`, `b` or `c`) whenever `F3 N a b c`, an explicit pair of linear conditions;
  by the mirror, sets with `2b ≥ N + 1` are handled through their mirror image.
  (`experiments/live3p/inward3.py`: `F3` is exactly the criterion of Theorem G for 3-sets.)
* `coReach_of_step`: Theorem G (or any co-reachability proof) after one valid extra step.
* `Dead3`, `not_extends_of_dead3`: the explicit dead 3-sets (the blocks `D_j`, their mirror
  images, and for odd `N ≥ 7` the corner sets in `{1, 2, N-1, N}`); dead for every `N`.
* `extends3_of_F`, `not_extends3_of_dead`: for every `N`, a valid 3-prefix whose set satisfies
  `F3S` is live, and one whose set is dead is not.
* `witB3`, `tblOK`, `coverX`, `Cert`, `cert_sound`: a kernel-checkable certificate format
  (witness orderings packed in base 64, checked by the bitmask checker of `Live7`).
* `extends3_iff_le_30`: **the 3-prefix analogue of Conjecture C for every `N ≤ 30`, `N ≠ 7`**:
  a valid 3-prefix is live iff its set is not one of the dead 3-sets `Dead3`.
-/

namespace Folds
namespace Live3p

open Live2 Live4 Adjacent Live7

/-! ## Arm counts of a 3-set -/

theorem toList_perm3 {a b c : Nat} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset Nat).toList.Perm [a, b, c] := by
  rw [List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (by simp [hab, hac, hbc])]
  intro x; simp

theorem leftCount3 {N m a b c : Nat} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    leftCount N ({a, b, c} : Finset Nat).toList m =
      (if m - reach N m ≤ a ∧ a < m then 1 else 0) +
      (if m - reach N m ≤ b ∧ b < m then 1 else 0) +
      (if m - reach N m ≤ c ∧ c < m then 1 else 0) := by
  rw [leftCount_eq (Finset.nodup_toList _), (toList_perm3 hab hac hbc).countP_eq]
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split_ifs <;> omega

theorem rightCount3 {N m a b c : Nat} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    rightCount N ({a, b, c} : Finset Nat).toList m =
      (if m < a ∧ a ≤ m + reach N m then 1 else 0) +
      (if m < b ∧ b ≤ m + reach N m then 1 else 0) +
      (if m < c ∧ c ≤ m + reach N m then 1 else 0) := by
  rw [rightCount_eq (Finset.nodup_toList _), (toList_perm3 hab hac hbc).countP_eq]
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split_ifs <;> omega

/-! ## Theorem G for 3-sets in closed form -/

/-- The closed-form criterion of Theorem G for `{a, b, c}`, `a < b < c`, `2b ≤ N + 1`.
The first clause excludes "positive panels in `(a, b/2]` together with negative panels in
`[(c+1)/2, b)`"; the second "negative panels in `((N+b)/2, c)` together with a positive panel
in `(a, b/2]` or at `b + 1`". -/
def F3 (N a b c : Nat) : Prop :=
  ¬ (2 * a + 2 ≤ b ∧ c + 3 ≤ 2 * b) ∧
  ¬ (b + 2 ≤ c ∧ N + b + 3 ≤ 2 * c ∧ (2 * a + 2 ≤ b ∨ 2 * b + 2 ≤ N + a))

instance (N a b c : Nat) : Decidable (F3 N a b c) := by unfold F3; infer_instance

theorem reach_eq (N m : Nat) : reach N m = if m - 1 ≤ N - m then m - 1 else N - m := by
  unfold reach; split_ifs with h
  · exact min_eq_left h
  · exact min_eq_right (by omega)

/-- **Theorem G for 3-sets.**  The centre is `c` if there are negative panels in
`((N+b)/2, c)`, else `b` if there are negative panels in `[(c+1)/2, b)`, else `a`. -/
theorem inward3 {N a b c : Nat} (h1 : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcN : c ≤ N)
    (hb : 2 * b ≤ N + 1) (hF : F3 N a b c) : ∃ c2, Inward N c2 {a, b, c} := by
  unfold F3 at hF
  have hne1 : a ≠ b := by omega
  have hne2 : a ≠ c := by omega
  have hne3 : b ≠ c := by omega
  by_cases n3 : b + 2 ≤ c ∧ N + b + 3 ≤ 2 * c
  · refine ⟨2 * c, fun m hm1 hmN hmB => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmB
    rw [leftCount3 hne1 hne2 hne3, rightCount3 hne1 hne2 hne3, reach_eq]
    refine ⟨by omega, fun _ => ?_, fun _ => ?_⟩ <;> split_ifs <;> omega
  · by_cases n2 : a + 2 ≤ b ∧ c + 3 ≤ 2 * b
    · refine ⟨2 * b, fun m hm1 hmN hmB => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmB
      rw [leftCount3 hne1 hne2 hne3, rightCount3 hne1 hne2 hne3, reach_eq]
      refine ⟨by omega, fun _ => ?_, fun _ => ?_⟩ <;> split_ifs <;> omega
    · refine ⟨2 * a, fun m hm1 hmN hmB => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmB
      rw [leftCount3 hne1 hne2 hne3, rightCount3 hne1 hne2 hne3, reach_eq]
      refine ⟨by omega, fun _ => ?_, fun _ => ?_⟩ <;> split_ifs <;> omega

/-- The criterion in either orientation: `F3` for `2b ≤ N + 1`, else `F3` of the mirror image
`{N+1-c, N+1-b, N+1-a}`. -/
def F3S (N a b c : Nat) : Prop :=
  if 2 * b ≤ N + 1 then F3 N a b c else F3 N (N + 1 - c) (N + 1 - b) (N + 1 - a)

instance (N a b c : Nat) : Decidable (F3S N a b c) := by unfold F3S; infer_instance

theorem image_mirror3 {N a b c : Nat} (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) :
    ({N + 1 - c, N + 1 - b, N + 1 - a} : Finset Nat).image (N + 1 - ·) = {a, b, c} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨y, hy, rfl⟩; omega
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨N + 1 - x, by omega, by omega⟩
    · exact ⟨N + 1 - x, by omega, by omega⟩
    · exact ⟨N + 1 - x, by omega, by omega⟩

/-- Co-reachability of a 3-set follows from that of its mirror image. -/
theorem coReach3_of_mirror {N a b c : Nat} (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N)
    (h : CoReach N {N + 1 - c, N + 1 - b, N + 1 - a}) : CoReach N {a, b, c} := by
  have := coReach_mirror h
  rwa [image_mirror3 ha hb hc] at this

/-- **Theorem G for 3-sets, both orientations**: `F3S N a b c` implies that `{a, b, c}` is
co-reachable. -/
theorem coReach3_of_F {N a b c : Nat} (h1 : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcN : c ≤ N)
    (hF : F3S N a b c) : CoReach N {a, b, c} := by
  have hB : ∀ {a b c : Nat}, 1 ≤ a → c ≤ N → ({a, b, c} : Finset Nat) ⊆ Finset.Icc 1 N →
      ({a, b, c} : Finset Nat) ⊆ Finset.Icc 1 N := fun _ _ h => h
  unfold F3S at hF
  split_ifs at hF with hb
  · obtain ⟨c2, hc2⟩ := inward3 h1 hab hbc hcN hb hF
    refine coReach_of_inward ?_ hc2
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Icc]; omega
  · refine coReach3_of_mirror (by omega) (by omega) hcN ?_
    obtain ⟨c2, hc2⟩ := inward3 (N := N) (a := N + 1 - c) (b := N + 1 - b) (c := N + 1 - a)
      (by omega) (by omega) (by omega) (by omega) (by omega) hF
    refine coReach_of_inward ?_ hc2
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Icc]; omega

/-! ## Theorem G after a valid extra step -/

/-- If `m` is a valid step after the background `D` and `D ∪ {m}` is co-reachable, then so is
`D` (complete `[N] \ (D ∪ {m})` from scratch, then place `m`: in the full sequence
`l, m, D` the step `m` is valid after `l` iff after `D`). -/
theorem coReach_of_step {N m : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 N) (hm1 : 1 ≤ m)
    (hmN : m ≤ N) (hmD : m ∉ D) (hs : SemiStep N D.toList m) (h : CoReach N (insert m D)) :
    CoReach N D := by
  unfold CoReach g at *
  rw [Finset.card_pos] at h ⊢
  obtain ⟨l, hl⟩ := h
  rw [mem_semiOrders] at hl
  obtain ⟨⟨hnd, hset⟩, hss⟩ := hl
  have hmem : ∀ x, x ∈ l ↔ (1 ≤ x ∧ x ≤ N) ∧ x ≠ m ∧ x ∉ D := fun x => by
    rw [← List.mem_toFinset, hset]
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_insert, not_or]
  have hnd1 : (l ++ [m]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, List.nodup_singleton m, fun a ha b hb e => ?_⟩
    rw [List.mem_singleton] at hb; subst hb; subst e; exact ((hmem _).1 ha).2.1 rfl
  have hf : IsFoldSeq N (l ++ [m] ++ D.toList) := by
    unfold IsFoldSeq
    have hnd' : (l ++ [m] ++ D.toList).Nodup := by
      rw [List.nodup_append]
      refine ⟨hnd1, Finset.nodup_toList D, fun a ha b hb e => ?_⟩
      subst e
      rw [Finset.mem_toList] at hb
      rw [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | ha
      · exact ((hmem _).1 ha).2.2 hb
      · subst ha; exact hmD hb
    rw [List.perm_ext_iff_of_nodup hnd' List.nodup_range']
    intro x
    simp only [List.mem_append, List.mem_singleton, Finset.mem_toList, List.mem_range'_1, hmem]
    constructor
    · rintro ((hx | rfl) | hx)
      · omega
      · omega
      · have := Finset.mem_Icc.1 (hD hx); omega
    · intro hx
      by_cases h1 : x = m
      · left; right; exact h1
      by_cases h2 : x ∈ D
      · right; exact h2
      · left; left; exact ⟨⟨hx.1, by omega⟩, h1, h2⟩
  have hstep : SemiStep N l m := (semiStep_compl hf).2 hs
  refine ⟨l ++ [m], mem_semiOrders.2 ⟨⟨hnd1, ?_⟩, semiSymmetric_concat_iff.2 ⟨hss, hstep⟩⟩⟩
  ext x
  rw [List.toFinset_append, Finset.mem_union, List.mem_toFinset, hmem, Finset.mem_sdiff,
    Finset.mem_Icc]
  simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton]
  constructor
  · rintro (hx | rfl)
    · exact ⟨hx.1, hx.2.2⟩
    · exact ⟨⟨hm1, hmN⟩, hmD⟩
  · intro hx
    by_cases h1 : x = m
    · right; exact h1
    · left; exact ⟨hx.1, h1, hx.2⟩

/-! ## The dead 3-sets -/

/-- The explicit dead 3-sets: the blocks `D_j = {1, 2j, 2j+1}` (`2 ≤ j`, `4j ≤ N + 3`), their
mirror images, and for odd `N ≥ 7` the 3-subsets of `{1, 2, N-1, N}`. -/
def Dead3 (N : Nat) (S : Finset Nat) : Prop :=
  (∃ j, 2 ≤ j ∧ 4 * j ≤ N + 3 ∧
    (S = {1, 2 * j, 2 * j + 1} ∨ S = {N - 2 * j, N + 1 - 2 * j, N})) ∨
  (N % 2 = 1 ∧ 7 ≤ N ∧
    (S = {1, 2, N - 1} ∨ S = {1, 2, N} ∨ S = {1, N - 1, N} ∨ S = {2, N - 1, N}))

theorem perm_of_toFinset {p : List Nat} {l : List Nat} (hp : p.Nodup) (hl : l.Nodup)
    (h : p.toFinset = l.toFinset) : p.Perm l := by
  rw [List.perm_ext_iff_of_nodup hp hl]
  intro x; rw [← List.mem_toFinset, h, List.mem_toFinset]

/-- **The dead direction, every `N`**: a prefix whose set is a dead 3-set cannot be
completed. -/
theorem not_extends_of_dead3 {N : Nat} {p : List Nat} (hnd : p.Nodup)
    (hp : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N) (hd : Dead3 N p.toFinset) : ¬ Extends N p := by
  have hm : ∀ {S : Finset Nat}, p.toFinset = S → ∀ x, x ∈ p ↔ x ∈ S := fun e x => by
    rw [← List.mem_toFinset, e]
  rcases hd with ⟨j, hj, hjN, e | e⟩ | ⟨hN, h7, e | e | e | e⟩
  · have := hm e
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    exact not_extends_block hj hjN ((this 1).2 (by simp)) ((this _).2 (by simp))
      ((this _).2 (by simp)) fun m hmp => by have := (this m).1 hmp; omega
  · have := hm e
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    exact not_extends_block_mirror hj hjN hp ((this N).2 (by simp)) ((this _).2 (by simp))
      ((this _).2 (by simp)) fun m hmp => by have := (this m).1 hmp; omega
  · exact not_extends_corner hN h7 (Or.inr (Or.inr (Or.inl (perm_of_toFinset hnd
      (by simp; omega) (by rw [e]; simp)))))
  · exact not_extends_corner hN h7 (Or.inl (perm_of_toFinset hnd
      (by simp; omega) (by rw [e]; simp)))
  · exact not_extends_corner hN h7 (Or.inr (Or.inl (perm_of_toFinset hnd
      (by simp; omega) (by rw [e]; simp))))
  · exact not_extends_corner hN h7 (Or.inr (Or.inr (Or.inr (perm_of_toFinset hnd
      (by simp; omega) (by rw [e]; simp)))))

/-- Boolean form of `Dead3` for a sorted triple `a < b < c`. -/
def dead3B (N a b c : Nat) : Bool :=
  (a == 1 && b % 2 == 0 && c == b + 1 && decide (4 ≤ b) && decide (2 * b ≤ N + 3)) ||
  (c == N && b == a + 1 && (N - a) % 2 == 0 && decide (4 ≤ N - a) &&
    decide (2 * (N - a) ≤ N + 3) && decide (a < N)) ||
  (N % 2 == 1 && decide (7 ≤ N) &&
    ((a == 1 && b == 2 && (c == N - 1 || c == N)) || (b == N - 1 && c == N && (a == 1 || a == 2))))

theorem dead3_of_dead3B {N a b c : Nat} (h : dead3B N a b c = true) : Dead3 N {a, b, c} := by
  unfold dead3B at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · left
    refine ⟨b / 2, by omega, by omega, Or.inl ?_⟩
    rw [show a = 1 by omega, show c = b + 1 by omega, show 2 * (b / 2) = b by omega]
  · left
    refine ⟨(N - a) / 2, by omega, by omega, Or.inr ?_⟩
    rw [show b = a + 1 by omega, show c = N by omega, show N - 2 * ((N - a) / 2) = a by omega,
      show N + 1 - 2 * ((N - a) / 2) = a + 1 by omega]
  · right
    refine ⟨by omega, by omega, ?_⟩
    have : (a = 1 ∧ b = 2 ∧ c = N - 1) ∨ (a = 1 ∧ b = 2 ∧ c = N) ∨ (a = 1 ∧ b = N - 1 ∧ c = N) ∨
        (a = 2 ∧ b = N - 1 ∧ c = N) := by omega
    rcases this with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-! ## A kernel-checkable certificate format -/

/-- The panels of `[N]` other than `a, b, c`. -/
def compl3 (N a b c : Nat) : List Nat :=
  (List.range' 1 N).filter fun x => x != a && x != b && x != c

theorem mem_compl3 {N a b c x : Nat} :
    x ∈ compl3 N a b c ↔ (1 ≤ x ∧ x ≤ N) ∧ x ≠ a ∧ x ≠ b ∧ x ≠ c := by
  unfold compl3
  rw [List.mem_filter, List.mem_range'_1]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  omega

/-- The witness check: `l` is an ordering of `[N] \ {a, b, c}` from scratch. -/
def witB3 (N a b c : Nat) (l : List Nat) : Bool :=
  semiB N 0 l && maskL 0 l == maskL 0 (compl3 N a b c)

theorem coReach_of_witB3 {N a b c : Nat} {l : List Nat} (h : witB3 N a b c l = true) :
    CoReach N {a, b, c} := by
  unfold witB3 at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hs, hm⟩ := h
  obtain ⟨hnd, hst⟩ := semiB_sound l 0 [] hs (fun x => by simp) List.nodup_nil
  rw [List.nil_append] at hnd
  have hmem : ∀ x, x ∈ l ↔ x ∈ compl3 N a b c := fun x => by
    have e1 := testBit_maskL l 0 x
    have e2 := testBit_maskL (compl3 N a b c) 0 x
    rw [hm] at e1
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or] at e1 e2
    rw [← e1, e2]
  unfold CoReach g
  rw [Finset.card_pos]
  refine ⟨l, mem_semiOrders.2 ⟨⟨hnd, ?_⟩, fun k hk => by simpa using hst k hk⟩⟩
  ext x
  rw [List.mem_toFinset, hmem, mem_compl3, Finset.mem_sdiff, Finset.mem_Icc]
  simp

/-- Base-64 digits (little-endian), at most `k` of them: a packed witness ordering. -/
def digits64 : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, n => if n = 0 then [] else n % 64 :: digits64 k (n / 64)

/-- A certificate table: entries `(a + 32 b + 1024 c, packed ordering of [N] \ {a, b, c})`. -/
def tblOK (N : Nat) (tbl : List (Nat × Nat)) : Bool :=
  tbl.all fun e => witB3 N (e.1 % 32) (e.1 / 32 % 32) (e.1 / 1024) (digits64 64 e.2)

theorem tblOK_append (N : Nat) (l₁ l₂ : List (Nat × Nat)) :
    tblOK N (l₁ ++ l₂) = (tblOK N l₁ && tblOK N l₂) := by
  unfold tblOK; rw [List.all_append]

/-- Boolean form of `F3`. -/
def f3B (N a b c : Nat) : Bool :=
  !(decide (2 * a + 2 ≤ b) && decide (c + 3 ≤ 2 * b)) &&
  !(decide (b + 2 ≤ c) && decide (N + b + 3 ≤ 2 * c) &&
    (decide (2 * a + 2 ≤ b) || decide (2 * b + 2 ≤ N + a)))

/-- Boolean form of `F3S`. -/
def f3SB (N a b c : Nat) : Bool :=
  if 2 * b ≤ N + 1 then f3B N a b c else f3B N (N + 1 - c) (N + 1 - b) (N + 1 - a)

theorem f3_of_f3B {N a b c : Nat} (h : f3B N a b c = true) : F3 N a b c := by
  unfold f3B at h; unfold F3
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, Bool.or_eq_false_iff,
    decide_eq_false_iff_not] at h
  omega

theorem f3S_of_f3SB {N a b c : Nat} (h : f3SB N a b c = true) : F3S N a b c := by
  unfold f3SB at h; unfold F3S
  split_ifs at h ⊢ <;> exact f3_of_f3B h

/-- A valid step, the placed panels given as a bitmask. -/
def stepB (N M m : Nat) : Bool := cntL M m (reach N m) == cntR M m (reach N m)

theorem stepB_iff {N m : Nat} {S : List Nat} :
    stepB N (maskL 0 S) m = true ↔ SemiStep N S m := by
  have hM : ∀ x, (maskL 0 S).testBit x = true ↔ x ∈ S := fun x => by
    rw [testBit_maskL]; simp
  unfold stepB SemiStep
  rw [beq_iff_eq, cntL_eq hM, cntR_eq hM]

/-- A valid step after the background `{x, y}`, in closed form (`x = y` allowed: then it is
the background `{x}`, counted twice). -/
def step2B (N x y m : Nat) : Bool :=
  let r := reach N m
  ((if m - r ≤ x ∧ x < m then 1 else 0) + (if m - r ≤ y ∧ y < m then 1 else 0) : Nat) ==
    (if m < x ∧ x ≤ m + r then 1 else 0) + (if m < y ∧ y ≤ m + r then 1 else 0)

theorem step2B_iff {N x y m : Nat} (hxy : x ≠ y) :
    step2B N x y m = true ↔ SemiStep N [x, y] m := by
  unfold step2B SemiStep
  rw [beq_iff_eq, leftCount_eq (by simp [hxy]), rightCount_eq (by simp [hxy])]
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split_ifs <;> omega

theorem step1B_iff {N x m : Nat} : step2B N x x m = true ↔ SemiStep N [x] m := by
  unfold step2B SemiStep
  rw [beq_iff_eq, leftCount_eq (by simp), rightCount_eq (by simp)]
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split_ifs <;> omega

/-- What the coverage check accepts for a sorted triple: dead, Theorem G in closed form, or a
table entry for the triple or for its mirror image. -/
def ok3 (N M a b c : Nat) : Bool :=
  dead3B N a b c || f3SB N a b c || M.testBit (a + 32 * b + 1024 * c) ||
    M.testBit ((N + 1 - c) + 32 * (N + 1 - b) + 1024 * (N + 1 - a))

/-- **The coverage check for first step `x`**: every valid 3-prefix `(x, y, z)` has an
accepted sorted set (`M`: the bitmask of the table keys). -/
def coverX (N M x : Nat) : Bool :=
  (List.range' 1 N).all fun y =>
    !(x != y && step2B N x x y) ||
    (List.range' 1 N).all fun z =>
      !(z != x && z != y && step2B N x y z) ||
      ok3 N M (min x (min y z)) (x + y + z - min x (min y z) - max x (max y z))
        (max x (max y z))

/-- A checked certificate for `N`: the witness table is valid and covers every valid
3-prefix. -/
def Cert (N : Nat) (tbl : List (Nat × Nat)) : Prop :=
  tblOK N tbl = true ∧ ∀ x, 1 ≤ x → x ≤ N → coverX N (maskL 0 (tbl.map Prod.fst)) x = true

theorem coReach_of_tbl {N : Nat} {tbl : List (Nat × Nat)} (ht : tblOK N tbl = true)
    {a b c : Nat} (ha : a < 32) (hb : b < 32)
    (hM : (maskL 0 (tbl.map Prod.fst)).testBit (a + 32 * b + 1024 * c) = true) :
    CoReach N {a, b, c} := by
  rw [testBit_maskL, Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_map] at hM
  obtain ⟨e, he, hek⟩ := hM
  unfold tblOK at ht
  rw [List.all_eq_true] at ht
  have := coReach_of_witB3 (ht e he)
  rwa [hek, show (a + 32 * b + 1024 * c) % 32 = a by omega,
    show (a + 32 * b + 1024 * c) / 32 % 32 = b by omega,
    show (a + 32 * b + 1024 * c) / 1024 = c by omega] at this

/-- Soundness of the certificate: every valid 3-prefix has a dead or a co-reachable set. -/
theorem cert_sound {N : Nat} {tbl : List (Nat × Nat)} (hN : N < 32) (hc : Cert N tbl)
    {x y z : Nat} (hx : 1 ≤ x ∧ x ≤ N) (hy : 1 ≤ y ∧ y ≤ N)
    (hz : 1 ≤ z ∧ z ≤ N) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hv : SemiSymmetric N [x, y, z]) : Dead3 N {x, y, z} ∨ CoReach N {x, y, z} := by
  have h1 : SemiStep N [x] y := by simpa using hv 1 (by simp)
  have h2 : SemiStep N [x, y] z := by simpa using hv 2 (by simp)
  have hcx := hc.2 x hx.1 hx.2
  unfold coverX at hcx
  rw [List.all_eq_true] at hcx
  have hcy := hcx y (List.mem_range'_1.2 ⟨hy.1, by omega⟩)
  rw [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, bne_eq_false_iff_eq,
    Bool.eq_false_iff, Ne, step1B_iff] at hcy
  rcases hcy with (h | h) | h
  · exact absurd h hxy
  · exact absurd h1 h
  rw [List.all_eq_true] at h
  have hcz := h z (List.mem_range'_1.2 ⟨hz.1, by omega⟩)
  rw [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, Bool.and_eq_false_iff,
    bne_eq_false_iff_eq, bne_eq_false_iff_eq, Bool.eq_false_iff, Ne, step2B_iff hxy] at hcz
  rcases hcz with ((h | h) | h) | h
  · exact absurd h.symm hxz
  · exact absurd h.symm hyz
  · exact absurd h2 h
  set lo := min x (min y z) with hlo
  set hi := max x (max y z) with hhi
  set mid := x + y + z - lo - hi with hmid
  have hS : ({x, y, z} : Finset Nat) = {lo, mid, hi} := by
    ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hl1 : 1 ≤ lo := by omega
  have hlm : lo < mid := by omega
  have hmh : mid < hi := by omega
  have hhN : hi ≤ N := by omega
  rw [hS]
  unfold ok3 at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · exact Or.inl (dead3_of_dead3B h)
  · exact Or.inr (coReach3_of_F hl1 hlm hmh hhN (f3S_of_f3SB h))
  · exact Or.inr (coReach_of_tbl hc.1 (by omega) (by omega) h)
  · exact Or.inr (coReach3_of_mirror (by omega) (by omega) hhN
      (coReach_of_tbl hc.1 (by omega) (by omega) h))

/-- **The 3-prefix iff from a certificate**: for `N < 32` with a checked certificate, a valid
3-prefix is live iff its set is not dead. -/
theorem extends3_iff_of_cert {N : Nat} {tbl : List (Nat × Nat)} (hN : N < 32)
    (hc : Cert N tbl) {x y z : Nat} (hx : 1 ≤ x ∧ x ≤ N)
    (hy : 1 ≤ y ∧ y ≤ N) (hz : 1 ≤ z ∧ z ≤ N) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hv : SemiSymmetric N [x, y, z]) : Extends N [x, y, z] ↔ ¬ Dead3 N {x, y, z} := by
  have hnd : [x, y, z].Nodup := by simp [hxy, hxz, hyz]
  have hp : ∀ w ∈ [x, y, z], 1 ≤ w ∧ w ≤ N := by
    intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hfs : [x, y, z].toFinset = {x, y, z} := by simp
  constructor
  · intro he hd; rw [← hfs] at hd; exact not_extends_of_dead3 hnd hp hd he
  · intro hd
    rcases cert_sound hN hc hx hy hz hxy hxz hyz hv with h | h
    · exact absurd h hd
    · rw [extends_iff_coReach hnd hp hv, hfs]; exact h

/-- **Theorem G for 3-prefixes, every `N`**: a valid 3-prefix whose sorted set `a < b < c`
satisfies the closed-form criterion `F3S` is live. -/
theorem extends3_of_F {N a b c : Nat} {p : List Nat} (hnd : p.Nodup)
    (hp : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N) (hv : SemiSymmetric N p) (hS : p.toFinset = {a, b, c})
    (h1 : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcN : c ≤ N) (hF : F3S N a b c) :
    Extends N p := by
  rw [extends_iff_coReach hnd hp hv, hS]
  exact coReach3_of_F h1 hab hbc hcN hF

/-- **The dead direction, every `N`**, for 3-prefixes. -/
theorem not_extends3_of_dead {N x y z : Nat} (hx : 1 ≤ x ∧ x ≤ N) (hy : 1 ≤ y ∧ y ≤ N)
    (hz : 1 ≤ z ∧ z ≤ N) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hd : Dead3 N {x, y, z}) : ¬ Extends N [x, y, z] := by
  refine not_extends_of_dead3 (by simp [hxy, hxz, hyz]) ?_ (by simpa using hd)
  intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> assumption

/-! ## Certificates for `N ≤ 30`

Generated by `experiments/live3p/mklean.py` from `experiments/live3p/gen.c`: for each `N`, the
witness orderings of the valid, non-dead 3-sets not covered by `F3S` (one per mirror pair),
checked in chunks, the bitmask of the table keys, and the coverage check `coverX N M x` for
every first step `x`.  Checked sequentially (`Elab.async false`) to keep the memory low. -/

set_option Elab.async false

/-! ### `N = 3`: 0 witness orderings -/

def tbl3_0 : List (Nat × Nat) := [
]

theorem tbl3_0_ok : tblOK 3 tbl3_0 = true := by decide +kernel

def tbl3 : List (Nat × Nat) := tbl3_0

def mask3 : Nat := 0

theorem mask3_eq : maskL 0 (tbl3.map Prod.fst) = mask3 := by decide +kernel

theorem cov3_1 : coverX 3 mask3 1 = true := by decide +kernel
theorem cov3_2 : coverX 3 mask3 2 = true := by decide +kernel
theorem cov3_3 : coverX 3 mask3 3 = true := by decide +kernel

theorem cert3 : Cert 3 tbl3 := by
  refine ⟨by simp only [tbl3, tbl3_0_ok], fun x h1 h2 => ?_⟩
  rw [mask3_eq]
  interval_cases x
  exacts [cov3_1, cov3_2, cov3_3]

/-! ### `N = 4`: 0 witness orderings -/

def tbl4_0 : List (Nat × Nat) := [
]

theorem tbl4_0_ok : tblOK 4 tbl4_0 = true := by decide +kernel

def tbl4 : List (Nat × Nat) := tbl4_0

def mask4 : Nat := 0

theorem mask4_eq : maskL 0 (tbl4.map Prod.fst) = mask4 := by decide +kernel

theorem cov4_1 : coverX 4 mask4 1 = true := by decide +kernel
theorem cov4_2 : coverX 4 mask4 2 = true := by decide +kernel
theorem cov4_3 : coverX 4 mask4 3 = true := by decide +kernel
theorem cov4_4 : coverX 4 mask4 4 = true := by decide +kernel

theorem cert4 : Cert 4 tbl4 := by
  refine ⟨by simp only [tbl4, tbl4_0_ok], fun x h1 h2 => ?_⟩
  rw [mask4_eq]
  interval_cases x
  exacts [cov4_1, cov4_2, cov4_3, cov4_4]

/-! ### `N = 5`: 0 witness orderings -/

def tbl5_0 : List (Nat × Nat) := [
]

theorem tbl5_0_ok : tblOK 5 tbl5_0 = true := by decide +kernel

def tbl5 : List (Nat × Nat) := tbl5_0

def mask5 : Nat := 0

theorem mask5_eq : maskL 0 (tbl5.map Prod.fst) = mask5 := by decide +kernel

theorem cov5_1 : coverX 5 mask5 1 = true := by decide +kernel
theorem cov5_2 : coverX 5 mask5 2 = true := by decide +kernel
theorem cov5_3 : coverX 5 mask5 3 = true := by decide +kernel
theorem cov5_4 : coverX 5 mask5 4 = true := by decide +kernel
theorem cov5_5 : coverX 5 mask5 5 = true := by decide +kernel

theorem cert5 : Cert 5 tbl5 := by
  refine ⟨by simp only [tbl5, tbl5_0_ok], fun x h1 h2 => ?_⟩
  rw [mask5_eq]
  interval_cases x
  exacts [cov5_1, cov5_2, cov5_3, cov5_4, cov5_5]

/-! ### `N = 6`: 2 witness orderings -/

def tbl6_0 : List (Nat × Nat) := [
  (6305, 12420),
  (6209, 16707)]

theorem tbl6_0_ok : tblOK 6 tbl6_0 = true := by decide +kernel

def tbl6 : List (Nat × Nat) := tbl6_0

def mask6 : Nat := 98655808808884311862403418290706514454174153845226856802499040698436783554291290905710407581999439323937848222524826700337343913346483527158843164322518271068327931903446816277585316947971824491690574525605201279715153063472376168110976418289708066008357804771393445937490069295873420179945853467241948010023552543949029454433118404566210599622591673665958173579806111560844292669011418595278933282356416929816292901587704105036424578319501292167627995072023184118902689371576644478050810205832537085110629002511591419963969581267029797013414460681577285739626349889761824852774298978553000783136069683316471699514712589350866354424578728207123591800430950788580540177372324481791301528084431785508855788745713348023628788049697845151591609031011267835236384013592283097406500535849646301162480084018039638479364857239118599229191456852170891668494801674991932754742929045862161242496741709064953221672751272683693829845901636318801320558013628415212958417325275213348037252313870462199382486613960599692732869317183071497126466314630046545964489753724176684996191171945531339902997877544545397625055693284067172403362522242742836585492371068447919147386963045480904245827369990889270920153337553183661919273872490517717108247690046695242684297759341444719535548952634111077918791675652138474961548652333896583433554438695512213012651858442113426625109083262394710468371897900482137202719403526675949671625178155243853021488786613203458219615776205073556041252618361685153850409040174994667420981232749251387927030756585144071252803595714675078784162494526556602304008374578748647004388978534154649367216045608272968772958450834382115680959169141457423528254892663992063238542776509664567749228719252298876191452496860770319337216772172932661571936505241771456082741498390404327984309032703348266840957844283754152507962407928844400937384882696768687182026862022804620991102932684179066528196460544

theorem mask6_eq : maskL 0 (tbl6.map Prod.fst) = mask6 := by decide +kernel

theorem cov6_1 : coverX 6 mask6 1 = true := by decide +kernel
theorem cov6_2 : coverX 6 mask6 2 = true := by decide +kernel
theorem cov6_3 : coverX 6 mask6 3 = true := by decide +kernel
theorem cov6_4 : coverX 6 mask6 4 = true := by decide +kernel
theorem cov6_5 : coverX 6 mask6 5 = true := by decide +kernel
theorem cov6_6 : coverX 6 mask6 6 = true := by decide +kernel

theorem cert6 : Cert 6 tbl6 := by
  refine ⟨by simp only [tbl6, tbl6_0_ok], fun x h1 h2 => ?_⟩
  rw [mask6_eq]
  interval_cases x
  exacts [cov6_1, cov6_2, cov6_3, cov6_4, cov6_5, cov6_6]

/-! ### `N = 8`: 9 witness orderings -/

def tbl8_0 : List (Nat × Nat) := [
  (7329, 51388934),
  (8353, 51921031),
  (8385, 67915911),
  (8417, 67916162),
  (7233, 84947462),
  (8257, 85475527),
  (7265, 84943366),
  (8289, 85475463),
  (8321, 51925127)]

theorem tbl8_0_ok : tblOK 8 tbl8_0 = true := by decide +kernel

def tbl8 : List (Nat × Nat) := tbl8_0

def mask8 : Nat := 58813023140880367119511960137084904382802092623956118013480441365622698445066663485697537401267230324128357251911468074123521063029058855563614208200004747946494486396134369725139184004675249497747467050608387174127792232316561773351774174937567096605606733511816824599031852987230092940791046270585900500183908526128548901831012926103146741500688127174349350226126558757018033261455557302273637512265972607849725097479850066902439582173799593076607686420885467006505395067486967239508521386675060419987291509107333196160465782427726205811628516616300207258861379684761289057936230116142508458912876311996870856851421864630888614911662531887223899956021367124979060586601555384653285151582418271598251587197533833924402872520856593262704226021405170880914901821492047290033565698139389405880141720422314001433873569006770960856790237003750027967138062550715142492621891539171932162146727536620376089132701785145543823290594230710471988364020076436525019421352140453618637214020763634006474213460131983992923017507176695534670425377293462576870844497789452448977758078775468095836058411816160084788913698596844407376165035844769019518577990954341586546150530747945800162062230815148016950454062848434113436802063386913732585918388719499141705342595534896451207446258114499998561566024754797841546674038451010019331953488632803771408232309044488026900274041786767662826189161513702907544642410995137296705166622275413910281409317251583416065927044624666132577451698688126456301617814885362311122981987123968195343465793388650882740265002561119308028183026433427337300732792838769698092623669644088227819044047555328761880890411126101488757332992127756177134916175333311760459628256314759812926265226621903157381818199265833474615541536074449184641418136669193942897085961189914991729145231340602082357888633967095636282959727998571110182806367030140610839868386830664274697003173825139977074285925611325397943821753087295904704521835010904041092981657432631448619284902223729605963905045438812861394855997907335341230256876392251049961781291577031513954397521462951987904796674311126314049827905539536459296705723608342865327892926057599215245737887977474842646927980306220441076828552074392785652727724578277952522979545604563488118651572508544843072305639543041694779961096324145501084473898245891890425905963122941772654587772128035569196064482126061378682731935661936149060851330274691413770336224030465041118564095435168648986258350231976243465924870725504186798655820163856450785281233886263886430655936721865068391684223499501568

theorem mask8_eq : maskL 0 (tbl8.map Prod.fst) = mask8 := by decide +kernel

theorem cov8_1 : coverX 8 mask8 1 = true := by decide +kernel
theorem cov8_2 : coverX 8 mask8 2 = true := by decide +kernel
theorem cov8_3 : coverX 8 mask8 3 = true := by decide +kernel
theorem cov8_4 : coverX 8 mask8 4 = true := by decide +kernel
theorem cov8_5 : coverX 8 mask8 5 = true := by decide +kernel
theorem cov8_6 : coverX 8 mask8 6 = true := by decide +kernel
theorem cov8_7 : coverX 8 mask8 7 = true := by decide +kernel
theorem cov8_8 : coverX 8 mask8 8 = true := by decide +kernel

theorem cert8 : Cert 8 tbl8 := by
  refine ⟨by simp only [tbl8, tbl8_0_ok], fun x h1 h2 => ?_⟩
  rw [mask8_eq]
  interval_cases x
  exacts [cov8_1, cov8_2, cov8_3, cov8_4, cov8_5, cov8_6, cov8_7, cov8_8]

/-! ### `N = 9`: 13 witness orderings -/

def tbl9_0 : List (Nat × Nat) := [
  (6305, 3288891975),
  (8385, 4347154569),
  (9409, 4347154568),
  (7329, 6493323848),
  (9441, 4346892424),
  (9377, 3339723270),
  (7233, 9748635848),
  (8386, 4379128391),
  (8321, 6494638217),
  (8289, 6527394375),
  (9313, 6560960648),
  (9345, 6494638216),
  (8322, 6526612039)]

theorem tbl9_0_ok : tblOK 9 tbl9_0 = true := by decide +kernel

def tbl9 : List (Nat × Nat) := tbl9_0

def mask9 : Nat := 10572776794085915612217889378311324751333451345923912857280366227144256880317774197654206675316149237625362672413131061511222863066049682291931984308149374111213631196649893783031657513958836901025361323306175167162133908421330397616067358066842966093614028955134019920435421338434811261698598577757646980712136392341061344911935913216459173329367869177303795581914629030218034023518762925887825347444112700653931883156336552225688722352432974048448144770435426752821799952211476353536214161894181962655250575502033272150380253672611585443825718209646259807847853723197557685346973840017771350762317629082744969100042038038553898304431299420005860750578042243480933063439406886091783915821900993798680472900637833998530643566385806622658564426285219603050584692270425832711228600953667103705912828073224554839982240958263606422573768717823944783834606400910624879176150185990028841665621128295998449832832495001122360657607591932238123492115704372010235140206816774949511541768671834216651980135287600770182555504575880401596522075407004193801648656538271351419993607390402570639437557129478073921255691029823967774591729097530188541711007637747141490496554429122778743451057595595501484014506291509074629358034488203785402684048622128249803303049012609544989140188297540962230053676740462493687144637241566509380551900428274545840614262183698505473281064302222203538954798665518705617434658617975795656491536017769199538263451467795949680302202730874320754934122297840562073033486488391512973747723732795026594855830107861277305037009432904658556621301178345283456032508886954240313598246610521527095708543698907030733857713257413075217343608924066062614477004021520783813378057168293671949517499809193987399659685894278699981677882810682950272698826957690192429189425166749681072184492648611075504450280821163057031839559657625963763576497094338117864433005163181229386221667631339416718064445590762977254435520232922761751147384968845518675758974182693824539686506203339314997107967539783120705009074487793087328836200514060040732328765207183674804293358514763923108088907704614638594108943950886860562850680732203747032963223316038450216776494535039781485222384258141867693626352797437072791195217668221314683727889566466174701805197320482797604502818128638418001278408180295889065922017772248315376802557082236271107003410809862070543261892550507710101806480930426577205313112605361557346016997310510814723050415162438836416619042800869988954027958410454627952394235503287282921585310494433339940179976557101443785397779258441081695256499272544218502953491334392007176704057843589420185751803888031230856588038837296280072556431507375904084463792206311650602071807341353829119322226804772245729119689742252686397612694703342124442587822479456688510113011275925168626117768990273968956580217497560032365893227909217473700940348592079503360

theorem mask9_eq : maskL 0 (tbl9.map Prod.fst) = mask9 := by decide +kernel

theorem cov9_1 : coverX 9 mask9 1 = true := by decide +kernel
theorem cov9_2 : coverX 9 mask9 2 = true := by decide +kernel
theorem cov9_3 : coverX 9 mask9 3 = true := by decide +kernel
theorem cov9_4 : coverX 9 mask9 4 = true := by decide +kernel
theorem cov9_5 : coverX 9 mask9 5 = true := by decide +kernel
theorem cov9_6 : coverX 9 mask9 6 = true := by decide +kernel
theorem cov9_7 : coverX 9 mask9 7 = true := by decide +kernel
theorem cov9_8 : coverX 9 mask9 8 = true := by decide +kernel
theorem cov9_9 : coverX 9 mask9 9 = true := by decide +kernel

theorem cert9 : Cert 9 tbl9 := by
  refine ⟨by simp only [tbl9, tbl9_0_ok], fun x h1 h2 => ?_⟩
  rw [mask9_eq]
  interval_cases x
  exacts [cov9_1, cov9_2, cov9_3, cov9_4, cov9_5, cov9_6, cov9_7, cov9_8, cov9_9]

/-! ### `N = 10`: 24 witness orderings -/

def tbl10_0 : List (Nat × Nat) := [
  (6305, 210489344647),
  (9409, 278234669703),
  (10433, 346887823943),
  (7329, 415572726408),
  (9441, 278201115272),
  (10465, 346887839881),
  (10497, 346920329799),
  (9377, 415607300743),
  (10529, 346921140356),
  (8257, 417753506375),
  (9281, 417753498247),
  (10305, 420991742535),
  (7362, 619617464968),
  (9442, 280382410954),
  (9345, 415673623175),
  (8386, 280264221255),
  (9313, 417754784391),
  (9378, 276121280712),
  (9410, 280381108871),
  (8289, 417753244231),
  (10337, 420991738439),
  (10369, 415674159241),
  (9346, 486540841162),
  (10401, 415607300679)]

theorem tbl10_0_ok : tblOK 10 tbl10_0 = true := by decide +kernel

def tbl10 : List (Nat × Nat) := tbl10_0

def mask10 : Nat := 35061003826597608976781004485010181306529913755972526032854347605519971321502238877316213933703133837230794702845751949734246498575852233074531394205903510700769758031226471775234543674028478937982490581640202651133171992304235001843408068553123462346581517712500579939943214212663696526942073712350149378074086360143891609165742896969265530027403725343295752184779587758859889841889560474316133606697610954504699755959884796835471289320480910041651450269296237441995887964266280262288422089413598709592174973214395192587384225142834896824923853708993157548646701212399365922855492020243832211782939126593300790985974759680261124254316405118393574731407454108432739161548985306886232517821705134135516728039855688638793502568557781134871097976415734571948836688859024965364088263929839535388303528648185855222793409736269554757001481472040569876977173587102330089046421988985236754640845090564582360868211848721319701694428921523002851038743257004283866858176019423033490273704093604935011878179015897602586025144066107939201693200812828274302413669956362101886141463244063590666881334553328477588834944677786118376721855104006509256167595781942108709087941952527740924074218083199386804005659932288091628667300502757780173894308477315613360007453324547964460412437021066114662050034693001479254934480245255711870071052485946529690439867921809150077659827463100372531288680862630975355398401972291289340314986041033109514195475719032545091578425907867361584509495367758469576408094293021659981799528712611792696989748505818677913213267340330860175861039176933566336617103066491927951116650774642310839506234532696378400592413865295806139721644728511141626680516193377659459561164917807662462194727504779422622719966979188288115039705221317553733916709652274313925254232576559554293855634440859949534927347343483786586606895296788267605942699609786824942179885142207552073141318961515701646365478091922934626524820853013949686391271797150999849564241132277613259077432739537101733532265458817470382012328494136256022102082380349986349089353307096510298326218469530537632509629785717890250857623136573330948253237023132549274750715298769631983067982413540204676696136610364938076036096477365829549531535193771814681667468565211086118444537184732171424130207401576515187448379288141939084084024264541397012346099410674589526648363101747619228586593310336957434280196364981924541140128360668331185559250045409634085029446435814148550625314840654007312575747855217537962254692973347818603896600961170993309331130745645660840448097611472136606746432976838567769730713504127317024637516552704878396125706952379183357900386685819620971846734142956600871293401928819688574005767040338108277421159724860842425763304683844125824296170886935081918779259489600869856662414785958934096793991986550406472836538533508782285136855753833659412673494564343921476285480119052158782029101227724602786165596738658973981695495897590087462786636982718272954114524190750210729203017569992602836266944092970759745518734444887385790695421341728070046395159176092919286891417721946382871306294913791780362838067734624378530823125682560857345369932425997550763711857385121062665613535576262726123520

theorem mask10_eq : maskL 0 (tbl10.map Prod.fst) = mask10 := by decide +kernel

theorem cov10_1 : coverX 10 mask10 1 = true := by decide +kernel
theorem cov10_2 : coverX 10 mask10 2 = true := by decide +kernel
theorem cov10_3 : coverX 10 mask10 3 = true := by decide +kernel
theorem cov10_4 : coverX 10 mask10 4 = true := by decide +kernel
theorem cov10_5 : coverX 10 mask10 5 = true := by decide +kernel
theorem cov10_6 : coverX 10 mask10 6 = true := by decide +kernel
theorem cov10_7 : coverX 10 mask10 7 = true := by decide +kernel
theorem cov10_8 : coverX 10 mask10 8 = true := by decide +kernel
theorem cov10_9 : coverX 10 mask10 9 = true := by decide +kernel
theorem cov10_10 : coverX 10 mask10 10 = true := by decide +kernel

theorem cert10 : Cert 10 tbl10 := by
  refine ⟨by simp only [tbl10, tbl10_0_ok], fun x h1 h2 => ?_⟩
  rw [mask10_eq]
  interval_cases x
  exacts [cov10_1, cov10_2, cov10_3, cov10_4, cov10_5, cov10_6, cov10_7, cov10_8, cov10_9, cov10_10]

/-! ### `N = 11`: 30 witness orderings -/

def tbl11_0 : List (Nat × Nat) := [
  (7329, 13471335088838),
  (10465, 22405922177736),
  (11489, 22405922177672),
  (8385, 17800662118731),
  (10497, 22410116481737),
  (11521, 22405840118407),
  (9409, 18149508928202),
  (11553, 22410116481672),
  (10433, 22198725144841),
  (11457, 18145315398279),
  (8257, 44398218613447),
  (9281, 48796266426570),
  (7362, 44600082576072),
  (10466, 22405921915592),
  (10401, 31202015199944),
  (8386, 31474662519497),
  (10498, 22410116219593),
  (10369, 31202015978184),
  (9410, 30859424739976),
  (10337, 31204162683592),
  (10434, 22197651403017),
  (9313, 31203021861512),
  (11361, 31204162683528),
  (9346, 31201947857544),
  (9345, 31201948119688),
  (11393, 31202015978120),
  (10370, 31204162417352),
  (11425, 31202015199880),
  (10402, 31202014937800),
  (6305, 13478717588103)]

theorem tbl11_0_ok : tblOK 11 tbl11_0 = true := by decide +kernel

def tbl11 : List (Nat × Nat) := tbl11_0

def mask11 : Nat := 6302892588045590957900913717818175815072362373141842760792414858808603410678689716502271065221222254080117749630700656794476355645430350680686972353446627279917599954353826241277103166122417349310493876380108098177222307845065190367198524169999317844179238105878601167421747799836461612477502975348664193129371457152666825704009195655362867617837108492082485266128509662376884269521507934058568123809777101524490702951854086958418467003231962869417866084038585350955133987464156532754868517294058127213804633473094706950374900208023231009773191894847248173110239659137221681483100798865380361844997761618975239353102413655689274388163134250107755205673957138384591750079875430339674557918868682107693521039454031822595609819733042331339835802694379637285841470566837877057649392782661671746618802023474805038599039474404035590668029537166636039324498988606242792445617294323435074628986181507132880335321815204807374654018117489763224932974369045147189874859047806852646421277443350896730655260345260768570617292522266854485201399293750958710457183561310135698331920606821733359024690125396381255699936527130236370787938292752834938081275043580891032263147817532970209824014066102248688139341822246130019508845684045062613950278097659531101938617524738122004647781953544484566722360827747574598917683753891804812026021201390217613618829179518566895031209842953121302809307246661513236765369778145670766059703047684941690750285765416753416895942312671033346829735585687324890827188800496943284141346384839792510650018710645492809262721568419069672096805328671537690120843193113509773170892727820641960174464975809700455713854905405940786447795196799279182975233303702580605096913688846007549677856353564640220828692831762469416723562492287288588778383355422724198193624118923855552355521255366501300029593464993820235462920195134160869132569052443332969684772495771054905238193045926304853183084750223423658095471692895582018182325364917095034879995853977565084898405327084716377742401182255565109319731528397540207943915871721505609224616915074346570287540987948936631325006503777797306921991005108017429903452688425690177191848085206806302952777409866587566205767721031324642867614976218908530437642853500937588555785965178214184775248534143982070914194302033899773270194489567453831414806870735617259157875459006296601959735361304914679355600039517394828617424129125872282288098941503421111218025547408658363654337111416646481158385064977579008962485554174117029854731817229673653641324561275861939771832334452535073075498999081726604720000018645763195628181069416453861920162561328581139357043118132117920984107302433874891091993964253917436037344751870706141703938116165995334132944056464052469376969249811800927746852187866333923178461458282377623489989670128297433863060294209562232212776255952564193760488423144508189032128636556307493417995482448459282164591214891895010552363618483465163444009467574262832243643614192496126227335550208395775608429374401043720608368574023498967594859688541011459715213973268684203412064090428079759739056686779092163232291898426866834582927679217614055990373985567056497266930767941792302180033282493583484179705657125586891529979574436324097852259197628344454764515183422119522277744703489262804925188386258887603468936955603557985128805557556899627983348388354611869744626922504994686589372334754965093184659890068472817169956946903084931063800288107313904383468461241674569517217101339910280331766315027186000608205055672186042318848

theorem mask11_eq : maskL 0 (tbl11.map Prod.fst) = mask11 := by decide +kernel

theorem cov11_1 : coverX 11 mask11 1 = true := by decide +kernel
theorem cov11_2 : coverX 11 mask11 2 = true := by decide +kernel
theorem cov11_3 : coverX 11 mask11 3 = true := by decide +kernel
theorem cov11_4 : coverX 11 mask11 4 = true := by decide +kernel
theorem cov11_5 : coverX 11 mask11 5 = true := by decide +kernel
theorem cov11_6 : coverX 11 mask11 6 = true := by decide +kernel
theorem cov11_7 : coverX 11 mask11 7 = true := by decide +kernel
theorem cov11_8 : coverX 11 mask11 8 = true := by decide +kernel
theorem cov11_9 : coverX 11 mask11 9 = true := by decide +kernel
theorem cov11_10 : coverX 11 mask11 10 = true := by decide +kernel
theorem cov11_11 : coverX 11 mask11 11 = true := by decide +kernel

theorem cert11 : Cert 11 tbl11 := by
  refine ⟨by simp only [tbl11, tbl11_0_ok], fun x h1 h2 => ?_⟩
  rw [mask11_eq]
  interval_cases x
  exacts [cov11_1, cov11_2, cov11_3, cov11_4, cov11_5, cov11_6, cov11_7, cov11_8, cov11_9, cov11_10, cov11_11]

/-! ### `N = 12`: 43 witness orderings -/

def tbl12_0 : List (Nat × Nat) := [
  (7329, 862714011353798),
  (10465, 1433971538825928),
  (11489, 1433971672252682),
  (12513, 1447373010116875),
  (8385, 1139243466649932),
  (11521, 1434247588496137),
  (12545, 1706926390387401),
  (9409, 2269876292203274),
  (11553, 1434247590060300),
  (12577, 1706926390387400),
  (12609, 1711330927845643),
  (11457, 1447441729593612),
  (12641, 1711330927878276),
  (9281, 1996993415914248),
  (10305, 1997001031168712),
  (11329, 2005857154404748),
  (12353, 2005925905605321),
  (8386, 1148656943894732),
  (8418, 1152499900224265),
  (11522, 1433973786153735),
  (11425, 1996921625673994),
  (9410, 2269603711730311),
  (9442, 2269604785443594),
  (11554, 1434320485237514),
  (11393, 1996921625674058),
  (10466, 1433970465084104),
  (11361, 1997059064627466),
  (11458, 1447514624770826),
  (11490, 1433970598510858),
  (9313, 1996993399137032)]

theorem tbl12_0_ok : tblOK 12 tbl12_0 = true := by decide +kernel

def tbl12_1 : List (Nat × Nat) := [
  (10337, 1997058931200712),
  (12385, 2005925907407561),
  (10402, 2278398566109895),
  (10401, 1996921492247240),
  (10370, 2278532817392327),
  (10369, 1996921625674059),
  (12417, 2010322880176840),
  (11394, 2278542580388044),
  (12449, 2010322963538187),
  (11426, 2278398716285703),
  (6305, 862714011353799),
  (12481, 1447441729593611),
  (7362, 2819435728745160)]

theorem tbl12_1_ok : tblOK 12 tbl12_1 = true := by decide +kernel

def tbl12 : List (Nat × Nat) := tbl12_0 ++ tbl12_1

def mask12 : Nat := 20901390945064948453166667609669163765075797992436518288518283801291101855989342787433595807991149226198954992777253031543644376601677321575037972199960614985238032817170918852181181086492321248005957849334133738599716301785819058706012174203004960550164077687751086622660168330120855064650769379712967370466234829100985036464442175468134086520616417129442062718828729268230868260077663963211872376526548394950524643761080020131525400138351051002739453623036757111437244095865675742793306986744631286889221623049956543076157808216036911813227340108144368678779033116075701584902772603898671210737166218826918298510229490480379091123613357670642279902986007288888827138213212567657066105643091415723322277233422759883945256876219009965553523733442113714155716583128886386454651317694056127628428600853731369872792850376514280187679251422318328857002849481107017031383487206490504198009627807756999758483534335382361716886020524068121813151166188135567307788996701012136392089266002724270943450491275063052531847730428707515795822532906693101572321118415404787799925546522334211414118905726852978585294589615703968696813216829707243734852178374077142776151371337721813253769543489495012052460130167812406264801517803368308937156339069908262754187994130836965761422540830272743442748612801820495648663608893376688820376960625441410601492532497710065772597213343111500112153417076896919250889981458206671743392314602793372075555684024136993504852799896674661341262072470322695995647497282923339346706151013952786742577662805464372819722344450699427794157228750398531837141754749963008350642506160557323339868781567724215068250202697329686258902142647185090614523660763692937989241168260049266905907123080511807181337877781604611057172722017021539710728132399833984656813535993420249331878044125586163051785533095193626611068934778844631175528415435605747252845865790786118012486530152973881796999164632464413442413029394339274026944908060618371787653726398999101334003057161122519592359395977116034266515589610805072676099693023140428811276027445655531715238138483027643272295196205619388478057387014146427059277789796984758706913228490052220734043402150488537544489330409313532574806082658353416607228529720683020410828379414137124976805991783037275009384939549959179112173139085013573186635728650770661137092416708372434150417221269454135167782765905637361873409702303337250907950848505451133281654550800119612040962856387718233254676953440643626110329202755274041458922761746570455020913256012228115727377614937769766653318496034869955947852863208823886195885919389773322085852312050156660266499084308178649235270968784518419789244504332655501103396382871988598106508388552913859692894848403897191143995563516546962221445235226626999748121915825445646066331626700237445641744477689358813807068237484394930746512765960938831310952042100732080957230997057106828712266368077534040104074608174980837678872504587982894427043443366182050812356812605409360125235012627893829488743246760428234113399728805968592661359256927248589310101276963917325570018552218706265368960634250253591857188969987709061901715493789784427418664459801698577046261946253382808105552029577535633394177005673068622305308111744740407928551029509470766916504379465786732755627400531532318550958293809265521348437843533105065008155303699753787369988918446786263684556957666924000466186799942856738958086304907957060930128770686671286143927798605925322549866921476598273911269951347102305062927897677321757067230405001524642260097322938978862053680136227402527384272205681814863901704199315593259823622677023557206872074409269282305452296692063257279567162123554355346906622829477613297964487928800633339827062180346022804157968208148208545515404258708220495293974843061646099361192580255144608210690166920314305159829238973574814813917282304

theorem mask12_eq : maskL 0 (tbl12.map Prod.fst) = mask12 := by decide +kernel

theorem cov12_1 : coverX 12 mask12 1 = true := by decide +kernel
theorem cov12_2 : coverX 12 mask12 2 = true := by decide +kernel
theorem cov12_3 : coverX 12 mask12 3 = true := by decide +kernel
theorem cov12_4 : coverX 12 mask12 4 = true := by decide +kernel
theorem cov12_5 : coverX 12 mask12 5 = true := by decide +kernel
theorem cov12_6 : coverX 12 mask12 6 = true := by decide +kernel
theorem cov12_7 : coverX 12 mask12 7 = true := by decide +kernel
theorem cov12_8 : coverX 12 mask12 8 = true := by decide +kernel
theorem cov12_9 : coverX 12 mask12 9 = true := by decide +kernel
theorem cov12_10 : coverX 12 mask12 10 = true := by decide +kernel
theorem cov12_11 : coverX 12 mask12 11 = true := by decide +kernel
theorem cov12_12 : coverX 12 mask12 12 = true := by decide +kernel

theorem cert12 : Cert 12 tbl12 := by
  refine ⟨by simp only [tbl12, tblOK_append, tbl12_0_ok, tbl12_1_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask12_eq]
  interval_cases x
  exacts [cov12_1, cov12_2, cov12_3, cov12_4, cov12_5, cov12_6, cov12_7, cov12_8, cov12_9, cov12_10, cov12_11, cov12_12]

/-! ### `N = 13`: 58 witness orderings -/

def tbl13_0 : List (Nat × Nat) := [
  (8385, 72951094456111948),
  (8417, 73759993483272969),
  (11521, 92055926058820361),
  (12545, 109256755773186889),
  (13569, 109256755773186825),
  (9409, 145254628071351111),
  (9441, 145254696673653578),
  (12577, 109247959778480970),
  (13601, 109247959778480906),
  (10465, 145254699844547401),
  (12609, 109529434755187529),
  (13633, 109529434755187465),
  (11457, 145285552789836553),
  (11489, 145254699844805385),
  (13665, 109529442137162505),
  (12513, 145267684788441419),
  (13537, 92913348716273932),
  (9281, 218169775529698120),
  (10305, 218170049365324617),
  (11329, 236184447876608777),
  (8386, 73514035755389703),
  (8418, 73759993466495753),
  (11522, 92055924985078537),
  (12546, 109234980319933257),
  (12481, 145285552792150857),
  (9410, 145254638791716941),
  (9442, 145254707508826954),
  (12578, 110105782742450381),
  (12449, 146098984298517190),
  (10466, 145263503601840969)]

theorem tbl13_0_ok : tblOK 13 tbl13_0 = true := by decide +kernel

def tbl13_1 : List (Nat × Nat) := [
  (12610, 110092657322373961),
  (12417, 146112109718573387),
  (11458, 146090191259738889),
  (11490, 145263491659637513),
  (12385, 146112178438050123),
  (12514, 110937082252505929),
  (10337, 146107917680030537),
  (11361, 146107917680288521),
  (13409, 146675336661717770),
  (9475, 219313061446054157),
  (11426, 146099120513524489),
  (11425, 146099121587266313),
  (10499, 92095859538272653),
  (11394, 146107916589769481),
  (11393, 146099124774937353),
  (11459, 90371962930492034),
  (11523, 92047129965798153),
  (10369, 146099124774679369),
  (13441, 146675335587975946),
  (10370, 146107928531972937),
  (12418, 146112108644831563),
  (13473, 146956810564682505),
  (12450, 146098983224775366),
  (6305, 181006152689287879),
  (13505, 145285552792150793),
  (12482, 145263777338897225),
  (7329, 55218170906596104),
  (7362, 201008390842667785)]

theorem tbl13_1_ok : tblOK 13 tbl13_1 = true := by decide +kernel

def tbl13 : List (Nat × Nat) := tbl13_0 ++ tbl13_1

def mask13 : Nat := 3757428701101663092392040002980969593064972763816551168541771761634810436633849171218303094342637839176625212165134527778573238805364982212633976525949909794561234506276214258003626871256036345149770553187230698058125239757669985627808393533356541813055224722803204059802032831483595564107176583143843147525203642968319182395580231157422228704077476291510751573425812947399056295577588642670196406202775451308051120410275007908717782740783652478851049978770826863230298512774929677694974072733755581652281278968838892581628378135922437875173933511469168081749166901814145082260290366282648280256121723948643106942603817145197478369555008031471612127175299428709496976903642397988604083890376262725462361646925866606972242234084381902769441983738613703529345841978199721136185162629489935304081389329760703715568652749143408155028844966122160594729151038908393144712418012539694987476448159104571623960409807266034640060874016285799400230390038102548215422812083853553867176334018413134072530511390258452719347876128626112049600999522247910292702124283188609704392531749995868550496575947707421117119814398262329680083567695306184488701048137739660056452967256327179905640840695090243119636884334120226116495321890848980767083943851112087825996931406887536774886676317200320529205970017021827877264334214988810331408743959399557184088436294744933848595127509135734477431806714462886571454725838261231651167872740121758517897142803945561043549590527665989562180294723873384428683410043029044142455636690958593611326508679403174136195463186565841003595659187998699989794155756012806867412908087179239892220666949477676454283813497559889592864922523828006267628650616957338333122280904477676007550337427049194420022285259689733706898155167081628077676966018973269051337035598182760951930754123169691663988539410248977447615857422289516272679928265942086745853529027021584914239743679661615955143808336978748314756184372357074885022220309526723085721752644455601522835610323671146698055561627022557275147915189904512932846394957385095446251139035732861375736309085042592032827465806910536954673731027721517657912389684398016369368287149282138354547527899263378926321306709048119868204388599597222185191954267220481276495905112496482318816870309857636221383417343304477500602823375762828839145068328786596776076318742635565225988239539348753433859374254821451148783520510416189819364944036037458668246598956534791766903821433210143757993589614858152545379321614039778931316992810545916349228953719220219470597644036262323522759751368842359598835858495936729802351988938909931052476839140329113194021462956316087177869052014071516531328622489711326383950135846949921472239982034361471865770306064210053375823429896022286721546021115239516996813870175240246195079103212971892347723215734678270894409973641638697448280000295268264022815439352450787191175884307015392377265993981999731206526651156756277716282465938856198938922903067426962407675238716064627727894929800400167182020411055291072445323789153425578650417774827694101160969213460430498640401695552219364907489453381366560905264315911522575020251356949293745720073440298320757133144679495484331268734431146762723654847746254188088171864482675705827324394045987674357528832062357714014082912286604945982329293653541630850107195620847906069845088825930572993710336672932748199510102010738248822387409968269223824436750247952676694616231944137545882784863739476249246908623622429109072809586681950128644086654142325657425283070362277029652322829916425544783150401805374101425670481426613029658123023474537227342243193211367800842896051420144505957718962628657931686179218257106301788872895372737519809377023034500725530962221754864644220157964429247527234817502448364442425147535082954731121616413421264859336900095084288195713587903342971052121376293307958200957110330285799016957508573430693598237688923001826037006705169092388472673954910220159353815138571746107593167832560271524290146044440530704734299840632476698813476016190637714268845761172156801526893488100263756215523679601146747549732894378385735804455382489087763818415357681689674595994629664982171648

theorem mask13_eq : maskL 0 (tbl13.map Prod.fst) = mask13 := by decide +kernel

theorem cov13_1 : coverX 13 mask13 1 = true := by decide +kernel
theorem cov13_2 : coverX 13 mask13 2 = true := by decide +kernel
theorem cov13_3 : coverX 13 mask13 3 = true := by decide +kernel
theorem cov13_4 : coverX 13 mask13 4 = true := by decide +kernel
theorem cov13_5 : coverX 13 mask13 5 = true := by decide +kernel
theorem cov13_6 : coverX 13 mask13 6 = true := by decide +kernel
theorem cov13_7 : coverX 13 mask13 7 = true := by decide +kernel
theorem cov13_8 : coverX 13 mask13 8 = true := by decide +kernel
theorem cov13_9 : coverX 13 mask13 9 = true := by decide +kernel
theorem cov13_10 : coverX 13 mask13 10 = true := by decide +kernel
theorem cov13_11 : coverX 13 mask13 11 = true := by decide +kernel
theorem cov13_12 : coverX 13 mask13 12 = true := by decide +kernel
theorem cov13_13 : coverX 13 mask13 13 = true := by decide +kernel

theorem cert13 : Cert 13 tbl13 := by
  refine ⟨by simp only [tbl13, tblOK_append, tbl13_0_ok, tbl13_1_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask13_eq]
  interval_cases x
  exacts [cov13_1, cov13_2, cov13_3, cov13_4, cov13_5, cov13_6, cov13_7, cov13_8, cov13_9, cov13_10, cov13_11, cov13_12, cov13_13]

/-! ### `N = 14`: 77 witness orderings -/

def tbl14_0 : List (Nat × Nat) := [
  (8385, 4669155986983412553),
  (8417, 4720639661129114441),
  (12545, 6992713844312810313),
  (13569, 6992713844479501193),
  (14593, 8144245566388839241),
  (9409, 9296296873074402119),
  (9441, 9296301270970708810),
  (12577, 6991869416211788618),
  (13601, 6991851961614902023),
  (14625, 8144245907836654410),
  (10465, 9296300790068065161),
  (13633, 7009883825558003982),
  (14657, 8162787944137236749),
  (11489, 9296300790068061065),
  (13665, 7009883825541226766),
  (14689, 8162787944120459533),
  (12513, 9297167070828995401),
  (14721, 8162800921414766859),
  (13537, 9297167070995686281),
  (14753, 8162819064278336066),
  (10305, 9350898013812068750),
  (11329, 9350898013779300748),
  (12353, 9351179623930045257),
  (13377, 9351179623929521033),
  (14401, 9405508615322505613),
  (9410, 4705184783935529800),
  (9442, 4720639661112337224),
  (9474, 13854510893337715085),
  (12578, 7046730720298443592),
  (13602, 7046779506846367950)]

theorem tbl14_0_ok : tblOK 14 tbl14_0 = true := by decide +kernel

def tbl14_1 : List (Nat × Nat) := [
  (13505, 9298556853693195145),
  (10466, 10521548173844943755),
  (10498, 10613863169960719243),
  (13634, 7046216625612423374),
  (13473, 9351210274006507790),
  (11490, 10521548173844943754),
  (11522, 10613863170060595662),
  (13666, 7046216556892946638),
  (13441, 9351210266524132233),
  (12514, 6936731595653808333),
  (12546, 7046730720298443593),
  (13409, 9351179624079958921),
  (13538, 6936731595653808332),
  (13570, 7046779506846348169),
  (10337, 9350906731538985865),
  (11361, 9350906731538981769),
  (12385, 9351179623913268041),
  (14433, 9405526756071850827),
  (9475, 13854792367090479946),
  (12579, 7046761299372729162),
  (12482, 10505495234118984520),
  (12481, 9298556853526504265),
  (10499, 10613863169960715147),
  (12450, 10504131766702875464),
  (12449, 9351210263169770313),
  (11523, 10613300215745889164),
  (12418, 10504131770947511112),
  (12417, 9351210266357441353),
  (12515, 6936960570089321288),
  (12547, 7046730720281666377)]

theorem tbl14_1_ok : tblOK 14 tbl14_1 = true := by decide +kernel

def tbl14_2 : List (Nat × Nat) := [
  (11393, 9350343985596507017),
  (14465, 9405499958815892297),
  (11394, 10503829000598589646),
  (13442, 10504131771130975112),
  (11426, 10503266050645168398),
  (11425, 9350343781585560457),
  (14497, 9405499966314782989),
  (13474, 10504131778613088526),
  (6305, 12864563330285888265),
  (14529, 9298539884191437642),
  (13506, 10505544020666908878),
  (12483, 10505525813193270090),
  (7329, 12791076451763393288),
  (14561, 9297167070995686217),
  (7362, 12918910470984073422),
  (8418, 4720639661112337225),
  (8386, 4705184783935529801)]

theorem tbl14_2_ok : tblOK 14 tbl14_2 = true := by decide +kernel

def tbl14 : List (Nat × Nat) := tbl14_0 ++ tbl14_1 ++ tbl14_2

def mask14 : Nat := 12460229193638509436896240507071786344653300054732606392357833704015518293810744830090887441142804366924201658648504701547833988821811456148133996644068804950164071191665286878499179896699309940759220844029101428885396453583806569608352278021408352807817442133814831233465472425192785216666691938732923613810569600268593029243613834247651659333939607326418594313915957160267742118144647614931639416314627453832412774723903844507214464810677270620893636361026919385841530350950994731577168290147307422038616223816399129809572672893066216590672612378725505896370879833485384962462826039938012481676036807666671580656103314377310014055008107968973616272024639210072860512451014665199709070586692231789875188933206427671015651061573054484616329857811612866146951939395006777147629717921034875962418404139690129626839669216723147288817754825157373946232565986322619336985267146131681156597937276721748309663231560414618750089921052892014741892358268066776197144764742014593145244666372896889449055708100264713094728107613463927871886445256965432648912674866169538404407978568599710423686421668057138499697624951451874184241570268522500454717957834637352765010260022331259086897774545424405715953395736831954130615926636491347851884463310941221129677802318558161138731910578959926316361537381532121370017242010188658659945945373915800869556315117064990916926369106171487439840599195703739514887697325316400339832867324263728908801558212034016090451607386176866940314443295712667094638474841575876086382045059106859545268529193139112362239252344544150393305611509097659086732632445989954464729090049703204611570049764993605647242056264595275842421890982604347348593444207108404189875811519103671227892278567570059620586208780381380919358561896233809305815645112476978461124102103153243143629753797271329340775223775062087949216910579727990968296763073051991578785505156340029028262260546978870464910792767812279114385618905881957482813339656568838578310944385194462238913390144093989302730937467180929734066352601274045947758477386642719699940578681405540913029689994283924385266117037719940642618668532906372151418735931266610354881210851612233872394754776042326189785185457294434498495588468529165723764509839708020424887240318985358252822660586772443802072231410100217337792610823176475788189313270403988313506653116426253672479220516365248889537074119365931394165276544858321250236215085365075062411517352318419849519647161254444597120021680741081701707374798722819510881922966539873653711980795938940786473392930456092350509879731355556754163957375097189500192940481874607605718100999456851170013412472783001554802204257149173566165738865898622511301109218875464607629799174959862477342710201182218609231688092329139388275657532391808423851339107235980487970550299727116301345367009775414304703531910634341526803290511231547755512313952384751999939422608372660881623760854959149090042906648750716318899237714393533090804222223612532627929829733191745775598902897417285671517072102849405643524045123999303600004243901611008664699418341767775313235867530176645496700983209949057476495404994205755081451830391595018446891934784026645694449139052495729912232150328616012047260293744705064505559656814113551549395442885681981307634555354419069755929769249251930120920042018221850118696627294919312884632306310276895557000656899828287886803598865341291772442388117266864689617555152789379723144904496920026646457693084312251897865460585298207824513708001605550934055506534112491492263340553993923597388978773979142087197118032732418437933812307779958531901599759735514681547663774744969188633738576185847923268144692777162931953923532913798363330234065797178360552627923573759037494057297951990538655009714146300160215719647242718547202109455402978269066665862699360861233350231369717721864632111460385876151405686964375020068484674263916824621819078580284688315200982562758820621172651230748303874205538234786239964163186716805778916422858549013943159404062073079195633789882720307501221509542684267701996471237071009478146913573616425389595732079240487504479009223154642163206881282226793946226541053001056389405195523552625865855057591208186442723759969830985638507936824782885172580955650623649966879945989375393340830109330778420024302617993854878594355295430252595746193047116891564956948477174911103454725022556199203606633357821451498662424894787249789223320681590023240707356212447473500714258003780741991289727484312582632809405390455308288

theorem mask14_eq : maskL 0 (tbl14.map Prod.fst) = mask14 := by decide +kernel

theorem cov14_1 : coverX 14 mask14 1 = true := by decide +kernel
theorem cov14_2 : coverX 14 mask14 2 = true := by decide +kernel
theorem cov14_3 : coverX 14 mask14 3 = true := by decide +kernel
theorem cov14_4 : coverX 14 mask14 4 = true := by decide +kernel
theorem cov14_5 : coverX 14 mask14 5 = true := by decide +kernel
theorem cov14_6 : coverX 14 mask14 6 = true := by decide +kernel
theorem cov14_7 : coverX 14 mask14 7 = true := by decide +kernel
theorem cov14_8 : coverX 14 mask14 8 = true := by decide +kernel
theorem cov14_9 : coverX 14 mask14 9 = true := by decide +kernel
theorem cov14_10 : coverX 14 mask14 10 = true := by decide +kernel
theorem cov14_11 : coverX 14 mask14 11 = true := by decide +kernel
theorem cov14_12 : coverX 14 mask14 12 = true := by decide +kernel
theorem cov14_13 : coverX 14 mask14 13 = true := by decide +kernel
theorem cov14_14 : coverX 14 mask14 14 = true := by decide +kernel

theorem cert14 : Cert 14 tbl14 := by
  refine ⟨by simp only [tbl14, tblOK_append, tbl14_0_ok, tbl14_1_ok, tbl14_2_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask14_eq]
  interval_cases x
  exacts [cov14_1, cov14_2, cov14_3, cov14_4, cov14_5, cov14_6, cov14_7, cov14_8, cov14_9, cov14_10, cov14_11, cov14_12, cov14_13, cov14_14]

/-! ### `N = 15`: 94 witness orderings -/

def tbl15_0 : List (Nat × Nat) := [
  (9409, 298843997634248110988),
  (9441, 302120942788492960648),
  (13601, 452019310709710828426),
  (14625, 525807655015082893647),
  (15649, 525807655015082893646),
  (10465, 673379083125912290187),
  (10497, 377061122053284606857),
  (13633, 452108498969787417483),
  (14657, 525807681188530496459),
  (15681, 525807681188530496395),
  (11489, 673379083114301932490),
  (11521, 743797353706593993676),
  (14689, 525895475131615028170),
  (15713, 525895475131615028106),
  (12545, 455567263483607708490),
  (14721, 525895475207816618319),
  (15745, 525895475207816618318),
  (13537, 673381607592848831370),
  (13569, 455567263483607958410),
  (15777, 525895475196056084812),
  (14593, 521229460737149145421),
  (15617, 455567280812843344206),
  (10305, 968564138534367966089),
  (11329, 1042369978316977918924),
  (12353, 1042368878874102395721),
  (13377, 1116155855168942936270),
  (9410, 301149800728236688135),
  (9442, 302120942788476183432),
  (9474, 973246197755213050763),
  (13602, 452019310708637086602)]

theorem tbl15_0_ok : tblOK 15 tbl15_0 = true := by decide +kernel

def tbl15_1 : List (Nat × Nat) := [
  (14626, 525807655015082889551),
  (14561, 673381607604759306575),
  (10466, 673379083125895512971),
  (10498, 679090214653458952654),
  (13634, 452108498968713675659),
  (14658, 525805698296702046415),
  (14529, 673381624990786920783),
  (11490, 673379083127169749962),
  (11522, 680461257346638688719),
  (14690, 525895475131615024074),
  (14497, 673435650800285664202),
  (12546, 680407495626103730639),
  (14722, 525895475207816614223),
  (14465, 673435650800287752527),
  (13538, 673381607591775089546),
  (13570, 678098292575860224907),
  (14433, 673435695043717907403),
  (14594, 521229456339102634317),
  (11361, 673398219014671745994),
  (12385, 673416233141524542410),
  (13409, 673416233825347613578),
  (15457, 673435695043717907339),
  (10499, 377242901699364696969),
  (10531, 378232338679724819339),
  (13635, 452019310575442768777),
  (13506, 673380239593151705994),
  (13505, 673380239594225447818),
  (11523, 748501921987567567820),
  (11555, 743708742332448515020),
  (13474, 673416268390153892746)]

theorem tbl15_1_ok : tblOK 15 tbl15_1 = true := by decide +kernel

def tbl15_2 : List (Nat × Nat) := [
  (13473, 673416268391227634570),
  (12547, 451047650705235530701),
  (12579, 452019320202742473039),
  (13442, 673416268390170669962),
  (13441, 673416268391244411786),
  (13539, 455586394782943724425),
  (13571, 450811458438560780622),
  (13603, 452019310572271874954),
  (11393, 673362194615699293130),
  (12417, 673416228743478031306),
  (15489, 673435650800287752526),
  (11394, 673398263486840320399),
  (12418, 673416229576650527055),
  (14466, 673435650800287748431),
  (12483, 747167225382078521679),
  (12482, 673380200779631563087),
  (12481, 673380199946459067338),
  (12450, 673416229576648180682),
  (12449, 673416228742404289482),
  (15521, 673435650800285664138),
  (14498, 673435650800285402058),
  (6305, 815188186574991688455),
  (15553, 673381624990786920782),
  (14530, 673381624990786916687),
  (13507, 747167215754795594633),
  (7329, 898290246950629995338),
  (15585, 673381607604759306574),
  (7362, 898291966378557371208),
  (14562, 673381607604759302479),
  (9475, 973246197755212788619)]

theorem tbl15_2_ok : tblOK 15 tbl15_2 = true := by decide +kernel

def tbl15_3 : List (Nat × Nat) := [
  (8385, 309183105483199521609),
  (8417, 302282473556930241353),
  (8386, 301131843976624403273),
  (8418, 302282474378174964553)]

theorem tbl15_3_ok : tblOK 15 tbl15_3 = true := by decide +kernel

def tbl15 : List (Nat × Nat) := tbl15_0 ++ tbl15_1 ++ tbl15_2 ++ tbl15_3

def mask15 : Nat := 2239966848021495874033015755452237859116591316900873650640797100961043277426294627114272582794387997672183008475463794044271577309032021083061151297323365035317814685726244985117118302557890560115689399006226863495592012680072171223048169408369999030646961451428748238086721338509396396961086060355708305495283668263106403075592858455548283031674513091596712284881022850073489549208241005577436762539313139111697363905956236336704354153933288885732479575490175099983961678877521683733583222520992082210850090175725105950146012804260614803005624980574498417116595783010328981374313222028111637273956651969875838541287860989898095274078968996196267896133123904861122794072629176980571876549059239122191011555011090830334681125739609604635632809351594657027277202095684503267717075037799577026690476144773617645508944950460713588499615503136958455230846011077481318391463832122383798401826639605454963465237265821028867916227233220520015398882031305348928840642580031672036320261183612391545828066523706485386482744206449721166006346578513906529936970128803930857333962536422262264679558039539300351806281327971229605566497338587623577556819262801241862566951895793133466480455867715852900151692587808001305033168335120730943988410825413296647287035364813977175836620462421111335152606238922642552242127768108481445004678496061286837207591054606572712323256621545741205073398577273931364952303878076631121984092939687243557299255120197780903941468907497798470247309786854840878200354331646268360751826025581843979530387963967928580502943075320150054854865016333702624416337256310855030285116382602911542972581283178046509223612459668254038248954606222775475625263822879241167582922421201744664002452755515906447318392150980367961511666357567378609653419816586539968166303102780240855522693597112592087619067039842605733766259862670748330851561066885092622360137814386271801986482313821462677650318893954661952525630918121414463907170041658739659358317465219458151787794468262451227303679680201763507345215764777374851364719965340247263187465901801577981563299446149365839633140214273326308993282431306973297837833250999430634276069149332297383201404016115659728300920254988890446382799287224645049979280805685094492852934797485985357436451177811561910804231138307454188813945958301957751583169544291481250134811635005320818875000825927499070234172770557177161751296002273540160000546409319338346063222954862156105340834224934399483879038156524347040105449034449288753955747557327469225597228348928941501444655781873845777693151396258180940665609008501390764928876066716247699687478695583561629080668407021370198366518150010629567061349635939578537545718134920611346357565225216746706655418619674814802338989584040335700386034814205557941636868486664821228086663576166790904922069384849962370255570126982508034138672047284933420375718667865134179486598645840231477516190709121672318731817285415285752680141162320034525687513325656525309579865354364438462119376257737825263619326339168639598150757551193320624255289932302420143880081867011369804171159394022760042089473392895730691158861490665890179714161608364482940488779215042016475281800504432242384398101119825776207004706047589168288467026731254248786551839937386011534555064794366677647308397338787213475733292622770285603156160546382980137782331440597759082851715241076507481010633567174040148119715073112067338967952356723817380640003000535543318899869017123974494870809569188486950888288015351948077817003686954754273136105274462484113032654798462877111907772168330238388325430044730573229072658803371343658492644777864188771948055841162733659437952714501307143969407846801702072128418694115859607991728259800192492531702409293078339959060598515181066589287363583996256489065416574471941622606385662784841575434633839491681500499363155547775038069172545884883701823945955712686870492999239910944431345962230257707012018112165311122787059553979644442440760871515426207691502817333269636231914474709687353998434531447164764470712004284241831118557024266902991333554150438038115881633445160253081550699031186212194936426192476887626002877313021613317383886511273514341649323314258834460418797256741310097058048438918354015835909016849809892702617269617112733946303476517147202818137505208077147803773135734676408096492348459207385045150829011705242259206564351101449285109821586698646639847913261815600910975218834636785494352516749474752990818571884759431663775000670749463595600846657143692067606835526341793794849495430561148978691188384822385111589412999431212913926859014828008975568923014857656738110595092877772254211166098983951267281941022657808598649942368057057172607835981280916741574953378826629018735030941646138818207571365401478521395880757452635083898145601423102864066019902619648

theorem mask15_eq : maskL 0 (tbl15.map Prod.fst) = mask15 := by decide +kernel

theorem cov15_1 : coverX 15 mask15 1 = true := by decide +kernel
theorem cov15_2 : coverX 15 mask15 2 = true := by decide +kernel
theorem cov15_3 : coverX 15 mask15 3 = true := by decide +kernel
theorem cov15_4 : coverX 15 mask15 4 = true := by decide +kernel
theorem cov15_5 : coverX 15 mask15 5 = true := by decide +kernel
theorem cov15_6 : coverX 15 mask15 6 = true := by decide +kernel
theorem cov15_7 : coverX 15 mask15 7 = true := by decide +kernel
theorem cov15_8 : coverX 15 mask15 8 = true := by decide +kernel
theorem cov15_9 : coverX 15 mask15 9 = true := by decide +kernel
theorem cov15_10 : coverX 15 mask15 10 = true := by decide +kernel
theorem cov15_11 : coverX 15 mask15 11 = true := by decide +kernel
theorem cov15_12 : coverX 15 mask15 12 = true := by decide +kernel
theorem cov15_13 : coverX 15 mask15 13 = true := by decide +kernel
theorem cov15_14 : coverX 15 mask15 14 = true := by decide +kernel
theorem cov15_15 : coverX 15 mask15 15 = true := by decide +kernel

theorem cert15 : Cert 15 tbl15 := by
  refine ⟨by simp only [tbl15, tblOK_append, tbl15_0_ok, tbl15_1_ok, tbl15_2_ok, tbl15_3_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask15_eq]
  interval_cases x
  exacts [cov15_1, cov15_2, cov15_3, cov15_4, cov15_5, cov15_6, cov15_7, cov15_8, cov15_9, cov15_10, cov15_11, cov15_12, cov15_13, cov15_14, cov15_15]

/-! ### `N = 16`: 122 witness orderings -/

def tbl16_0 : List (Nat × Nat) := [
  (9409, 19862676671909154829194),
  (9441, 19347392808158509441928),
  (13601, 47599662229739605115915),
  (14625, 33651528618418782380365),
  (15649, 33651528336943739085198),
  (16673, 33951305397034151616845),
  (10465, 43096261320138700145611),
  (10497, 24131912097968102093769),
  (14657, 33657313214300636103627),
  (15681, 33657313214300836340747),
  (16705, 38158478096462917419979),
  (11489, 43096261320138700145610),
  (11521, 47603033996783116895180),
  (14689, 33657313214300636103626),
  (15713, 33657313214300836340746),
  (16737, 38158480054061666943948),
  (12545, 47603031766685808382987),
  (15745, 33657313249825430987790),
  (16769, 38232104056345141748045),
  (13537, 43096261583405330772874),
  (13569, 47603031766685808378891),
  (15777, 33657456489323379098507),
  (16801, 38232104056345141748044),
  (14593, 33952461155004783813647),
  (16833, 38306035996591773720975),
  (15617, 33952461155004783813646),
  (16865, 38306035996591773769862),
  (11329, 43097486017007712256970),
  (12353, 43097486004637099139470),
  (13377, 43097486004636025397646)]

theorem tbl16_0_ok : tblOK 16 tbl16_0 = true := by decide +kernel

def tbl16_1 : List (Nat × Nat) := [
  (14401, 43097650121374121894285),
  (15425, 43097650403331057922954),
  (16449, 43248483541147943748555),
  (10466, 24058268620600221930312),
  (10498, 24131912097967028351945),
  (10530, 24206870009414420579275),
  (14658, 33651564695307423888329),
  (15682, 33651564695307423888265),
  (15585, 43096261302683029512590),
  (11490, 47818666342529663026121),
  (11522, 47597341442442167370697),
  (11554, 47597359456909229347788),
  (14690, 33658553674517698368460),
  (15714, 33658463875275068588937),
  (15553, 43096261302683029512654),
  (12546, 47905297303421200642512),
  (12578, 47599662230643658736651),
  (15746, 33658553674523200459787),
  (15521, 43099719785721873342862),
  (13538, 47818664152712452551561),
  (13570, 47905297021946223931856),
  (13602, 47599662230643641959435),
  (15778, 33658553674523200197643),
  (15489, 43099720067196850053518),
  (14594, 33953701579702336017355),
  (14626, 33651528614020735869261),
  (15457, 43099702114094953845642),
  (15618, 33953701579702553285643),
  (15650, 33651528332545692574094),
  (11361, 43097486017762368209866)]

theorem tbl16_1_ok : tblOK 16 tbl16_1 = true := by decide +kernel

def tbl16_2 : List (Nat × Nat) := [
  (12385, 43098638921058645750666),
  (13409, 43098638921058628973450),
  (14433, 43099702114094953845706),
  (16481, 43248483541148127732683),
  (10499, 24144719754012467463115),
  (10531, 24206870009414403802059),
  (14659, 33651564695307407111113),
  (14562, 47818664143916359529417),
  (14561, 43096261584158072807757),
  (11523, 47903907947413694596044),
  (11555, 47597359456908155605964),
  (14691, 33658553665722679088076),
  (14530, 47822268659146097210313),
  (14529, 43096261302683029512655),
  (12547, 47905296740466869158925),
  (12579, 47599665638988844114384),
  (14498, 47822268694260722500555),
  (14497, 43099720348671893348621),
  (13539, 47818664152712435774345),
  (13571, 47905296740466869158924),
  (13603, 47599665638920124637648),
  (14466, 47822122908430180070345),
  (14465, 43099720348671893348685),
  (14595, 33953701570906259772363),
  (14627, 33651492589621763416397),
  (12417, 43098638639583669040010),
  (13441, 43098638639583652262794),
  (16513, 43322415473195734553548),
  (12418, 47821005136333573461001),
  (13442, 47821005136331226002313)]

theorem tbl16_2_ok : tblOK 16 tbl16_2 = true := by decide +kernel

def tbl16_3 : List (Nat × Nat) := [
  (15490, 47822122908430180070281),
  (11588, 66268920690673773233097),
  (13507, 47818702700838486324105),
  (13506, 47818699293322012308361),
  (13505, 43096332796574438568842),
  (12612, 28926927518836565218313),
  (13474, 47821005180093771854729),
  (13473, 43098638639514932786058),
  (13540, 28487810831801607524560),
  (13636, 28926927518834217759625),
  (12449, 43098638639514949563274),
  (16545, 43322415473195734549452),
  (12450, 47821005180244211274000),
  (15522, 47822268694260722500491),
  (6305, 57490575817761745327114),
  (16577, 43396039475479209353549),
  (15554, 47822268659146097210249),
  (14531, 47822268694123217486795),
  (7329, 57490575804840336217098),
  (16609, 43396038362773442044237),
  (7362, 57786879767673795023056),
  (15586, 47818664143916359529353),
  (14563, 47818664143916342752201),
  (8385, 19862658648725222630281),
  (8417, 19347392808158509441929),
  (16641, 33952458318538758463821),
  (8386, 19273608093337764537225),
  (8418, 19347392809047399900041),
  (9475, 62509353439321799803916),
  (9474, 62509353720801154576848)]

theorem tbl16_3_ok : tblOK 16 tbl16_3 = true := by decide +kernel

def tbl16_4 : List (Nat × Nat) := [
  (9442, 19347392809047399900040),
  (9410, 19273608097735874773898)]

theorem tbl16_4_ok : tblOK 16 tbl16_4 = true := by decide +kernel

def tbl16 : List (Nat × Nat) := tbl16_0 ++ tbl16_1 ++ tbl16_2 ++ tbl16_3 ++ tbl16_4

def mask16 : Nat := 7428085143522917654348799186596392773281323528565488527129782281361788149511959569615642615512772516622943114468137524447813478767452779920881825679694743998724089933424233515387113809468422929788272885737321957897274988099042994228604992471483617897065970626994491916780882274796773336768365620154858677323811418675804874849843646981841050861432043208220126547374949174870776517876978142404791896548700873107512614669602215543293186460825199462861677816720487671695898872123201521034138341676657644729413400371379452374902917294810275989216467106836860884034905979280286768030401169928269410206790605372338147258963476467140360848005497484216606900747326301147297415500598313237943085075243484482634759855240331776504153150998447677564872496813628150978761853457218173246891031131713536293518191488465177575238686047410129127566739941059651858104243806037407821172674468694309790136208739511687896016448199913242923550361128270212416834084524901535240495861020721367406471054655159826366112620007636032195181116482626927186218177654708820702869637850316678620207302681405076918768184874936162459252944344219702232672028297846266500544589249883848979280837615819096920241442146984829913597296417680872726087969253886065616159165188753452451190149696703230049338094968026879786251395420511388352449764013939414023007355068203979025859494000920970401484803473541235953861491648759385303291208404800638579785054841343156149043323488384897893574953515978324164167045835709322690306511812682560780854989824230891437885637679114441489545831541227002367656883334932496536340062892879470379666565594060691517128894190785369070267533183880768727231718367446866932283582893845180773325480528998965758549184393326613343874674981625870664659205368575684150849237695698451314332216327004201526704889776615772365846619494466416738692153331484647550555550120910882702713428774091936750225417180826261299686023154230935830543807038965335285599396514273255823269872535675172789213320219438863568467937341026352876034857150532809295784345563126813369457182982816757881348689585624545811886619132706000812053871996161473836307565265909351401718614071433080000269881650783213552246114853258246838278719102580700606131446843049512229743697103308674522893145448819678791588981504053876116508642866304529662779741874542361799937139702057295960227737337129258226672203270650203763204196192970858758607974017900044921872852563141964168453351477008270302312958723638309362085460707989877134770281553618884850974353928294727241819805494182445095971381579087002412209598681636141862331817546907395294543643576964900498135119971901325686861556776517834611049232910904311828296628455621950838687557504494111625990220607955589416737147395015242449804431410433287017195620529940699446903657707521258326237812023872264736322779772310013576573019049892416088352685604516951588973284503446725814895418766678878285595221310902087082386757814256090447282822534745353304547745759049299961930153669239246281690019070109720053217181779376671129557621629243487003293723890766469237498646325731904820592531793619977366975467626573676296115401954462733779788530805975004765106628251343165850203091721578263604543413204511412982194637260715537393292809177127850455931784206983436021549144846916120656117564698171147259697185993202213857369698875825238419108872351394534700663599692827291432693795880955465611122168915231816275299644175869426550608330549456573157060846342307406211626927874132528189354375201527258505082509274281498158284638769651810020754817315353305824652221517598310967906669921910342244042871019613075939748149013691166765512748363732959294701518784977187064793412193674853798863677717758718971431853003569485877881506424126140234939792295408141816451162540130889462029550445536027930288507291958024541467138258529232878889730476202567103735198796309538767363901084705763676684005767278893744768439147348554526999111471411294142029292129301704797243636497508313893052392981583783960052656796177896951016578409396088611959496729693024691090304791308861068170036595477781285980241700172679151672133840719950056976060796966045325217056099240025550359839984358641630108935581064932514675528054016653451842174572815944809166574866661372883508752278523689375102547782225526542589132756971055463077201369655133596387225657330129271866071667363718847329853709005282331439569477234517121252636664829872035266385752412463950760201747907376929923083407066367495198262896477913342716875031324252387820238022879473925684547452560202980332052123760779671505832578492929188609778431613346203495315112842618180694155243943238904749315857872991158131016283543550099456916353450676645015269112093251139081496775064637163581227846921098839648877320947841857125787075469744336373384893897264511018839026932524821812013463308642266453750377229055295672461133737566670181894556569467338526732391885442432125682328965858255260881100482287869603555119193531749130144219931764222189253231451705225183723747290075475089225304486945561899986626529972394605835792574197348527472530721230494300839545448855562789142404860804595712

theorem mask16_eq : maskL 0 (tbl16.map Prod.fst) = mask16 := by decide +kernel

theorem cov16_1 : coverX 16 mask16 1 = true := by decide +kernel
theorem cov16_2 : coverX 16 mask16 2 = true := by decide +kernel
theorem cov16_3 : coverX 16 mask16 3 = true := by decide +kernel
theorem cov16_4 : coverX 16 mask16 4 = true := by decide +kernel
theorem cov16_5 : coverX 16 mask16 5 = true := by decide +kernel
theorem cov16_6 : coverX 16 mask16 6 = true := by decide +kernel
theorem cov16_7 : coverX 16 mask16 7 = true := by decide +kernel
theorem cov16_8 : coverX 16 mask16 8 = true := by decide +kernel
theorem cov16_9 : coverX 16 mask16 9 = true := by decide +kernel
theorem cov16_10 : coverX 16 mask16 10 = true := by decide +kernel
theorem cov16_11 : coverX 16 mask16 11 = true := by decide +kernel
theorem cov16_12 : coverX 16 mask16 12 = true := by decide +kernel
theorem cov16_13 : coverX 16 mask16 13 = true := by decide +kernel
theorem cov16_14 : coverX 16 mask16 14 = true := by decide +kernel
theorem cov16_15 : coverX 16 mask16 15 = true := by decide +kernel
theorem cov16_16 : coverX 16 mask16 16 = true := by decide +kernel

theorem cert16 : Cert 16 tbl16 := by
  refine ⟨by simp only [tbl16, tblOK_append, tbl16_0_ok, tbl16_1_ok, tbl16_2_ok, tbl16_3_ok, tbl16_4_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask16_eq]
  interval_cases x
  exacts [cov16_1, cov16_2, cov16_3, cov16_4, cov16_5, cov16_6, cov16_7, cov16_8, cov16_9, cov16_10, cov16_11, cov16_12, cov16_13, cov16_14, cov16_15, cov16_16]

/-! ### `N = 17`: 147 witness orderings -/

def tbl17_0 : List (Nat × Nat) := [
  (10465, 1540539697782994981950411),
  (10497, 1545261901287195354117065),
  (10529, 1549972810067117779239883),
  (14657, 2158425909425757602759627),
  (15681, 2158425909409193036657038),
  (16705, 2441995223205559753032651),
  (17729, 2441995024256086235956235),
  (11489, 3065120274177121386288140),
  (11521, 3046155886643728590619657),
  (11553, 3046157239917696731857932),
  (15713, 2158864217175625618707468),
  (16737, 2442211970812966782911564),
  (17761, 2442211970812966782911500),
  (12545, 3046377232087010842555401),
  (12577, 3046378382761182401713163),
  (15745, 2158864219431536705213453),
  (16769, 2446934160194901279252817),
  (17793, 2446934160194901279252816),
  (13569, 3046377228384074857755593),
  (13601, 3046378382703335802454987),
  (16801, 2446934160234745554302031),
  (17825, 2446934157116804569280846),
  (14593, 3046457934005678664627145),
  (14625, 3046452168852660440843211),
  (16833, 2451656685992460457133003),
  (17857, 2451656523590878121472397),
  (15617, 3046458133012874340385803),
  (15649, 3046452168836095874740622),
  (17889, 2451656685992456395731342),
  (16673, 3046520245248063140573647)]

theorem tbl17_0_ok : tblOK 17 tbl17_0 = true := by decide +kernel

def tbl17_1 : List (Nat × Nat) := [
  (17697, 2177605911898136142742410),
  (11329, 4576501252292146094199820),
  (12353, 4576501252291608099214347),
  (13377, 4878806493609157949461451),
  (14401, 4878806493929521644094411),
  (15425, 5181037948833175933333902),
  (10466, 1540539697783009960858571),
  (10498, 1545261901349301520741321),
  (10530, 1549239681499383812375499),
  (14658, 2158425909426716252881867),
  (15682, 2158425909404794990145934),
  (16706, 2460432598385570526835151),
  (16641, 3046458133012874340385739),
  (11490, 3065120274177120312546316),
  (11522, 3046229874021054285419532),
  (11554, 3046231026889647095862284),
  (15714, 2158864056505831730238476),
  (16738, 2461401159699436883702863),
  (16609, 3065114563555837345313736),
  (12546, 3065938812376326872543696),
  (12578, 3046378382761181327971339),
  (15746, 2158864056505834901132299),
  (16770, 2461107222118998645682641),
  (16577, 3065410810339325776540111),
  (13570, 3066012796380845704025035),
  (13602, 3046378382765579374478283),
  (16802, 2461107164715762087433163),
  (16545, 3065409711179541721428431),
  (14594, 3066011643459341097178059),
  (14626, 3046452168853619090965451)]

theorem tbl17_1_ok : tblOK 17 tbl17_1 = true := by decide +kernel

def tbl17_2 : List (Nat × Nat) := [
  (16834, 2461106011794257480586187),
  (16513, 3065409711461016698139087),
  (15618, 3064895526207283690254734),
  (15650, 3046452168831697828229518),
  (16481, 3065412017022550935122383),
  (16674, 2479996630647240668287947),
  (12385, 3065268066777991107855371),
  (13409, 3065267830119721350534091),
  (14433, 3065341617051352927880139),
  (15457, 3065338229492102236516880),
  (17505, 3074861346531547723613196),
  (11523, 1545335652234694246835081),
  (11555, 1549239698950832351659018),
  (11587, 4600471661031403987997709),
  (15715, 2158426109814146024653834),
  (15586, 3065120274115766871175566),
  (15585, 3065120274120164917686670),
  (12547, 3368165655576515069666317),
  (12579, 3372143325740657142981645),
  (12611, 3395462334340805922448397),
  (15747, 2158944742095636127867917),
  (15554, 3065333582617313673785872),
  (15553, 3065120345614809002193230),
  (13571, 3368239697283191727211596),
  (13603, 3372143325746024941887953),
  (13635, 3401006624916785889088393),
  (15522, 3065341634763176409084302),
  (15521, 3065341634767574455595406),
  (14595, 2134971038185723421594570),
  (14627, 2154363249897758561453002)]

theorem tbl17_2_ok : tblOK 17 tbl17_2 = true := by decide +kernel

def tbl17_3 : List (Nat × Nat) := [
  (14659, 2158426145842943043617739),
  (15490, 3065341635044651385794958),
  (15489, 3065341635049049432306062),
  (15619, 2134953565903771498746190),
  (15651, 2154363213868961542489098),
  (15683, 2158425873380396017693070),
  (12417, 3065267848692660999345163),
  (13441, 3065267848634883102786507),
  (14465, 3065341635065613998408651),
  (17537, 3074861505564909565137932),
  (12418, 3065267848692659925603339),
  (13442, 3065267848697057972110283),
  (14466, 3065341635066572648530891),
  (16514, 3065412016182524051501519),
  (11588, 4600472813952907520840717),
  (14563, 3367351965457572218323914),
  (14562, 3065120274137688133911499),
  (14561, 3065120274136729483789259),
  (12612, 3395536121312701640401933),
  (14531, 3367573326386383768830922),
  (14530, 3065351040573869276542031),
  (14529, 3065120345613987540681675),
  (13636, 3334443927452487143141841),
  (14498, 3065341634785097671820235),
  (14497, 3065341634784139021697995),
  (14596, 2125511192543034820039489),
  (14660, 2158278335474126576468939),
  (13473, 3065267848634814383309771),
  (17569, 3079583872007798549660683),
  (13474, 3065267848697057955333067)]

theorem tbl17_3_ok : tblOK 17 tbl17_3 = true := by decide +kernel

def tbl17_4 : List (Nat × Nat) := [
  (16546, 3065410863261019444654543),
  (13507, 3367351966069238958421070),
  (13506, 3065120274744468295697355),
  (13505, 3065120274682293426373579),
  (6305, 3641257198817047644013383),
  (17601, 3079583694946844061475152),
  (16578, 3065410810334927730029007),
  (15555, 3367573290357586749867018),
  (7329, 3986425613911472668992587),
  (17633, 3046384310029713857332235),
  (7362, 3986425850099422818481230),
  (16610, 3065116868277344698676168),
  (15587, 3367351929428775199360010),
  (8385, 3986425630522963060909131),
  (8417, 3948344651007458422334345),
  (17665, 3046457934063400823309323),
  (8386, 3963260090220966384046985),
  (8418, 3948344654930717605929865),
  (16642, 3064895508192885114188239),
  (10531, 1549239681499383795598283),
  (10499, 1545262136314391955817419),
  (9409, 1275933744416750710338506),
  (9441, 1238308242597453817492426),
  (9410, 1233584796117443048640721),
  (9442, 1238308242598422077838282),
  (9474, 4293387665912193644041163),
  (9475, 4293454607416782148932556)]

theorem tbl17_4_ok : tblOK 17 tbl17_4 = true := by decide +kernel

def tbl17 : List (Nat × Nat) := tbl17_0 ++ tbl17_1 ++ tbl17_2 ++ tbl17_3 ++ tbl17_4

def mask17 : Nat := 1335341766768390962209775250407931901356481234993175909052874751536606182045211776464313896301274011412636662387030646365158748640866802457970666675528362329685450184511249830767744065187911305279435063406969338081875395352276186492966755770725624571997863777608161625861174227909273859317150991461876683779707317123853025859327345004151641177015646740262558624119626587793262277203189521521737894062644609430113331258638941050115926449332621529585026555358065879442000193174052185769902772361378508182277206850621120948790902350245908256420726112008744213172353796612848366923245937175092766014202368656950448903274875269369204948143803606815601639044568308375769061845998382121860315418131121943851681647229533657671491225615216057559694904405110174300571942719585714155696329372394865506964961792437021137127714152654838658267843746852179395097684393888465553881668551047883495170272391851101553115354243966557318713889653835910420808216609275314071246507432661594030453566052940456055153121340343581996988874404162213009835669131524405454664575770860219489633561404874531279631398160046048435658497149929778303886364669563070639792114632708971763637226599783605160887497102319898365951175567069715135988743978638627924544927304648117368406945173293811214591491684983879476411839322222551791449280308028298128980517188752626510494940170389412511553457232732147419815829541132559648443370604582355998491981973066113375074119951421353239580907148782057165567245996988199611054617076720512436870926047148022218340608190849362509245972414377101575750414085800098836633927637932660652342039199271820001378320970339922544409222990151812886557959496428555353848882017192026620614585161319727572289118984145755206501698167434230688004785018560001538886347747207140060467290636661519502260216441842238949693934013227161219921578506678912281288144075926387870720070001479166227213377574369218665491083650780313155132763147033787223887626237132964108988061129137351931126590243698537310584129044882718207872534191318104113619348554727784535855179452086643900031176560146312973012961407885850758008155324704368452820039492948984642529276458344634767656927526002028566948221648283815473553250808785998056885498416068360200957135542119764346862265325010094615565997619420893103328946881823053149315254889269292500513013989688998113040830197848084517303020995534436024022593526404480904872412157829613645030149522767091898947232968822553420291030695593949419751735867943686220979404064722614676024753942460002268829097113512322755178717618363587996668809672841775628617752109573908648951195904994582774892828001336566906479075787906828998624057684852227908927375106447855704680325303325651329784639143291418937646679618332324300319469552225441001230466656357231149310803958409777454677196631853772116007316645346855759831550520785992499954804346123986161663105490285323852340125087745195692911794415948923347827318921036545060262215862076353659213414549337679865778174194697068153721839065516447205482820363682740101739275245108683380861544471142048144365412009986322438801128446506400603112251803288138306296998042232660886946454381892073423769086624056782808254448959206090253124228913271441733789550675788978192156030343065580631968747070936085183156549928539083349184900037309358853504858268529725434159528953010146620532872786624149781885573141474086844069004081309664157991506771977194374196000760350077119332192606236704670204959604083102981969565856368896318937095181976374222074296916833973953615726652345820980263693823206079129174438914486061352781633075556251642398534918201026452467183513580880610902757997437029202299277767023651675211430838867097280695547304919447470684642065510769974468443391823155127684831220386338345723733511605211280651647311293578175973794487104237902109602068111752915913319550662031327720793982025994606739176566577452462262789723691315256100625995194112510580971541479637320700989770843734014947889481611496300134644966688482302237594752470986374063414501441295293008727450573612187226906356215985169358703128703338317344312248833522406987662800977882156195506473408513852219639005144977378503897334191785171339302707023064512617762662200904411429796391323451028787098857379261496086678454254305293164964201443014230563218742879719932437373698719041794599852352697125105117073758345267359485505844982646254721148661955370217991771924683975761868870558574186915272754269332608322744116397353451481771703039446579692065656496751398364538007580455615889454909277169008927965958476763362881135426657784805722794257971911733188771673695442650541870093273552410130066016711869622575439863780938423180505337397364422237588885989245089698259678346287398284873432371742667324557623456388983044514243051432639470872248482238433809479622435500586932885975700936210398410959926575431722150473140534106010076129803643317443051476471439873559912200608656472200048652141819423542028181338546973384287809766873727585853644284733031417124779005331395357694026331209982405606079188029233148725816015389595063272084613436785867385099449481179096102357879903597453206516389439618799335104237981744445155897150488520335624538420377587951919336952072851748371854797271252815955238128736226648843280638904395720281594577480234999076924323528804372940552494866314926781096621004398093553130565688209893475201702375267952188148240102950098630385201325400004608378397810573315145728

theorem mask17_eq : maskL 0 (tbl17.map Prod.fst) = mask17 := by decide +kernel

theorem cov17_1 : coverX 17 mask17 1 = true := by decide +kernel
theorem cov17_2 : coverX 17 mask17 2 = true := by decide +kernel
theorem cov17_3 : coverX 17 mask17 3 = true := by decide +kernel
theorem cov17_4 : coverX 17 mask17 4 = true := by decide +kernel
theorem cov17_5 : coverX 17 mask17 5 = true := by decide +kernel
theorem cov17_6 : coverX 17 mask17 6 = true := by decide +kernel
theorem cov17_7 : coverX 17 mask17 7 = true := by decide +kernel
theorem cov17_8 : coverX 17 mask17 8 = true := by decide +kernel
theorem cov17_9 : coverX 17 mask17 9 = true := by decide +kernel
theorem cov17_10 : coverX 17 mask17 10 = true := by decide +kernel
theorem cov17_11 : coverX 17 mask17 11 = true := by decide +kernel
theorem cov17_12 : coverX 17 mask17 12 = true := by decide +kernel
theorem cov17_13 : coverX 17 mask17 13 = true := by decide +kernel
theorem cov17_14 : coverX 17 mask17 14 = true := by decide +kernel
theorem cov17_15 : coverX 17 mask17 15 = true := by decide +kernel
theorem cov17_16 : coverX 17 mask17 16 = true := by decide +kernel
theorem cov17_17 : coverX 17 mask17 17 = true := by decide +kernel

theorem cert17 : Cert 17 tbl17 := by
  refine ⟨by simp only [tbl17, tblOK_append, tbl17_0_ok, tbl17_1_ok, tbl17_2_ok, tbl17_3_ok, tbl17_4_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask17_eq]
  interval_cases x
  exacts [cov17_1, cov17_2, cov17_3, cov17_4, cov17_5, cov17_6, cov17_7, cov17_8, cov17_9, cov17_10, cov17_11, cov17_12, cov17_13, cov17_14, cov17_15, cov17_16, cov17_17]

/-! ### `N = 18`: 179 witness orderings -/

def tbl18_0 : List (Nat × Nat) := [
  (10465, 98599252522521974851052424),
  (10497, 98901569419378685790176267),
  (10529, 99203789309328512227263499),
  (15681, 138186860007471177871467532),
  (16705, 156287766919210614443000907),
  (17729, 156287766919210629424227467),
  (18753, 175635290834574677820580939),
  (11489, 196167711343497787300434956),
  (11521, 195010791489446561753875468),
  (11553, 195010353486731730747970572),
  (15713, 138167297308001562698241036),
  (16737, 156301115355155426241725513),
  (17761, 156301115355155426241725449),
  (18785, 175635290834574677820612753),
  (12545, 194968142871869726485718091),
  (12577, 194968216497002369002296395),
  (16769, 156603786273566151276024907),
  (17793, 156603786273566151276024843),
  (18817, 175946235061126748425204046),
  (13569, 194968142871869657766241355),
  (13601, 194968216497002369002292299),
  (16801, 156603786273606009642054801),
  (17825, 156603786273606009642054800),
  (18849, 175946235061126748424941902),
  (14625, 194972938806570339015377931),
  (17857, 156906017728228191959016592),
  (18881, 176249133859462496833786959),
  (15617, 194973393146878748017607691),
  (15649, 194972951470146104769168395),
  (17889, 156906017509821349340128395)]

theorem tbl18_0_ok : tblOK 18 tbl18_0 = true := by decide +kernel

def tbl18_1 : List (Nat × Nat) := [
  (18913, 176249133859462496833786958),
  (16673, 194978117875494953417778253),
  (18945, 176248756836617824698413455),
  (17697, 194978117875494953417778189),
  (18977, 176249135015752290871083714),
  (12353, 196177069642878716031316497),
  (13377, 196177069642878716014539281),
  (14401, 196181644403307450468426895),
  (15425, 196181656018903910696141835),
  (16449, 196186370423023459321300043),
  (17473, 196186370423023459321299979),
  (18497, 197097860761369846740464145),
  (11490, 98599252794954293107495186),
  (11522, 98901569419378701627868170),
  (11554, 99151340734032367607112848),
  (11586, 295337996590923711954301522),
  (15714, 138186630598095592617706640),
  (16738, 157529821794716956173870157),
  (17762, 157529821794716956173870093),
  (17665, 194973393146878763014825099),
  (12546, 215567708175027905063887949),
  (12578, 215817172847744697596699725),
  (12610, 217677563860752147295032393),
  (16770, 157515657001111356451923021),
  (17794, 157515657001111356451922957),
  (17633, 196187031067619375037572240),
  (13570, 215567705869184895784133710),
  (13602, 215817172847744697596699724),
  (13634, 217677563860752147295028297),
  (16802, 157515654695268347172168782)]

theorem tbl18_1_ok : tblOK 18 tbl18_1 = true := by decide +kernel

def tbl18_2 : List (Nat × Nat) := [
  (17826, 157515654967995267939082450),
  (17601, 196187030924070984136311819),
  (14626, 215817174000947672935617548),
  (14658, 217966745288508949379953234),
  (17858, 157515654695268347238229005),
  (17569, 196187043695109582592484365),
  (15618, 215558408710171746236179469),
  (15650, 215817174000943274889106444),
  (15682, 217966744135587444773106258),
  (17890, 157515728482244652764509325),
  (17537, 196187043695109582592746509),
  (16674, 155069690398531399978857549),
  (16706, 157529821794716542970409425),
  (17505, 196186370423023459304522763),
  (17698, 155069690398531399978857485),
  (17730, 157529821794716542970409424),
  (12385, 196177157448130382636590157),
  (13409, 196177157448130382636590156),
  (14433, 196181863491286658185741323),
  (15457, 196181877272027947850056715),
  (16481, 196186370423023459304522827),
  (18529, 197098239138272436578173457),
  (11523, 98901569423345382038512652),
  (11555, 99151340734032367606850704),
  (11587, 295337995437980423140164750),
  (15715, 138186630598095592617444496),
  (16739, 157529456318582143873467468),
  (16642, 215558261136219156559766605),
  (16641, 194973393146878748033598539),
  (12547, 215567340393050071590560845)]

theorem tbl18_2_ok : tblOK 18 tbl18_2 = true := by decide +kernel

def tbl18_3 : List (Nat × Nat) := [
  (12579, 215817172847744697579922509),
  (12611, 217677563860774067517318221),
  (16771, 157515289219133522978595917),
  (16610, 215529844181444098065507404),
  (16609, 196187031067619375037572241),
  (13571, 215567340393050071590560844),
  (13603, 215817172847744697579922508),
  (13635, 217663396670972062141846408),
  (16803, 157515289219133522978595916),
  (16578, 215529844037905049857868874),
  (16577, 196187030924070984136311883),
  (14627, 215817174000947671861875724),
  (14659, 217966742982644155958969487),
  (16546, 215529844037905677925770385),
  (16545, 196187043695109582592484429),
  (15619, 215557897965927353473057804),
  (15651, 215817174000943273815364620),
  (15683, 217966742982644155958969486),
  (16514, 215529183539984327768827025),
  (16513, 196187043695109582592746573),
  (16675, 155077946597488278737052746),
  (16707, 157529820641777599637111884),
  (13441, 196177142316616998193775691),
  (14465, 196181864644199366699566091),
  (15489, 196181877290042208920585227),
  (18561, 197097862111852479013761358),
  (13442, 215519955430451063915332682),
  (14466, 215524677758099264404767754),
  (15490, 215524690403877302011741194),
  (17538, 215529183539984327768827024)]

theorem tbl18_3_ok : tblOK 18 tbl18_3 = true := by decide +kernel

def tbl18_4 : List (Nat × Nat) := [
  (12612, 118853642785152523842692173),
  (12644, 118853274841916257335829581),
  (15587, 215557883053431859798639760),
  (15586, 215557883053431859798901904),
  (15585, 196215299348973378257363980),
  (13636, 235514015781491485969019982),
  (13668, 233951440638087706979136590),
  (15555, 215524690658347163982308364),
  (15554, 215525132102269163658880012),
  (15553, 196215299348995299720111116),
  (14660, 138129813470348648997504011),
  (14692, 138129813470348648997504010),
  (15522, 215524690403595827035030538),
  (15521, 196181877289760733943874571),
  (15620, 139386035552817896966398986),
  (15652, 137827216757466532147630418),
  (15684, 138186861286225939618628752),
  (15716, 138186628292252583404012688),
  (13473, 196177142316616998176998475),
  (14497, 196181864626184968190084107),
  (18593, 197097862111852479013761924),
  (13474, 215519955430451063898555466),
  (14498, 215524677740084865895285770),
  (17570, 215529844037905677925770384),
  (14563, 215510526981634272922248204),
  (14562, 215510510658650655469126666),
  (14561, 196167697544750757763925003),
  (14531, 215524694081082880783885324),
  (14530, 215525353462978691242144274),
  (14529, 196167702119295273405039627)]

theorem tbl18_4_ok : tblOK 18 tbl18_4 = true := by decide +kernel

def tbl18_5 : List (Nat × Nat) := [
  (6305, 255131239290339595952907339),
  (18625, 197399945992803546630762830),
  (17602, 215529844037905049857868810),
  (16579, 215529844037904913492657226),
  (7329, 255131239290335197906396235),
  (18657, 197399945992794761091097675),
  (7362, 256344901346665573163516433),
  (17634, 215529844181444098065507340),
  (16611, 215529844181443960643331148),
  (8385, 274776284922748526957216907),
  (8417, 274776284922202963031409803),
  (18689, 194973393202606262194869195),
  (8386, 274781007289298120998392146),
  (8418, 274781007288686862377424010),
  (17666, 215558261136219156559766541),
  (16643, 215557895660084344259363916),
  (11588, 290780386179054487988655116),
  (9409, 273236351865245967843893711),
  (9441, 273236353014807433652515786),
  (18721, 194978103948408744615879755),
  (9410, 273236352134331916970435530),
  (9442, 273236353287270738785805258),
  (9474, 275990385017502006359434253),
  (9475, 275990019541367194059031564),
  (10531, 99151340734032358027109387),
  (10499, 98901569423354862137533584),
  (10530, 99151340734032358027371531),
  (10498, 98901569419378701627868171),
  (10466, 98599252794954293107757330)]

theorem tbl18_5_ok : tblOK 18 tbl18_5 = true := by decide +kernel

def tbl18 : List (Nat × Nat) := tbl18_0 ++ tbl18_1 ++ tbl18_2 ++ tbl18_3 ++ tbl18_4 ++ tbl18_5

def mask18 : Nat := 4428204974559847448471211504988665361079145297077197548064612486748053768442318036906679356975555454457676115982073158458590728255867436765927905849744548737810325658749150775368656196739113154620816418841290624581214107402788503416719031640281839167001895680656273101236586377072781300406283303172304262515558729387365897073536229325141616197260719725327190343360305060924875105826002264992862359200123950219867175700420928622336353250601264189180563153564225804696999107065123384725997397977965919195038767315658226164457987485186849882283579960072446091412664271021065975313004544737557479446383018145896246670261906504804069615129892629026903484632834857619981942542139288120986185694595879352625317141732327092195926260928160904216924157692072706001078702131727441571098367407018578140832511735015570333486011039125659013109711759717797521603387506778685384422968389082488577836705463412189539217073030299791762440081601956559958913028216033550454752438547440736001285757906233631505593803823339816161488309933502407841877223107506121841370775648883755327830796738557593377316295124117644416882979165122845006593475865001997837465049645307795210124814497285865432828670266289628287441686307746664873745747902361982311781965590585252752255103295622774501903085647953781042802012460862114921327009812652731257100248062996200326039844809121490219419299706423413020067131651691832393949789634326814566654147584283245509880630539786815908467480862390119931134619554558973603265033470789487575212764459954318964441211596869364079952819334663470438305153079687799167000249231279771767290821245438073963313995821696678676375707193388448842782627067130253084475710297310177188458685356356228417036784689241937246713621274940785839352334812043728779279551645952683870719915515179970619269152842774935813320948740910948165530654678936528121278616406091295632066918025906618509571380195333031932890828508170022085651479559737064471969241811308240571863805275991012783604805573941734486747988203779563269710921583255443276794148443926152346813690878053145336812343788503974593421249492187296978765051376375134812243418430977038665648851215529399811500198951593837306623258604240722362978908711305309596782821188088696524895496823958285333372212165567405451554878978428909231206727607554883961343184911835277205264940100040747943154109434112664077980894892849934818034038973836658061857505649803342036262700479353270224133363501334973557308133228917854574048461985724291103482539079558156290632860293791816271353187605293072117138887778429893046510460722972310202897956502094366004376484096677505723857485504775972561551715820155201386680152066677550580949607415925317736400867135594393907055349845886200400886091775571900357481959239220246218880761096600485082667657126196507693537795915609831761716617286445174312941674053417717168486026833481784634628060286345040345386167974792951346614950562053397571227577205479779602532026239991286396972930801028772317245629713400294767179686979228369884107018483364125885282077640277369876818339415336404480482592101515810811619718446970461985876561521818626002402379133488507212078875388297380704371029891026619733478759978980869405785829799150125958752035957176117037216596517645236836826708210763451166935612751845880952249209758665008687230675088658088473209805822224612421085204154772312718346584643054392872234633032665052074398104333198096549570024280165554122194219697795370654244216808028050802610572718274449028465885654196222710881034871498456231574266042262094378031363347205379600671175817982202186748808835355894913705056374260331604423242829379724044580491838657153169302294415441149349827235808008806696525753200002865574909472538306505330591558850839257195484732659800350886153939727565725006365050623693006975564063128892291622108353440872699325847330024741029072015523712733181331151066241442816882941129315678449466699576853250718750133826790547439849374692597123611453703649139808138485195748792046268056788560881057399699227695500214018530217217601949976460951814396172483201286973464353516935430077928209227372676901966721243473958509233497640730435126857647986238867448562511828553193443853094881602013524810587212137901325387260455821776506740407828644425942229680016405417077117363037770706059797865416705595645028264898874119764452489524250941230367313950075129235028418887324980773179983440652732390496943789091289772173140848117345439969253691619408588616552899519840877059647008012125933795041024223470325851762011753504025250710864505498043059366654224624444735791022126560167320293921792448333749493189705203768073662717415268354847184790292108575835833307843683688712087875454138918820905424646924276873568637973963090264718842675875286304126631629978477924894650486365827561045292780183497185364495175094460893142701113446782661903297395467875365242239061111924930216946041411035660727461231736755655357106858210298687886485673780420433739399000089961772034775402879346544877949645445126721767339787859030626630336057236337228989255539059053527320044110803953067173085657401755783198366594377620892717128352376454967256369283310066074563488481000728086706293173585098999655020286444958794081565152087253319447475012231012839685718592327065079141551018435554991356588893142020032761162079174259015710117773815503416347370229978517657504472622324323329688592261996593640193898613556330916085469330100609147173955494882099180766306331469099540854935538485476316388366445473959104831681936637847919281973795252998745196317893122740135376899263227431316170877969947196353093524764394145281595598251341050348181721826170798468049153279832683084148755070739492085881836376969414346520528790048260641458654468008280879007161115206915657402507673401819136

theorem mask18_eq : maskL 0 (tbl18.map Prod.fst) = mask18 := by decide +kernel

theorem cov18_1 : coverX 18 mask18 1 = true := by decide +kernel
theorem cov18_2 : coverX 18 mask18 2 = true := by decide +kernel
theorem cov18_3 : coverX 18 mask18 3 = true := by decide +kernel
theorem cov18_4 : coverX 18 mask18 4 = true := by decide +kernel
theorem cov18_5 : coverX 18 mask18 5 = true := by decide +kernel
theorem cov18_6 : coverX 18 mask18 6 = true := by decide +kernel
theorem cov18_7 : coverX 18 mask18 7 = true := by decide +kernel
theorem cov18_8 : coverX 18 mask18 8 = true := by decide +kernel
theorem cov18_9 : coverX 18 mask18 9 = true := by decide +kernel
theorem cov18_10 : coverX 18 mask18 10 = true := by decide +kernel
theorem cov18_11 : coverX 18 mask18 11 = true := by decide +kernel
theorem cov18_12 : coverX 18 mask18 12 = true := by decide +kernel
theorem cov18_13 : coverX 18 mask18 13 = true := by decide +kernel
theorem cov18_14 : coverX 18 mask18 14 = true := by decide +kernel
theorem cov18_15 : coverX 18 mask18 15 = true := by decide +kernel
theorem cov18_16 : coverX 18 mask18 16 = true := by decide +kernel
theorem cov18_17 : coverX 18 mask18 17 = true := by decide +kernel
theorem cov18_18 : coverX 18 mask18 18 = true := by decide +kernel

theorem cert18 : Cert 18 tbl18 := by
  refine ⟨by simp only [tbl18, tblOK_append, tbl18_0_ok, tbl18_1_ok, tbl18_2_ok, tbl18_3_ok, tbl18_4_ok, tbl18_5_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask18_eq]
  interval_cases x
  exacts [cov18_1, cov18_2, cov18_3, cov18_4, cov18_5, cov18_6, cov18_7, cov18_8, cov18_9, cov18_10, cov18_11, cov18_12, cov18_13, cov18_14, cov18_15, cov18_16, cov18_17, cov18_18]

/-! ### `N = 19`: 215 witness orderings -/

def tbl19_0 : List (Nat × Nat) := [
  (11489, 6310659862425693145010599116),
  (11521, 6330001932948651219526394825),
  (11553, 6349350284714792428827128908),
  (16737, 10098503214295453704681239628),
  (17761, 10098503229501509568673428620),
  (18785, 11336471673275168628343911502),
  (19809, 11336470707055220724201431442),
  (12545, 13812323405938521764017267789),
  (12577, 13812355506839497836122137677),
  (12609, 7602973456429731803025953867),
  (16769, 10100296835032708599245497421),
  (17793, 10100296831662878011479347794),
  (18817, 11336428584062031189101851725),
  (19841, 11336428583825900840822776082),
  (13569, 13812322463103443984750273676),
  (13601, 13812294339670824194453333132),
  (13633, 14974685739755529966417933454),
  (17825, 10100297801360224609985180814),
  (18849, 11338237840645604884867527758),
  (19873, 11338237826703859905474380239),
  (14625, 13812294413460610758401119372),
  (14657, 14974686034885420747210945677),
  (17857, 10100297799054381600771486863),
  (18881, 11338237838339761875657696463),
  (19905, 11338237838339761875657696399),
  (15617, 13812322445630383984378721356),
  (15649, 13812294413456344874610381900),
  (15681, 14974686034885353969260749901),
  (18913, 11338237838339761875653833806),
  (19937, 11338236872119813971511353746)]

theorem tbl19_0_ok : tblOK 19 tbl19_0 = true := by decide +kernel

def tbl19_1 : List (Nat × Nat) := [
  (16673, 13812350785625914755712341068),
  (16705, 10177668087488093995345720396),
  (18945, 11338236873437662273852949708),
  (19969, 11338236873437662273852949644),
  (17697, 13812351751845929178142160014),
  (17729, 10177669051509717867952682127),
  (20001, 11338236873165216429740147724),
  (18753, 11240606885251253767776285137),
  (19777, 10177668538301490917816419468),
  (12353, 20002929488765766977222128081),
  (13377, 21240869528051147320823689680),
  (14401, 21240869529204080925443933195),
  (15425, 22479126045262340862325351501),
  (16449, 22479107747245735245391934541),
  (17473, 23717047786531115520294401165),
  (11490, 6310659862425694258426299596),
  (11522, 6330001933239410257719215308),
  (11554, 6345685881865337903701898316),
  (11586, 20100895639609795437054973001),
  (16738, 10098503215738835244679984337),
  (17762, 10098503215702806447661020370),
  (18786, 11336470780845560617193231436),
  (18721, 13812351751845929178142159950),
  (12546, 13812322535773523173937308749),
  (12578, 13812299062256566235497817165),
  (12610, 13932337477926701464181068873),
  (16770, 10100296909110422282173211725),
  (17794, 10100296908801653931008119248),
  (18818, 11336428584062031189101589581),
  (18689, 13812351238834689842212844620)]

theorem tbl19_1_ok : tblOK 19 tbl19_1 = true := by decide +kernel

def tbl19_2 : List (Nat × Nat) := [
  (13570, 13812322536890415881525191820),
  (13602, 13812299062274017684053877900),
  (13634, 13951075828130728223934551250),
  (17826, 10100296909074393485154247820),
  (18850, 11338236944757236762187457612),
  (18657, 13813559795719141522236847181),
  (14626, 13812299136060993974647444620),
  (14658, 13949870671229807812444738130),
  (17858, 10100296909074446667632899282),
  (18882, 11338236945910158262549664844),
  (18625, 13813559785235935932514620492),
  (15618, 13812322538043109093633979601),
  (15650, 13812299136079003975110415436),
  (15682, 13969214437791430523654820937),
  (18914, 11338236945910153864503153740),
  (18593, 13813560677665543807316866126),
  (16674, 13812350859416884116944901196),
  (16706, 13911195443182894062559351881),
  (18946, 11338236947224638361457947855),
  (18561, 13813560676351341808564626509),
  (17698, 13812350859416321166991479948),
  (17730, 13911185998449928323365418125),
  (18529, 13813560676333327206277763601),
  (18754, 11240611604176986522110439889),
  (13409, 13812624831537648774780085388),
  (14433, 13812927062995362701183341708),
  (15457, 13812927062991096817392604236),
  (16481, 13813229302481600608159741004),
  (17505, 13813229302736031164723704972),
  (19553, 13813560750120303501099192848)]

theorem tbl19_2_ok : tblOK 19 tbl19_2 = true := by decide +kernel

def tbl19_3 : List (Nat × Nat) := [
  (12547, 7567943083779483548246660171),
  (12579, 7583625921150718178583983179),
  (12611, 7602973456701966877924553937),
  (12643, 7622623227038223021877552205),
  (16771, 10098503215520714265337844811),
  (17795, 10098503215520705469244822667),
  (17666, 13812323333558947272358393042),
  (17665, 13812323347357650393370801292),
  (13571, 15050262563512016708272186507),
  (13603, 15050249367134977440002684046),
  (13635, 15073264989016415168690930258),
  (13667, 14972897003892540179695334542),
  (17827, 10100627542568795918966781070),
  (17634, 13813230027923613782742193292),
  (17633, 13813230027923613783815935116),
  (14627, 15050248620079339987729699979),
  (14659, 15073265868766120141969765519),
  (14691, 14973501466802347494249133197),
  (17859, 10100627542568795924251604109),
  (17602, 13813230027923658246369604818),
  (17601, 13813230027923658246369866962),
  (15619, 15050262563332440958088041547),
  (15651, 15050248620097349988192670795),
  (15683, 15073568100221023799183467593),
  (15715, 14973501540824904875624383697),
  (17570, 13813230027923658244239422674),
  (17569, 13813230041722361365251830924),
  (16675, 10177995040158573219272213709),
  (16707, 10083112810062898538609394893),
  (16739, 10098503215738835244679722193)]

theorem tbl19_3_ok : tblOK 19 tbl19_3 = true := by decide +kernel

def tbl19_4 : List (Nat × Nat) := [
  (17538, 13813229302736031846532674770),
  (17537, 13813230041722079890275382413),
  (17699, 10177994892293579975781315725),
  (17731, 10077931996756826533507412368),
  (17763, 10098503215702806447660758226),
  (13441, 13812624683981710583613154444),
  (14465, 13812926915439424510016410764),
  (15489, 13812926915435158626225673292),
  (16513, 13813230026516305501259904076),
  (19585, 13813559711445877378151096722),
  (13442, 13812624831774359394735416460),
  (14466, 13812927063229263047784453260),
  (15490, 13812927063247273048247424076),
  (16514, 13813229302772060643551638737),
  (18562, 13813560676351341807490884685),
  (12612, 7606632248301932674932331595),
  (12644, 7622623208470197941893391437),
  (16772, 10098503213214871256140928075),
  (16643, 15050263372662235364934341707),
  (16642, 13812323333594976069377357009),
  (16641, 13812323332151594529378612300),
  (13636, 15073265062821607634251306126),
  (13668, 14972897003910541385139025038),
  (16611, 15051170067245014063868859467),
  (16610, 13813230027686959916501488716),
  (16609, 13813230027686889016389325900),
  (14660, 15073265869919323121552536719),
  (14692, 14973501466820357493638362253),
  (16579, 15051170067245067247420994769),
  (16578, 13813230027687522866438132812)]

theorem tbl19_4_ok : tblOK 19 tbl19_4 = true := by decide +kernel

def tbl19_5 : List (Nat × Nat) := [
  (16577, 13813230027687451897623270476),
  (15620, 15050262415758488368428405835),
  (15684, 15068684739726945432179106893),
  (15716, 14973500351963343389060817997),
  (16546, 13813230027959687041258386641),
  (16545, 13813230026516305501259641932),
  (16676, 10177993852449088743666406475),
  (16708, 10078234244568236274758739151),
  (16740, 10098503213432992235466290385),
  (14497, 13812926915421410111506928780),
  (15521, 13812926915417144227716191308),
  (19617, 13813559711445595903174386066),
  (14498, 13812926915421410110433186956),
  (15522, 13812926915421691516690420812),
  (18594, 13813559785235935796166186060),
  (13701, 21358706888617582510853928079),
  (15587, 15050263608003387944193307725),
  (15586, 13812322452511884202103067724),
  (15585, 13812322452507336913128838220),
  (14725, 8864199469854453266144621709),
  (15555, 15050868070913195257706918989),
  (15554, 13812928031628426103990551761),
  (15553, 13812322747637218897879159884),
  (15621, 8706094800517425027579397326),
  (15749, 8859655601002283378311746635),
  (6305, 16152539060192711367580480654),
  (14529, 13812322747641493577729365132),
  (19649, 13813559785232290723035881810),
  (14530, 13812927957859464207661827282),
  (18626, 13813559785235935931440878668)]

theorem tbl19_5_ok : tblOK 19 tbl19_5 = true := by decide +kernel

def tbl19_6 : List (Nat × Nat) := [
  (14531, 15050867997144233361378194573),
  (17603, 15051170067209038450402030802),
  (7329, 17585989121955542374432175244),
  (19681, 13813559780621167654561915282),
  (7362, 17585990145820717465512755794),
  (18658, 13813559782930092786952492108),
  (17635, 15051170067208985266849895563),
  (8385, 17585989195723616891862840460),
  (8417, 17410359747048912256437363657),
  (19713, 13812351223901078933294097420),
  (8386, 17585989195723616890789098636),
  (8418, 17410359747048630781460653001),
  (18690, 13812351225035986721200436433),
  (17667, 15050263372662226568841319563),
  (16644, 15050263370356392355737424971),
  (9409, 18728136548583183947328205836),
  (9441, 18728093452341933499250160650),
  (19745, 13812350785625981273999679890),
  (9410, 18728136548583183964487103500),
  (9442, 18728093452632389555333649616),
  (9474, 18843310426752885121453159632),
  (18722, 13812350859416321166991479884),
  (9475, 18843575315156516618542793933),
  (11588, 20100819498404376223526216781),
  (11587, 20100895565821424961489527881),
  (11555, 6345685881865337903685121100),
  (11523, 6330003044494103273364313164),
  (10465, 6310357629727510269994517515),
  (10497, 6329699701493747562232722441),
  (10529, 6348990861489826945890567179)]

theorem tbl19_6_ok : tblOK 19 tbl19_6 = true := by decide +kernel

def tbl19_7 : List (Nat × Nat) := [
  (10466, 6310357629727581513620177931),
  (10498, 6329699701784506737630458891),
  (10530, 6348995600145526058438649040),
  (10499, 6329700816498575938280776912),
  (10531, 6348995600145526047784907787)]

theorem tbl19_7_ok : tblOK 19 tbl19_7 = true := by decide +kernel

def tbl19 : List (Nat × Nat) := tbl19_0 ++ tbl19_1 ++ tbl19_2 ++ tbl19_3 ++ tbl19_4 ++ tbl19_5 ++ tbl19_6 ++ tbl19_7

def mask19 : Nat := 796055368252939402245311537131429693998494260074497548995947299946310074031878592400647343322749245529315265340086161982286214927193883756536571066949474241964360301701691661706758056750622496115208657879706445993836212567950045173687640883952410275695363312942904564566151554367007149840228268574548918837393324397211435858588922308793213617463548463757374781157237804867028010275901393875095317513493224875159658541040841150630090987124751039118241045473059738424346639266285760965502674197862738435265707804872376677276459742387942121978631560426552342230025352933039119181425530074230930561794248091548050483680863533572221438677740302041796055217700452912702756643060129287833734845242895033991724762415349812253944551923091943572971367295768945824480384492871366242779932032734087821501348464150248645068945816461812868016684416133630061804499573333531943453895961947467424479407579593023426538804001075788710287585917140398673129110955678072507183112842119741721828322624191705226705514646783066516541446444861982264281275231542348199219980937783745918405791333224043590611997348009125915643392097036700420275236890489247739685159918271967346888421443418395213758483022596875782419790041181880865257081180680984891894099118568154217455640508314092118915545921876477169312891627257018711726503327854966621638028979270332470386332281273232878162644987605141473196792255092402073513980062513174363816192569093163917687056424547093844524282388881704224951677664893601972351378270968159970043695854855854820045740687378973559122962583563831797599466237103690576853057758011149731625256789288292948789206366531573626021768694675787680831838354581710143348937000964771789099903844178795622503313422604833126560993430407648824697219793674037199823902224517123013140886116355706669486489844088177453094851655328898525124983927611166046837068688034907382536590478996248694570510872264127650436774960094425008597632592573928942322407040562388575145884832485244413757850205867262215830900000472507919795831157098766619657844147563754217242778387848954844880737777830356093178660129437811976547375375380779804739161201527337472958935925008778601462703837923943379244840121204221285177157354606403841492496856932750274262676101158159679604917810364137760969428317008008775873487380695812179076578421607240714951108793688568506977399905157383982343337461205572471011428029231163535475548563705693738386716225870173943596818379404884180731275725593648401702233085406872655359985334688398277505087464653243792434463632914445770296803938695197648921039438263261339983851363741450775430427513174242311854037551169176633662649043104866228003609137156109519478022802795770553545781142053518799623960547947182787498850480832437131950929652817575373392785999424817091557585869305505351895741358895341403545058162773380928849824185385283978049866979808721257708212356964470498310962288888524679593998735359201017329248397104712323833212524246301879935277380789883117309452188069192773552406473345172093107344589580381625422034878279559568952632861233929768192808912740289456677178574324742277865371840997278163953002596138280630515516656318660227740803860650687672527002753985026568053261733778038966502859422537751787128064946793919888427985527261814394853124163841901266711891164416344670058901319574547670936689096233847506148853596052346720385181509436826763947476796869443070589714122211398295256839693891830361272458021597979312298251352329557932196487408681260493764999932715540837317234335903932948341595115953992896246443836203784183888659010299495076276653973580979242937638852189039583827575396907774858377384944790741975523252712391266542890583440616138548348501867814470271326094456631518324157950647985645889578952594596021518977268042253215024468731165284098040491629046031472576652001010638146464429803791608779054138356465171639432185240479686204006874398192737765996543671784919670068211791402191682920921182327634405190508878019825591800838776751679736951492960650619911527048193345809402746024177509626202429491327260447977629341539481802331364001352579126706651628789724755475516061213356961827943723439132696747699687192164209201168725772576889118203229773513230220370768432990265300954708716880025493446180561006960607001695401213769334931738945980221612083766864368159120987076949744854131945882386969434106852594480504654072524888297207682069684959780960770598194679088494153670849513986279013512461654613798373234221672753728037509505205253274358339203793860680730865049514863154734497637852176363793654890063600120785111169875656012456098524829343014284733755282960330143371954367470190465993915697328714255799440005382619427699007850510573634382293587004117512288904131875314263281799838410961665251288751803875902747304761145176565802432832029826919935110413755357077830168902079411752235902521339456087818844219315566057053215441189941349882363099177365379487812146579809631088326420105995061149705520405093806178763725968522009989536997561024851190020794802946236484199894681306983566294328599423711430954875894282045608453065327813270718821805732953352579305047716055585000974182419387699650234022512097153082943503881432131892489357818335954348817139991584776738368466977021349589316506288704063671626300299843098822727583471569741549077631244182413460051757260307321588240932413706895370279432272244839589402514386938766944942932021021434209185262077540974141872386320808222771746249790142727477640504789203245581310411656447316028445296056488126058602318356069079562494000080563906177569976608849390350404738974504825156267340944802525307137864059774229168079191345036221414354310861506023141997085503081529484741978614765902584009435703132116685457664254767009433535496486765104749676041319870028060195637202066964166648354590081182619891717314096843597052010063156268457440507101389176675107073967087523754538269138578698813996944754877553931041866688883352680626867769169187907968989158235093031299528575773656813126340917076897290804936846168704062082709338267860580102177763356746807753708499107840

theorem mask19_eq : maskL 0 (tbl19.map Prod.fst) = mask19 := by decide +kernel

theorem cov19_1 : coverX 19 mask19 1 = true := by decide +kernel
theorem cov19_2 : coverX 19 mask19 2 = true := by decide +kernel
theorem cov19_3 : coverX 19 mask19 3 = true := by decide +kernel
theorem cov19_4 : coverX 19 mask19 4 = true := by decide +kernel
theorem cov19_5 : coverX 19 mask19 5 = true := by decide +kernel
theorem cov19_6 : coverX 19 mask19 6 = true := by decide +kernel
theorem cov19_7 : coverX 19 mask19 7 = true := by decide +kernel
theorem cov19_8 : coverX 19 mask19 8 = true := by decide +kernel
theorem cov19_9 : coverX 19 mask19 9 = true := by decide +kernel
theorem cov19_10 : coverX 19 mask19 10 = true := by decide +kernel
theorem cov19_11 : coverX 19 mask19 11 = true := by decide +kernel
theorem cov19_12 : coverX 19 mask19 12 = true := by decide +kernel
theorem cov19_13 : coverX 19 mask19 13 = true := by decide +kernel
theorem cov19_14 : coverX 19 mask19 14 = true := by decide +kernel
theorem cov19_15 : coverX 19 mask19 15 = true := by decide +kernel
theorem cov19_16 : coverX 19 mask19 16 = true := by decide +kernel
theorem cov19_17 : coverX 19 mask19 17 = true := by decide +kernel
theorem cov19_18 : coverX 19 mask19 18 = true := by decide +kernel
theorem cov19_19 : coverX 19 mask19 19 = true := by decide +kernel

theorem cert19 : Cert 19 tbl19 := by
  refine ⟨by simp only [tbl19, tblOK_append, tbl19_0_ok, tbl19_1_ok, tbl19_2_ok, tbl19_3_ok, tbl19_4_ok, tbl19_5_ok, tbl19_6_ok, tbl19_7_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask19_eq]
  interval_cases x
  exacts [cov19_1, cov19_2, cov19_3, cov19_4, cov19_5, cov19_6, cov19_7, cov19_8, cov19_9, cov19_10, cov19_11, cov19_12, cov19_13, cov19_14, cov19_15, cov19_16, cov19_17, cov19_18, cov19_19]

/-! ### `N = 20`: 255 witness orderings -/

def tbl20_0 : List (Nat × Nat) := [
  (11489, 403882183376855065851863581640),
  (11521, 405120478182586802172989592652),
  (11553, 406358366055578332671790597194),
  (16737, 958323374783443576962824594573),
  (17761, 958323431082978005392609567885),
  (18785, 725530521714954661605100536081),
  (19809, 725530517139839261939054199314),
  (20833, 731817579037057827349813535950),
  (12545, 883988703662743162271535522957),
  (12577, 883991115836351504644828095629),
  (12609, 486590306021420688312066167947),
  (17793, 646419058394800666775953400973),
  (18817, 725647221952530737884140487886),
  (19841, 725647221952530737884140487822),
  (20865, 799923591165376354791743562957),
  (13569, 883988703662743162271535522956),
  (13601, 883991115836351504644828095628),
  (13633, 958379953019388800282773222542),
  (17825, 646419058394800666775953400972),
  (18849, 725647221948892665283559355598),
  (19873, 725647221948892665283559355534),
  (20897, 799923591165376354791743562956),
  (14625, 883986842461497046051421213772),
  (14657, 958379906232667214654198576333),
  (18881, 725647221653744760041845626063),
  (19905, 725647221653744760042113213711),
  (20929, 801161531204661783236594709580),
  (15649, 883986842461497046051404436556),
  (15681, 958379906232667214654198572237),
  (18913, 725647221653744760041845626062)]

theorem tbl20_0_ok : tblOK 20 tbl20_0 = true := by decide +kernel

def tbl20_1 : List (Nat × Nat) := [
  (19937, 725647221653744760042113213710),
  (20961, 801161531217436176845770360017),
  (16673, 883986846743465317995629331532),
  (16705, 958379910954958477956813481101),
  (19969, 725650224478210104264499938573),
  (20993, 802402506913904225911225984205),
  (17697, 883986846743465317995632443668),
  (17729, 958379910969927619517411812493),
  (20001, 725650224493323048945044767886),
  (21025, 802402506913904226649993957840),
  (18753, 731836921850171661416341247182),
  (21057, 803640446968305982027876540947),
  (19777, 731836921850171661416608834830),
  (21089, 803640446968305982027876606088),
  (13377, 884007989218409520779479803020),
  (14401, 884027332031448210718013051980),
  (15425, 884027332031448210717996274764),
  (16449, 884027331738609794388811891217),
  (17473, 884027331738609794386664407570),
  (18497, 884030699153779837847144563788),
  (19521, 884030703886594956824512836749),
  (20545, 886560352527946026065466811597),
  (12546, 484367983528451749387852591700),
  (12578, 485352063663348641639355991051),
  (12610, 486590306021420763677853799563),
  (12642, 487847891091528998771181544589),
  (17794, 646304211325022004344265954443),
  (18818, 725531429452404757827305657419),
  (19842, 725531429452404833260722508875),
  (19745, 883986842168367937126142099986)]

theorem tbl20_1_ok : tblOK 20 tbl20_1 = true := by decide +kernel

def tbl20_2 : List (Nat × Nat) := [
  (13570, 963216804064823455165361218699),
  (13602, 963215958529213068451993674891),
  (13634, 958265105066436258324278207627),
  (13666, 958265407297980389534257443982),
  (17826, 646440162724403849136287315086),
  (18850, 725668325238520637987258950161),
  (19874, 725666516500730600026886431883),
  (19713, 883986842168367937126142100050),
  (14626, 963215911668973516757757121739),
  (14658, 964708674812790211288252600915),
  (14690, 958304098688672524689666265683),
  (18882, 725668325238629067134692553933),
  (19906, 725668325238629067134692553869),
  (19681, 884064496615561140584377025676),
  (15650, 963215911668973516689037645003),
  (15682, 964708665368056137241241637459),
  (15714, 958304098686365573372732035667),
  (18914, 725668325238629067134692549837),
  (19938, 725668325238629067134692549773),
  (19649, 884064515577338279251171918354),
  (16674, 963215916027034264347568297035),
  (16706, 964728008181171079615757472338),
  (16738, 958323374783443651589793965197),
  (19970, 725668325238649604987549705357),
  (19617, 884064213420823273393323295250),
  (17698, 963215916995197850439400871051),
  (17730, 964670584204739384729958928978),
  (17762, 958323431085287824154063594637),
  (20002, 725668325238649886458515083728),
  (19585, 884064213273572168405664203916)]

theorem tbl20_2_ok : tblOK 20 tbl20_2 = true := by decide +kernel

def tbl20_3 : List (Nat × Nat) := [
  (18754, 731858025435055968509188170957),
  (18786, 725530823873470655824968352844),
  (19553, 884063907658183686294895658125),
  (19778, 731858025435055968509188170893),
  (19810, 725530819149951251110342738450),
  (13409, 884007989218409520710760326284),
  (14433, 884027332031721170389483443276),
  (15457, 884027332031721170389466666060),
  (16481, 884046674404436793530841646156),
  (17505, 884046674404436793530844758292),
  (18529, 884063907658073682979453976849),
  (20577, 886560352527946027093070456013),
  (12547, 484367983528451749387852587604),
  (12579, 485352063681706404643284210957),
  (12611, 486590306021710928305441031309),
  (12643, 487847891110104683523837822226),
  (17795, 646304211325022004344249177227),
  (18819, 725531429452368733428333204555),
  (18722, 963215916995197770607937508427),
  (18721, 883986846743483336792188436753),
  (13571, 963216804064823455165344441483),
  (13603, 963215959719152406611654407310),
  (13635, 964689936462495902060855444623),
  (13667, 958265408487652326549694248078),
  (17827, 646440162724403849135213573262),
  (18851, 725668325238520633589212439057),
  (18690, 963296342500486872726674125265),
  (18689, 883986842168367937125069145161),
  (14627, 963215911686249038094328190155),
  (14659, 964708660645600426805052912585)]

theorem tbl20_3_ok : tblOK 20 tbl20_3 = true := by decide +kernel

def tbl20_4 : List (Nat × Nat) := [
  (14691, 958304098688672524963220092109),
  (18883, 725668325238629067134675776717),
  (18658, 963296343237184876160538174669),
  (18657, 884064520299704762461190685772),
  (15651, 963215911686249033696281679051),
  (15683, 964708660645600426805052891731),
  (15715, 958304098686365855121245537485),
  (18915, 725668325238629067134675772621),
  (18626, 963296343237186564869738259661),
  (18625, 884064520299704762461193290193),
  (16675, 963215917216830929551936275533),
  (16707, 964728003458714314270923048079),
  (16739, 958323374802108740247386907789),
  (18594, 963293288247653106875118703691),
  (18593, 884064217995938673059369632017),
  (17699, 963215916995488015065931138189),
  (17731, 964670579482282619385124504719),
  (17763, 958323431085287824154046817421),
  (18562, 963293288247653106943838180427),
  (18561, 884064217995938673059366765644),
  (18755, 731858025435055968509171393741),
  (18787, 725530823873452641426458870860),
  (14465, 884027322588141126154799862860),
  (15489, 884027322588141126154783085644),
  (16513, 884046664959703827791551480908),
  (17537, 884046664959703827791551464716),
  (20609, 887798293372979705375056471244),
  (14466, 963255494562108452294751970579),
  (15490, 963255494562108447896705459475),
  (16514, 963274837215001957795397424203)]

theorem tbl20_4_ok : tblOK 20 tbl20_4 = true := by decide +kernel

def tbl20_5 : List (Nat × Nat) := [
  (17538, 963274837214947918997915489419),
  (19586, 963293288247653182308552332363),
  (13636, 486844170614919989793242801292),
  (13668, 487847891090380333330090484876),
  (13700, 1349512436642356784128488170635),
  (17828, 646304211322716161335052256395),
  (17667, 963216861382079354718424978571),
  (17666, 963216861382079354718441755787),
  (17665, 883988636520362325591168434452),
  (14660, 1043935330965861168555463083215),
  (14692, 1044938995008313048349514204367),
  (14724, 1052578499335836714916034704587),
  (17635, 963274889821656978350837154957),
  (17634, 963274889821366193956263613579),
  (17633, 884046669754399233658586727692),
  (15684, 1043935330965861168555463083214),
  (15716, 1044938995008313048349514204366),
  (15748, 1052520470527561175803827139595),
  (17603, 963274889821656978350919992461),
  (17602, 963274889821366813723332760715),
  (17601, 884046669756705076667919679824),
  (16676, 636437516331467330787864822859),
  (16708, 645257531277803139293713818897),
  (16740, 646304145519939138597749028110),
  (16772, 646304144551503656611900085323),
  (17570, 963274889821420856918827652235),
  (17569, 884046664959703827791554330900),
  (17700, 636437516331467330787864822795),
  (17732, 645261800572491377133933880460),
  (17764, 646304145519939067819073257936)]

theorem tbl20_5_ok : tblOK 20 tbl20_5 = true := by decide +kernel

def tbl20_6 : List (Nat × Nat) := [
  (17796, 646304211322716161335052260491),
  (14497, 884027322586988204650193015884),
  (15521, 884027322586988204650176238668),
  (16545, 884046664959703827791551218764),
  (20641, 887798293372979423900079760588),
  (14498, 963255485101036999063865709771),
  (15522, 963255485101036999062791967947),
  (16546, 963274832492635474925752210507),
  (19618, 963293288247653182308535555147),
  (13701, 1349512436642338769729978688651),
  (16644, 1042444957122825344579619832907),
  (16643, 963216804053293972725349536843),
  (16642, 963216804053293972725366314059),
  (16641, 883988636520362325591165322316),
  (14725, 1052578499335836710517988193483),
  (16611, 963274833461071211246613251149),
  (16610, 963274832268735628845970936907),
  (16609, 884046669754395591874232505420),
  (15749, 1052520470527561158214862320651),
  (16579, 963274833461071211246696088653),
  (16578, 963274832271274546041271145547),
  (16577, 884046669756701153408469488716),
  (16677, 636437516331467330787864560715),
  (16773, 646246125556895120150804616267),
  (6305, 1125503322693468070052048729292),
  (15553, 883988655849073546353120695372),
  (20673, 889035930522635603258452530252),
  (15554, 963255556612231472788098057421),
  (19650, 963296343237186566052896847117),
  (15555, 963255556612231472788081280205)]

theorem tbl20_6_ok : tblOK 20 tbl20_6 = true := by decide +kernel

def tbl20_7 : List (Nat × Nat) := [
  (18627, 963296343237186564868664517837),
  (15587, 963216870986003804723210159309),
  (15586, 963216799474809330929201370315),
  (15585, 883988636960760536516585641036),
  (7329, 1125503303805155060078108275916),
  (20705, 889035931180809948687637230668),
  (7362, 1131712375753074761342971073043),
  (19682, 963296343237189688305008805137),
  (18659, 963296343237184876091818697933),
  (8385, 1205969411079900258205963179084),
  (8417, 1205969411079864229477663691852),
  (20737, 890273871220278001743911764243),
  (8386, 1205988753893014087874727957707),
  (8418, 1205988753892974755869901247691),
  (19714, 963296343764289805073520570580),
  (18691, 963296343233726384598331745485),
  (17668, 1042445023894037849302772008075),
  (9409, 1198404260931441880995807928784),
  (9441, 1198404265653611049975515231242),
  (20769, 890273904065586502536901436622),
  (9410, 1198404260931441599520831218128),
  (9442, 1198404265653593035577005749258),
  (9474, 1210940575968846212209026352334),
  (19746, 963215916995197846041354359883),
  (9475, 1210940575603370077316113818829),
  (18723, 963215916995161746208965055563),
  (12644, 487847891090380333330090484877),
  (12612, 486844170614919989793242801293),
  (10465, 403882183376855065859279111112),
  (10497, 405120478108710317727752963147)]

theorem tbl20_7_ok : tblOK 20 tbl20_7 = true := by decide +kernel

def tbl20_8 : List (Nat × Nat) := [
  (10529, 406358366055578332671790597195),
  (20801, 731836921850171661416608834766),
  (10466, 403882184641482686155436331284),
  (10498, 405120478108710392420254139467),
  (10530, 406358370795385844980150723857),
  (10499, 405120478127320919733197890833),
  (10531, 406358370795385844980150461713),
  (11588, 1270283967926211747956229174542),
  (11587, 1291408774138257868376724751503),
  (11555, 406358370795385810197375697996),
  (11523, 405120478201107925649387169041),
  (11586, 1291408778860714633721559175762),
  (11554, 406358370795385810197392475212),
  (11522, 405120478182586877757682697292),
  (11490, 403882184641446657358417629460)]

theorem tbl20_8_ok : tblOK 20 tbl20_8 = true := by decide +kernel

def tbl20 : List (Nat × Nat) := tbl20_0 ++ tbl20_1 ++ tbl20_2 ++ tbl20_3 ++ tbl20_4 ++ tbl20_5 ++ tbl20_6 ++ tbl20_7 ++ tbl20_8

def mask20 : Nat := 2639845790380455958078398707509281996358058270155977385663865157160052458554089383949333366927389649009172357185441552893392204328128096717847465360602196904358023410167113013321668261263214031937454573263656113145065911224103956238262218399214347243812697594843341145572597349782899037176800947313369631850930193953606219182251221931641393962639370028665439691403774738095009112833882925581279986982221456396936994915211634600278563665243604622569247101787374244531189046460870937508573968254509207076060340900572646583859162974371896047721398420498185008418862118573976391549659395318973321331391726503873129211964834962313299777117154654808570566332645814069441491085786773143312844616489737409892793414529892562224489231205785981162763046141951792524237928536621522997966344123202266940211640460819601103618983398886123644417592400603032945912759070714002846983611590311868193909217718886413241165105013448920583231479571073865136928165096467456556986584628345216654706720906101421253041273671721865430555727336406415285207233795381058897497228882453189720064986766783501029154935167664935974975772267108182506119927824432772441514490284440710485210079869775826808963002877254031891846134978834043716108328152261698308115530698383710468987222726185365046277687954898358822359254879068318547480941545934539397520512600497742915816946774788145337110068344687580773673308235985886946336684026838585699424645868502292379583272777550723466543302473056470961392614022244533937073395536005381247511423581821846943468213529682790436209992336051351492511986892090604965916143626336942567704958146251537401432621943921025982993814934372967137384709989900025938101043830931811137291841674461676036995226569137874938845139087046690214222979067233846106696737727816455689024233698438631150565224433449071809450589629315690482943898252358219729606845841564628581900129307012360994700738595931118699988716418139085831649048390707092223430321003680033677277426651501001192696622432533147570516459977755525539294139920586652696853326755008220751607728036677415810182799176720165468465026625122569403980850971455495524067309302767291635062550410783305046316293308467607158302093622850615328884838116222318980957745851930741975314232676373558977630403793617557093320530132409126317056036630968423754705366163955147241439503804938764234948765452059771365548249864281753106594019230124783612461420441641145185385848256321704593729410332802379747820799790735454875708900078331485246730743319639270093582870473082367293779238225384206777136434575287761563106060558450994629306468410563942437995695811436698809018247484307700055185489068674870581516256932111438989205164469842042670379584189083488156795268734193837450920274006131484826646596143386924652766651025262014221439524964784522542651903029848868286778647163981705839315546772478236336552040425649616356513850202647879961070611026841239386022123654110915523936380186805390480952572583312288902044062546384672661986568381002773719362315039196007050510384836817041681116800956056362329965056556054035269548671426637482238900065463683439414068653805718904044633573018180046955982432811045446542538851229273850634803032627424870878577817042802564926738771823904458490917097669135113783616285419906215451271588321969269714299122494421664248206791438623159724399889694441766333970593819332972961303329037018786130372933198026915544221754813400005668221155663849313843899876077104294652189438364875350904241290845109808004821291533014021161362606852367947797210403235573063176984349668389126889387011696400504140478055518940908922679482965405251231406473584106471358884557408383879585062449666833531305287514101027463590380285618161519677462254490344819600609538271356844381349698240661107961681513579014799251680892189691909030226620808256276451238608860365879595541424754956724731953042999543020392158980128753159250268148267907536223653307155975945621581991438122638238006429951688819663520149694034436121807658562169402072084272380434135209486633454376273595051939425650347979422715350221220782056181267511972014880969090433942090930629629079654143694696946292447866004202800806174265744677077642446067553064329073761654715804335377726266705785685393425253257841950488388226434746499189823272680076942247226704943231192478181909914070694087779168354442527857474588008719726717078316580495571850973805342129640316466004717001771518364131201373117353757612297519029088564718132990071849379261889026897947496209684024844740395354575014902183592447138268733044217496573795213464144171946016327137240116664165553806025924746042071497556658252767988160095441331743974488972105093316137935336801979604026329410448603103270688747644871718324762180637323917246546517357601164562737915695875114009774179997524228864241416911037723538088448749358248056704569474093958632476545287621512385283490362379141216530695773226667707804327756183206765876481624864146886523986026368360216884102529284869358052653764413878585185083740266872118688509553868876719735048152412232941645092018175072974979399137419392260852518314145627725895114110981376639932005690831509393057856241776959853742154386174128007846867801683132595038450389383718014490887771189357954025646575778094716733638340181342087627390651877412515234043279528163243056974530551991046574518859104075368066844921390641882071876810167221460872060703860571529323530772557174671582178289623407458545993175160072067303957475804718838789528910260989246942223821429034316469834773323982376434521958730013487449856127215704116620022302870777390388954354102179437579008374804464187609463817562388326034203881577419276815081356106898612052839774476374975071263275586175138625094097407194516994862880199018586402693196371554054716149437155420126647616106852832475280937045602346776768676017298182449996017044070335221143088028697240628421080638609401188252767198894976476637634967392607655605093323128790517264935820682336470561386438597730002693284176262433960281380553520506091542510115142691787531658828955972177152435053389136036479113123150729621327112440876806933253678165129368507226696371606230830332420262621529187458918864989486820310073372115383070882700180635265712147539664874446222762381490814929175586280278501703036709106783663378469066550534425746609105366644459597327323521657766068489559027455884146926018771249394302403119351713721428790964830021081219928686592

theorem mask20_eq : maskL 0 (tbl20.map Prod.fst) = mask20 := by decide +kernel

theorem cov20_1 : coverX 20 mask20 1 = true := by decide +kernel
theorem cov20_2 : coverX 20 mask20 2 = true := by decide +kernel
theorem cov20_3 : coverX 20 mask20 3 = true := by decide +kernel
theorem cov20_4 : coverX 20 mask20 4 = true := by decide +kernel
theorem cov20_5 : coverX 20 mask20 5 = true := by decide +kernel
theorem cov20_6 : coverX 20 mask20 6 = true := by decide +kernel
theorem cov20_7 : coverX 20 mask20 7 = true := by decide +kernel
theorem cov20_8 : coverX 20 mask20 8 = true := by decide +kernel
theorem cov20_9 : coverX 20 mask20 9 = true := by decide +kernel
theorem cov20_10 : coverX 20 mask20 10 = true := by decide +kernel
theorem cov20_11 : coverX 20 mask20 11 = true := by decide +kernel
theorem cov20_12 : coverX 20 mask20 12 = true := by decide +kernel
theorem cov20_13 : coverX 20 mask20 13 = true := by decide +kernel
theorem cov20_14 : coverX 20 mask20 14 = true := by decide +kernel
theorem cov20_15 : coverX 20 mask20 15 = true := by decide +kernel
theorem cov20_16 : coverX 20 mask20 16 = true := by decide +kernel
theorem cov20_17 : coverX 20 mask20 17 = true := by decide +kernel
theorem cov20_18 : coverX 20 mask20 18 = true := by decide +kernel
theorem cov20_19 : coverX 20 mask20 19 = true := by decide +kernel
theorem cov20_20 : coverX 20 mask20 20 = true := by decide +kernel

theorem cert20 : Cert 20 tbl20 := by
  refine ⟨by simp only [tbl20, tblOK_append, tbl20_0_ok, tbl20_1_ok, tbl20_2_ok, tbl20_3_ok, tbl20_4_ok, tbl20_5_ok, tbl20_6_ok, tbl20_7_ok, tbl20_8_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask20_eq]
  interval_cases x
  exacts [cov20_1, cov20_2, cov20_3, cov20_4, cov20_5, cov20_6, cov20_7, cov20_8, cov20_9, cov20_10, cov20_11, cov20_12, cov20_13, cov20_14, cov20_15, cov20_16, cov20_17, cov20_18, cov20_19, cov20_20]

/-! ### `N = 21`: 298 witness orderings -/

def tbl21_0 : List (Nat × Nat) := [
  (12545, 31789276296134845972129504355469),
  (12577, 31078798756993880614578137916557),
  (12609, 31158023580717777866192147764363),
  (12641, 31222264968831467479812650886285),
  (17793, 41442713072638095657652513465485),
  (18817, 46513315459824244244006945739221),
  (19841, 46513315459824244525550641926610),
  (20865, 51192849119757668751076572325005),
  (21889, 51192849119757668751076572062861),
  (13569, 61725127247614344424725966812366),
  (13601, 61725127247614255478633326245070),
  (13633, 61328967093194796141687115936974),
  (13665, 61328986435045328579767460754638),
  (18849, 46521885252280465831902078891214),
  (19873, 46521885252297974428723745977614),
  (20897, 51196462628414808945256607864015),
  (21921, 51196462627298691191623206314452),
  (14625, 61725127247614309521622696260813),
  (14657, 61328963726302219216716077257931),
  (14689, 61328983073837466753846794843341),
  (18881, 46521885252280519874891448906957),
  (19905, 46521885252297974441917835179277),
  (20929, 51275690790929055264053595821263),
  (21953, 51275690789812955529216750002580),
  (15649, 61725122662494127109443737937037),
  (15681, 61328963725197742088876981277835),
  (15713, 61328983072720576579534775706765),
  (19937, 46521885252280519874892522382477),
  (20961, 51275690789812955529199421285517),
  (21985, 51275690789812955529199421023373)]

theorem tbl21_0_ok : tblOK 21 tbl21_0 = true := by decide +kernel

def tbl21_1 : List (Nat × Nat) := [
  (16705, 61332676615304548728154667144331),
  (16737, 61332695986140393700874853082253),
  (19969, 46521885252280536785243901846669),
  (20993, 51354918953219652829484069459282),
  (22017, 51354918953219652829484069459218),
  (17697, 61725122662563082084800691233933),
  (17729, 61332680246495118140799676896395),
  (17761, 61332695986140388929954313987213),
  (21025, 51354922268162794249695919690894),
  (22049, 51354922268162794249695919686798),
  (18753, 61334053921583503961887553676493),
  (18785, 61333933898214325271652225831381),
  (21057, 51434150382716766492717454992717),
  (22081, 51434150382716766492717454992653),
  (19777, 61334053921583503961888627156109),
  (19809, 61333933898214325553195922018770),
  (22113, 51434150382716766418295452914130),
  (20833, 61335076333036651665414003413587),
  (21857, 46915553527839787524087406413069),
  (13377, 92153728439201362173350747894990),
  (14401, 92153728439201362190668056032461),
  (15425, 97224330840114279796655942329485),
  (16449, 97224330840104136564395180352653),
  (17473, 102296171172431282256029721900370),
  (18497, 102296171177142008896430927040981),
  (19521, 107366773578054926502486459339218),
  (12546, 30999552763277111859272311674194),
  (12578, 31078798756993880615813712766093),
  (12610, 31158023580718104935641821500754),
  (12642, 31222264968831472528971674215565)]

theorem tbl21_1_ok : tblOK 21 tbl21_1 = true := by decide +kernel

def tbl21_2 : List (Nat × Nat) := [
  (17794, 67520078634290746371270278730959),
  (18818, 46513315762074397807102587580885),
  (19842, 46513315762052258679092624544210),
  (20866, 51578890235466513344293243245011),
  (20801, 61334053921583503963050197968013),
  (13570, 61725122979714732223138096280782),
  (13602, 61725122965547632774666599593166),
  (13634, 61328967093194796142917405963470),
  (13666, 61328986435045328659530221155534),
  (18850, 46521885252280465911664839292110),
  (19874, 46521885252297974428722672235790),
  (20898, 51598892584537156049655078622546),
  (20769, 61725046788224660286074022843594),
  (14626, 61725122964725564078670300378317),
  (14658, 61741356468437020449313697600851),
  (14690, 61331462316387572531384055321807),
  (18882, 46521885252280519954860317406413),
  (19906, 46521885252297974441916761437453),
  (20930, 51592723421912563148376089859411),
  (20737, 61731215648617798283704190423635),
  (15650, 61725122964725582008634265625741),
  (15682, 61742592523594878163715472020052),
  (15714, 61331462617207690506223095960146),
  (19938, 46521885252280519870494475871373),
  (20962, 51592722227392407393255838463309),
  (20705, 61731217145391188081718616969811),
  (16706, 61742592523594949095409553822290),
  (16738, 61332695986140393700806133605517),
  (19970, 46521885252280536785175182369933),
  (20994, 51592722227153842982355850794322)]

theorem tbl21_2_ok : tblOK 21 tbl21_2 = true := by decide +kernel

def tbl21_3 : List (Nat × Nat) := [
  (20673, 61731217145607973353381723165267),
  (17698, 61725122964813150625045746111629),
  (17730, 61743811206480847402461874132306),
  (17762, 61332695986140393979113337316493),
  (21026, 51592702884340729148289055495506),
  (20641, 61731236488421087187448518464083),
  (18754, 61743811197036114436722583704915),
  (18786, 61333933907676603975325257576917),
  (21058, 51592702874895996182549765068115),
  (20609, 61731236488424509923165320041043),
  (19778, 61720095339819781439616929026514),
  (19810, 61333933907654464847315294540242),
  (20577, 61731236497865820153187808891475),
  (20834, 51988863039725164670323570546002),
  (14433, 61727603127619128500141137121811),
  (15457, 61727603429850583403867034145298),
  (16481, 61728841370858197040784039298189),
  (17505, 61728836180376800272870993613394),
  (18529, 61730074120490159747105628112205),
  (19553, 61730074120490177765902184105101),
  (21601, 61889788990067169839859616727636),
  (13571, 31000790703304886549277062784204),
  (13603, 31062532382294729105587832181836),
  (13635, 31141779887985277590300759979345),
  (13667, 31222265337784924529216201512143),
  (13699, 92635444534700434059632947037387),
  (18851, 46513319737995543743369629488332),
  (19875, 46513319737995538359357679920268),
  (19746, 61725122964791011497053063008722),
  (19745, 61725122662562997343511080391122)]

theorem tbl21_3_ok : tblOK 21 tbl21_3 = true := by decide +kernel

def tbl21_4 : List (Nat × Nat) := [
  (14627, 66795725365638482515887887021260),
  (14659, 66811862158979410267014076363347),
  (14691, 66876095680535762100685903299791),
  (14723, 67369030304446481146741435729099),
  (18883, 46523258271128074755614864377039),
  (19907, 46523258269714717659308874593418),
  (19714, 61729900941569064200029782701329),
  (19713, 61725124461344552185530285311117),
  (15651, 66795725365638499967336443077900),
  (15683, 66813099494555785839974388130388),
  (15715, 66876095680607243233971527812366),
  (15747, 67440845966270196364908307722516),
  (19939, 46523258270980733288161907660048),
  (19682, 61730074719715042308742181081618),
  (19681, 61730074710344419188343427110029),
  (16707, 66813099495509322570312386172175),
  (16739, 66876095982838702104119211496788),
  (16771, 67440850169538147015174560765201),
  (19971, 46523258270980733288567782069519),
  (19650, 61730074720225786535283014291922),
  (19649, 61730074710785647241163641770450),
  (17699, 66795725365726068231032558670988),
  (17731, 66814337430826241467717640082639),
  (17763, 66876095982912471066015540221267),
  (17795, 67520078332052411374345924183243),
  (19618, 61730074724948153018152659505618),
  (19617, 61730074422720138864610676888018),
  (18755, 46041545523550798588199069897804),
  (18787, 46447612193074040791267520632015),
  (18819, 46513315762074397807102587576789)]

theorem tbl21_4_ok : tblOK 21 tbl21_4 = true := by decide +kernel

def tbl21_5 : List (Nat × Nat) := [
  (19586, 61730074422721273771716774253010),
  (19585, 61730074422721291786115283734994),
  (19779, 46041545432868930540934170456466),
  (19811, 46447612193074040708117931828495),
  (19843, 46513315762052240664694115062226),
  (14465, 61727603127695221309691235988685),
  (15489, 61727598557635308071062450029709),
  (16513, 61728836497674593389016421295245),
  (17537, 61728836496407622503899438834829),
  (18561, 61730074422721291504571587547605),
  (21633, 61889788988877261191334111748564),
  (14466, 61727603127695221389522699089101),
  (15490, 61727598557635290056663940547725),
  (16514, 61728836497674575374617911813261),
  (17538, 61728836497747536252351307666573),
  (18562, 61730074422721614650762921776461),
  (20610, 61731236497864649217284692562515),
  (13636, 31159260916294480508601059530065),
  (13668, 31222265337764066169807132456275),
  (13700, 92635093979427171631908590519503),
  (18852, 46513319737847969790791663777107),
  (18723, 66795729341647214167316880774348),
  (18722, 61725122964813150625063026045397),
  (18721, 61725122662562997061967384203733),
  (14660, 66811856667016043102595005613263),
  (14692, 66876095680514870785478550160591),
  (14724, 67346552189305009172395525997775),
  (18884, 46523258269792183780858138002639),
  (18691, 66800681102995426296242119988428),
  (18690, 61730271822747928496623613130065)]

theorem tbl21_5_ok : tblOK 21 tbl21_5 = true := by decide +kernel

def tbl21_6 : List (Nat × Nat) := [
  (18689, 61725124461344534166733729318221),
  (15684, 66813099495510475772814154880272),
  (15716, 66876095680607243515445414003982),
  (15748, 67440846268576228398304629965834),
  (18659, 66800681101803202766019579143372),
  (18658, 61730074720247925662384729411985),
  (18657, 61730074710785646959620062237073),
  (16708, 66813099495510475773291968943375),
  (16740, 66876095982838702104184710010196),
  (16772, 67440850174261666423941490890001),
  (18627, 66800681101803202766911870424268),
  (18626, 61730074720247925663292977328597),
  (18625, 61730074710785646959619945583061),
  (17700, 66795724761263158423729682019666),
  (17732, 66791935397062285269780468655244),
  (17764, 66876095981574002109980983227598),
  (17796, 66086405689147063620566041031886),
  (18594, 61730074724970292146162622542293),
  (18593, 61730074422720138583066980700629),
  (18756, 46041506837924570902490455500112),
  (18788, 46447612193074004762470501930191),
  (18820, 46513315157611487999788000227797),
  (15521, 61727598556518436389855396160653),
  (16545, 61728836497674593388947701818509),
  (17569, 61728836496407622222424462124173),
  (21665, 61969017104620851609575564526861),
  (15522, 61727598556518436385457349649549),
  (16546, 61728836799906030278137766536333),
  (17570, 61728836799978991156827848996178),
  (20642, 61731236488419934265943911617107)]

theorem tbl21_6_ok : tblOK 21 tbl21_6 = true := by decide +kernel

def tbl21_7 : List (Nat × Nat) := [
  (14725, 36388338985494911909648796021965),
  (14757, 36388242261984614262957707429071),
  (17668, 66795724776311142805059969832078),
  (17667, 66795725380774052621921244706130),
  (17666, 61725122979861135016003151623506),
  (17665, 61725122676289766081599764751501),
  (15749, 72042269394600041679574350193936),
  (15781, 71550676961957230265154948896016),
  (17635, 66799439200891908705091379848332),
  (17634, 61728836798711948741266086618253),
  (17633, 61728836798711621671829393171597),
  (16773, 41460144290689058761564440831249),
  (16805, 41460087481501154777683056481553),
  (17603, 66799439200891908762745925301586),
  (17602, 61728836798711715667081057068173),
  (17601, 61728836798711710617922033738893),
  (17701, 41770786228516680368424588440912),
  (17733, 41280428132459226033363088074064),
  (17797, 41438999556091608451231202964818),
  (17829, 41438999556091608441615795704974),
  (6305, 72429611358018005983352973489357),
  (15553, 61725123885291898267502495458445),
  (16577, 61728836798711715388842572833933),
  (21697, 61969016802389396705918270850317),
  (15554, 61727603429779012194190815711826),
  (16578, 61728836798711715388773853357197),
  (20674, 61731217145606820431877116318291),
  (15555, 66798205836599445567737982944526),
  (16579, 66799439200820391600663281825108),
  (19651, 66800681101803197382899920856204)]

theorem tbl21_7_ok : tblOK 21 tbl21_7 = true := by decide +kernel

def tbl21_8 : List (Nat × Nat) := [
  (16644, 66795729956373319119686792975630),
  (16643, 66795725380702535459838601229652),
  (16642, 61725122979788174137313069163661),
  (16641, 61725122677556737248123004445837),
  (16611, 66799439200820391543008736371980),
  (16610, 61728836798711930928580866925709),
  (16609, 61728836798711930932978913436813),
  (7329, 77183300201153620442245689050381),
  (21729, 62048245011674334681371600020621),
  (7362, 77183304168669839642174659302672),
  (20706, 61731217145391170067320107487827),
  (19683, 66800681101803197361184566207628),
  (8385, 77183299596690455347032459904269),
  (8417, 76383435934362118015379162350601),
  (21761, 62048245011672028785806951900301),
  (8386, 77183299596838284587450968114445),
  (8418, 76383435934362117733904185639945),
  (20738, 61731215950848082251458367771219),
  (19715, 66800681101581729775136671851660),
  (18692, 66800681101655843565647234421966),
  (9409, 82253901997601124526422486217997),
  (9441, 82333130160129112189712628794509),
  (21793, 61332815981988003290056387257485),
  (9410, 82253901997748698479011055334669),
  (9442, 82333130160276668610940668798093),
  (9474, 82333134651232258555945324934417),
  (20770, 61725046788223507364569415996618),
  (9475, 82334372642921312344621118461198),
  (19747, 66795729341647208783304931206284),
  (18724, 66795729341499640214738915063123)]

theorem tbl21_8_ok : tblOK 21 tbl21_8 = true := by decide +kernel

def tbl21_9 : List (Nat × Nat) := [
  (13701, 92635093979427171627510544008399),
  (10465, 81852673699572894476542137123915),
  (10497, 82333130429513869727573633721485),
  (10529, 81535742910906176423860695516235),
  (21825, 61334053921583503963050197705869),
  (10466, 81852673699572894195067160413259),
  (10498, 81866506512053941202974483198417),
  (10530, 81535762325197955852431181005899),
  (20802, 61720095037292348556266868888019),
  (10499, 81866506861212724862015638922508),
  (10531, 81535762325197955570956204295243),
  (12644, 31222264964127714633530766873741),
  (12612, 31158022976255195128327234147666),
  (12643, 31222265049719417894080260089167),
  (12611, 31158023581981597692318257280338),
  (12579, 31078798756994190831524071896402),
  (12547, 30999552763277111859272311412050),
  (11489, 25849720381579493240102005822604),
  (11521, 25928945200210110928657574351881),
  (11553, 26008196351275644474657000739980),
  (11490, 25849720381579498372327877694604),
  (11522, 25928945201549787381280015388949),
  (11554, 26008196351370326174089006052690),
  (11586, 87483137874554929414431646192978),
  (11523, 25928950376531239117739203503440),
  (11555, 26008196351370326204394295031122),
  (11587, 87484222885423755871061886124629),
  (11588, 87484217383043963363143414273166)]

theorem tbl21_9_ok : tblOK 21 tbl21_9 = true := by decide +kernel

def tbl21 : List (Nat × Nat) := tbl21_0 ++ tbl21_1 ++ tbl21_2 ++ tbl21_3 ++ tbl21_4 ++ tbl21_5 ++ tbl21_6 ++ tbl21_7 ++ tbl21_8 ++ tbl21_9

def mask21 : Nat := 474563265446212994262423718257486107103666433486934611814901486897886424871394998571028290105951813800731693397470054939568090516532394283750637681819941000364082840994314943979930270734094955117595404605338192071464723135881460109312152845599407656456782945039392837728014486610030819551989114531515692172652804278896514714445122949477239222299244367876080131268984722815172492647472164535638965210962347056477813775474700461091651132530902884907174854058651972924529555183940669399605077172058379914230704462691945918126373249572989407167337865387742198763364910790167300941863690388115714544360934367335437023936208824748314579007347864558754237593781723861490499401518081407520430900365417300194941121636567712138996321810103494609008135075273995618141858582147002599896160062592516732963814460553270159473721614596795408999646441558405153159112577477472809758786940722857061388468068871262360018817050215203226411143751103513584959078264991128386883985705904476412899273878347877355561830414734750902417964497191329969253867222168142009819464165793678102429915140305651429303206705194211475425284739011882174652215412179698633791414788104820139984693294626579079754013093731643489904267544872989899371503147406929935216962082617337591212545586655595169715267796032975815634385624691798598952284714912994753063352394917647520380044479167825966213069473057253621902756398507862463273035328377265959567338669126590049958463419709461790640620629700291970465507865352365270932151488577727994595720481267688912983793004024456255523149526716719967500421676959137345157864601917798901040743365844579771436843129713433435926687337487882066504046070172411096618646901382676044867567346384869614301843630803580316980932629313349036816476557890721714735928880386882168384633651165133353283883887583007387306571624013677019660681390445164345086874840535546127914599525748848220460639746498863482693934763065974688768864091001029448901035449860783981809928543371458234016144863936285820786464303682571210134431135372441497259256776355781557080775945188492477659931355084888645941799591247377276311380670871804884635510848394752857068894232063483997266613818739247841099447949992009158700085916726587472409832664601853869916303922859684798176466787357263307033676475338189467695602003323154885752352073065986329176587482882250309293147678825289826702718238993521554056726280800000312689780502020397126376117013642816475913018885128981005751328370256026148955644588866847271646721021644590467968628884664023553675086611856250146219000953780544427010410050908684566900987480617253117560410442900340699723702229575229365890372122986214815441768895020831536062214153957848136788496055249842767901227487596851859808964824001178136752439309908103308437720244754008745915901098502542766450835840622383068639902052644725899066646227708007324780456907880251185970986998873483797618617332536003054099260999370819580539913575281328731436556583874683649250896172189116902472708510915377092914231324049813816461856754694120731770158850909396506316819824232705939163437005946114574696661347015727321630280264725232093536122994276677045519607209442741475589088811855350412579400945381448432211709528747121780679753354212069360374487845858535754910805686267321772725460772572429783563998794187201777209096271196612269078233717163801676347401125395260091768001223774385092073765041740357978714150891895656315209963539865977440133415872479684461858212618373445156527299594966243317280122345171505052489636196478755382867914777761451352070797473164649858721011903219081119743291300597174450518596596624281944443568952472096513940559051312475118975442301411578096584376197673653247065863062742794771356568637116177788677970136318346714213323759161229709811014075593543258274922212425305424948876880359932276313874258388417344587757666122682210894866115807629963244619022929656537397860836389305079024061211546642791875774668051360982020117804345861543716681872210186488715716519583385784221311415094537385386183083676182855060321760861112382692299013660116932695705710690227559864120854480216496193145089746223685394223555219066148367676177292292204297183957525928214518788173358705075086881593987893905058975506438105488378219735992213372971464670905630713426322259368441201836035603297915025761853009393591426624042382497656165907421968358030638742256070313705581282581995693710339767141746903046270488982997987656920814088311083101928801384543051666913527343154154066360817344221037507610801686515942086743679123322117443314388030303692612153134852549181321347644502487064105331228698591678732154825594264306918132067081434763805633405369124405716463592050729912243706109765763992742235476510640936233233121074151737843816448997360627998409852990129202984478642840801982830759724776686860990647835965263190313578131728173401289473626005295548576648289257931663324561341833672515321473931183447322309273002062572889555250251010268580501935221011800459826309500786569677073256530403273237975692393046249021365701323637743923911661453058122913531537855224954278562669840321239793528913394955431157284299510298254859534689722446330502697603056899481729584292005885278875912649312844252278380434086375864426849390531188792009104071708095844966539992974042716133944389802390885132542935424087085855327845299061786549275950472835383604795496228303126159349640314776563538639036633222531845341527117754550249129107740060253847310028408659405996469410837012866650337284098398848444866453339155515337740849146978163634492897627400095896753265515675052931413393505333287354936232895187332582596273808873521224550818943367011312114179784557976678119969242002105130253505148803685987056951851297073307655842802049263608802429404766328289843533095040492520224562324537047794695177399332550067265494470395462687960227037178995735081273052996314636951149563824349016476672087717019935112454504579090875270085862149726121275105840579493810853565561932646686018904549669493829645187224490814312145425379434987426264791143551910507445421868924570119283104290069469137613572814694059590602291033317686877829416881611511442907176335846307289975502047516368054315754300609529830478982722151731516784012252835345799528203318372218042187391617127019841247718884861421852717789999737512386736203167915433181013780135070741580153025845954187854094494406899037808558207903931098410197079134752728795247129802162065718551966992491157353171634228635818145283882086620047468759843808253839037091132488896321582820765897265798244383573619777800420465119113200513530894948889434409747132974313045635885996462473104578778793023913100767960421423735596330144106415596010217099333932274992582337912522854648529406656512

theorem mask21_eq : maskL 0 (tbl21.map Prod.fst) = mask21 := by decide +kernel

theorem cov21_1 : coverX 21 mask21 1 = true := by decide +kernel
theorem cov21_2 : coverX 21 mask21 2 = true := by decide +kernel
theorem cov21_3 : coverX 21 mask21 3 = true := by decide +kernel
theorem cov21_4 : coverX 21 mask21 4 = true := by decide +kernel
theorem cov21_5 : coverX 21 mask21 5 = true := by decide +kernel
theorem cov21_6 : coverX 21 mask21 6 = true := by decide +kernel
theorem cov21_7 : coverX 21 mask21 7 = true := by decide +kernel
theorem cov21_8 : coverX 21 mask21 8 = true := by decide +kernel
theorem cov21_9 : coverX 21 mask21 9 = true := by decide +kernel
theorem cov21_10 : coverX 21 mask21 10 = true := by decide +kernel
theorem cov21_11 : coverX 21 mask21 11 = true := by decide +kernel
theorem cov21_12 : coverX 21 mask21 12 = true := by decide +kernel
theorem cov21_13 : coverX 21 mask21 13 = true := by decide +kernel
theorem cov21_14 : coverX 21 mask21 14 = true := by decide +kernel
theorem cov21_15 : coverX 21 mask21 15 = true := by decide +kernel
theorem cov21_16 : coverX 21 mask21 16 = true := by decide +kernel
theorem cov21_17 : coverX 21 mask21 17 = true := by decide +kernel
theorem cov21_18 : coverX 21 mask21 18 = true := by decide +kernel
theorem cov21_19 : coverX 21 mask21 19 = true := by decide +kernel
theorem cov21_20 : coverX 21 mask21 20 = true := by decide +kernel
theorem cov21_21 : coverX 21 mask21 21 = true := by decide +kernel

theorem cert21 : Cert 21 tbl21 := by
  refine ⟨by simp only [tbl21, tblOK_append, tbl21_0_ok, tbl21_1_ok, tbl21_2_ok, tbl21_3_ok, tbl21_4_ok, tbl21_5_ok, tbl21_6_ok, tbl21_7_ok, tbl21_8_ok, tbl21_9_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask21_eq]
  interval_cases x
  exacts [cov21_1, cov21_2, cov21_3, cov21_4, cov21_5, cov21_6, cov21_7, cov21_8, cov21_9, cov21_10, cov21_11, cov21_12, cov21_13, cov21_14, cov21_15, cov21_16, cov21_17, cov21_18, cov21_19, cov21_20, cov21_21]

/-! ### `N = 22`: 351 witness orderings -/

def tbl22_0 : List (Nat × Nat) := [
  (12545, 2039663610234402537959568031933645),
  (12577, 1989122134624942485991939661194314),
  (12609, 1994194208293377196264451739280589),
  (12641, 1998224981555947342946828180579533),
  (18817, 2977810548135546413376226828285134),
  (19841, 2977810548135546413376226794730766),
  (20865, 3276343562261716971540840059299021),
  (21889, 3276343562261716971540841132254477),
  (22913, 3600941130429747169355318053627085),
  (13569, 3950408139630094863547477714854483),
  (13601, 3950408139630096012545722987115726),
  (13633, 3925053889694935723102737459111115),
  (13665, 3925055127639698523964397858649294),
  (18849, 2977400656079914974526225813927118),
  (19873, 2977400656079914978449485264118226),
  (20897, 3276573603943912577581945608266259),
  (21921, 3276566253670206954153353373345035),
  (22945, 3600941264964129979955458027615438),
  (14625, 3950408163558250978695923593966861),
  (14657, 3925053678488139570709264374224139),
  (14689, 3925054916730410078213390844097805),
  (19905, 2977400656151704028122592715535629),
  (20929, 3281644210916003737518203712369869),
  (21953, 3281644210916003737598034101990605),
  (22977, 3606155433648260321269874704053453),
  (15649, 3950408163559070633274136786724112),
  (15681, 3925053678488139570709264357446923),
  (15713, 3925054916730410078213390844093709),
  (19937, 2977400656151704028122592715531533),
  (20961, 3281644210916821051341652142667088)]

theorem tbl22_0_ok : tblOK 22 tbl22_0 = true := by decide +kernel

def tbl22_1 : List (Nat × Nat) := [
  (21985, 3281644210916821051421565441557904),
  (23009, 3606155433649077635093406043882832),
  (16705, 3925291303379566098173384698680523),
  (16737, 3925292543112985215216536545191117),
  (20993, 3286714813317733968956366295487695),
  (22017, 3286714813317733968956366592238799),
  (23041, 3611226036049990552628207194559695),
  (17697, 3950407850404037577122306642470093),
  (17729, 3925291303379563519388292979414155),
  (17761, 3925292543112985215212138498680013),
  (21025, 3286714813313011602473496650273999),
  (22049, 3286714813313011602473496947025103),
  (23073, 3611226036045268186145337549345999),
  (18753, 3925380669578570425107085528720589),
  (18785, 3925372021221131501292359121429709),
  (22081, 3291785416016155974983139683013903),
  (23105, 3616310309838004909004947000194254),
  (19777, 3925380669578570425107083381237005),
  (19809, 3925372025514288312581052379260174),
  (22113, 3291785411132776242596382884811218),
  (23137, 3616310309838004909004947233497554),
  (20833, 3925459684088173896137244857918669),
  (23169, 3616302726851087609251192674730515),
  (21857, 3925459684088173896138474074465485),
  (23201, 3616310329214105444630890665246986),
  (14401, 3950565108060387864661629037236884),
  (15425, 3950565108060387864661629020459668),
  (16449, 3950644335618219011180886990812499),
  (17473, 3950644335618218976559461634176338),
  (18497, 3950719892027953872769070132679187)]

theorem tbl22_1_ok : tblOK 22 tbl22_1 = true := by decide +kernel

def tbl22_2 : List (Nat × Nat) := [
  (19521, 3950719892027953872769070132679186),
  (20545, 3950799158824017098789169449460941),
  (21569, 3950799158824017098789167302239437),
  (22593, 3966091428517435760446802142491853),
  (13570, 1984051746289657364057950595408969),
  (13602, 1989122134626355949421467630327185),
  (13634, 1994194208293525062163277003126163),
  (13666, 1998224981555947348273131779843276),
  (13698, 5948949641227704015270785835689233),
  (18850, 2977805441921460582621725872157902),
  (19874, 2977805441992751586822100735796628),
  (20898, 3302331595808238657782997214884437),
  (21922, 3302331601594027600102573149044950),
  (21825, 3925380669578570425107153173406989),
  (14626, 4274926423400863997932552008037644),
  (14658, 4276045777223667518273118572209424),
  (14690, 4280070123558847573882595721151759),
  (14722, 4316535056663880174253956081214737),
  (19906, 2977488529341726008459425880802575),
  (20930, 3302014741186620941934823424979541),
  (21954, 3302014746972409884254399359140054),
  (21793, 3950812699147810992464230659744975),
  (15650, 4274926423400863997932552008033548),
  (15682, 4276045719204672909736657476740368),
  (15714, 4280070123558847573882595721151758),
  (15746, 4316535056663869942075602695447825),
  (19938, 2977488529341726008459425880802574),
  (20962, 3302014688649844233554313563956560),
  (21986, 3302014688649844233554313563956496),
  (21761, 3950812699147810992464231733486799)]

theorem tbl22_2_ok : tblOK 22 tbl22_2 = true := by decide +kernel

def tbl22_3 : List (Nat × Nat) := [
  (16706, 4276124941271061631145245908726357),
  (16738, 4280070142825440091369616753095886),
  (16770, 4321286309220283691417152510584145),
  (20994, 3302014683158181600432623039345237),
  (22018, 3302014688943971695673703580090582),
  (21729, 3950812696092738484225238067930317),
  (17698, 4274926423406470614614615203833036),
  (17730, 4276124941271061631145245908464213),
  (17762, 4280070142825440091369616736318670),
  (17794, 4321286270534657463749018820896082),
  (21026, 3302014683158181600432623039083093),
  (22050, 3302014688943970542752198973243606),
  (21697, 3950812696092738484168408138573005),
  (18754, 4275890976389425636592865908146390),
  (18786, 4280070162167888899825309960434894),
  (18818, 4326356872935570381355005732807953),
  (22082, 3302015921098221118887489882354260),
  (21665, 3950799158885994666599257999967635),
  (19778, 4275887262870199648095731098412304),
  (19810, 4280070162167888899825310210253266),
  (19842, 4326358110875609670671187489678409),
  (22114, 3302017159038260404267764781478482),
  (21633, 3950799158885994663802170212181197),
  (20834, 3250838263690130915746912941970636),
  (20866, 3302331595808234045245056926143059),
  (21601, 3950799158824017098790329946531021),
  (21858, 3250838284256710286002990508160270),
  (21890, 3302331601594027600102573150057046),
  (14433, 3950566619884012747446836365685332),
  (15457, 3950566619884012747446836365681236)]

theorem tbl22_3_ok : tblOK 22 tbl22_3 = true := by decide +kernel

def tbl22_4 : List (Nat × Nat) := [
  (16481, 3950645867389413912313317524034131),
  (17505, 3950645867384691545830447878820435),
  (18529, 3950725032635400279526537487246541),
  (19553, 3950725037518766468665839963394580),
  (20577, 3950799158824017098789100729984205),
  (22625, 3966099034818797588716626997953875),
  (13571, 1984051746232842564139424484254926),
  (13603, 1989122134710921427580872557946062),
  (13635, 1994194208293525062163277002864019),
  (13667, 1998224981641553012692098866513299),
  (13699, 5948949621884440400753741100303435),
  (18851, 2977805442006918691028434999068051),
  (19875, 2977805441992751591861301038589332),
  (20899, 3302324245538880790573086508638739),
  (20802, 4275887256783518838132465276613205),
  (20801, 3925380669578570425107152100451533),
  (14627, 4274926423400863997932551991260428),
  (14659, 4276038368935689563563225757315668),
  (14691, 4280070123558868464916328080803087),
  (14723, 4316535037320616559736911345828939),
  (19907, 2977488529343065809575357426214292),
  (20931, 3302007338380860887380881844531797),
  (20770, 4275331252806079821654392460080334),
  (20769, 3950812699147810992464230362993871),
  (15651, 4274926423400863997932551991256332),
  (15683, 4276038368935689563563225757311572),
  (15715, 4280070123558868464916328080803086),
  (15747, 4316218182698998843888737555924043),
  (19939, 2977488529343065769631961891038480),
  (20963, 3302007338380860887380881844527701)]

theorem tbl22_4_ok : tblOK 22 tbl22_4 = true := by decide +kernel

def tbl22_5 : List (Nat × Nat) := [
  (20738, 4275331252806079821658790506591438),
  (20737, 3950812699147810992464231436735695),
  (16707, 4276117591001703763935336275960339),
  (16739, 4280070142906380743505905213306062),
  (16771, 4321286251191393613338414064161867),
  (20995, 3302007332888823733222713406579219),
  (20706, 4275331249751165210924221541442764),
  (20705, 3950812696092738484145463567377613),
  (17699, 4274926423406470614614546484356300),
  (17731, 4276117591001703763935335202218515),
  (17763, 4280070142906380743505905196528846),
  (17795, 4321286251191393613338414064141643),
  (21027, 3302007332888823733222712332837395),
  (20674, 4275331249751165210950266223125708),
  (20673, 3950812696092738484167178922026189),
  (18755, 4275879970324041498504205830472278),
  (18787, 4280070162253864471604493397034387),
  (18819, 4326356853592306766837960997422155),
  (20642, 4275317712544421354543472199685326),
  (20641, 3950799158885994666599257699607891),
  (19779, 4275879912596493935439429733773908),
  (19811, 4280070162253864471604493397034386),
  (19843, 4326358091532346986134816424264843),
  (20610, 4275317712482443824727900539905228),
  (20609, 3950799158885994663802169915430093),
  (20835, 3250971791110537610059709483615571),
  (20867, 3302331576465050933684401926890003),
  (15489, 3950566619884099161940603966940432),
  (16513, 3950645535855987351847419549902029),
  (17537, 3950645535855986198925914943055053)]

theorem tbl22_5_ok : tblOK 22 tbl22_5 = true := by decide +kernel

def tbl22_6 : List (Nat × Nat) := [
  (18561, 3950725032937631733867244827501773),
  (19585, 3950725037518779096464718025811215),
  (22657, 3966091451830641777999369645389005),
  (15490, 4275085173542366840193940813579534),
  (16514, 4275164089514414060616177060996300),
  (17538, 4275164089514412907694672454149324),
  (18562, 4275243586596058465976704447341772),
  (19586, 4275243591177046778402319740790030),
  (21634, 4275317712482443830111854406694291),
  (14660, 2318791990105021320318218557744530),
  (14692, 2322743554552484583916292566443410),
  (14724, 2327815395266045903396176580375821),
  (14756, 2327815395266776797898312961819919),
  (19908, 2977805441940347742701399079187725),
  (19747, 4275879656626458498993925120894356),
  (19746, 4275879656626458493954724818101652),
  (19745, 3951366209110826593725694856459534),
  (15684, 4600556608528709932696558311638285),
  (15716, 4604591382745444561868790871688461),
  (15748, 4610685529747397912825334223934736),
  (15780, 4579243325489933175380785233466640),
  (19940, 2977567757452805183025952818005261),
  (19715, 4275243591177723448693100715242764),
  (19714, 4275252235625187074601933006005519),
  (19713, 3951366209110827746647199463306510),
  (16708, 4600636167686388200762618133681487),
  (16740, 4604591172444979574950911312958869),
  (16772, 4610785957320820744811491861538129),
  (16804, 4579401801239006114816283117163855),
  (19683, 4275243591177047913310312714503572)]

theorem tbl22_6_ok : tblOK 22 tbl22_6 = true := by decide +kernel

def tbl22_7 : List (Nat × Nat) := [
  (19682, 4275243591177047913310312714765716),
  (19681, 3950725037518852900610917723890958),
  (17700, 4599445290516086087348014602057037),
  (17732, 4600636167686388200762618133677391),
  (17764, 4604591172444979556936512803476885),
  (17796, 4610785957320820744811491861538128),
  (17828, 4579401801239022433908323076842901),
  (19651, 4275243591177047913310312731280788),
  (19650, 4275243591177047913310312731542932),
  (19649, 3950725037518852900610986443367694),
  (18756, 3002919530308278926114369374545299),
  (18788, 2971771784794035163345695286261135),
  (18820, 2977810569891703190475388627018959),
  (18852, 2977805441916758030547714097055123),
  (19618, 4275243591177047931324711241024916),
  (19617, 3950725037518779096473514068501775),
  (19780, 3002919530308278926114369374545298),
  (19812, 2971771784794034837358448584758412),
  (19844, 2977810569891703190475388911629711),
  (19876, 2977805441992751586540625758823828),
  (15521, 3950566619884099161940603950163216),
  (16545, 3950645535855987351847350830425293),
  (17569, 3950645535855986198925846223578317),
  (18593, 3950725032937630580945740220654797),
  (22689, 3966091451830641777717894668678349),
  (15522, 4275085173542366840193940796802318),
  (16546, 4275164108857227174450106417341644),
  (17570, 4275164108857226021528601810494668),
  (18594, 4275243586898308529467733469590931),
  (21666, 4275317712544421354543472512951502)]

theorem tbl22_7_ok : tblOK 22 tbl22_7 = true := by decide +kernel

def tbl22_8 : List (Nat × Nat) := [
  (14725, 2328934452794236030548834352956687),
  (14757, 2328927041191372513524229126817039),
  (18724, 4600398210232481376625975275091149),
  (18723, 4275879656640625598161059081373075),
  (18722, 4275879656555167489754349954462926),
  (18721, 3951366209110826593725694890013902),
  (15749, 4610685529747397917314574701892880),
  (15781, 4579243325489785601428196630795536),
  (18692, 4599762139948503516118190420485327),
  (18691, 4275243592084344026427777758065868),
  (18690, 4275252235625334648554525787251919),
  (18689, 3951366209110827746647199496860878),
  (16773, 4610785957320820744811423142061393),
  (16805, 4579401801239006078800678090249551),
  (18659, 4275243586893586162984863824110995),
  (18658, 4275243586893586162984863824373139),
  (18657, 3950725033225696000376200544969933),
  (17701, 4600636167687431576406286218077589),
  (17797, 4610785957320820744811423142061392),
  (17829, 4579401801239022433899526984082837),
  (18627, 4275243586893586162984863824115091),
  (18626, 4275243586893586162984863824377235),
  (18625, 3950725033225696089322293185537229),
  (18757, 3002919472884302494419483576001939),
  (18789, 2971536576186570941093464452658575),
  (18821, 2977810569877537243948284298486991),
  (18853, 2977805383893021241119525486261454),
  (6305, 4939731462243175863882502280643853),
  (16577, 3950645555117549803246470609298637),
  (17601, 3950645555117549803242072562787533)]

theorem tbl22_8_ok : tblOK 22 tbl22_8 = true := by decide +kernel

def tbl22_9 : List (Nat × Nat) := [
  (22721, 3971159574990268262737617142211789),
  (16578, 4275164108775976530029557910398156),
  (17602, 4275164108775976530025159863887052),
  (21698, 4275331249751165210951564142372044),
  (16579, 4275164108857227174168562721154252),
  (17603, 4275164108857226021247058114307276),
  (20675, 4275331249751165174921537923638476),
  (15814, 6181791252618521676003726948111632),
  (17668, 4599445290516086087352412648568141),
  (17667, 4274926424369683228515752459166924),
  (17666, 4274926424369683228515821178643660),
  (17665, 3950407851368443405913065591727309),
  (16838, 2652175199752596006082275616019596),
  (17635, 4275164108857226021225342759658700),
  (17634, 4275164108775991481347345680229580),
  (17633, 3950645555117564754568587706164429),
  (17702, 2611939888355346754779568984646990),
  (17862, 2652175199752594853160771009172620),
  (7329, 4939731212948935030202876795880717),
  (16609, 3950645555117564754850062682875085),
  (22753, 3971159578352293438386863023080784),
  (7362, 4965163511140777888488467935593742),
  (16610, 4275164108775991481628820656940236),
  (21730, 4275331249751165211008394071729356),
  (16611, 4275164108857227174146847366505676),
  (20707, 4275331249751165174899822568989900),
  (8385, 5269320330247528786885177798878541),
  (8417, 5269320330247529020786413454058829),
  (22785, 3976230180753206355921664173757647),
  (8386, 5269399558419505293611835534898581)]

theorem tbl22_9_ok : tblOK 22 tbl22_9 = true := by decide +kernel

def tbl22_10 : List (Nat × Nat) := [
  (8418, 5269399558419505293611835534894485),
  (21762, 4275331252806079827033952558552467),
  (20739, 4275331252806079821658721787114702),
  (19716, 4599762139948503516119353332102543),
  (9409, 5269320330247384905598324767778125),
  (9441, 5269320330248356780919418221303117),
  (22817, 3976230180753206355921663100015823),
  (9410, 5269399558419343902901656494859596),
  (9442, 5269399558420315778266385738720593),
  (9474, 5294752841808715357015077217952970),
  (21794, 4275331252806079827033952558548371),
  (9475, 5294752688954860702369805589865676),
  (20771, 4275331252806079821654323740603598),
  (19748, 4600398210232481376617179182069005),
  (10465, 5563104544444237998178796173575307),
  (10497, 5598909503548227307235400079434957),
  (10529, 5598909503548153520259105241228493),
  (22849, 3925380709506247096527781354595533),
  (10466, 5563104544444237997897321196864651),
  (10498, 5563743498290930782397300118709451),
  (10530, 5598988732012917574503262080787660),
  (21826, 4275887262569307780452041210773718),
  (10499, 5563743497988694751840819463120076),
  (10531, 5598988732012917574498864034276556),
  (20803, 4275879906514160970922554570367507),
  (13701, 5852201960550232521473451575801038),
  (13700, 5852201960560941991011743414650259),
  (13668, 1998224981551244743299138470049171),
  (13636, 1994194208284080329197537712698771),
  (11489, 5568166481265904091043756019864716)]

theorem tbl22_10_ok : tblOK 22 tbl22_10 = true := by decide +kernel

def tbl22_11 : List (Nat × Nat) := [
  (11521, 5567928782624089616868205642208396),
  (11553, 5567921451697919473756890223957132),
  (22881, 3925459684088173896138474074203341),
  (11490, 5568166481265904073029357510382732),
  (11522, 5567928801966829751875970599801996),
  (11554, 5567922689637885780310863285376140),
  (11586, 5619279980375384946368596498510421),
  (11523, 5567928801966829733861572090320012),
  (11555, 5567922689637885762296464775894156),
  (11587, 5619272630106027079158685792264723),
  (11588, 5619351881294799053540406247097679),
  (12644, 1998224981551244743299126759613645),
  (12612, 1994194208284080329197526002263245),
  (12643, 1998224981641553046776959327569299),
  (12611, 1994194208293525062163265292428493),
  (12579, 1989122134710921427572067929744589),
  (12547, 1984051746232842564091250038334669),
  (12642, 1998224981555947348273131779843277),
  (12610, 1994194208293525062163265292690637),
  (12578, 1989122134626355949421465752047958),
  (12546, 1984051746290239589417777053131849)]

theorem tbl22_11_ok : tblOK 22 tbl22_11 = true := by decide +kernel

def tbl22 : List (Nat × Nat) := tbl22_0 ++ tbl22_1 ++ tbl22_2 ++ tbl22_3 ++ tbl22_4 ++ tbl22_5 ++ tbl22_6 ++ tbl22_7 ++ tbl22_8 ++ tbl22_9 ++ tbl22_10 ++ tbl22_11

def mask22 : Nat := 1573727015128086788640698165426466780790976634628422224451673865756850244511335669212582762157936238665357681671104691080577674924441147928997236853413085928359206349825206180609210579355024295366252440623615977446104108263181470844447489673833205499044091722097155840318280014713443837405079503994489307156748152545916988735526615240947685514802106870615779895204777200533610231237790626866764440722207632041773648908186714017287397685262217613645446246473532949564511540003375423140829204839144683530954298383777785666404691574796688776103308339912731249809159583981928731951293637289944342147395227625903698350386540163692732503330693269894112248297975121509343035324929453197847928855305075091523041345558172807869901758261805691610886741982354160474169805855431141437085652486486651170368801167241827862251016327032786883572757980082384466223477319242759872564015890392100403779690749048833012391688703713490721531248918725968253876608099899606309673174230038010573351393136246846842704789378099793069725649478767808617407554586603272322778944728050224236423036365780499468559699846323175124965377949203431575236790583718416180232708801672639762536003046188155449003634089343938357534626092577723963788693140974446072431183363721448105145638854462288478551349615600335229378780256427049803240708749166453811966317955130842650903667668271893162779535082704536589377916323189673575516203811200743936794106077945843552976134009502744169269475566550967903115778519190330710527967225410604357834339029775759743199627386793128456369324669540009522914441840261344917809415357250471260629273848358275571515808322789622389004003680197099749064977888755471274701373408798431423053281565221324642120337287305681136731464627875778350706790008712389980993732362345999039018848891002615597679585095403818265476660556489574271596493980459734643150405409470018752945710178308648514559746546004453907035076752002950314708730090972387174571298065436640279063131484919312941142046255025936107327135177097498701256030885288699385924586279454728939486862368858247103675210313374160460931147684877433539370435804518299182206908483912816473439264629862126104773830079705906590675639038956968565091804651812420066903744884035525316245702640209952530309409736959876347106810335457746453419782225653529051741203770911512915648356589661628907975751620841116330172127032440447070872997422384818555932430926276135358496370989925887306401308838787761118818518434338427738851900751165417443735197173942268829852351841063810896387827020348489995424715882619701618428776629832989072955645803337245181124640370384269596793116653447148835198311066512487133734461702701698975839663374383812846705026751119227749974952140771117096313058101211975625224466957206936171433561281492425213965473279207654545809540309091274259241876954941723331419202269070968252935041409249586475892375383138910929292552293415407499326751599558103469136275810656402842466060324504580629374936783231014250950617617224579267149057302537245942351474837597751141600701941598454275289861689329261019703819675351318118122546382844840280586408089402541793372484170190097772514019105246068551479259918090939911319210237553362169531801932083023102444566982423931406087124241764124734048998849215304475794643929289200535967926953836466171574467557897388891890254719677741121212340177226136437503399817336522601408383367277204525897057693053571690902977374644636071474026295083858260866491916132264796004033128700297021190876025492777822571060089699213723232651148823394538164159576767916759959822927821764795904890541692351418743883627706981437809833747822106462222555173163967273810579464907386769733472731198524785235146376350639941016780556460938450615411913201301901593565833107387145721717825131331677869926407673969178263564245357666229651878976697244054834037795017197002454066635207786276369080869798461903383541737149822333165299898959619681128199049429234719625635794369866502053867775525360246094309172825055210736492882246724357634447570700656173150384029809266965654228355697870690209789208724133957489607705809945426560528834349480146506929930914430621015430620979825865262378696762395418499183624025492883119603263682507182675544921455627726701995692115010218458004803328752901612308812906496339306675800042157176762725718147897662160575043771171500773854535363017627585073003564132005980777314531023412968680021786253146773707238815090799862062656462262107688146997234679852324080272903103444700484812564259643738938060036312940447662886453245315755963763763638412329041399619139560023394704516116170637211446113061431714446612255874352432306659954384017892594075752617227086743225794470427390757805461220176213084511967866221823762676810627662368713100188610299623661641468007718000286305496435841519673726127914501713201509292749010446750920031981573612131615265339374917909528331020461120856735360421994539416182320473460327668614706012525331733856463496356352516021740209719939878888348047071594374648106426609442665258974459499392182134198389394209128422068404885716882450414929903389643206172543309799232855760765179556220037440327156072495677099485329160647464719546376997746771429689909107120619851902352804080304243348953070191369972790369960970022740864565934737704420858658285265097165049588952076705117497142794220416901796818901075356101896104322134136807289472252755219779746631950592661114835281763356395534702984026701328560770565346719826518612153746730492802147639784023164683508130578708770552596910449469112689411179639652768240269193275997212690423060636371954033123755455787694793267817409553511784521041042902082623515754814001001186113745258689421780538435110884391060222781887452329513982147728161022836552427588241359019775158590242207671777591557193223620358078495929605486558083216665876314469757915074502510617806368413885003640741329665497759104671318475438365855046855549462759446854098751454464053081820611180624274374027796631057486437145736435678866464254108568217720795110165443951820161091689734986145881919420404166719245024712011998355733780772355149244327147744886479720106130088062032460341623302074293427533647825190278795363463147500269259419336590272834728996849553596555550999949770676306753502566286231946012639402559793133022793783366102436225817029489213946019427329607223261762226018067426197508372796293084725185275411246110310279901836788939898972077224145231658638838393881037527629074258003817637172941586648245562060870307892938596238913947632042768703465383224400215790435393742982019691933779630854796676352325776770749332721490440074239837733538726052665945855641332723996264462920714461417311372322167076539310226236081031801856604493269764071292715470686205902607146194139787819998847039204270769939220582595531598290351612727428157079899096755566137310244939462331522686332576316939843654859924573252732478704535086617401781521859680484524440575722289426265038709624892542891790758397204012542315100425430494889135336709039918749436107074377901376434548172064600835166830592

theorem mask22_eq : maskL 0 (tbl22.map Prod.fst) = mask22 := by decide +kernel

theorem cov22_1 : coverX 22 mask22 1 = true := by decide +kernel
theorem cov22_2 : coverX 22 mask22 2 = true := by decide +kernel
theorem cov22_3 : coverX 22 mask22 3 = true := by decide +kernel
theorem cov22_4 : coverX 22 mask22 4 = true := by decide +kernel
theorem cov22_5 : coverX 22 mask22 5 = true := by decide +kernel
theorem cov22_6 : coverX 22 mask22 6 = true := by decide +kernel
theorem cov22_7 : coverX 22 mask22 7 = true := by decide +kernel
theorem cov22_8 : coverX 22 mask22 8 = true := by decide +kernel
theorem cov22_9 : coverX 22 mask22 9 = true := by decide +kernel
theorem cov22_10 : coverX 22 mask22 10 = true := by decide +kernel
theorem cov22_11 : coverX 22 mask22 11 = true := by decide +kernel
theorem cov22_12 : coverX 22 mask22 12 = true := by decide +kernel
theorem cov22_13 : coverX 22 mask22 13 = true := by decide +kernel
theorem cov22_14 : coverX 22 mask22 14 = true := by decide +kernel
theorem cov22_15 : coverX 22 mask22 15 = true := by decide +kernel
theorem cov22_16 : coverX 22 mask22 16 = true := by decide +kernel
theorem cov22_17 : coverX 22 mask22 17 = true := by decide +kernel
theorem cov22_18 : coverX 22 mask22 18 = true := by decide +kernel
theorem cov22_19 : coverX 22 mask22 19 = true := by decide +kernel
theorem cov22_20 : coverX 22 mask22 20 = true := by decide +kernel
theorem cov22_21 : coverX 22 mask22 21 = true := by decide +kernel
theorem cov22_22 : coverX 22 mask22 22 = true := by decide +kernel

theorem cert22 : Cert 22 tbl22 := by
  refine ⟨by simp only [tbl22, tblOK_append, tbl22_0_ok, tbl22_1_ok, tbl22_2_ok, tbl22_3_ok, tbl22_4_ok, tbl22_5_ok, tbl22_6_ok, tbl22_7_ok, tbl22_8_ok, tbl22_9_ok, tbl22_10_ok, tbl22_11_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask22_eq]
  interval_cases x
  exacts [cov22_1, cov22_2, cov22_3, cov22_4, cov22_5, cov22_6, cov22_7, cov22_8, cov22_9, cov22_10, cov22_11, cov22_12, cov22_13, cov22_14, cov22_15, cov22_16, cov22_17, cov22_18, cov22_19, cov22_20, cov22_21, cov22_22]

/-! ### `N = 23`: 402 witness orderings -/

def tbl23_0 : List (Nat × Nat) := [
  (13569, 130863068856198423216032868510528782),
  (13601, 127308981398898855591080589052933390),
  (13633, 127633485019584358275791740164949131),
  (13665, 127886400081071402657938952387618060),
  (19873, 293086845278602895776032590191723791),
  (20897, 211617414494945921247161980286731598),
  (21921, 211617414494945921247161980303246606),
  (22945, 232387140507663082515835781801407758),
  (23969, 232387140507663082515835781801403662),
  (14625, 273924978011091364515457991521928463),
  (14657, 273924960970059354872141601784530191),
  (14689, 273924487907695843644897027279357199),
  (14721, 148980185292828457368262518199088397),
  (19905, 190883307916827044076658334304634127),
  (20929, 211652496588892737453648616760603155),
  (21953, 211652496588892663666953865501930068),
  (22977, 232387150332857728237538269772711183),
  (24001, 232387150332857728237538269772449039),
  (15649, 273924959563229265821815062556116302),
  (15681, 273924960994289380355884420286973262),
  (15713, 273924487908074298216623671953130830),
  (15745, 293106593052847954694920561382724944),
  (20961, 211652496593779949890565803148641614),
  (21985, 211652496593779949890565804222121230),
  (23009, 232421683947833749420047333718820110),
  (24033, 232421683947833749420047333718557966),
  (16705, 273924960994290261153578234123457870),
  (16737, 273924489146014337502540714685035854),
  (16769, 293106578048009618050721829258859855),
  (20993, 211652496593780830688259616985126222)]

theorem tbl23_0_ok : tblOK 23 tbl23_0 = true := by decide +kernel

def tbl23_1 : List (Nat × Nat) := [
  (22017, 211652496593780830688259617001117070),
  (23041, 232421683967176562529114956366705934),
  (24065, 232421683967176562529114956366701838),
  (17729, 273924960662094600230917990721844494),
  (17761, 273924489140828167023353435254224142),
  (17793, 293106578042829256008370632626078991),
  (22049, 211652496593780830688259617001637134),
  (23073, 232421683967176577624823972225447182),
  (24097, 232421683967176577624823972225443086),
  (18753, 273924960662373515001031004165567758),
  (18785, 273924490378744889623943066303395086),
  (18817, 293106579280769291601436654930822415),
  (22081, 211653379144031081837993743265367311),
  (23105, 232421683986519301767026566963754254),
  (24129, 232421683986519301767026566963750158),
  (19777, 273924976792489564596779498216420622),
  (19809, 273925515373782628559018216161867022),
  (19841, 293106579280769291596102921877259535),
  (23137, 232421683986524024133426356053419342),
  (24161, 232421683986442790745989994453148118),
  (20833, 273925515375941703543995578831402318),
  (20865, 213275089362072964322175397088003406),
  (23169, 232421684003698317874316995284772046),
  (24193, 232421684003698317874316926565295310),
  (21857, 273925515375941703543995579904881934),
  (21889, 213275089362072964322175397104518414),
  (24225, 232421684003693594372988251902874562),
  (22913, 230459285225978817031557125371384405),
  (23937, 213275096673656321351453948931278094),
  (14401, 398555298450476343025505879208031501)]

theorem tbl23_1_ok : tblOK 23 tbl23_1 = true := by decide +kernel

def tbl23_2 : List (Nat × Nat) := [
  (15425, 419329556426329431260380236638638611),
  (16449, 419329556448330934738547265669199313),
  (17473, 440098743882523014160532173709468878),
  (18497, 440098757612250519340191671635202643),
  (19521, 460873240934544688027596690573559055),
  (20545, 460872936420628244849371917277541839),
  (21569, 481642123854767555363493902879045007),
  (13570, 126984391046868161159296501078914121),
  (13602, 127308981398898855596771379628569870),
  (13634, 127633485019585846679127312065385938),
  (13666, 127886400081071402663542400562816268),
  (13698, 400528646886069562410211328538801423),
  (19874, 293086845279208848497895539365184783),
  (20898, 211617414494945921247163351153050958),
  (21922, 211617414494945921247161911583769870),
  (22946, 232387140507663082515835781784630542),
  (22881, 273925515375941703544079752435168526),
  (14626, 273924978011697316084399504808019215),
  (14658, 273924960970059378115477580979963151),
  (14690, 273924487907695866888233006474790159),
  (14722, 276278288741449372335760092984866063),
  (19906, 190883307917432995645599847590724879),
  (20930, 211652496588892760763993026658890259),
  (21954, 211652496588892662514032360895083092),
  (22978, 232386275364371304239506438503625999),
  (22849, 273925522728921177642230469971739918),
  (15650, 273924959558700607808613992539948366),
  (15682, 273924960994289380361553280830866766),
  (15714, 273924487908074298222292532497024334),
  (15746, 276587595507247873423559355362276686)]

theorem tbl23_2_ok : tblOK 23 tbl23_2 = true := by decide +kernel

def tbl23_3 : List (Nat × Nat) := [
  (20962, 211652496593779949896234663692535118),
  (21986, 211652496593779949890284329245410574),
  (23010, 232421683947833749420047264999343374),
  (22817, 273950868329917828790607486113379598),
  (16706, 273924960994290261153579604989777230),
  (16738, 273924489146014337502629355021235534),
  (16770, 276562329073674806356812397055669583),
  (20994, 211652496593780830688260987851445582),
  (22018, 211652496593780830688259548281640334),
  (23042, 232421683967176562529114956349928718),
  (22785, 273950868390656846720028429903242708),
  (17730, 273924960662094600230913592675333390),
  (17762, 273924489140828167023349037207713038),
  (17794, 276886839867875838127843811280364943),
  (22050, 211652496593780830688259548282160398),
  (23074, 232421683967176577624823972225185038),
  (22753, 273950868387946268132109672611902734),
  (18754, 273924960662373515001026606119056654),
  (18786, 273924490378744889623938668256883982),
  (18818, 276886839867875838127843420387209814),
  (22082, 211653379144031081837989345218856207),
  (23106, 232421683986519301767026566946977038),
  (22721, 273950868387946268132109686499276046),
  (19778, 273924976792489564959877744708908302),
  (19810, 273925515373782628922116462654354702),
  (19842, 275913522281233699325479416637519119),
  (23138, 232421683986524024133421958006908238),
  (22689, 273950885836296328143212030995228112),
  (20834, 273925515375941703544084150464902478),
  (20866, 275913284616088969646300702800966991)]

theorem tbl23_3_ok : tblOK 23 tbl23_3 = true := by decide +kernel

def tbl23_4 : List (Nat × Nat) := [
  (23170, 232421684003698317874312597238260942),
  (22657, 273950885813648008384623124651246863),
  (21858, 273925515375941703543991181858370830),
  (21890, 275913284206900557947493952325481046),
  (22625, 273950885819131500066557294870590039),
  (22914, 230459285225974094665074255726170709),
  (15457, 273930032636929728129317639244547406),
  (16481, 273935103239329461630716229269124430),
  (17505, 273935103239329462783637734932673806),
  (18529, 273940173841707059016453077895542030),
  (19553, 273940173845640479851827874666181902),
  (20577, 273945244603143602362292512910795349),
  (21601, 273945244603143602362292513984275028),
  (23649, 273950885819131500066557294870590038),
  (14627, 148078168833039580977144559582147855),
  (14659, 148402672459509977556745073805030669),
  (14691, 148655587515301037909622460561061135),
  (14723, 148980185298609525496331736072623572),
  (14755, 149309853759012597790617287109658065),
  (19907, 190848227037804496499197601125008852),
  (20931, 211617414491281676417756297537029589),
  (21955, 211617414491281676037144359806235917),
  (21826, 273924976797363852789527867534411022),
  (21825, 273924976797363852789527936253887758),
  (15651, 294694146992778602427776209170269517),
  (15683, 294694148177280198457197529763247440),
  (15715, 294693850065211961657115392243209552),
  (15747, 295090310246308368954091692625827147),
  (15779, 293071653438964494329110787263919441),
  (20963, 211658122911542987283952177818441040)]

theorem tbl23_4_ok : tblOK 23 tbl23_4 = true := by decide +kernel

def tbl23_5 : List (Nat × Nat) := [
  (21987, 211658122911542984978109168604747152),
  (21794, 273945259206966696153864738650518798),
  (21793, 273945259206966622420927241294247182),
  (16707, 294694148173606341469330988446053709),
  (16739, 294693835036478698597490314887918927),
  (16771, 295090301653593846788051544207594827),
  (16803, 293081774676807789177554540735305039),
  (20995, 211658122911542987283978563882915151),
  (22019, 211658122911542984978135554669221263),
  (21762, 273945259206967592206947863308367252),
  (21761, 273945259206967592206666594473309588),
  (17731, 294694148173606415250330566983742733),
  (17763, 294693835036780922844136340771632397),
  (17795, 295095371851585905103540302075462358),
  (17827, 293081774676807862583699406721713423),
  (22051, 211658122911542962894708072764736783),
  (21730, 273945259206967592206666389422175636),
  (21729, 273945259206967592206666458141652372),
  (18755, 294694148173965164918958611305657613),
  (18787, 294693836274720871103856286207898893),
  (18819, 295095371851585921353649653283885782),
  (18851, 293086845279208775500487081988785423),
  (22083, 211658122911542962910778534699533583),
  (21698, 273945259206967504459951814785697038),
  (21697, 273945259206967504459951883505173774),
  (19779, 294694164227839139817158724809688532),
  (19811, 294693836273828367114599686164018447),
  (19843, 295100363615485132766380013127221975),
  (19875, 293086845279208848497895539348407567),
  (21666, 273945244603143603515231384335090958)]

theorem tbl23_5_ok : tblOK 23 tbl23_5 = true := by decide +kernel

def tbl23_6 : List (Nat × Nat) := [
  (21665, 273945244603143603515231453054567694),
  (20835, 213280652704201904874931553553184079),
  (20867, 211374496152268811958582382515470935),
  (20899, 211617414494945943276792240525112656),
  (21634, 273945244603143616124994167727023376),
  (21633, 273945244603143616124998565773534480),
  (21859, 213280652697797349860882287232086612),
  (21891, 211267135643623132285875502430343636),
  (21923, 211617414494945918941318971089552654),
  (15489, 273930032641510257435719232621708622),
  (16513, 273935103243911170353299174752843086),
  (17537, 273935103238725073660806715183527182),
  (18561, 273940173841183683072941216364848398),
  (19585, 273940173845630886755086287701898510),
  (20609, 273945244603143616124998565773276496),
  (23681, 273950885813648008384623124650984719),
  (15490, 273930032636929728134986499771663694),
  (16514, 273935103239330641052593441136801102),
  (17538, 273935103239330714833596662901437710),
  (18562, 273940173841788145964927036742497550),
  (19586, 273940173845641818738127034361120014),
  (20610, 273945244603143616125086044656072016),
  (22658, 273950885813648008384623124634469647),
  (14660, 148402669977834460127053125654418898),
  (14692, 148655587515206011725602883148281103),
  (14724, 148980185292527564800273332726232335),
  (14756, 149309853369383335418380859429684495),
  (19908, 190848226999117457961008792076088589),
  (20932, 211617414491281676055247520039499085),
  (20803, 294694164227838918474244238804551125)]

theorem tbl23_6_ok : tblOK 23 tbl23_6 = true := by decide +kernel

def tbl23_7 : List (Nat × Nat) := [
  (20802, 273924976797363852789529307103692110),
  (20801, 273924976797363852789527936237372750),
  (15684, 294694148177280175257255824269837645),
  (15716, 294693850065210490604987883521381712),
  (15748, 295090285270845634930792432983147851),
  (15780, 293071653432876932648930903129396560),
  (20964, 211658122911542964302360355203257680),
  (20771, 294714446641106006776157272526353741),
  (20770, 273945259206966696534128619769627982),
  (20769, 273945259206966622420927240220767566),
  (16708, 294694148173606341463724577565504845),
  (16740, 294693835036478675392223532881343821),
  (16772, 295090301268532527667936916611605841),
  (16804, 293081794637678758484142876721485135),
  (20996, 211658122911542964047718476500768079),
  (20739, 294714446641106900235717128709772757),
  (20738, 273945259206967592206949300040406485),
  (20737, 273945259206967592206666594473305557),
  (17732, 294694148173606415250607575194465549),
  (17764, 294693835036780922861869195584926989),
  (17796, 295095371870933440585541465968551312),
  (17828, 293081795879816684246750990540285327),
  (20707, 294714446641106900562416600309863893),
  (20706, 273945259206967592206667825080735189),
  (20705, 273945259206967592206666458141648341),
  (18756, 294694148173965164936968543049151757),
  (18788, 294693836274720872238758994258752781),
  (18820, 295095371870933505113121618059920022),
  (18852, 293086866482586597688069532520117652),
  (20675, 294714446637442570144668186055837141)]

theorem tbl23_7_ok : tblOK 23 tbl23_7 = true := by decide +kernel

def tbl23_8 : List (Nat × Nat) := [
  (20674, 273945259206967504459953254354978126),
  (20673, 273945259206967504459951883488658766),
  (19780, 294694164227837653719661754529412365),
  (19812, 294693836273732871888595677823694093),
  (19844, 294998072433240643540565974574761231),
  (19876, 293086842803328769927134989566936335),
  (20642, 273945244603143603515232823904372046),
  (20641, 273945244603143603515231453038052686),
  (20836, 213280652698099655103966942072735055),
  (20868, 211272206246110152278998553578993107),
  (20900, 211617414494945920094241846529426766),
  (16545, 273935103243911170353017699776132430),
  (17569, 273935103238724999873830420345320718),
  (18593, 273940173841102596106645763308188942),
  (19617, 273940173845631035118862135375754510),
  (23713, 273950885836296328143212030995228048),
  (16546, 273935103243911170353106340112332110),
  (17570, 273935103238724999873826022298809614),
  (18594, 273940173841102596106641365261677838),
  (19618, 273940173845631035481960381868242190),
  (22690, 273950885836301070306027313801213393),
  (15749, 149056856937163565719889897879860429),
  (15781, 149309854938833942253248003115386190),
  (15813, 421630899377721532509727752063886673),
  (19748, 294694164169814010531618718660490509),
  (19747, 294694164208501049069807527709410772),
  (19746, 273924976773757275645534775348626702),
  (19745, 273924976773151325485652453392479502),
  (16773, 315859076564167657502716857927148881),
  (16805, 316117050990778003988370104308802897)]

theorem tbl23_8_ok : tblOK 23 tbl23_8 = true := by decide +kernel

def tbl23_9 : List (Nat × Nat) := [
  (16837, 318038970230831859646996404101784913),
  (19716, 294709375976413698685140424579708175),
  (19715, 294709376366910830467873098936395220),
  (19714, 273940188932785176308973181722207700),
  (19713, 273924965752253059342927060621128974),
  (17797, 315864169685503479125219805699077522),
  (17829, 316117050991165907863953798260159890),
  (17861, 318435417972460331587313002556974482),
  (19683, 294709376015099324912818173577299412),
  (19682, 273940188580960014398696256980157908),
  (19681, 273940188580354063085548909224097038),
  (18757, 193814607605114890382825775279441294),
  (18821, 190600239347868588866269282799781262),
  (18853, 190848231044811245309397197370492174),
  (18885, 190848231044801800576431458080064783),
  (19651, 294709376015703787822625488147875284),
  (19650, 273940188580960014398352735787091214),
  (19649, 273940188580354064238470413830944014),
  (19781, 187612614842481445772148569936831825),
  (19813, 190255517593416988217469004324594957),
  (19845, 190503329554263515509159634737591764),
  (19877, 190848226997908605928370472700704014),
  (19909, 190848226999117457961008792059311373),
  (6305, 318095063752419198288367913656976718),
  (16577, 273935100768031091782538624954594638),
  (17601, 273935100762844995090046165385278734),
  (18625, 273940171365303604502180666566599950),
  (23745, 273950868387946268132109686499271950),
  (16578, 273935100763450562481832891338552654),
  (17602, 273935100763450636262836113103189262)]

theorem tbl23_9_ok : tblOK 23 tbl23_9 = true := by decide +kernel

def tbl23_10 : List (Nat × Nat) := [
  (18626, 273940171365908067394166486944249102),
  (22722, 273950868387946268132109686482498830),
  (16579, 294704288197589872995954876721231181),
  (17603, 294704288197589946776975347008730381),
  (18627, 294709358799980458059258380705920269),
  (21699, 294714446637442569764056248325043469),
  (15814, 421630978605883391051837845412844877),
  (18724, 294694168215498355452884392804418831),
  (18723, 294694146992777719306440420267455757),
  (18722, 273924959558705328641348526505784590),
  (18721, 273924959558100865749362706128135438),
  (16838, 318044040830536444359488198221305165),
  (18692, 294709380022701094185717771630347535),
  (18691, 294709380022701020399585833002796303),
  (18690, 273940192588576831586440780739077391),
  (18689, 273924965748017262937460530700940558),
  (17862, 312552891615016356497258852040648080),
  (18659, 294709358800047377908284005495141645),
  (18658, 273940171365908067394166418224772366),
  (18657, 273940171365303604501899191589889294),
  (18758, 187937133376797059457111958839190733),
  (18886, 190832998014878427983012533244589325),
  (7329, 337241655942618205605536169388217678),
  (17633, 273935100762844995090046096665801998),
  (23777, 273950868387946268132109672611640590),
  (7362, 337241655942708610882178946619495497),
  (17634, 273935100763450636262836044383712526),
  (22754, 273950868387946268132109671538160910),
  (17635, 294704288197589946776953631654081805),
  (21731, 294714446641106900181611475722134799)]

theorem tbl23_10_ok : tblOK 23 tbl23_10 = true := by decide +kernel

def tbl23_11 : List (Nat × Nat) := [
  (17668, 294694168215196123998262210486936975),
  (17667, 294694146992788120941763373383087373),
  (17666, 273924959558648810427624139477546254),
  (17665, 273924959558043169254834191759635726),
  (8385, 337241650990858046127829667044152657),
  (8417, 333637100182404838718785033363858769),
  (23809, 273950868390656846720028429903242644),
  (8386, 337241650986358392012815012980397390),
  (8418, 333637100182404838718786404230178129),
  (22786, 273950868387946269593501224896591316),
  (21763, 294714446641106900235624228488832271),
  (20740, 294714446641106900199688331691070933),
  (9409, 358010838419893311098267235277145486),
  (9441, 358335356973551737825102822156629391),
  (23841, 273950868329917828790607486113375502),
  (9410, 358010838420497774008070151784433038),
  (9442, 358335356974156200734915354021365206),
  (9474, 358335378195898576049697355521140111),
  (22818, 273950868329917828790607486096602382),
  (9475, 358340448664798915987453448295642514),
  (21795, 294714446641106006776063975333885197),
  (20772, 294714446641105859202204682866718029),
  (10465, 356037738907599425451125663147279499),
  (10497, 358335358211471620620432901830178190),
  (10529, 354739590397220548307342478322222219),
  (23873, 273925522728921177642230469971477774),
  (10466, 356037738907599425450844188170568843),
  (10498, 356104619995783175179818244903871887),
  (10530, 354739669957228396951596560467965330),
  (22850, 273925522728921177642230468897998094)]

theorem tbl23_11_ok : tblOK 23 tbl23_11 = true := by decide +kernel

def tbl23_12 : List (Nat × Nat) := [
  (10499, 356104621233695249201182775049004431),
  (10531, 354739669957228396733740168471168139),
  (21827, 294694164227838918093632301073757453),
  (20804, 294694164227838918111735461307020621),
  (14757, 149309853369383355197903165814801679),
  (14725, 149051786332680089183338383657465101),
  (11489, 377137546758897351534605341306705100),
  (11521, 377178043569367644302243489785902478),
  (11553, 377177159607706111806855607644939468),
  (23905, 273925515375941703544079752435164430),
  (11490, 377137546758897351516590942797223116),
  (11522, 377178043569372386120903447997642126),
  (11554, 377177160845646151095028572017739155),
  (11586, 379429788201675914491951698629149267),
  (22882, 273925515375941703544079752418391310),
  (11523, 377137567961976638444329297924388237),
  (11555, 377177160845646150877452834759562444),
  (11587, 379434154646791912544618720639119956),
  (11588, 379434154647094217787610145933034767),
  (13701, 400533066057016748578245059371623888),
  (13700, 400527050945967550991041508522394895),
  (13668, 127886400081066701209827232343487758),
  (13636, 127633482543705768108366762267137490),
  (13699, 400528645647916572687408199487734487),
  (13667, 127886400081161653605159883035706638),
  (13635, 127633485025370224321693924651988434),
  (13603, 127308981398900270409344140597274066),
  (13571, 126984391046824851788232306324206862),
  (12545, 130538471055001762771403222271190221),
  (12577, 127303910777150401469905041704412365)]

theorem tbl23_12_ok : tblOK 23 tbl23_12 = true := by decide +kernel

def tbl23_13 : List (Nat × Nat) := [
  (12609, 127628414417184859629496507112674507),
  (12641, 127951988327375209233340275405415629),
  (12546, 126979319186891313949283919305991374),
  (12578, 127303910777150401469900643657901261),
  (12610, 127628414417184859611482108603192523),
  (12642, 127951988327375209233058800428704973),
  (12547, 126979319186839591369407108893697229),
  (12579, 127303910777151724983822883671827661),
  (12611, 127628414422667078611557215857337549),
  (12643, 127951988678251815284204515855230157),
  (12612, 127628435519881314199588693530436813),
  (12644, 127951988678256534192204346656613581)]

theorem tbl23_13_ok : tblOK 23 tbl23_13 = true := by decide +kernel

def tbl23 : List (Nat × Nat) := tbl23_0 ++ tbl23_1 ++ tbl23_2 ++ tbl23_3 ++ tbl23_4 ++ tbl23_5 ++ tbl23_6 ++ tbl23_7 ++ tbl23_8 ++ tbl23_9 ++ tbl23_10 ++ tbl23_11 ++ tbl23_12 ++ tbl23_13

def mask23 : Nat := 282907825124312559006379844629280819796492845207488622436848789659815700683847864654920660484728236427705883697577263146644650147044021979682221572085663867685611963369232813893212179715010930294201031341615537982244104572372360050955454448702503952404414767553876376400172028783256347000563846183220340724422346922233803815677942433493607327565340660348214649263846389196013495274147930779479520486151316105689380873426116293556715301553913928203370873471924132265291213782079073777875914979142480451116952928624322351047994405921137430291532992277569855773294719203521343976843574153817690704045008500817065984111330352466040983302863422500085069605802617846516644015303606082744778217745226930501160928125269496004088756404261190245538198326660288835071656404937633962730140953949860665411886217050158374090052258917253320168648243450381527121723356402843250266033809355368354334129436813562384476733352782553062170852632476328754586960079005639454918774124833407871640496572580327854889664092530781432455905429048272909231421912240205354553479759846986129009629723640680610196827619732224308440138903952729100976653190983567621144381459991857109189748909202837001953659475317141745473530506435259093710008811806928695978049349307020434023944041331651222214416329104784656678685691430799103571503532381121747574261818709165605439933878624423345675600843679506642985347474095824557035729645764895960524623052180560581259641995293698259308462700020126440781074721651347729117625292527384972035531192369464108826566971308231279738665422189360988630372710862002647124949166184355154006170761397722146192493823618004409721872025043641684112444300534911454021041017180707387983372474305173653328424964634626677010235398445653005212452859487674186826619360484558844653431475873998030951755960018048051108876401109790065113253225003786766786300670373402391437656262007237051784294259996226268002784198743101418222783949944183555432156988568874550121514815757907884458540686944833562828370142099136386496565468981605349995497417461661878889808661865251515941526395815312421606697409191215487559728416093396894254988887048021041461060482799012668796177542648972347880460112142487374241266180712659481729165795823803340776214460687711853964061915658180857706406167532271226848090949569223511270915979633731083280558750472471639240876809008785218501576891126237632374257884323739508786038095203940557671768534646484983430474257872020279172630194222736948919752356341763611954649172381946259708777956280886900275695775100977951567811559831374262457378400481287597828518925272582759351884840033540300775777159712198235590675150349485474220342468277910048657831250327588653928973245681216973592022261530923506358319277652636145113639725517479710559563260492175587417770173802418594895671181265183543673319475273512107105903369013810840948450852049211889256510638302582954842862017217895879685059597061944194869101096759554311565187453759288846284145559964715037597359728935913226475560729311206866943926642161639235220903706609620237804167383224263692387188695250622687739309638169410079492909876685323314024282515525982754744501758505514854341962629527352826606290941222785921000570090810294581641613200850696338912786681400440131961670311279175205426937968260100428216467634916047635060462809407740440503556954198492552317685921765882173365958680366612966565538844166309822510805790209033145903509753658797804730798289239224993644580176112436204327950929998440485621698560064041162630453540174589234117282646006636097221993974429396868844873080037708939037461836433278715235247390587742793972998415517702797927346280906550047436698277090372857807982290328650096029207010245231998324359126797454431638485357628014852931476585660506874655005837285875856487789006409273389986423530715090596452669685240796998154935352706260389857782215740366300709076865475944494570320358892439685312682553504275371920191224002587688334230068248546294314095209372169736765049092119828718247020620768821971800724462982937894363203225506119083797056851952530835941994032718648553940024436847286813381102604910200824792552064665804918055668470600009809877599548215210153536367989218453506214335464762025221762904208792581318141284604852806279745818976117590876797073248879303774571976115539064503227302116945128671658575982823434622126132217299345476292196258157418253432267082515686729598102363742177297905916529953644421086617626793308900313606960597649420902165866129938979662207118188492210673025936289257788296651486854612574934140620299182890180098782702799388581682725923735008603969406914549656910019009466683076948273925621950254752555234892367465345871150441344188818833770119831440848135832767525602035639926498276587727783014363382798656309166470129061642604730214084351390466050698869539049039334775190245104652037630505498601496193949924749342942462819628997757315447515312006978715594957860205019624882774697319872999302586445119775761797470586028537589783674976015180195520786493770732090917904085525184871284629413898192507243915413751958598348508584737197875106890873676616507797420453557869069835460594830301754806132541499545939841594542575070891303024344616246159462807198781226631170025487735364297010593058437835695290524169407632066977779783486127833403266381749935738001497550130722285756380531059706329069648610540298354101048049220745040471041379085707286619364500767871141351791199907333330079754758458175822372575214549497957198763891685620346500982367018613847366716711575830956722646249828700161496445164338573774951697112466619256082253574843649785345697489832392399984480232287485871183421244332550590694767153179279999410691519161969426788930340636493320682518987382278402702646754894114938716187060769165352263484299221952029647756320849952101488845745063736553211638918515485722585677422438604379848271659671405725536907739050290357655209528523958301720793947056892781747587477894662661220144796399749188575156237260201972735882987007140846269285315732584413276658286613113401251211432699486118100701336024998596699770998109997003281080714423243828551970930224597591898507535034539078252418908982581680683225445200420464825633255415770778190911709346419602770964237331636059499379257286170779371989733405597621374008034568188692225092712896165873768195647446338121996473423468701866573018403192976383439774104694784169774405492207264449880094658021270622489273902078395397773463325637594140923636605174180221372921876594359236563629939582086961697275912921010058469323854131918460470690835532288026662350579461097881355775375659676265565785518664043208016895222566880838216893831401005001299053662307271845627657569791168681949038275894342306652679749818747626796168752296334464267345689880490164927039007860659246107577018426939748057678379972224663531919749194710646155868732240994507072737826066898216596741816319108179992541536885255332211692787013835425154352829380380920960228163301550941788995847373261484545146208708225186828259511976095782748229654986738007756282891510507597378419060031587047558931849117120396297349784158450304353579871088229539905622833947608564593000103036571385777653408927352595536679162341591148829566509548015052267264659586802608003345903030763146262611338113851533997847093844698162983147348910715740539517772922525718879332236940704715204870787062300672

theorem mask23_eq : maskL 0 (tbl23.map Prod.fst) = mask23 := by decide +kernel

theorem cov23_1 : coverX 23 mask23 1 = true := by decide +kernel
theorem cov23_2 : coverX 23 mask23 2 = true := by decide +kernel
theorem cov23_3 : coverX 23 mask23 3 = true := by decide +kernel
theorem cov23_4 : coverX 23 mask23 4 = true := by decide +kernel
theorem cov23_5 : coverX 23 mask23 5 = true := by decide +kernel
theorem cov23_6 : coverX 23 mask23 6 = true := by decide +kernel
theorem cov23_7 : coverX 23 mask23 7 = true := by decide +kernel
theorem cov23_8 : coverX 23 mask23 8 = true := by decide +kernel
theorem cov23_9 : coverX 23 mask23 9 = true := by decide +kernel
theorem cov23_10 : coverX 23 mask23 10 = true := by decide +kernel
theorem cov23_11 : coverX 23 mask23 11 = true := by decide +kernel
theorem cov23_12 : coverX 23 mask23 12 = true := by decide +kernel
theorem cov23_13 : coverX 23 mask23 13 = true := by decide +kernel
theorem cov23_14 : coverX 23 mask23 14 = true := by decide +kernel
theorem cov23_15 : coverX 23 mask23 15 = true := by decide +kernel
theorem cov23_16 : coverX 23 mask23 16 = true := by decide +kernel
theorem cov23_17 : coverX 23 mask23 17 = true := by decide +kernel
theorem cov23_18 : coverX 23 mask23 18 = true := by decide +kernel
theorem cov23_19 : coverX 23 mask23 19 = true := by decide +kernel
theorem cov23_20 : coverX 23 mask23 20 = true := by decide +kernel
theorem cov23_21 : coverX 23 mask23 21 = true := by decide +kernel
theorem cov23_22 : coverX 23 mask23 22 = true := by decide +kernel
theorem cov23_23 : coverX 23 mask23 23 = true := by decide +kernel

theorem cert23 : Cert 23 tbl23 := by
  refine ⟨by simp only [tbl23, tblOK_append, tbl23_0_ok, tbl23_1_ok, tbl23_2_ok, tbl23_3_ok, tbl23_4_ok, tbl23_5_ok, tbl23_6_ok, tbl23_7_ok, tbl23_8_ok, tbl23_9_ok, tbl23_10_ok, tbl23_11_ok, tbl23_12_ok, tbl23_13_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask23_eq]
  interval_cases x
  exacts [cov23_1, cov23_2, cov23_3, cov23_4, cov23_5, cov23_6, cov23_7, cov23_8, cov23_9, cov23_10, cov23_11, cov23_12, cov23_13, cov23_14, cov23_15, cov23_16, cov23_17, cov23_18, cov23_19, cov23_20, cov23_21, cov23_22, cov23_23]

/-! ### `N = 24`: 462 witness orderings -/

def tbl24_0 : List (Nat × Nat) := [
  (13569, 8375560925350357535862321188641240334),
  (13601, 8147773852585920337251758749309281742),
  (13633, 8168549146794230377605004964696257806),
  (13665, 8189317379756353530406644886267553036),
  (19873, 18757558097830680821484034471262750031),
  (20897, 18757883797437376842300938201545639247),
  (21921, 18757883797437457787784239660524438927),
  (22945, 14872711463348474189543966120969298453),
  (23969, 14872711384100968862164118805983060630),
  (24993, 14999278381188648946421552589422731735),
  (14625, 17531198690524375034357201528806245711),
  (14657, 17531197503630005900029525359396455759),
  (14689, 17531167226116684685125122981529453903),
  (14721, 9534731939495475956622111213929690445),
  (20929, 13545760883534322519044867500988761423),
  (21953, 13545760883534403464528168959967561103),
  (22977, 14874988879318667815617028778004120911),
  (24001, 14874988879318667815622698660812391759),
  (25025, 16100435751602317315260712765262702037),
  (15649, 17531198690524375034357201528806245710),
  (15681, 17531197503630005900029525359396455758),
  (15713, 17531167226116684685125122981529453902),
  (15745, 18758821935711213078797092524765812048),
  (20961, 13545760883534322519044867500988761422),
  (21985, 13545760883534403464528168959967561102),
  (23009, 14874988879318667815617028778004120910),
  (24033, 14874988879318667815622698673596565013),
  (25057, 16100436459872924146020343156215453008),
  (16705, 17531197504867950663879989547027723534),
  (16737, 17531167305364190014701895684955632910)]

theorem tbl24_0_ok : tblOK 24 tbl24_0 = true := by decide +kernel

def tbl24_1 : List (Nat × Nat) := [
  (16769, 18758820995092335713912512091942622607),
  (22017, 13545760883553665334357302610870990094),
  (23041, 14874988879338010702518375907470406926),
  (24065, 14874988879338010702518464545675904270),
  (25089, 16121139508814858516791351972720375054),
  (17729, 17531197504867950663879989547010946318),
  (17761, 17531167305364190014701895684938855694),
  (17793, 18758820995092335713912512091942618511),
  (22049, 13545760897285268071136761449041438223),
  (23073, 14874988893070183964651014969246164431),
  (24097, 14874988893070183964651016360710129167),
  (25121, 16121139508814858516791351904000898318),
  (18785, 17531167384239673009450598295240766734),
  (18817, 18758821073969234662510315120174630223),
  (23105, 14874988893070183950816203363432076751),
  (24129, 14874988893070183950816203363432076687),
  (25153, 16141964694466075143771101570988516815),
  (19777, 17531197482391905032431304813812970766),
  (19809, 17531167384239673008297676790633919758),
  (19841, 18758821073969234662510310722128119119),
  (23137, 14875049331605310163469723789269206351),
  (24161, 14875049331605310163469723790342161807),
  (25185, 16141964694466075143771101569914774991),
  (20833, 17531167454918310656564860470890935822),
  (20865, 18758891743150014358476902228742440271),
  (24193, 14875049331878858108489655165626975569),
  (25217, 16162738952795495360365217520699929937),
  (21857, 17531167454918310656564860677049365774),
  (21889, 18758891743150095668195015863358784911),
  (24225, 14875049331878858108489655185071162008)]

theorem tbl24_1_ok : tblOK 24 tbl24_1 = true := by decide +kernel

def tbl24_2 : List (Nat × Nat) := [
  (25249, 16162738952795495360365217521001317841),
  (22913, 14999604017675019813900935275333359055),
  (25281, 16183508140229634671207010998493135511),
  (23937, 14999604017675019813900935275333358991),
  (25313, 16183508140229634671207010998826864906),
  (15425, 17531522089056590800918170373372052814),
  (16449, 17531846607317085617884076464440145166),
  (17473, 17531846607317085617884076464423367950),
  (18497, 17532171125869250435147297049840252174),
  (19521, 17532171125869250435147015574863541518),
  (20545, 17532171119737573974069516477908705941),
  (21569, 17532171119737573974069516477908705940),
  (22593, 17532237916469332107458878248886002197),
  (23617, 17532237995911479303168318064107746707),
  (24641, 17574663165279258407763833787260929359),
  (14626, 9477326362031065150537194367749771926),
  (14658, 9498101661132814218973550409851635219),
  (14690, 9513957679932342455331506846070047949),
  (14722, 9534731939495475957003505332834108749),
  (14754, 9555830716186956536956107298017727561),
  (20930, 13543514622724071953876515224402589005),
  (21954, 13543514622724071953876515224402588941),
  (22978, 14872721624533504837736533362103603732),
  (24002, 14872721624533504837736533704626983440),
  (23905, 17531167375670800607971732926543749782),
  (15650, 18860426667856839056020130342950962709),
  (15682, 18860425483341054572872706357145404949),
  (15714, 18860406409144669783227912861801075785),
  (15746, 18756580754383576882327726882467959881),
  (15778, 18756585824988669766655527271390787090)]

theorem tbl24_2_ok : tblOK 24 tbl24_2 = true := by decide +kernel

def tbl24_3 : List (Nat × Nat) := [
  (20962, 13546119866338675703631882388508841296),
  (21986, 13546119866338675703631882388775436820),
  (23010, 14875347862121200422777252189976986261),
  (24034, 14875312442239127355403123074381448589),
  (23873, 17531167375670800607971732926543749846),
  (16706, 18860425483110810651267663470203565453),
  (16738, 18860405442354286188944224588774306390),
  (16770, 18886109213444350859977778097250207122),
  (16802, 18757233579315703300153007618033522063),
  (22018, 13546119866338755670012804437702153615),
  (23042, 14875347862122717717030622511484441935),
  (24066, 14875347862122717717030715807603168591),
  (23841, 17532789730754605198812635926014780054),
  (17730, 18860425483110810651267663401484088717),
  (17762, 18860405442354286180879953245047195023),
  (17794, 18886108975798548943412433450208953746),
  (17826, 18757233579315703300153073998895027734),
  (22050, 13546119866338755670012804437702149519),
  (23074, 14875347862122717717030622511484437839),
  (24098, 14875347862122717717030715807603164495),
  (23809, 17532789968400407115377980573056033430),
  (18786, 18860405521601791434464969427045676367),
  (18818, 18886433466887523799453359869320819285),
  (18850, 18757558097869366448846609573511759183),
  (23106, 14875347862123019948483305155273229647),
  (24130, 14875347862123019948489256511984469327),
  (23777, 17532789968439088019239165837001417366),
  (19778, 18860425483128278831002870492956521741),
  (19810, 18860405521601100996872029959320556052),
  (19842, 18886433466887523799453359868247077461)]

theorem tbl24_3_ok : tblOK 24 tbl24_3 = true := by decide +kernel

def tbl24_4 : List (Nat × Nat) := [
  (19874, 18757558097869366447693688068904912207),
  (23138, 14875347862123019947330383650666382671),
  (24162, 14875347862123019947336335007377622351),
  (23745, 17532789968439092741605648706646631062),
  (20834, 18860405611894935288661968668718330453),
  (20866, 18885475149227905222846566262511563352),
  (20898, 18757883797437376866697473784542233935),
  (24194, 14875347862123373960056893881004651030),
  (23713, 17532779825983105739393362563796886032),
  (21858, 18860405611894935289007870565265191512),
  (21890, 18885459938652546463731199004577203602),
  (21922, 18757883797437457787790191018309158287),
  (24226, 14875347862123288315445053747962376724),
  (23681, 17532779825983105739393437256380375382),
  (22914, 14999962986727855811568037067174511951),
  (22946, 14872711463348474115756989826131091989),
  (23649, 17532774703597835187512833269998044560),
  (23938, 14999962986727855811573988423885751631),
  (23970, 14872711384100968788377142511144854166),
  (15457, 17531522088763502581936628622367458638),
  (16481, 17531846607317085617866062065930663182),
  (17505, 17531846607317085617866062065913885966),
  (18529, 17532171125869251850571239037138171150),
  (19553, 17532171125869251849418317532531324174),
  (20577, 17532495634563865207217331948015641112),
  (21601, 17532495634563865207217332154174071316),
  (22625, 17532774703597835187712890710808425743),
  (24673, 17574663165279186926797503278078850383),
  (14627, 9477326386979945104935699335043712399),
  (14659, 9498101661132814218973550409851373075)]

theorem tbl24_4_ok : tblOK 24 tbl24_4 = true := by decide +kernel

def tbl24_5 : List (Nat × Nat) := [
  (14691, 9513957680321974663047260218577159699),
  (14723, 9534731939501554322741956158361273681),
  (14755, 9555830716186956536956389046793373009),
  (20931, 13543514622724073439867600635870414159),
  (21955, 13543514622724073439867600635870414095),
  (22979, 14872721624533504841171966307919000845),
  (22882, 18860405611888252456447954542944637460),
  (22881, 17531167454918305935351580241529987605),
  (15651, 18860426667856839056020130342950700565),
  (15683, 18860425483347146060063441810767287632),
  (15715, 18860406409144669783228194610576721233),
  (15747, 18885799905446708379145026681731302104),
  (15779, 18756585824988669766655527546151261714),
  (20963, 13546119866338769859195560845285332304),
  (21987, 13546119866338769859195560845551927828),
  (23011, 14875347862120596033654421170227839637),
  (22850, 18862089663197434583434411107187216916),
  (22849, 17531167375670800607971728528498287883),
  (16707, 18860425483110810651273265483020825997),
  (16739, 18860405442354286188944224862261548431),
  (16771, 18886108896570385988625683275628221142),
  (16803, 18757233579315703300153007616959780239),
  (22019, 13546119866338755693249060127021012367),
  (23043, 14875347862122717716994598112511989071),
  (22818, 18862089678033041903176286849029965135),
  (22817, 17532790047628569629643993821246972437),
  (17731, 18860425483110810651273261084974314893),
  (17763, 18860405442354286180879953245046932879),
  (17795, 18886108896570385988625683275628217046),
  (17827, 18757233579315703300153073998894765590)]

theorem tbl24_5_ok : tblOK 24 tbl24_5 = true := by decide +kernel

def tbl24_6 : List (Nat × Nat) := [
  (22051, 13546119866338755693213030856481908111),
  (23075, 14875347862122717716994598112511984975),
  (22786, 18862089678033069942279364952379426127),
  (22785, 17532790047628569629643993821246972501),
  (18787, 18860405521601791434464969427028899151),
  (18819, 18886433387657562057813304639303255371),
  (18851, 18757558097869366448846609504792282447),
  (23107, 14875347862123019948447557833230976335),
  (22754, 18862089678033069942227278887548421455),
  (22753, 17532790047686593346619013151987655189),
  (19779, 18860425483134066891273165838827189517),
  (19811, 18860405521601101000307462905135953165),
  (19843, 18886433387657562057813304638229513547),
  (19875, 18757558097869366447693688000185435471),
  (23139, 14875347862123019947294636328624129359),
  (22722, 18862028204656544590081870323047518740),
  (22721, 17532790047686598068985496021632868885),
  (20835, 18860405611894935288662250417165505871),
  (20867, 18885475069980399895360893151534924504),
  (20899, 18757883797437471976915016492410541391),
  (22690, 18862028204657149056409377659917497613),
  (22689, 17532779905211268693011437013684208977),
  (21859, 18860405611894935289007307677472409105),
  (21891, 18885459859405040695830614763201172182),
  (21923, 18757883797437457810968489388081747343),
  (22658, 18862028204657148833159998240575550733),
  (22657, 17532779905211268693011437013684213073),
  (22915, 14999962986727855811532289745132258639),
  (22947, 14872711460872594110973205571171050005),
  (16513, 17531846607629587318285344235392660750)]

theorem tbl24_6_ok : tblOK 24 tbl24_6 = true := by decide +kernel

def tbl24_7 : List (Nat × Nat) := [
  (17537, 17531846607629587318285344235375883534),
  (18561, 17532171125836056847387660949784982798),
  (19585, 17532171125836052125021178080139769102),
  (20609, 17532495635834092142476528808487126350),
  (21633, 17532495635834092142476528808487126286),
  (24705, 17595432352713397717125035568020653390),
  (16514, 18861074603102081697505808986745370134),
  (17538, 18861074603102081697505804588698859030),
  (18562, 18861399121655074419301635984413488461),
  (19586, 18861399121655074416667695266276373773),
  (20610, 18861723636575956566035830331173565773),
  (21634, 18861723636575956566035830331173565709),
  (23682, 18862028204657148833160020162091471190),
  (15684, 9498101661094128592745600801284326931),
  (15716, 9513957679913088930114934522461840915),
  (15748, 9534731939495175137750460419380381205),
  (15780, 9555830715778007630922291091509151054),
  (15812, 26629404891606354041320318124117001549),
  (20964, 13543514622724071880089538929547601229),
  (21988, 13543514622724071880089538929547601165),
  (21827, 18860426605863736931482828876991792399),
  (21826, 18860426605863735445491743465523967245),
  (21825, 17531197482391903562748808630206543118),
  (16708, 20189653478895726524171189055490418061),
  (16740, 20189633438139202037565269807165965709),
  (16772, 20215306838653464146287445540325107089),
  (16804, 20231491263434537381636884450750047633),
  (16836, 20381074031512385401302474110914102673),
  (22020, 13546444384892414095586666089099105678),
  (21795, 18861724680077448586082621688108872973)]

theorem tbl24_7_ok : tblOK 24 tbl24_7 = true := by decide +kernel

def tbl24_8 : List (Nat × Nat) := [
  (21794, 18861724680077448586082621688125650189),
  (21793, 17532495556548508830314439053902951694),
  (17732, 20189653478895726524171188986770941325),
  (17764, 20189633438139202053777858200158438798),
  (17796, 20215306838653464146287445540325107088),
  (17828, 20231491263434537381636884450750047632),
  (17860, 20379775948690209303485346588731975053),
  (22052, 13546444384892414095586666089099101582),
  (21763, 18861724680077463944131367899975153168),
  (21762, 18861724680077463944131367899975415312),
  (21761, 17532495556548504107947955637727584852),
  (18788, 20189633517386707307369053564222666062),
  (18820, 20215631357207127295273434484479690059),
  (18852, 20231491342682042718094276750374409552),
  (18884, 20400642189344092196172655404910736589),
  (21731, 18861724680083238666110014898519164433),
  (21730, 18861724680077160300366237770247144717),
  (21729, 17532495556606537269655941254288585998),
  (19780, 20189653478918982837945653320459543821),
  (19812, 20189633517386021521772762141713818893),
  (19844, 20215631357207127295273434483405948235),
  (19876, 20231491342682042718094276750357632336),
  (19908, 20400642189344092196172655404910716365),
  (21699, 18861724680078370638389961501074097423),
  (21698, 18861724680078369152398876089606272269),
  (21697, 17532495556606537269655941254288848142),
  (20836, 13336754874140733520010763335298254221),
  (20868, 13526679899592332104919123245104432462),
  (20900, 13543513493805006994844019995515323923),
  (20932, 13543514622724071880089538929547605325)]

theorem tbl24_8_ok : tblOK 24 tbl24_8 = true := by decide +kernel

def tbl24_9 : List (Nat × Nat) := [
  (21666, 18861723636575956566035830331156788493),
  (21665, 17532495635834699783920278847832798478),
  (21860, 13336754874141035751465666992591930637),
  (21892, 13526679899592332104919123107665479054),
  (21924, 13543513493805006994844015597468812819),
  (21956, 13543514622724071880089538929547605261),
  (16545, 17531846607629587317132422730785813774),
  (17569, 17531846607629587317132422730769036558),
  (18593, 17532171125830566224343570903547573518),
  (19617, 17532171125830566223190649398940726542),
  (20641, 17532495635834699783920278641674368526),
  (24737, 17595432352713397717129859809500235221),
  (16546, 18861074603414881642409910845472568717),
  (17570, 18861074603414881657469652222544807311),
  (18594, 18861399121616388793073967919542367565),
  (19618, 18861399121616388790440308607662486797),
  (20642, 18861723636575956566035830331156788557),
  (23714, 18862028204657149056414413696958255510),
  (15749, 9539645187029416922986367719083902485),
  (15781, 9555830715778007651854735870960633365),
  (15813, 26629404891606355382078795599599142421),
  (20965, 13543514622666043514535013037919798605),
  (20804, 20189654601648651244608574230949324109),
  (20803, 18860426605863736931482828876991792463),
  (20802, 18860426605863735445491743465523967309),
  (20801, 17531197482391903562748808424048113166),
  (16773, 20215306838653464146292554547855435153),
  (16805, 20231491263434537381641993458280375697),
  (16837, 20381074031512375934485290724978922893),
  (20772, 20190952675861759996076621433818637645)]

theorem tbl24_9_ok : tblOK 24 tbl24_9 = true := by decide +kernel

def tbl24_10 : List (Nat × Nat) := [
  (20771, 18861724680077448586082621688108873037),
  (20770, 18861724680077448586082621688125650253),
  (20769, 17532495556548508830314438847744521742),
  (17797, 20215306838653464146292554547855435152),
  (17829, 20231491263434537381641993458280375696),
  (17861, 20379775949928149342770726861483615629),
  (20740, 20190952675861775354125084870341133648),
  (20739, 18861724680077463944131366599608075600),
  (20738, 18861724680077463944131366599624852816),
  (20737, 17532495556548504107947955637727584853),
  (18821, 20215631357207127301019463564941661520),
  (18853, 20231491342682042718093164044607100240),
  (18885, 20400642189344394427627559060056929485),
  (20707, 18861724680083238666104688595774309713),
  (20706, 18861724680077160300366237770247144781),
  (20705, 17532495556606537269655941048130156046),
  (19781, 20189654839275110421447094050632819981),
  (19813, 20189633517386021521772480666737108237),
  (19845, 20215631357207127301019463564924884304),
  (19877, 20231491342682042718093164044590323024),
  (19909, 20400642189344394427627559060056909261),
  (20675, 18861724680078370638389961501074097487),
  (20674, 18861724680078369152398876089606272333),
  (20673, 17532495556606537269655941048130418190),
  (20837, 13336759944743133460859929751690241228),
  (20869, 13526679899592332105247296264126629397),
  (20901, 13543513257352669945076936597881491928),
  (20933, 13543514622666043514535013024016692557),
  (6305, 21583465980352088334256344071447582094),
  (17601, 17531846449173262289756669048287982862)]

theorem tbl24_10_ok : tblOK 24 tbl24_10 = true := by decide +kernel

def tbl24_11 : List (Nat × Nat) := [
  (18625, 17532170967379731818858985762697082126),
  (19649, 17532170967379727096492502893051868430),
  (24769, 17616206626724032272916563733140829454),
  (17602, 18861074444645756668977129401610958358),
  (18626, 18861398963198749390772960797325587789),
  (19650, 18861398963198749388139020079188473101),
  (23746, 18862028204656544590081870665570898448),
  (17603, 18861074444645756668977129401610696214),
  (18627, 18861398963198749390772960728606111053),
  (19651, 18861398963198749388138738604211762445),
  (22723, 18862028204656544593517303268862915853),
  (16838, 10889936631090429201475752008392160790),
  (16870, 10889936624900719560329369989154940305),
  (19748, 20189654839567033096867365519465973198),
  (19747, 18860425407537774107958389136150033677),
  (19746, 18860425407537774107958670611126744333),
  (19745, 17531197411718751816312153424990139662),
  (17862, 21586016484478922399141319377658127757),
  (17894, 21436135589085869055836064805831128466),
  (19716, 20190628395228008375768701764325410254),
  (19715, 18861400399443087780552450631881786831),
  (19714, 18861400399443087780552455029928297935),
  (19713, 17531197807873104900362794512076829966),
  (18886, 12213311872952219465893226491080930637),
  (18918, 12213311872952219465893226491080926541),
  (19683, 18861398963203328522590545220814566669),
  (19682, 18861398963203328522608559619324048653),
  (19681, 17532170967379727095339581388445021454),
  (19782, 12321381543912706728961369208971388173),
  (19814, 12171738335871447236033227678131758541)]

theorem tbl24_11_ok : tblOK 24 tbl24_11 = true := by decide +kernel

def tbl24_12 : List (Nat × Nat) := [
  (19910, 12213311872952219463259004366686582029),
  (19942, 12213311872952219463259004366686577933),
  (7329, 21583465980352088334256344002728105358),
  (17633, 17531846449173262289756387573311272206),
  (18657, 17532170967379731817706064258090235150),
  (24801, 17616206626724032272916563733140567310),
  (7362, 21708405781947258639509874388479832662),
  (17634, 18861074444645756668977129401610954262),
  (18658, 18861398963203339306120063168226100693),
  (23778, 18862089678033069942227278888621376911),
  (17635, 18861074444645756668977129401610692118),
  (18659, 18861398963203339306120063168209323477),
  (22755, 18862089678033069794671340696381490511),
  (18724, 20189654842042913175471652377785599310),
  (18723, 18860425407537774110592611260544382285),
  (18722, 18860425407537774110592611329263859021),
  (18721, 17531197411718756538678636294635353358),
  (18692, 20190628397703888454499058625885832526),
  (18691, 18861400401918967859229608722843895119),
  (18690, 18861400401918967859229613120890406223),
  (18689, 17531197807873104901515716016683676942),
  (8385, 22933462846653312948730893451390190862),
  (8417, 22933462846653312947577971946783343886),
  (24833, 17636965672953369757595473676112590094),
  (8386, 22933787602897551596104774313926796687),
  (8418, 22933787364899655496293226202972652946),
  (23810, 18862089678033069942279364953452381583),
  (22787, 18862089678033069794705693837679723855),
  (21764, 20190952675861775354125086170691696144),
  (9409, 22933462846653312948730893451373413646)]

theorem tbl24_12_ok : tblOK 24 tbl24_12 = true := by decide +kernel

def tbl24_13 : List (Nat × Nat) := [
  (9441, 22933462846653312947577971946766566670),
  (24865, 17636965672957024421920158622428440018),
  (9410, 22933787602897551596104774312853054863),
  (9442, 22933787364899655496293226202972390802),
  (9474, 23037633788852502635683044312094705040),
  (23842, 18862089678033041903176286850102920591),
  (9475, 23037633777732175241060327519665849741),
  (22819, 18862089678033032458461335508249019727),
  (21796, 20190952675861759996076621433818637581),
  (10465, 24262690921319727299589717905721062670),
  (10497, 24283460108753262147194032645153289486),
  (10529, 24283460108753238830509523476280046862),
  (24897, 17657734843364014151277546883482395095),
  (10466, 24263015439873385726316858049486751181),
  (10498, 24283784627326264714029349382279427607),
  (10530, 24283784627326254237449946143360349645),
  (23874, 18862089663197434583434411449710596624),
  (10499, 24283784627326264714029349382279165463),
  (10531, 24283784627326254237449946143343572429),
  (22851, 18862089677955665927273603801634637135),
  (21828, 20189654601648651244608574230949324045),
  (20805, 20189654601590622879054048339321521485),
  (15814, 26650174079431321730359597547344958800),
  (11489, 24136737385504973547643373693276312780),
  (11521, 24135434162717058902783316357000512083),
  (11553, 24135434264440601235541471940039214540),
  (24929, 17657734372758480692229166709983420887),
  (11490, 24136737385504973547643092218299602124),
  (11522, 24135439255813328116866721698044237004),
  (11554, 24135439335043002592189460536361813453)]

theorem tbl24_13_ok : tblOK 24 tbl24_13 = true := by decide +kernel

def tbl24_14 : List (Nat × Nat) := [
  (11586, 24387631763034163788119828219471660365),
  (23906, 18860405611888252456447954885468017168),
  (11523, 24136829391855650337272833291394811341),
  (11555, 24135439335043002592189460535288071629),
  (11587, 24387631755683894439386765945607095631),
  (22883, 18860405611888252459883387488760034573),
  (11588, 24387956274241463276060431005176321360),
  (14757, 9555830715778007651854735857119495503),
  (14725, 9539645187029416922986367705242764623),
  (14756, 9555830715778007630922291091509151055),
  (14724, 9534731939495175137750741894357091861),
  (14692, 9513957679913088930115215997438551571),
  (14660, 9498101661094128592745882276261037587),
  (12545, 8375555853507910555723478231945110797),
  (12577, 8147773852585920337288351111218021842),
  (12609, 8168549145553894850162878665952388365),
  (12641, 8189317379756353530406644886267553037),
  (24961, 14999602899742307373148335745443307991),
  (12546, 8127005621208692521443671876394100175),
  (12578, 8147773852585920337287787477608768973),
  (12610, 8168549145554500560263819462482650381),
  (12642, 8189317379756353530406363411290842381),
  (12547, 8127005620953949793732867564651734285),
  (12579, 8147773852951643562145176130728813837),
  (12611, 8168549145554500560263537987505939725),
  (12643, 8189317380126644312061430159676364244),
  (12612, 8168549145906028135915620750912222478),
  (12644, 8189317380126644298120242592996975885),
  (13701, 25717194397378435600174307581754152272),
  (13700, 25717194397378435594428278500235216203)]

theorem tbl24_14_ok : tblOK 24 tbl24_14 = true := by decide +kernel

def tbl24_15 : List (Nat × Nat) := [
  (13668, 8189317380126644076651236388396397838),
  (13636, 8168549147143968248989639988121523668),
  (13699, 25716899905060127803145172559318549835),
  (13667, 8189317380126644075552353681271485710),
  (13635, 8168549146794239821196831778722870542),
  (13603, 8147773852951643340784247246214198542),
  (13571, 8127005622192192045035615505163810062),
  (13698, 25716899984290089544785227789336113749),
  (13666, 8189317379756353530406363411290842380),
  (13634, 8168549146794239821197113253699581198),
  (13602, 8147773852585920337251758680589805006),
  (13570, 8127005622446631678853854377739888079)]

theorem tbl24_15_ok : tblOK 24 tbl24_15 = true := by decide +kernel

def tbl24 : List (Nat × Nat) := tbl24_0 ++ tbl24_1 ++ tbl24_2 ++ tbl24_3 ++ tbl24_4 ++ tbl24_5 ++ tbl24_6 ++ tbl24_7 ++ tbl24_8 ++ tbl24_9 ++ tbl24_10 ++ tbl24_11 ++ tbl24_12 ++ tbl24_13 ++ tbl24_14 ++ tbl24_15

def mask24 : Nat := 938167194147740806263584082605798587973343505415754576934871715788363211021058525255948934637628610612699504859959566959216682860051384949143411544668893623524420441747041060597272913133916032457102667424395935826034266094644359532125105339609239314369607101178770966621010432426366523716085796759072898573537473234281971745152542166898373305652549803243789631416347232808597058746759628087200371284648014956750924158742211280036887291227297736652797089587759991082796789095775693215904878068135778169060924346890064050262199507095847502895029469830474453995481852226393365347894376457024561345479568471759790256593255493087943392917992861054409750716787257315701483427687435955115096342075862604415178173138588082437926401339962134398045337775174489403988203797518130321213530211028699994547690568100467518166740195493066075408535070840482663018612394669252561892563198064113681738531166286763213644974973729295809475366679242138015883316311505604329144764098218300253656822255567444769657972032671265109853930846069106174410547001284532054703361538319584079639982274900995946943233121317380849263375359478688976432494126670211093782886414200874292352966336451781830039814324720873578296751355329916645213357870535440858346318832579927893513423769577368466534440849235180301102326502928252672894050910175703825483653946525684671245282766072377371567685064256238104843676150289873616123473829327046857348608184914344385453769742239976467174621819654158031974800519597179525335647189735019506264256617083663852422334656399144067924261307702588762595425425064156263441611745706053054631766251653049506281490842734247502597375060985257478262555854072280713693146552831346770919703249890111942644486339227603418221085266849946203222204252078467526624276667468090890258625609359710677009323068057727204769063518798633506771188461498162317005813299344523380182530670250154739389366965099327341224224969988779460919085413524813476738224009964380476856016149467510703691152056032736832620407856011774190759066486782426303438882131110787436789104192734066722021960344756476171362465985359885746976219146137201976822362639576616969468695376299250910584511983470366567241260338563270037566240636319725907334466410654836971729294581841007815912233837644045590006339098585286317065281288065089963634671236993874274667117858618325858467914984304484768107339451295166089632247007477515793759712370481567770860377798524415489309495043041986697782988983974867759818343898317102354875608754518238655166295237288508035030988557694236151281810253437819252283629660920047471885310914940819824252647209257124568446598881739013524621954246346351718405333027677941818988939366682863606247452284064604726622844117366162008424762983749373703521854591934103659060348999012273653328581974937670351253073438422013852927095191423487759668862960746980057843967192297684085041555364931586451147002278843694960125699304164353993456890558538231396630418560542798291516622379365762955020662820394364987310410044965899397613893952774703101106646721086483581137298219338642561499165031420492665142364854380866349501768652353154881233906461433822666935571682899047976787035310263794057246127952337106462213218911695372932919636958660455613468985217154724338823318885040836092541341495401873197375913158587393412718763899805576246241020644270846266798446788407416328844401529711449174191166575417940405851164938048361594999771522062520785144696177625771401613479352116472419138346957605247901646145155797698150674116028439597939612606456505392311191385991475262360792583516771472496182550841709401474656683079483386704319346605359827604745351436567938338160008385653463953430005215053727295372284579852024105486160890785986982513837586510881178372067619762883248303682720276858761455818346215529113101949176694034631638632457843879472874011284669336637617679543517954547198573776171310065565080307723971876402156655549755650897017107665154040338564360058954294098900119984179257277353463065907985911327656007874359685739397553547936411275642442454121752394181540777483470908117192928308276069805035604444329093450865411618622800362561721960694204907489472083205173863273866796276950263588930643185791357674393307563156101920190050617712831990203644657875083356061602822436338101296427080743978189269691056339104179578849576566304354114890520009300806430533337266070118063397620327443069142062809609388615158403587008047711707266579300654925093260012371301458164852493340762825727198736969503362306534436182765250372011195981619512449639509628427513450634613625850536744138503369638842180953581390758860788535384344760807165263139049762564923126379255576310445054321411918894562183922589501221070254974756708032440122945097574128748506113927553483978547643387093455782462268967769296642691487279638501020298518533773684684851801497717752480924313213451632316621687792176803069547168884952571376182305447643614749349332124681709173062903343735625973219697488342121772072198768675406186992366197318948932125294971890093489018545282048080180593467826449086182920069422455517853072816999988231741066403557138125650123048307583209599971966723163304701968597169453530583145024933913462901478077810868371298927352014466902400826888460055964564916004970256217071698397466707222523800191125530682792521486682624350895594823543360788320650282356032006473849007147978065155869641645922310107104631358655232775835374230728632202359250270772606047103912401442100825496686855011178927706952523059512192523326123655833405500807068604406804170112147884235259065713571564377030066745427568497896985967164760149042800020900199353588011778639300928957386840917906220290136278606105236247003116337606302828347485824369747300376897670159839106419645222694136279157164137219731302135972850700073558377034405981799483882881129376255776320550962380944705580002697608604809940779280684483365999820012978747193695779216506382489363951954666366760779185788607994557556518531812349761242621125254925103291490863885227735131010647462710625956685565931147273492164280665303253018469766806248871403592255779459343789634591396849082907578985013344443666327611246296364828605567034469381976195378019747388978945200938495109210145617769551953954403310597120185898516028950279980964183104482362200252288166154847982742929522916083551867705209617952881989199064493850725316285269353728427488470101182803313788198688348996889464969974830004311526896381328242556527043023761545028047829468139758540560387226530721180521378637198753079195827910464285531111545613041186450380939424571320936538497184598344259810625488921707084724956836691373372649870009242334061494021217832655802139167412474964425302928460843445606514848080498516386302097176709160671989289502796832041313873038953956753705109658038618285625402722500923438434872245959387275636907574981086591647621217775677981104716815383882382474967072303775535019612098296001150093803260270686282832032412980663429322874341397051728574080178651148124091663577317167453232058120733037387288840843151396058308607252071254329234114365435364251451431209641457923548403956219972728627384855685724448569341804892471414518104141419905799029641079921128450790494764869279305965774114355613984902874157734682634413925425705229107124463630675485600709210376651286040767418314908370845886567705952546185305373198521261175742870507697753902121418338513552243692851534722198879172475685562079473978284406410762362612908157814870020902914681161650060032930228376863127363843866315618345459849048098725577961419955085546379976932921812383030477283143072176769167036159426773580689070190063702236170682560198247394326101819246577815226818311158221298156538167296

theorem mask24_eq : maskL 0 (tbl24.map Prod.fst) = mask24 := by decide +kernel

theorem cov24_1 : coverX 24 mask24 1 = true := by decide +kernel
theorem cov24_2 : coverX 24 mask24 2 = true := by decide +kernel
theorem cov24_3 : coverX 24 mask24 3 = true := by decide +kernel
theorem cov24_4 : coverX 24 mask24 4 = true := by decide +kernel
theorem cov24_5 : coverX 24 mask24 5 = true := by decide +kernel
theorem cov24_6 : coverX 24 mask24 6 = true := by decide +kernel
theorem cov24_7 : coverX 24 mask24 7 = true := by decide +kernel
theorem cov24_8 : coverX 24 mask24 8 = true := by decide +kernel
theorem cov24_9 : coverX 24 mask24 9 = true := by decide +kernel
theorem cov24_10 : coverX 24 mask24 10 = true := by decide +kernel
theorem cov24_11 : coverX 24 mask24 11 = true := by decide +kernel
theorem cov24_12 : coverX 24 mask24 12 = true := by decide +kernel
theorem cov24_13 : coverX 24 mask24 13 = true := by decide +kernel
theorem cov24_14 : coverX 24 mask24 14 = true := by decide +kernel
theorem cov24_15 : coverX 24 mask24 15 = true := by decide +kernel
theorem cov24_16 : coverX 24 mask24 16 = true := by decide +kernel
theorem cov24_17 : coverX 24 mask24 17 = true := by decide +kernel
theorem cov24_18 : coverX 24 mask24 18 = true := by decide +kernel
theorem cov24_19 : coverX 24 mask24 19 = true := by decide +kernel
theorem cov24_20 : coverX 24 mask24 20 = true := by decide +kernel
theorem cov24_21 : coverX 24 mask24 21 = true := by decide +kernel
theorem cov24_22 : coverX 24 mask24 22 = true := by decide +kernel
theorem cov24_23 : coverX 24 mask24 23 = true := by decide +kernel
theorem cov24_24 : coverX 24 mask24 24 = true := by decide +kernel

theorem cert24 : Cert 24 tbl24 := by
  refine ⟨by simp only [tbl24, tblOK_append, tbl24_0_ok, tbl24_1_ok, tbl24_2_ok, tbl24_3_ok, tbl24_4_ok, tbl24_5_ok, tbl24_6_ok, tbl24_7_ok, tbl24_8_ok, tbl24_9_ok, tbl24_10_ok, tbl24_11_ok, tbl24_12_ok, tbl24_13_ok, tbl24_14_ok, tbl24_15_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask24_eq]
  interval_cases x
  exacts [cov24_1, cov24_2, cov24_3, cov24_4, cov24_5, cov24_6, cov24_7, cov24_8, cov24_9, cov24_10, cov24_11, cov24_12, cov24_13, cov24_14, cov24_15, cov24_16, cov24_17, cov24_18, cov24_19, cov24_20, cov24_21, cov24_22, cov24_23, cov24_24]

/-! ### `N = 25`: 530 witness orderings -/

def tbl25_0 : List (Nat × Nat) := [
  (14625, 606549278403389979390153053498574439759),
  (14657, 607878440076402553040805101307134313675),
  (14689, 609208063977925844898983049314040874319),
  (14721, 610537225744982826428743481805452145997),
  (14753, 611861935983878883764217505666612397391),
  (20929, 868114416823172644123067846731157800271),
  (21953, 868114416823172543872134811038713442841),
  (22977, 953185008245082718703463438385750798869),
  (24001, 953185008245082416473161737162579833430),
  (25025, 1030386426095927499573318016421505331735),
  (26049, 1030386349726461446568065775802330973583),
  (15649, 1208396865588097063327334300532204700374),
  (15681, 1208396783766643594671086911618994738576),
  (15713, 1208396783449730958781129009853754578320),
  (15745, 1200400327077325357417398274704376399245),
  (15777, 1200400728424715809640066789139596023184),
  (21985, 868278698795085991647726421244857128336),
  (23009, 953349290547742517354651260145702872529),
  (24033, 953349290547742517354651260145719387537),
  (25057, 1030446785933143610222182025569432606098),
  (26081, 1030446785933143610222182025569432602002),
  (16705, 1208396783766643595113771614691098170767),
  (16737, 1208396783433449797602883641737763689871),
  (16769, 1200462711488329600952325639660057728399),
  (16801, 1200463035988255865377133788703938155919),
  (22017, 868278698801275389761025603062777320847),
  (23041, 953349290531515483498345580596891555279),
  (24065, 953349290531515483498345580597965034895),
  (25089, 1031775944128916690193304040748637037969),
  (26113, 1031775944128916690193304040748636775825)]

theorem tbl25_0_ok : tblOK 25 tbl25_0 = true := by decide +kernel

def tbl25_1 : List (Nat × Nat) := [
  (17729, 1208396783767881535153056994965997290831),
  (17761, 1208396783433450099834338545395057362255),
  (17793, 1200462624499660913565742050034300810573),
  (17825, 1200462949097437931345064151331642905935),
  (23073, 953349291411549959703337670900867167698),
  (24097, 953349291411555763413382668071908439570),
  (25121, 1031775944107696501162969223001268351321),
  (26145, 1031775944107696501162969223001268351320),
  (18785, 1208396783434688039865661561528748672335),
  (18817, 1200483393687095052361299637045487834445),
  (18849, 1200483718284872070655286106765555729743),
  (23105, 953349291411549960072308764926921749969),
  (24129, 953349291411555764440706128256384472595),
  (25153, 1033105172103481417035873029992828957017),
  (26177, 1033105172103481417035873029992828957016),
  (19777, 1208396783744111107660229430457764218191),
  (19809, 1208396783434682312889496441989606999375),
  (19841, 1200483393663632593121189075123271468365),
  (19873, 1200483718261163873630488447045098079567),
  (24161, 953349291411549960072308764927995225489),
  (25185, 1033105172120929757502058615844458026449),
  (26209, 1033105172200157920016322954899275404817),
  (20833, 1208396783435786666551927429445862884687),
  (20865, 1200504238513686252806552807386273346893),
  (20897, 1200504492519118826777962265675716166991),
  (24193, 953353483995037636021721937001635190160),
  (25217, 1034434465872179303529739940980984190416),
  (26241, 1034434398919719757012025403864513004056),
  (21857, 1208396783435786566300994393753418527257),
  (21889, 1200504239720755439717121981508560946575)]

theorem tbl25_1_ok : tblOK 25 tbl25_1 = true := by decide +kernel

def tbl25_2 : List (Nat × Nat) := [
  (21921, 1200504492519118726527029229983271809561),
  (25249, 1034434465872179303529745921889140020624),
  (26273, 1034434465872179303529745921889139758480),
  (22913, 1200527609556396731305071492872483964239),
  (22945, 1200525261319019605101877823930935341589),
  (25281, 1035763692904867434760917794488254001685),
  (26305, 1035763692904867434760917794419534524949),
  (23937, 1200527609556396731305071497269456471375),
  (23969, 1200525261319019302871576122707764376150),
  (26337, 1035763692904867402048829996175729947286),
  (24993, 1200543784228351897720303736605455217367),
  (26017, 961283044391882400854836773958983714190),
  (15425, 1803974661866993955474703718240221463254),
  (16449, 1803974661866824682466027420516459278934),
  (17473, 1889066022784432462151210476321349366357),
  (18497, 1889066022784451804964408493126921291087),
  (19521, 1974136614514686420830252149313116374351),
  (20545, 1974136614530721263446500858332673279311),
  (21569, 2059227975290168248961589141220558980688),
  (22593, 2059227975369161856108509821778699285013),
  (23617, 2144298567099396443712012599674256028182),
  (14626, 606549278403389979390153049100527928655),
  (14658, 607878440076402553040804819832157603019),
  (14690, 609208063977925844898965034915531392335),
  (14722, 610537225744982826428725467406942664013),
  (14754, 611573166147595107346615083174247597391),
  (20930, 1306970333105297390031099350887062648337),
  (21954, 1302983624430085205209063320582306239889),
  (22978, 953185008245082823701153516015263478293),
  (24002, 953185008245082411750795254292934619734)]

theorem tbl25_2_ok : tblOK 25 tbl25_2 = true := by decide +kernel

def tbl25_3 : List (Nat × Nat) := [
  (25026, 1038150156717942388047544631733007451601),
  (24961, 1200527609556396731305005320137389437463),
  (15650, 1208396865588097688094721259054435734928),
  (15682, 1208396783766643596306274662456671376982),
  (15714, 1208396783449730960416316760691431216726),
  (15746, 1200421173113467462004866978445714625938),
  (15778, 1200421497638324729255508084827397920146),
  (21986, 868278633453133579449259166241221555798),
  (23010, 953349225183310195209564758164709938642),
  (24034, 953349225183310085627996899092532893072),
  (25058, 1038548695526910372765447331835250807383),
  (24929, 1208394537157684719608906184648779953612),
  (16706, 1208396783766643595114172149092334245263),
  (16738, 1208396783433449797603284176138999764367),
  (16770, 1208711014696966642989803638563621615190),
  (16802, 1200463035988256471478326731579700581974),
  (22018, 868278633453133579309647577792736179798),
  (23042, 953349225183310195044752139250712258001),
  (24066, 953349225183310085917380197909549609558),
  (25090, 1038424431712651233345764662990080882262),
  (24897, 1208519451447831209334129669782637703895),
  (17730, 1208396783767881535153457529367233365327),
  (17762, 1208396783433450099834739079796293436751),
  (17794, 1208731743720596776472984785454570976855),
  (17826, 1200462949076205313805665475339639101013),
  (23074, 953349225183368185730830321505427535442),
  (24098, 953349225183329500078934110292700124690),
  (25122, 1038424406602198105228655830669063927383),
  (24865, 1208519476555808457446454717848694616791),
  (18786, 1208396783434688039891229310021998318927)]

theorem tbl25_3_ok : tblOK 25 tbl25_3 = true := by decide +kernel

def tbl25_4 : List (Nat × Nat) := [
  (18818, 1208731743715723378821421810973875696217),
  (18850, 1200483718263639453116179315849979266645),
  (23106, 953349225183367581267920514190840182355),
  (24130, 953349225183328895616024302978112771603),
  (25154, 1038424406597324707577092856188368646745),
  (24833, 1208519476563157843125818437722738586327),
  (19778, 1208396783744111107659076508953157371215),
  (19810, 1208396783434682312888343520485000152399),
  (19842, 1208752511068235662475529158151968453206),
  (19874, 1200483718263639753635271668350104700239),
  (24162, 953349225182920249547821346686077306191),
  (25186, 1038424404920859176949220935620741600323),
  (24801, 1208519152203061392957726578967137284823),
  (20834, 1208396783435786666550774507941256037711),
  (20866, 1208752186549682004048802374995947876950),
  (20898, 1200504492519118826776809344171109320015),
  (24194, 953353483997474830252757862253879956880),
  (25218, 1038424080402305518522494152464721024067),
  (24769, 1208519152282289555471990916560681235159),
  (21858, 1208396783435786671298690439122929336857),
  (21890, 1208772957255124357705542711062593058390),
  (21922, 1200504492519118831524725275352782619161),
  (25250, 1038424081920313732868714187493540148822),
  (24737, 1208519801240168709811180145279178437335),
  (22914, 1208772957255124357705542711058298148175),
  (22946, 1200525261319019710099567901560448021013),
  (25282, 1038424081920313732868714187489245238607),
  (24705, 1208519801240168709884967121574016643799),
  (23938, 1208291345250252875254155771737944420950),
  (23970, 1200525261319019298149209639838119162454)]

theorem tbl25_4_ok : tblOK 25 tbl25_4 = true := by decide +kernel

def tbl25_5 : List (Nat × Nat) := [
  (24673, 1208519801240188052698080955640811942615),
  (24994, 1046399772895568672186643777982423667779),
  (16481, 1208438403960476522966321875934787769745),
  (17505, 1208438409031074933097751409892385944213),
  (18529, 1208459178218470386778937970539995918869),
  (19553, 1208459183309051198505650986102787470667),
  (20577, 1208479952417257175300747848989953553739),
  (21601, 1208479844972534811193223591503453286934),
  (22625, 1208500614161208102721253136735044432405),
  (23649, 1208500614161207800490951435511873466966),
  (25697, 1211180190255615150318632259227080557968),
  (15651, 606570047590824120269738451141671585230),
  (15683, 607899209290070335031751566070072542670),
  (15715, 608893296684382947585075190592706191897),
  (15747, 610222849206033106043015982460404012628),
  (15779, 611573170980960343573972093086255388050),
  (15811, 1813407169740056637962301049545482621657),
  (21987, 868114493534737174114718900323259299414),
  (23011, 953185085248744392872252233204192282197),
  (24035, 953185085248744391156431199076966532430),
  (23906, 1208396783435786259348326209866760778326),
  (23905, 1208396783435786264070692692736405992022),
  (16707, 1293467375496960777947753743869779715473),
  (16739, 1293467375163684433624483248997158393430),
  (16771, 1293779659402457739785927781595829343633),
  (16803, 1294815440859893266421604106837714900370),
  (16835, 1304477702779692339417348788716563387097),
  (22019, 868301993327129370526377241642076755539),
  (23043, 953372585057363991113738746561322046233),
  (24067, 953372585028655255995969304282141103500)]

theorem tbl25_5_ok : tblOK 25 tbl25_5 = true := by decide +kernel

def tbl25_6 : List (Nat × Nat) := [
  (23874, 1208497064738249621186606348023071016469),
  (23873, 1208396813692356135497127327813082346070),
  (17731, 1293467375498140689031601451773121107410),
  (17763, 1293467375163684721688856714045979399767),
  (17795, 1293800413379322616396974465895606883792),
  (17827, 1294815440861073182742761546277266494930),
  (17859, 1305641137050686006808698664344408397267),
  (23075, 953372585053650457864408809856850802130),
  (24099, 953372585053643469430707214703587829136),
  (23842, 1208500629285140584364090156542688555670),
  (23841, 1208500629285140589086456639412333769366),
  (18787, 1293467375164922661728141812845901809239),
  (18819, 1293800413369510700185727072224418796247),
  (18851, 1294815445931675583508105195276356392403),
  (18883, 1305641101852470489237534609053039293643),
  (23107, 953372585053648343933324844409076159955),
  (24131, 953372585053648342244224194465694574099),
  (23810, 1208500629293727612573650835903983186518),
  (23809, 1208500629293727612647437812198821392982),
  (19779, 1293467375499378624348107685285679433105),
  (19811, 1293467375164922963958025205862679774606),
  (19843, 1293821182556501745015411408849281815254),
  (19875, 1294815445932913495213191677792119264790),
  (19907, 1306970328034559310806654339617720967896),
  (24163, 953372585053648342244224194465694582162),
  (23778, 1208500629293728793386632482199801229910),
  (23777, 1208500629293728798108998965069446443606),
  (20835, 1293467375166411056364664413132070913358),
  (20867, 1293821182477273582501147071255737864918),
  (20899, 1294815451003515593894654661595524601366)]

theorem tbl25_6_ok : tblOK 25 tbl25_6 = true := by decide +kernel

def tbl25_7 : List (Nat × Nat) := [
  (20931, 1306970328034559382450383642850145429011),
  (24195, 953372585053628999431110360398899283346),
  (23746, 1208500629372956955900896819793345180246),
  (23745, 1208500629372956960623263302662990393942),
  (21859, 1293467452169682856335626840635960493654),
  (21891, 1293758890127207228938606996359855838609),
  (21923, 1294815450999859802216535201049258014294),
  (21955, 1302983619358648942767239138397830304473),
  (23714, 1208500624302412583353533739712080048726),
  (23713, 1208500619231810187236769592889750647382),
  (22915, 943961239034030109988431312297374044629),
  (22947, 952123909353110426927669761626454959569),
  (22979, 953185008245492040287991727214291883604),
  (23682, 1208500619231810201182508112614171669078),
  (23681, 1208500619231810201256295088909009875542),
  (23939, 943961237199031341175957720248916431311),
  (23971, 952123909353110425215725974249655051665),
  (24003, 953185008245043730846934069028989235798),
  (16513, 1208438403961727101092414027345855616399),
  (17537, 1208438409032332215729148593191190369615),
  (18561, 1208459178219766355039370548625103193423),
  (19585, 1208459081190216789063195788695320982165),
  (20609, 1208479850377631585634431497459736839503),
  (21633, 1208479850351404841897059150821308036357),
  (22657, 1208500619231810503486596790132180840981),
  (25729, 1211180190255615116162448026989623608722),
  (16514, 1208438403961733806193473224022628341137),
  (17538, 1208438409032332217366278262097241764185),
  (18562, 1208459178219766356676792384013838905689),
  (19586, 1208459081190216486831740885038027305621)]

theorem tbl25_7_ok : tblOK 25 tbl25_7 = true := by decide +kernel

def tbl25_8 : List (Nat × Nat) := [
  (20610, 1208479850377631283402976593802443162959),
  (21634, 1208479850378875925013111825049591321999),
  (22658, 1208500619231810505104216236547950834197),
  (24706, 1208519801240168705162600638704371430103),
  (15684, 607899199122631895247850212643703669963),
  (15716, 608893296683954737928298469833097111120),
  (15748, 610222849178626479096043747997526798873),
  (15780, 611573170980532363456072414678531507598),
  (15812, 1813399983652698234035449287094007309713),
  (21988, 868114493534737172482326235905449047638),
  (23012, 953185085248744391255767905152132744789),
  (22883, 1293467452169682856335626840635960493653),
  (22882, 1208396783435786671298684471589089636885),
  (22881, 1208396783435786566300994393959576957461),
  (16708, 1293467375496531254083161626516667045262),
  (16740, 1293467375163684328926474759087405208974),
  (16772, 1293779546794264865933774077333892048273),
  (16804, 1294815440859464644355876041564411471249),
  (16836, 1304016850131951458058839349488853001617),
  (22020, 868301993299734474449036947922750875025),
  (23044, 953372585029969075119322330444553851477),
  (22851, 1293571298130589361053401446895085196885),
  (22850, 1208504595462084546270034177548584568273),
  (22849, 1208396813692356437727429029036253311509),
  (17732, 1293467375498140689031206898553827202514),
  (17764, 1293467375163684721688457899463252706766),
  (17796, 1293800413369086953257510507260394623703),
  (17828, 1294815440861073078171808583371874182608),
  (17860, 1305641024528301179697624563484665390540),
  (23076, 953372585053643771662144105467456333264)]

theorem tbl25_8_ok : tblOK 25 tbl25_8 = true := by decide +kernel

def tbl25_9 : List (Nat × Nat) := [
  (22819, 1293571298106838780730932667346227053209),
  (22818, 1208500629293727614263904056180468675093),
  (22817, 1208500629293727612646284609764698681877),
  (18788, 1293467375164922661727747470952957249111),
  (18820, 1293800413369086953240377627139056678353),
  (18852, 1294815445931675479084726254966577370576),
  (18884, 1305641100118021900556615786928802985164),
  (23108, 953372585053648342317993156385573279187),
  (22787, 1293571298106834210075083616495782622805),
  (22786, 1208500629293729111254079125857998030159),
  (22785, 1208500629293729109636459679442228036943),
  (19780, 1293467375499378624348125695286125626769),
  (19812, 1293467375164922963958042938717493069198),
  (19844, 1293821182556521092550891747549512803729),
  (19876, 1294815445932913495213209410646932559382),
  (19908, 1306970328113806816429106674480280838936),
  (22755, 1293571298106834210075083616495749596757),
  (22754, 1208500629293729205336990743922130088469),
  (22753, 1208500629293729100339300666292617409045),
  (20836, 1293467375166411061085877693022132569422),
  (20868, 1293821182477292930036627409955968853393),
  (20900, 1294815451003515593894672675925297829398),
  (20932, 1306970328113807076159371327497917244184),
  (22723, 1293571298106853552888197450562544895573),
  (22722, 1208500629372957367851255081515674038805),
  (22721, 1208500629372957262853565003886161359381),
  (21860, 1293467452169682854719142512583900956246),
  (21892, 1293758777606873680822602479798366606736),
  (21924, 1294815450999429996551069257267648697942),
  (21956, 1302976433271290538840387375946354992529)]

theorem tbl25_9_ok : tblOK 25 tbl25_9 = true := by decide +kernel

def tbl25_10 : List (Nat × Nat) := [
  (22690, 1208500624302412995377678973331200602645),
  (22689, 1208500619231810489467071294112921612821),
  (22916, 943961237278651186128069608406986290772),
  (22948, 952123909353110425289513048443676075473),
  (22980, 953185008245063480888039677550421668373),
  (17569, 1208438409032332215878628698797589726543),
  (18593, 1208459178219766355186943656789849474383),
  (19617, 1208459081190216789063177774296811500181),
  (20641, 1208479850377631585634431215984760128847),
  (21665, 1208479850351404841601911245641805263385),
  (25761, 1212509417288303247378278236875261023631),
  (17570, 1208438317072153816987714729017044657746),
  (18594, 1208459086259587956298228851002344760913),
  (19618, 1208459086260818901544024705690224362831),
  (20642, 1208479855448233684315893636839302563151),
  (21666, 1208479855449478325920360217070239245905),
  (24738, 1208519801240168705088813662409533223639),
  (16773, 695628571450869813528984539179820807761),
  (16805, 696643762710766979321049708133921691022),
  (16837, 697973315204213506870928432483824637327),
  (16869, 697973313788029412071158498427761137038),
  (22021, 868114493534736266230301733901478204815),
  (21828, 1293467452185910251811544495195159311958),
  (21827, 1293467452185910253443937159612969563734),
  (21826, 1208396783744111112333205463839992463897),
  (21825, 1208396783744111007335509418470481654297),
  (17797, 1378871004685945124442509606332236379602),
  (17829, 1379886753327304728066357259094871848402),
  (17861, 1381531635413884160361621553380361319890),
  (17893, 1371913007391754098730831567628559267282)]

theorem tbl25_10_ok : tblOK 25 tbl25_10 = true := by decide +kernel

def tbl25_11 : List (Nat × Nat) := [
  (21796, 1293550528935646804328928657257567925846),
  (21795, 1293550528935646805970538527245183587729),
  (21794, 1208479860495070776950878233895738077716),
  (21793, 1208479860493826734071436015817035149849),
  (18821, 1378871004685945124811443924856423658961),
  (18853, 1379886686699017411804023191661550310863),
  (18885, 1381531711002386283988331381660590622163),
  (18917, 1371954545766622377351854200994260137425),
  (21764, 1293550528935646804331234500266764842582),
  (21763, 1293550528935646805963627164615872394838),
  (21762, 1208479860495066266801433497989363806681),
  (21761, 1208479860493828231061611085494564505167),
  (19781, 1378538059286407489192786899150217221519),
  (19845, 1378891773873379264121957944750602528145),
  (19877, 1379886686700255427931353698516199118358),
  (19909, 1381552480189820423298434242115091908114),
  (19941, 1371954550837224778264771704958637647249),
  (21731, 1293550528935646805963627164684591871574),
  (21730, 1208479860493828326762148117714464686617),
  (21729, 1208479860493828221764452072344953877017),
  (20837, 874968664727199108900305305761101461009),
  (20869, 865811040088047714473873146144222426641),
  (20901, 867057191393685500578191803927431026191),
  (20933, 868114508746582154595423980949100369423),
  (20965, 868114508746543468600260881860382758416),
  (21699, 1293550528935646810685993647554237085270),
  (21698, 1208479860493847669575261951781259985433),
  (21697, 1208479860493847564577565906411749175833),
  (21861, 874968558066049314234561560112984331662),
  (21893, 865370956625264789968274992130695161101)]

theorem tbl25_11_ok : tblOK 25 tbl25_11 = true := by decide +kernel

def tbl25_12 : List (Nat × Nat) := [
  (21925, 867057191393280817458397002601794442639),
  (21957, 868114401611365446131078038447785787929),
  (21989, 868114493534736265861748501228406486614),
  (6305, 1389338294626158966995629101701054928271),
  (17601, 1208438317072147426583639915197931820367),
  (18625, 1208459086259581565893861870631844644175),
  (19649, 1208459086235873368869064210911386993999),
  (20673, 1208479860493847664828498942104193533263),
  (25793, 1212509482964539711758170962270512813455),
  (17602, 1208438317050914809043087776741617079890),
  (18626, 1208459086238348948353601898726933956177),
  (19650, 1208459086238349248873847432216393614671),
  (20674, 1208479860493847664827346020599586686287),
  (24770, 1208519800844046339623565589319657489873),
  (17603, 1293508908781149429336167932186186819022),
  (18627, 1293529677968583568646682054170429953486),
  (19651, 1293529677968583870876567202343841498510),
  (20675, 1293550452249070701090043490140606760270),
  (23747, 1293571298106853551172376416435319145806),
  (16838, 698287357103545194022252898286551209558),
  (16870, 698285409761972180979875582651885205078),
  (20805, 1378538059127951164164258223963162088975),
  (20804, 1293467375499334446078288702877049357646),
  (20803, 1293467375499334143847987002199339238734),
  (20802, 1208396783744111107585289532658319164751),
  (20801, 1208396783744111107586442454162926011727),
  (17862, 1381531640484486561200752183071262193106),
  (17894, 1371913007391778928193637210577667700178),
  (20772, 1293550452249070998014600426617607095630),
  (20771, 1293550452225305088949015331159763125582)]

theorem tbl25_12_ok : tblOK 25 tbl25_12 = true := by decide +kernel

def tbl25_13 : List (Nat × Nat) := [
  (20770, 1208479860495070473083171960776797783375),
  (20769, 1208479860493826734512999071623780828495),
  (18886, 1381531711081614446502595719184341353939),
  (18918, 1371954545766641115702440931530006410705),
  (20740, 1293550452249070998597889761856031098190),
  (20739, 1293550452225300877919253976699505804622),
  (20738, 1208479860495066262053428339240073233743),
  (20737, 1208479860493828232605062262305681638735),
  (19782, 1378475659667310822208621994892832638353),
  (19910, 1381132838001837922687289230117933491601),
  (19942, 1371954449245854728768688513212552910222),
  (20707, 1293550452249070696367677007270961546574),
  (20706, 1208479860493828322014232186532791387471),
  (20705, 1208479860493828322015385108037398234447),
  (20838, 874968563135804910634285727001279288849),
  (20870, 865391402891433687960647532592605795857),
  (20934, 868052109285858646587226376953678333263),
  (20966, 868052109285858646587226376953678333262),
  (7329, 1467762807947592570996319353525330326994),
  (18657, 1208459086259581565892708949127237797199),
  (19681, 1208459086235873368867911289406780147023),
  (25825, 1213838710960324632353441252200421590351),
  (7362, 1467762807947598057646017424655533815250),
  (18658, 1208459086238348948353602158211661334101),
  (19682, 1208459086238349248872694510711786767695),
  (24802, 1208519476325492681196838806163636913617),
  (18659, 1293529677968583568646682402089685517911),
  (19683, 1293529677968583870876566920868864787854),
  (23779, 1293571298106834208359262582368523846990),
  (17927, 1899841671347696895496795198020554933715)]

theorem tbl25_13_ok : tblOK 25 tbl25_13 = true := by decide +kernel

def tbl25_14 : List (Nat × Nat) := [
  (19748, 1293467467556172872959161850547522311568),
  (19747, 1293467370406281452945024836387890857358),
  (19746, 1208396778676046830942305066260442973519),
  (19745, 1208396778673570950937521844955436352847),
  (18951, 783376862575483641639698300830900106705),
  (19716, 1293529775118475286168337733565108262288),
  (19715, 1293529775118474983862988344597543977686),
  (19714, 1208459183308761977015951429245650138443),
  (19713, 1208396804027814781641206897284235724111),
  (19783, 769790579131419255146127821449442465296),
  (19975, 782981512462571339818420814645863445902),
  (8385, 1467762715953855288363625097340551243215),
  (8417, 1451648808265560306670633095133971953106),
  (18689, 1208396804027820593381313957023373919567),
  (25857, 1213838641155361697129762546289041797464),
  (8386, 1467762731184424429155639180890772682194),
  (8418, 1451648808265560306670633192622028830162),
  (18690, 1208459178245902193093062447942190511699),
  (24834, 1208519476563157843052031461427900379863),
  (18691, 1293529770050355467320793579807470360019),
  (23811, 1293571298106834208361461183411610781006),
  (18692, 1293529770050348765842429373613429036496),
  (22788, 1293571298106834208458599288443690055253),
  (9409, 1552833307684089904229468744800446780879),
  (9441, 1554162535678636794324889758375717700943),
  (25889, 1215167869151146613002666353280602403160),
  (9410, 1552833322914659045021482832748697957841),
  (9442, 1554162535678636794324895933434580763983),
  (9474, 1554162627911551026213232562428937848275),
  (24866, 1208519476558284332655085042939171238615)]

theorem tbl25_14_ok : tblOK 25 tbl25_14 = true := by decide +kernel

def tbl25_15 : List (Nat × Nat) := [
  (9475, 1554183396317845000808458707246655030739),
  (23843, 1293571298106831790734748326567769867598),
  (22820, 1293571298106832094454899001104744089169),
  (10465, 1554162540749239195094737574350178026831),
  (10497, 1554162540749239194799590513595755332943),
  (10529, 1538090171516278636557833048212875572684),
  (25921, 1215167869152326524618621315693092635983),
  (10466, 1554162540749239195095138390226374034767),
  (10498, 1554162540749239194799990485063072322895),
  (10530, 1538084279955585910614547739179888231891),
  (24898, 1208519451447831204611763186912992490199),
  (10499, 1554183309936673434547115579038465627603),
  (10531, 1538084279955585911131056485355083609550),
  (23875, 1293571298101880319008591861931462165838),
  (22852, 1293571298103118561279337744914824103246),
  (21829, 1378538043916143961425363645049130521999),
  (11489, 1629826307773232436850711108952726230284),
  (11521, 1630012957046356035778261087829333443919),
  (11553, 1630009006673328519069500267426697544972),
  (25953, 1200506830236408004912468872675185432085),
  (11490, 1629826307773232436850710827477749519628),
  (11522, 1630012957046356339426256549104582722895),
  (11554, 1630009011743930919982417592280756344340),
  (11586, 1640562452549716633910046967395558704657),
  (24930, 1208395185719441503760480857407757795863),
  (11523, 1629826404842741221839863847547342750488),
  (11555, 1630009011743930920572338195812907844878),
  (11587, 1640583221111991053381462082540013962769),
  (23907, 1293467452169682854619805806508734743886),
  (11588, 1640583221111991058103828565408568657425)]

theorem tbl25_15_ok : tblOK 25 tbl25_15 = true := by decide +kernel

def tbl25_16 : List (Nat × Nat) := [
  (22884, 1293467452169682854719142512583900956245),
  (15814, 1813400308171257687698169509205083444819),
  (15813, 1813399983652697629572539479779436733841),
  (15781, 611573170980532363478157780893870098006),
  (15749, 610557979720609763074673147447106365012),
  (12545, 1631069887852732674741850254571780539661),
  (12577, 1631069857647958351852337123248278922509),
  (12609, 1640562364992496217244509632844133369167),
  (12641, 1624506799251707585913113003161120990477),
  (25985, 1200527533186930678299753079518215079311),
  (12546, 1631157230077044424148101846868217103695),
  (12578, 1631069862718931585957063609402492249357),
  (12610, 1631446356223476160511722877139174871636),
  (12642, 1624506799410515401320336724448814097677),
  (24962, 1208291340178411619779231935448891557329),
  (12547, 1631153036778065868720486399543421765133),
  (12579, 1631069862718931585957063605004445738253),
  (12611, 1631446360589690679065548542449599701588),
  (12643, 1624506799410515401320336720050767586573),
  (12612, 1631446360589556880993839746538290910737),
  (12644, 1624506896799121943306602559062868837905),
  (14757, 611573166147614450081330536402754012495),
  (14725, 610537317322894720150152016003969647951),
  (14756, 611573166147614450085941377996251268431),
  (14724, 610537225745373883962365237991598781773),
  (14692, 609208063977931870401095342235767080271),
  (14660, 607878536824032718650780235063491626319),
  (14755, 611573166147595107346614801699270886735),
  (14723, 610537225745373879461341669607958705485),
  (14691, 609208063977931865678746878162677859663)]

theorem tbl25_16_ok : tblOK 25 tbl25_16 = true := by decide +kernel

def tbl25_17 : List (Nat × Nat) := [
  (14659, 607878440101398254871174376709760808267),
  (14627, 606549278403389980885091143131842282831),
  (13569, 537365132288676612849136941639531558222),
  (13601, 521478686593907820586307109150838027598),
  (13633, 522807848346211732763725633498878108376),
  (13665, 524137472168290785071059843505258034510),
  (13570, 520149164504406772922564151858155283029),
  (13602, 521478686593907820586307109082118550862),
  (13634, 522807848346211732763725629100831597272),
  (13666, 524137472168290785071041829106748552526),
  (13698, 1726965480293106574393567163261512643158),
  (13571, 520149164504406773290322498853477086542),
  (13603, 521478686593907916283294399476391052622),
  (13635, 522807848371161821643561457733389579598),
  (13667, 524137472168679742770315043575859049806),
  (13699, 1726983364307659443701917549820500837707),
  (13636, 522807945014699229149948424975269557582),
  (13668, 524137472168679747492627764724952528206),
  (13700, 1726983364386906949029294877055909954891),
  (13701, 1727004134598193049474991752620477064593)]

theorem tbl25_17_ok : tblOK 25 tbl25_17 = true := by decide +kernel

def tbl25 : List (Nat × Nat) := tbl25_0 ++ tbl25_1 ++ tbl25_2 ++ tbl25_3 ++ tbl25_4 ++ tbl25_5 ++ tbl25_6 ++ tbl25_7 ++ tbl25_8 ++ tbl25_9 ++ tbl25_10 ++ tbl25_11 ++ tbl25_12 ++ tbl25_13 ++ tbl25_14 ++ tbl25_15 ++ tbl25_16 ++ tbl25_17

def mask25 : Nat := 168653672427243512465503370940614885668391918760027487013592683959277979083673726058024398261437175320150612510302841819765796560583261087453422914854810635707156921252092105629969343489232675804012955463850615696987302413512434135582266670000710008088444418507931575711013099873090663355799760664509704982361792997495176986305085135624213451109987995617033026959974305768798823619806415461358917381795098971567874126323489590153348811192479815819556586038202012423427974563051720558905510444547887470651556306818403309571549457373363078254254618592858918993032439397619561640093583364011715009630597441743659503490321575928041137503608650019723275377287848947904502179432398389431604698049052258129882569019351337835000076889489540571194818086392227977559682934440049138227735432870284716003033348602598638729523462554343128061150666230801743062436429574573506215708006462219326096363164812608307676947373111235375540998492664398447300449079933476954123936588228231828459252496616097866811023618607439058332625801865635215323846651943667750638372859436111004053865420480360352738525692245821666541300962593113630464376947357561153899039714236979126997731506703314839440189959030378512479501492664006747337123141458780130177974133378815814564392090875003661099648850304913554735058227980589148953655121967676539893053591503167597154351596547144488045389751673860585137529733733733022481840273921273342724591282607973574619962281227394624548317301000875184568537706062800483103900378613218209887531353775274766857409063705601471096607238655717953082081046038006140610028883185078444317948232257785692985044848516792348481832355909508302491940626439226374050270953852244083137533738593854871980082169906183537615154279495800863329673169486837191909553438136499677849133945808136708054882385944460540416660873072368938230317762341093129664454830397593594245511808918197569224850751753171192523732507297582401708277253199805965045241645747563708475192110103472565451596974608083777198370995964669558624507539736926373190482092694665164101928948197047661939678526232271713733416677312546174358737720710811754762932239703365021237351695067924780741576558754944047497585922757664053467872015730654591413570392510371980286283871630541458018451998138395301966207237921167513043621158612755698020753840587584210331510966608937320429155507985366231856557615096826136579568977818319937398185312902261260241086677150841786953593153753126032634929573086488565183399037043146484597524059977614412270265002284046157567492726329711121381716661957917212216476880903358452365040317899309882306675798483173770398520846452354355383076068930189245837831610592036701700077308475431694563864290305331488303884043105147002997022254221645596675463660323022307069414858019741608663613825849594345298712097236024808316627532271661361957952742369107248645247669198801285378910547964031536587678959670778775107948839191872092300999360113735168828766888018258591657209731420845254797977399503763535604036525972633120193885420551007035665782360699119440907692696054510468315818382687579963261773484148665179266134129545351705422562972447526403328521745335116176982331380588333001552431019744254733009122483287619330366093101618110681445410599076238988505679780948405599817758370009123396980017872381094281279408994155185687164898120385605909732151033704686519508970118735581949364333134132687688062010477256867050938250180895227248632250778851589224580629129126666662547424566426903559895177244506535962593157276397173773417455582612406731098890039095505988479270700562533856883639316708893444718135229502664576802171860309021174434667689618197560129594275803958968553377195028349141459857214001506785709797295093855570075778996197900515351667687885057912564317287415818895385919777532305905721111084312147796970836637983150317396484739928572692511705445746034633368660501651969416571473916770247694612666474636012424489766633736945412133020898649656016195875552219035266477739550464856573099417043670585022185423809047543926414533131618230336001464599578279358672503246099947776473431491574626133376306701230880932170644638686815670898570400813868313558507691116664764676265472173828586008969976980355788237144336928399049576959428979938308268731401129265466947964083454898107538498391520128019511218169885735930527884494613975840674981047405884368743845228981715667046621938819424698610444633245154037745762787073370298173351511189830198423820276465423197066215613841679682454478494255418854453534182161347854118021761499817857952303237652619810230918327976226372072755167197997876258690084651137907427819094355731960416939677728622302517514419293577294341449012779118128992925113726029848780456866316899687932650712476302117799139540239941103984001384600532832280197132745084255228528562051010010733468399058975938029209047826013338837992402532486657915889726284471304338942279160990079173867883394507824004421434877605858809342228736443929960133312197310122668580248114407273465037523381155300202732337436991445565740457041118314687133126603563297546019493635778820411292738668080297806855880877438944517376801723397117188644868389059975016881938770021902581514496779985971041267247087997147281050894268763493520859080877384618049648179248639658848860980212515951917927159974329707425064320987797062463915451023899980500755659989315283432593908079082760263203174920263043719906715149140308737176852537690624792312286330356674623410182992707948400510804767665959473915655673022163035299259431986372730415126594992260366221863937695452163756124996833386900775645256868670857616837461695169104630342427322504324241381009515703682800813702554155628486112089155337073236241573656785544740023669748220897555706948509197368940925545463871655985816066876959055289208656508105160228619508496313291057462636413295394553825496029890695640425052772146156690104316059792593248832258781187520082585478647811102171149479157248685780636552611209370671358804924422319381719228325736475810715429711537930675840077230342252956036065197091862756977393279921270110195228410196950947113147329713022949151019990785295656076151549069101835702212496611663300556493562688398080449484441047881431697876009449718376062242421345862111578403368377644153294843244410730275231159613399046227330382601935815367373172726528511666993448130933586055391484720359707499147067834162372624894074534695541673877832551377734424775512161253328184163919138730742778315595295474563280166477145603342576561972151633150253990030326999164014733661188314674436268579880635029339992988576184616126165531051641608400568504604766878589067531375690425765937700372603494121619878978433254029671213665535921264379908133101407523727429008577101762069519796399177484779893045740170308749666110127685506389279304930861304794558394569891639435763180915009256209741744479313960013453007614383534978606396066664640561968116200145595378045172043926694822768553585847955553846166794106407655198607735931572850920079278355374933275598947526702382370791827187299814020244741935891197722766975764624746026685971251579467805163369653451605590763902901988731797217230873016953073061892200303778832942361236064621287920573071118326675072167717404944170322652961544267642951224087981177132193472870448662589840031035302961381778506252713875671256873349693115341128027532328338540035375971336364083974154471127670580763948123823285565863269995142526501799371486669199329095471366922715726486503082068032890972599345831044679365597465009694225222361343221023622176373312299033749533466350752326068475975210343594895623355021575612111936043927072773158089908232612928698693881534897289060690901697319366979455597025443076530725264297592763441296254780394700463284382658419758310799013202077662326601041999598081810289174155633464753222055925876650492312620022031782891508960674194497598514110482447006530688906606377603903782265636629294920105714442964584913147609039909053623339449312878745088363676055198505276708604852922482688

theorem mask25_eq : maskL 0 (tbl25.map Prod.fst) = mask25 := by decide +kernel

theorem cov25_1 : coverX 25 mask25 1 = true := by decide +kernel
theorem cov25_2 : coverX 25 mask25 2 = true := by decide +kernel
theorem cov25_3 : coverX 25 mask25 3 = true := by decide +kernel
theorem cov25_4 : coverX 25 mask25 4 = true := by decide +kernel
theorem cov25_5 : coverX 25 mask25 5 = true := by decide +kernel
theorem cov25_6 : coverX 25 mask25 6 = true := by decide +kernel
theorem cov25_7 : coverX 25 mask25 7 = true := by decide +kernel
theorem cov25_8 : coverX 25 mask25 8 = true := by decide +kernel
theorem cov25_9 : coverX 25 mask25 9 = true := by decide +kernel
theorem cov25_10 : coverX 25 mask25 10 = true := by decide +kernel
theorem cov25_11 : coverX 25 mask25 11 = true := by decide +kernel
theorem cov25_12 : coverX 25 mask25 12 = true := by decide +kernel
theorem cov25_13 : coverX 25 mask25 13 = true := by decide +kernel
theorem cov25_14 : coverX 25 mask25 14 = true := by decide +kernel
theorem cov25_15 : coverX 25 mask25 15 = true := by decide +kernel
theorem cov25_16 : coverX 25 mask25 16 = true := by decide +kernel
theorem cov25_17 : coverX 25 mask25 17 = true := by decide +kernel
theorem cov25_18 : coverX 25 mask25 18 = true := by decide +kernel
theorem cov25_19 : coverX 25 mask25 19 = true := by decide +kernel
theorem cov25_20 : coverX 25 mask25 20 = true := by decide +kernel
theorem cov25_21 : coverX 25 mask25 21 = true := by decide +kernel
theorem cov25_22 : coverX 25 mask25 22 = true := by decide +kernel
theorem cov25_23 : coverX 25 mask25 23 = true := by decide +kernel
theorem cov25_24 : coverX 25 mask25 24 = true := by decide +kernel
theorem cov25_25 : coverX 25 mask25 25 = true := by decide +kernel

theorem cert25 : Cert 25 tbl25 := by
  refine ⟨by simp only [tbl25, tblOK_append, tbl25_0_ok, tbl25_1_ok, tbl25_2_ok, tbl25_3_ok, tbl25_4_ok, tbl25_5_ok, tbl25_6_ok, tbl25_7_ok, tbl25_8_ok, tbl25_9_ok, tbl25_10_ok, tbl25_11_ok, tbl25_12_ok, tbl25_13_ok, tbl25_14_ok, tbl25_15_ok, tbl25_16_ok, tbl25_17_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask25_eq]
  interval_cases x
  exacts [cov25_1, cov25_2, cov25_3, cov25_4, cov25_5, cov25_6, cov25_7, cov25_8, cov25_9, cov25_10, cov25_11, cov25_12, cov25_13, cov25_14, cov25_15, cov25_16, cov25_17, cov25_18, cov25_19, cov25_20, cov25_21, cov25_22, cov25_23, cov25_24, cov25_25]

/-! ### `N = 26`: 601 witness orderings -/

def tbl26_0 : List (Nat × Nat) := [
  (14625, 38820478776063719803896563004289330001487),
  (14657, 38905574730773577793041400727143224808847),
  (14689, 38990641083396048566521067899146020902156),
  (14721, 39075737008011951000319281940745190442383),
  (14753, 39160803041355928797873512400156738520463),
  (21953, 87812937781286133481450033997741176464849),
  (22977, 61022598343657118200627626810472678364624),
  (24001, 61022598343657118200627626810472678364560),
  (25025, 65944751714808240549441415071685222401423),
  (26049, 65944751714808240549441415169003404428950),
  (27073, 71390594255562855199699835402355443340754),
  (15649, 77337399316975353815310896744889317655254),
  (15681, 77337399321818103675172925386017216992656),
  (15713, 77337399321808335554550439182285591090576),
  (15745, 76846929758360583036710605475270149608848),
  (15777, 76846765272772329144079986016474471142800),
  (21985, 87806417514099665393814279084441380136401),
  (23009, 61014349761642315370119672669638188160656),
  (24033, 61014349761642315370119672669844346590608),
  (25057, 65948589420990671701474444822240476878288),
  (26081, 65948425229733861636119409641258585753101),
  (27105, 71390597151724637888902939838614692495957),
  (16705, 77337394161145983803943923981796011218383),
  (16737, 77337394139740806771474658978311327782351),
  (16769, 76829613864921478686936391248991091008975),
  (16801, 76829634634097887427494386435772732777935),
  (23041, 61014354995140160711428472550506826900945),
  (24065, 61014354995140160711428472550504679417361),
  (25089, 66033660429223376312253722015169831605647),
  (26113, 66033660429223376312253722015444712878424)]

theorem tbl26_0_ok : tblOK 26 tbl26_0 = true := by decide +kernel

def tbl26_1 : List (Nat × Nat) := [
  (27137, 71478034862916133409792807797413449586257),
  (17729, 77337394161145983803943923981796011214287),
  (17761, 77337394139740806771474658978311327778255),
  (17793, 76829613864921478686936391248990017267151),
  (17825, 76829634634097887427494386435771659036111),
  (23073, 61014354995140160711428472550506826900944),
  (24097, 61014354995140160711428472550504679417360),
  (25121, 66033660429223376312253722015168757863823),
  (26145, 66033660429223376312253722015443639136600),
  (27169, 71478034862916133409792807176403358905605),
  (18785, 77337394139820054276794074785830459213199),
  (18817, 76830937196054573703520640445176558978447),
  (18849, 76830957970312605374176138240458825991567),
  (24129, 61014354979928353503967405344535536547344),
  (25153, 66118731020969801146114698846718029018704),
  (26177, 66118731020969801146114698846718029018640),
  (27201, 71563105453227711710228069713636629737817),
  (19809, 77337394139820054276794074785761739736463),
  (19841, 76830937196054573401289185541519265301903),
  (19873, 76830957970312609941747831257816788993686),
  (24161, 61014354979928353503967405344535536543248),
  (25185, 66118731020811344822553893047763612550736),
  (26209, 66118731020811344822553893049293588682384),
  (27233, 71563105454345643213354648613240785360464),
  (20833, 77337394139890346972247070603451765687695),
  (20865, 76832266711944225623162100743230084937037),
  (20897, 76832287521223605226713300122162375755151),
  (25217, 66203801612620807901695499278949667120720),
  (26241, 66203801612620807901695499278949667120656),
  (27265, 71648446941986650421802494804366841135574)]

theorem tbl26_1_ok : tblOK 26 tbl26_1 = true := by decide +kernel

def tbl26_2 : List (Nat × Nat) := [
  (21857, 77356151955862164446894935011177710032272),
  (21889, 76832271660534031570385112881361060165005),
  (21921, 76832292358822049309192509037085693642127),
  (25249, 66203801530863610654396465920871711700228),
  (26273, 66203801530863610654422007812995886909079),
  (27297, 71648446941986650421802494804366824358358),
  (22913, 76833787456278271284408363177001173452239),
  (22945, 76833621668985097211248538417864876041680),
  (26305, 66288872122262159527800023464358705164821),
  (27329, 71733517533692025924525067605076246274585),
  (23937, 76833787456278271284408363177001173452175),
  (23969, 76833621668985097211248538417864874993296),
  (26337, 66288872122261769749130763649660877337104),
  (27361, 71733517533692025924525067513199310493072),
  (24993, 76835117354384500177903287601430821938640),
  (27393, 71733369223808112679534012371542604792471),
  (26017, 76835117354384500177903287601431894894096),
  (27425, 71733517859025014208026428963577760629204),
  (16449, 77340032166036380898668270482150711162316),
  (17473, 77340032166036380898668270482150694385100),
  (18497, 77341361394025701098054121377684949366156),
  (19521, 77341361394025701098054103363286439884172),
  (20545, 77342690607126532228458405825701519328853),
  (21569, 77342695210999619172542163555961111873110),
  (22593, 77343937798648259939890350958029507724751),
  (23617, 77343937798648259939890350958029507724687),
  (24641, 77345267674649022385163602726023239894415),
  (25665, 77345267674649022385163519114691205460504),
  (26689, 77601829376364729244086474135209794409935),
  (15650, 38820478776063719803896563004288256259662)]

theorem tbl26_2_ok : tblOK 26 tbl26_2 = true := by decide +kernel

def tbl26_3 : List (Nat × Nat) := [
  (15682, 38905574730773616478667628447707590403670),
  (15714, 38990641083396048566521067617671027414284),
  (15746, 39075737008011951000318129019240583595406),
  (15778, 39140682943171412996339673449317023688272),
  (15810, 116398299904066794233256728336561460295121),
  (21986, 87806414628925659243583166194242984154510),
  (23010, 61022491583411183335070761285454539036311),
  (24034, 61022491583411183335070761285454539036310),
  (25058, 66467158052097284488161354935364655326673),
  (26082, 66467158052097284488161354935365728282129),
  (25985, 76833787456278271380269402606819987195542),
  (16706, 82781912031880999219358336249502974416334),
  (16738, 82781912010475822186889071246018290980302),
  (16770, 82803371540874737333754729784913429374419),
  (16802, 82868188215108779224454286156448528180691),
  (16834, 83567760061250347875560682928593229865818),
  (23042, 61015845443439742615714933094928801109655),
  (24066, 61015845443436028795651389244458402686482),
  (25090, 66460513210192574542503743032687335908817),
  (26114, 66460513210192574542503743032688408864273),
  (25953, 77345536057602011723548808630641756808720),
  (17730, 82781912031880999219358336249502974412238),
  (17762, 82781912010475822186889071246018290976206),
  (17794, 82803370243038207187590615665069978920403),
  (17826, 82868188215108779224453133234943921333715),
  (17858, 83567760061250347875560682928592997646746),
  (23074, 61015845443439742610992566612059155895959),
  (24098, 61015845443436028790929022761588757472786),
  (25122, 66460512019622176046706352905520956126674),
  (26146, 66460512019650859327499555040962703893971)]

theorem tbl26_3_ok : tblOK 26 tbl26_3 = true := by decide +kernel

def tbl26_4 : List (Nat × Nat) := [
  (25921, 77345536057602011723548808912116733519376),
  (18786, 82781912010555069692234787512287793022614),
  (18818, 82804699470793870421468383366933419763219),
  (18850, 82868188539706561012780658286578149111443),
  (18882, 83646123184038154479474027627267552290324),
  (24130, 61015845443439685487539013376643204466195),
  (25154, 66460512024481340046417336541752677213779),
  (26178, 66460512024481340046417336541752677213715),
  (25889, 77345536001196588823606322971257318995077),
  (19810, 82781912010555069692234769497889283540630),
  (19842, 82804699470793831735842154313415178167828),
  (19874, 82868188539706560408317748479256079140500),
  (19906, 83646122210640949829222375952986578462228),
  (24162, 61015845443439685487539013376643204466194),
  (25186, 66460512024481301360791107488234435618388),
  (26210, 66460512024481301360791107488234435618324),
  (25857, 77345536001196588824120417875920782160344),
  (20834, 82781912010625362387659911400855450224014),
  (20866, 82806028576285470397894951320330650854865),
  (20898, 82868188864303873731313195976792887067350),
  (20930, 83731192679656701740772766023111728772561),
  (25218, 66460511912118359908796835900063253603793),
  (26242, 66460511912118359908796835900064326559249),
  (25825, 77345540904765907873098349512579547211280),
  (21858, 82800563066588922191453095210633423038032),
  (21890, 82800773971864633152334878458045480117713),
  (21922, 82868188864302635791273910596517987943126),
  (21954, 83731192679656701740772766023111711995345),
  (25250, 66460532681305798260893011134312058529233),
  (26274, 66460532798740575841053826008266104936083)]

theorem tbl26_4_ok : tblOK 26 tbl26_4 = true := by decide +kernel

def tbl26_5 : List (Nat × Nat) := [
  (25793, 77345540904765907873172136488874385417744),
  (22914, 82800711786808952868302015038168786380243),
  (22946, 82868189188900867069357048040841150309842),
  (22978, 83816284040574389838762112375956423119509),
  (26306, 66460553450493232400211469581224891716181),
  (25761, 77345267674649022380437783939638649484420),
  (23938, 82800711786806476988223444277618988131859),
  (23970, 82868189188900867069357430253003322176154),
  (24002, 83816304809761826060124348295409755821453),
  (26338, 66460574219680666539513930804799424238166),
  (25729, 77345267674649022380441134617423050764824),
  (24994, 65431793988984210059263370584583969759760),
  (25026, 66467158052097206819397468562753753257359),
  (25697, 77345267674649022389882516905377939911812),
  (26018, 65431794314459711084958130215242414227928),
  (26050, 66467158052097206819397474161740864615558),
  (16481, 77340058184492758925120679311679668430289),
  (17505, 77340058184492758925120679311679668430288),
  (18529, 77341387737007097499420308512113271838096),
  (19553, 77341387736849879105274580716705756541654),
  (20577, 77342717289443445842014688672209713820374),
  (21601, 77342716006581038411046534357546069979862),
  (22625, 77344045219365016124180685342248939352727),
  (23649, 77344045219365016124180685342248939352726),
  (24673, 77345267674649022389882510725854041277839),
  (26721, 77601978087780881463650654438199403759191),
  (15651, 38820478883404162004353197423018731963790),
  (15683, 38905574730773616478667628447707573626454),
  (15715, 38990641085072467483385088012974960215438),
  (15747, 39075737008011951097791877626226461181326)]

theorem tbl26_5_ok : tblOK 26 tbl26_5 = true := by decide +kernel

def tbl26_6 : List (Nat × Nat) := [
  (15779, 39140682943171412996413532452488293721680),
  (15811, 116398299579539576807428270727546731308493),
  (21987, 87806414628926070239094499657156292580750),
  (23011, 61022491583411183335070761285728343185047),
  (24035, 61022491583411183335070761285728343185046),
  (25059, 66467014290370495533665202695266518766992),
  (24962, 82800711664302330734403336092089529476561),
  (24961, 76833787456278271380269402509501805168015),
  (16707, 82781912031881005925578321784037733639633),
  (16739, 82781912010475822188523895598529769481681),
  (16771, 82803226481318936504110324783630726795991),
  (16803, 82868188215108779224454286174033198556627),
  (16835, 83567759736652566054107794633547420812122),
  (23043, 61015845443439742615714933095202605258391),
  (24067, 61015845443436028795670863930672744285848),
  (25091, 66460368257902903559713294231242843432401),
  (24930, 82790053928333120476732133668530514367888),
  (24929, 77345536057602011723548808630641756808784),
  (17731, 82781912031881005925578590332742353135058),
  (17763, 82781912010475822188523895598529769481680),
  (17795, 82803226481318936504110326472757356897747),
  (17827, 82868188215108779224453133252528591709651),
  (17859, 83561114894747856108450182730870101394266),
  (23075, 61015845443439742610992566612332960044695),
  (24099, 61015845443436028790948497447803099072152),
  (25123, 66460368257902903559713294231242843432400),
  (24898, 82790053928333120476733286590035121214864),
  (24897, 77345536057602011723548808912116733519440),
  (18787, 82781912010555069693851149358250319783312),
  (18819, 82804555708995371575473828147900623688408)]

theorem tbl26_6_ok : tblOK 26 tbl26_6 = true := by decide +kernel

def tbl26_7 : List (Nat × Nat) := [
  (18851, 82868188539706561012780658286784206886547),
  (18883, 83646121886122394074053365852500799882443),
  (24131, 61015845443439685487539014502541970458131),
  (25155, 66460368262682841200422781322719881138905),
  (24866, 82790053871931604248391256218611187254670),
  (24865, 77345536001196588823606317073208397071759),
  (19811, 82781912010555069693849996436745712936336),
  (19843, 82804555708995332889847599094382382355160),
  (19875, 82868188539706560408317748479461163816596),
  (19907, 83646121886122394074066082017159056303636),
  (24163, 61015845443439685487539014502541970458130),
  (25187, 66460368262682802514796552269201639805657),
  (24834, 82790053871931604248974545553849611257230),
  (24833, 77345536001196588824120412540821947352463),
  (20835, 82781912010651589635900949378306727544206),
  (20867, 82805884814558681443398799080232514295184),
  (20899, 82868188864303874042769188817513553925520),
  (20931, 83731192355129484314944308414098056750541),
  (25219, 66460368150391570954300683659965117044112),
  (24802, 82790053871931603337562514992119152969102),
  (24801, 77345540904765907873098349512578474255824),
  (21859, 82800563066588922191822012047060217964112),
  (21891, 82800568876131202755187364201459454645648),
  (21923, 82868188864302636102729903437238654801296),
  (21955, 83731192355129484314944308414096983008717),
  (25251, 66460367825873017295873956876809096467856),
  (24770, 82789785546583522801702772362520873739856),
  (24769, 77345540904765907873172136488873312462288),
  (22915, 82800568025010454022307459819135990305495),
  (22947, 82868189188900867069357048322109968852434)]

theorem tbl26_7_ok : tblOK 26 tbl26_7 = true := by decide +kernel

def tbl26_8 : List (Nat × Nat) := [
  (22979, 83816283716047157637016962623909078836557),
  (24738, 82789785545384037795850618557518435386766),
  (24737, 77345267674649022380437777760114750850447),
  (23939, 82800568025007978142228889058586192057048),
  (23971, 82868189188900867069357430253071991325338),
  (24003, 83816304485234606830867375397815241221517),
  (24706, 82789785545384037805295351241782749103502),
  (24705, 77345267674649022380441235961678617970063),
  (24995, 65433950816390924545871465361847571289488),
  (25027, 66467157727571212558278440850227613472144),
  (17537, 77340058184494247098340436329751802303955),
  (18561, 77341387737008585672638913980802590856851),
  (19585, 77341387736850129347610109948886548288218),
  (20609, 77342710424250452830636482165163377886607),
  (21633, 77342715899141538303004283530822172345743),
  (22657, 77344045219365266366589983536734016180887),
  (23681, 77344045219365266366589983536734016180886),
  (26753, 77601829777870871189009489236429667325521),
  (17538, 82784576055226555743308501576664442545616),
  (18562, 82785905607740894317608136665736574772624),
  (19586, 82785905607582438064242054687878636394128),
  (20610, 82787228294985467943819020980414375593358),
  (21634, 82787233769876553718418276968255487018382),
  (22658, 82788563090097575083221868915367569827479),
  (23682, 82788563090097575083221868915367569827478),
  (25730, 82789785545384037805295357702781624444035),
  (16708, 44351421830058954110448380802486067328334),
  (16740, 44413689181787687437642078112025493218833),
  (16772, 44498780549094191269697240468308462696081),
  (16804, 44585201136670587524060654434480099718805)]

theorem tbl26_8_ok : tblOK 26 tbl26_8 = true := by decide +kernel

def tbl26_9 : List (Nat × Nat) := [
  (16836, 44670292504075157524556087573572848752279),
  (16868, 44670292504089858660630263167234532255185),
  (23044, 61022491582372256903952661170804115445199),
  (24068, 61022491582372647160973551968192192358040),
  (23907, 82800563066351244996726736161361508718230),
  (23906, 82800563066351244996726736161087704569494),
  (23905, 77356151955862164446869607967197552514448),
  (17732, 88226429902592268371943397529444779071122),
  (17764, 88226429887380499854830872379617931204242),
  (17796, 88247738093957433541266701480410594485711),
  (17828, 88312752115889347726229523279035044013519),
  (17860, 88417631974243880845941026073969076811218),
  (17892, 87802432471571976271400466564329048192466),
  (23076, 61017174670389115157583904951179774862799),
  (24100, 61017174670389115157583904951042335909391),
  (23875, 82788563090111448980742001928989078511898),
  (23874, 82788728884068568845337409406053644514074),
  (23873, 77356151955862203131913610275504685389200),
  (18788, 88226429886360687810719362167981431911758),
  (18820, 88249073853914047805104632507297102902801),
  (18852, 88312747948817605203718810463560148784655),
  (18884, 88419379501334703573717620927292070512147),
  (18916, 87805091253685056247231792589997135705617),
  (24132, 61017174670389507501014398537259056436751),
  (23843, 82788563090097613466682328619795138782870),
  (23842, 82788563090097613361970701011926906938768),
  (23841, 77344045219367742846481606696064225187216),
  (19812, 88226429886360687810719344153582922429774),
  (19844, 88249073853914047805104632507297102898705),
  (19876, 88312747948817604598747462272782661391887)]

theorem tbl26_9_ok : tblOK 26 tbl26_9 = true := by decide +kernel

def tbl26_10 : List (Nat × Nat) := [
  (19908, 88419379501334703573717620927292070512146),
  (19940, 87805091253685364504139232300131496314385),
  (24164, 61017174670389507502204303222820716193432),
  (23811, 82788563090097613466682328619795155560086),
  (23810, 82788563090097613362117896970079914497424),
  (23809, 77344045219367742846483948559005645346192),
  (20836, 88226429886457226799762098871066048132430),
  (20868, 88250403081909832721046711532986441213393),
  (20900, 88312748273415386798353884490025239418321),
  (20932, 88420708729330507855501142695834684827085),
  (20964, 87806414628926070939103455762329071064526),
  (23779, 82788563090097613466616611605443411985050),
  (23778, 82788563090097613362118274964516583351696),
  (23777, 77344045219366504906443600329012527310480),
  (21860, 88245080936047757137654527444070286300559),
  (21892, 88245086817464579135894016214294950389201),
  (21924, 88312748273412539139504233680541074134415),
  (21956, 88420708729330507855501142695833611085261),
  (21988, 87806414628926070243595523225539932657038),
  (23747, 82788563090097613768848066509100705661594),
  (23746, 82788563090097613664349729868173877028240),
  (23745, 77344045219366504911165966811882172524176),
  (22916, 61527577441438324603757687314799607445141),
  (22948, 60918626148830983052485732715351177753934),
  (22980, 61022598713895136790917974159982686971345),
  (23012, 61022491583411176344852535466591334770128),
  (23714, 82788563090097594426025873343894126093970),
  (23713, 77344045219365266366737558600724963206801),
  (23940, 61527577441438330623447934067236038309198),
  (23972, 60918626148830983354717187620308684457358)]

theorem tbl26_10_ok : tblOK 26 tbl26_10 = true := by decide +kernel

def tbl26_11 : List (Nat × Nat) := [
  (24004, 61022598713895136790917974151186593949201),
  (24036, 61022491583411176344852535466614094845584),
  (17569, 77340058184494247098488744646587385144786),
  (18593, 77341387737008585672788374955324414387857),
  (19617, 77341387736850129347757685294352406496913),
  (20641, 77342710424250452830636481883688401175951),
  (21665, 77342715899141538393515341576053650163087),
  (22689, 77344045219365266366737558600724964255185),
  (26785, 77601829777870871187522238826407558181332),
  (17570, 82784576055226575086121979892846547248592),
  (18594, 82785899391429035163117852423692483061395),
  (19618, 82785899391429033047498852570912228222353),
  (20642, 82787228619504021602245747200620442748302),
  (21666, 82787233774947156209841099697969170810254),
  (22690, 82788563090097594426025867463368801625554),
  (25762, 82789785545384037795850624737042334016644),
  (16773, 44521584106505066842614456280396427273550),
  (16805, 44585201136670548739701794581872920864078),
  (16837, 44670292504075156918532140375886566856143),
  (16869, 44670292504089858660630627649349858436561),
  (23045, 61022491582372256903952661170804098667983),
  (22884, 88245080936047333981022629765345572361679),
  (22883, 82800563066351244996726736161361508718231),
  (22882, 82800563066351244996726736161087704569495),
  (22881, 77356151955862164446869607967197552514512),
  (17797, 88247738093957433542756186830805741938127),
  (17829, 88312752115889309040603295610901470193103),
  (17861, 88417631979314483248342346944689725846994),
  (17893, 87802432471571976272888869829063958148562),
  (23077, 61017174670389115159073390301574922315215)]

theorem tbl26_11_ok : tblOK 26 tbl26_11 = true := by decide +kernel

def tbl26_12 : List (Nat × Nat) := [
  (22852, 88233080863447658652838646009862744286542),
  (22851, 82788563090111448979178658691481757656530),
  (22850, 82788728884068568843774155373718890980818),
  (22849, 77356151955862203131913610275504685389264),
  (18821, 88249073853914047805104632225822126192145),
  (18853, 88312747948817605203718810182085172073999),
  (18885, 88419379501335941513780125458958211696147),
  (18917, 87805091253685056247231792308522158994961),
  (22820, 88233080878668020280715055821839460501141),
  (22819, 82788563090097613466682328619795138782871),
  (22818, 82788563090097613361970701011926906938832),
  (22817, 77344045219367742846481606696064225187280),
  (19845, 88249073853914047805104632225822126188049),
  (19877, 88312747948817604598747461991307684681231),
  (19909, 88419379501335941513780125458958211696146),
  (19941, 87805091253685364504139232300131479537169),
  (22788, 88233080878668015472983979186950647871125),
  (22787, 82788563090097613466682328619795155560087),
  (22786, 82788563090097613362117896970079914497488),
  (22785, 77344045219367742846483948559005645346256),
  (20837, 88226436123998463530191117350915367310799),
  (20869, 88250403081909832721046710407292692800977),
  (20901, 88312748273415386798353848461228237231569),
  (20933, 88420708729331745796055711375758117385682),
  (20965, 87806420806199727308527667854578174502487),
  (22755, 82788563090097613466616605650558362166738),
  (22754, 82788563090097613362118274964516583351760),
  (22753, 77344045219366504906443600329012528358864),
  (21861, 88245080936047757137654527162595309589903),
  (21893, 88245086817464579135893944169895051994577)]

theorem tbl26_12_ok : tblOK 26 tbl26_12 = true := by decide +kernel

def tbl26_13 : List (Nat × Nat) := [
  (21925, 88312748273412538535262648773313982436751),
  (21957, 88420708729331745796055711375758100608466),
  (21989, 87806420806198489368488382474303275378263),
  (22723, 82788563090097613768848060554215655843282),
  (22722, 82788563090097613664349729868173877028304),
  (22721, 77344045219366504911165966811882173572560),
  (22917, 61527577426226517604445123161232643040590),
  (22949, 60918563846313074133328171914557191681358),
  (22981, 61022598713895136790917974159982670194129),
  (23013, 61022491583411176344852535466591317992912),
  (6305, 93936819617063158210910592121232660440527),
  (18625, 77341381520694013069372353073111085155727),
  (19649, 77341381520694017636942893450439418021526),
  (20673, 77342711071606250861947647413584927196559),
  (21697, 77342715909282685166901835285826889909647),
  (26817, 77686900369602343730747518198943482180869),
  (18626, 82785899389989367736637744819627925210774),
  (19650, 82785899389989367736636591898123318363798),
  (20674, 82787228942341266277360488210988611732878),
  (21698, 82787233780017700582314676083230574445966),
  (25794, 82789785546583522801702772362520873739792),
  (18627, 82785899389989367736637744819627924948630),
  (19651, 82785899389989367736636591898123318101654),
  (20675, 82787228944022575260667862579233012647310),
  (21699, 82787233780018109694353469687760597353870),
  (24771, 82789785546583522801776631365692143773264),
  (17862, 44691746393893218729328207039321481434775),
  (17894, 44691601273573146514096343424043726742992),
  (17926, 120049501378104018548608114617878219609751),
  (21829, 88245080936047757142376893645464954803599)]

theorem tbl26_13_ok : tblOK 26 tbl26_13 = true := by decide +kernel

def tbl26_14 : List (Nat × Nat) := [
  (21828, 88245080936047757142376893926939931514255),
  (21827, 82800563066588922191822012328535194674768),
  (21826, 82800563066588922191453095492108399748688),
  (21825, 77356151955862164446968721987472548238736),
  (18886, 93863774384609722786377585967720426980883),
  (18918, 93928715466882153822327659790787951543827),
  (18950, 94542735712854051044790630576217909708307),
  (21796, 88231751650673896951392098043046308148622),
  (21795, 82787233779938881531476034513265943184782),
  (21794, 82787233779938470827577964787888004859278),
  (21793, 77342715909203455412163971350454690186639),
  (19910, 93863774384609722786377585967720426980882),
  (19942, 93928715466882153822347095382774517179924),
  (19974, 94537418765614379076619637735257182656020),
  (21764, 88231751650673896951974323402872765871502),
  (21763, 82787233779938881531841403951210140337550),
  (21762, 82787233779938472325742644300436604257678),
  (21761, 77342715909203456910328668595926822356367),
  (20838, 54712439330550458972654990779041564669518),
  (20934, 55555334994377003772487567335269593318799),
  (20966, 55555334994377003772487567335269593318798),
  (20998, 55555334994378241717251417799457224586574),
  (21731, 82787233779938881531839205350167053403534),
  (21730, 82787233779938472419800411745637030495630),
  (21729, 77342715909203457004387570948233345959311),
  (21862, 54712439330550458972654996166577267517011),
  (21894, 55406631515028917844408981247013666252370),
  (21926, 55470243698983467182702783210460801484370),
  (21958, 55578081167441413967722770992235405715024),
  (21990, 55577972739358184139471863384525676029520)]

theorem tbl26_14_ok : tblOK 26 tbl26_14 = true := by decide +kernel

def tbl26_15 : List (Nat × Nat) := [
  (22022, 55577972738082003372455101351058175497615),
  (7329, 93936819617063157908679137217575366763983),
  (18657, 77341381520694013069371200151606478308751),
  (19681, 77341381520694017636942893168964441310870),
  (20705, 77342711071605012921908362033310028072335),
  (26849, 77686900369602343730747518198874762704133),
  (7362, 94448568872174198343776387396804721616338),
  (18658, 82785899389989367736637744819627908433558),
  (19682, 82785899389989367736636591898123301586582),
  (20706, 82787228942340028337321202830713712608654),
  (25826, 82790053871931603337562521453118028309635),
  (18659, 82785899389989367736637744819627908171414),
  (19683, 82785899389989367736636591898123301324438),
  (20707, 82787228944022575255945496096363367433614),
  (24803, 82790053871931603342281422991949954352526),
  (17927, 120049501377921786303251889221199332980178),
  (20805, 88226436123998463530330728939363852686799),
  (20804, 88226429902775689259582105687629796537678),
  (20803, 82781912032039435597176247350991891269006),
  (20802, 82781912030358126613868872982747490354574),
  (20801, 77337394159623111198456032185343805818255),
  (18951, 94542735712854051044790630013267973064211),
  (20772, 88231746814758828913046762590305169765710),
  (20771, 82787228942419545724571828395368614528398),
  (20770, 82787228942419545724571828676843591239054),
  (20769, 77342711071604911008908333208992043304335),
  (19975, 94537418765614379065757014349511473583636),
  (20740, 88231746814758828913628987950131627488590),
  (20739, 82787228942419256499835359926341129799054),
  (20738, 82787228942419256499835377940739639281038)]

theorem tbl26_15_ok : tblOK 26 tbl26_15 = true := by decide +kernel

def tbl26_16 : List (Nat × Nat) := [
  (20737, 77342711071605006891613429784974956234127),
  (20839, 54712439330550458972654990779040490927694),
  (20999, 55555334994378241717251417517982247875918),
  (8385, 99466403905867091942156016815565473121807),
  (8417, 99466403905867091942156016815496753645071),
  (19713, 77337395457780537701584682176913047356815),
  (26881, 77771929361259900183819809379691074953689),
  (8386, 99467733133862876858028920724595486336526),
  (8418, 99467733133862876858028920724595486074382),
  (19714, 82785905607596389256193192358424060147350),
  (25858, 82790053871931604248974550888948446061016),
  (19715, 82785905607582868701927935010324780696282),
  (24835, 82790053871931604248974527539451101775246),
  (19716, 88230423483388036131167492608929588385295),
  (23812, 88233080878668405242209652702855139751246),
  (19748, 88226435799400681709389762662745019848207),
  (19747, 82781911706002012989017880476942477067926),
  (19746, 82781911706002012989017880476942477330070),
  (19745, 77337393836706662889324182029258576987798),
  (9409, 99466402283512008137565175938610683774479),
  (9441, 99466402283432779975050911601017139824143),
  (26913, 77771929421539053752561752492206119252313),
  (9410, 99467732486344680884805053269581809690131),
  (9442, 99467731511428564890923815409651223692814),
  (9474, 99978157334639448375056225040178971780497),
  (25890, 82790053871931604248391262679610062595203),
  (9475, 99978157334639448375056225040178971518353),
  (24867, 82790053871931604248391255937136210544014),
  (23844, 88233080878668405243382159847237022230037),
  (10465, 104910920478686349048891597173933482771983)]

theorem tbl26_16_ok : tblOK 26 tbl26_16 = true := by decide +kernel

def tbl26_17 : List (Nat × Nat) := [
  (10497, 104995991070416577864509641893507506963855),
  (10529, 104995991070416577841125997865078889186703),
  (26945, 77857000013344802709722982590749757965910),
  (10466, 104912249706682133964764501083084900861454),
  (10498, 104997320298412362780409313702357111776654),
  (10530, 104997320298412362756999314873274027541902),
  (25922, 82790053928333120476733286668992707625496),
  (10499, 104997320298412369487340962614747542886038),
  (10531, 104997320298412369487340962614747542881942),
  (24899, 82790053928333120467288571638694340269456),
  (23876, 88233080965903173149855677055974117021199),
  (22853, 88233080863447658648116279526993099072846),
  (11489, 104308594304181642434135394233359429326092),
  (11521, 104303675216146502280885397033915660178959),
  (11553, 104303675216146502280883197869922619823631),
  (26977, 77857000013344760189092448974695224608342),
  (11490, 104308594304181649436746439739793538602252),
  (11522, 104303277067697500036644848216912067642894),
  (11554, 104303277392225956308691480699558896182801),
  (11586, 105422678461017946730784005360647275819802),
  (25954, 82790053928333120476732133747488100778520),
  (11523, 104308992173844640576397733957433471604108),
  (11555, 104303277392225956308691480699558879405585),
  (11587, 105422678461017946730784005360715944968986),
  (24931, 82790053928333120467287418717189733422480),
  (11588, 105424008013208906666791000678971367564817),
  (23908, 88245080936047724238043520562733649274520),
  (22885, 88245080936047333981022629765345555584463),
  (16870, 44691601273573146514096343424043726742993),
  (16838, 44691746393893218729329359960826088281751)]

theorem tbl26_17_ok : tblOK 26 tbl26_17 = true := by decide +kernel

def tbl26_18 : List (Nat × Nat) := [
  (12545, 109839822486747927035908854263424480515661),
  (12577, 109839822456541914480269641680277995840845),
  (12609, 110525579821985007939726051007132554560911),
  (12641, 110525579821982665645950547663106561344911),
  (27009, 76833787477193209644174381846155256726927),
  (12546, 109839822486827155197380966872872877614413),
  (12578, 109839822461612907057186329074665070585165),
  (12610, 109851892656766514611773227995565811618390),
  (12642, 110526909049978450561823451465768795178382),
  (25986, 82800711664302330734403336092090602432017),
  (12547, 109839822486827155197380966591397900903757),
  (12579, 109839822461612907057186329070267024074061),
  (12611, 109851892651695912210494834277016674820694),
  (12643, 110526909049978456903810582728998729876878),
  (24963, 82800567902575541779907183851991392916880),
  (12612, 109851892976205920647599869851907807323729),
  (12644, 110528238278053469982271267638322548503886),
  (15814, 114603651674423880568201715505861037987216),
  (15813, 116398299584612655088935042380538793244114),
  (15781, 39140682943171413000988324978370216011344),
  (15749, 39075737009527052998689263492334627394960),
  (15812, 116398299584611417148380473700614303720909),
  (15780, 39140682943171413001135898930891172947536),
  (15748, 39075737008011951097864511399541715830158),
  (15716, 38990641085072467483386186891352758093198),
  (15684, 38905574732361005553710311784929471063636),
  (13569, 109924726894767787364619643559131115479637),
  (13601, 109924726894767806707432488584663888360782),
  (13633, 109919409983022351531483666369203398833486),
  (13665, 109919286990490514987754215553071600432462)]

theorem tbl26_18_ok : tblOK 26 tbl26_18 = true := by decide +kernel

def tbl26_19 : List (Nat × Nat) := [
  (27041, 76835112126297870615113829121263734724050),
  (13570, 109924726900101064859027207074993911690574),
  (13602, 109924726899863380372676499048816848467278),
  (13634, 109919409983022351531483648354804889351502),
  (13666, 109919286990490514987754197538673090950478),
  (13698, 110952431387031064006633065821766947251665),
  (13571, 109924726900101064859027189060595402208590),
  (13603, 109924726899863380372676499044418801956174),
  (13635, 109919410090320976084461431820724556355154),
  (13667, 109919287097789139540731981004592757954130),
  (13699, 110952287625304275052136913581668810691984),
  (13636, 109919410090320976117495047134255852627535),
  (13668, 109919287097789139573765596318124054226511),
  (13700, 110953617249916195830243736122574726571473),
  (13701, 110953617249916195830243734996880978159057),
  (14757, 39140682943171409402989982127515622507919),
  (14725, 39075737009531040333322134840366598022738),
  (14756, 39140682943171409402989982131913669019023),
  (14724, 39075737008011951097864511399541715830159),
  (14692, 38990641085072467483386186891352758093199),
  (14660, 38905574732364583402730026660059530487380),
  (14755, 39140682943171409100758545524129861535119),
  (14723, 39075737008011951097791877626226461181327),
  (14691, 38990641085072467483385088012974960215439),
  (14659, 38905574730773616478667628390878718563727),
  (14627, 38820478883404162004353197423018731963791),
  (14754, 39140682943171409100389629030676572729942),
  (14722, 39075737008011951000318129019240583595407),
  (14690, 38990641083396048566521067617671044191500),
  (14658, 38905574730773616478667628390878735340943)]

theorem tbl26_19_ok : tblOK 26 tbl26_19 = true := by decide +kernel

def tbl26_20 : List (Nat × Nat) := [
  (14626, 38820478776063719803896563004288256259663)]

theorem tbl26_20_ok : tblOK 26 tbl26_20 = true := by decide +kernel

def tbl26 : List (Nat × Nat) := tbl26_0 ++ tbl26_1 ++ tbl26_2 ++ tbl26_3 ++ tbl26_4 ++ tbl26_5 ++ tbl26_6 ++ tbl26_7 ++ tbl26_8 ++ tbl26_9 ++ tbl26_10 ++ tbl26_11 ++ tbl26_12 ++ tbl26_13 ++ tbl26_14 ++ tbl26_15 ++ tbl26_16 ++ tbl26_17 ++ tbl26_18 ++ tbl26_19 ++ tbl26_20

def mask26 : Nat := 559282312443119695686645606766995577694755737657141756695564471325958986582540366171432706650080081853672574429095271928698498543740775590834269419850857733835883854804183508020086678419564602688748739461597727662102423539472025860736935205562676085126445762744067958399000513952017099029494895691329163205540870545098939615338364949128062418890967087036707400322245029542456432575816321364734685589878035134823122526937966379638833464442898046239174913536402428150816554684960751872738500535552898637717148613319143273218447724570751593059146312075908008155158876517142137955508441421302526671863305439170889332167106415979679810427809068405612234032969747789528481346408510735007240082976169358065259293750508814435154544420963290649807104701728623454272617151251851813197204262700249839313242085670759384954576473531664882847162634695521778046752256299561032527270672868404181544010089143410717859798488288815312315986067412235779697673696540646540504687765042215089851370603219974077365789946755460252437382799658265691317525827773899440608769940430198676733482698267612195360920562856892191832021731596450286400124409465213208812416775236377045327081382200332463064620469995851028039930175584836517575506332121221177672496614668297856307516824714789715089521906827067671016150168779203115984121025597641782998524151734095312623190686423050387330134573515527740079618560943059289147246859518509550477831663793052990585087012350642834910318728486903402066399052152818731797905559224524798161404803390628740799563679038996925574155246283008066715139675099662866429811211848405455036302317374170938061813210984532209451261458226243972878776250101327705190123717204905785290442686341258403717152712623563850361412003573272283812301014584076901240243818687705802522320816193340872811213096169385978986304849289456426488787697624389185203003459515161993384061822424457392377078644610560026736936360585506234806162501768610484732835430326558252672539622555547566196934933322040788575666971460644734591287880975481917485246850669381289276647637067889751534076845940696664454529227614846585215816011511273598624738631407263257147976033863428176593179486369958748927213250820433649180322170596041482761875147908637616057378030796915199420300161388633085183615863640880143687673072840525571288620540403398948033526180352581099751933380670169011041585825755935082762909275403685178225018445289805461601455105374105739768885766588301664056039136645634813458662126615167759230984191717324755260881262942310933169920753646481514409290351989021738965241514112894696775663246990271304143530819404820978950807557071937358702436087688178906928700842468253574340285090146659346145048523103949735083496632193306663206565322025725728128579715361687116096312987268861997923200266040495649160446031354108381994419332740503660857946227170699572809694093874151640907475207646277598831527419350907853255103089034875833170978205868193169092598157641441063987314035036648317727061682352969048976135956736363222917430592005708658949381597345254482213223744897701326402959155787932705748935289808091947557732489929264933153916142543140885358610968634522387495211870715840121174735513059828843281992297740613234758277636758588013949715366647762552117288598342932068257059631263279612133889423426607436742808855747970267898232987555758295687874028313754326560991855298899228409677458270997270436483045115424973679933779797097250067004078789138603699340564081563863165710413457323985830231150309937132828740798985708445542562710867387771275319828061523655901368836358194739888279616521926929690414057131417718244045313595667771075531693859164370176791867790069820578072368782135575101736419522080176011029647673149576631758033618792397963780143131317349785798310989648774772876943186738867156307170858944689225617693429172040575354909086623604857938953595711970713360786407271049794199243902198287065704564554488992643932823417363934073547178986354486298031473406957441744539777946632712058227733153156204439042687650844327986920259129555674178083254420866811041642400995511873775302421330899626062564677113628915488354592808869549002381271087310810464199172207831727390214711395167702463509187153883003190179003611260358087690482939894142653606632891347654974594262526473348997546890525449901014301002109232920471100206291780894007802706159416891375475387439652831841734387364488531764168789236641811241958049437865537969720611708120618942085746353411693786665755883797082274772970397602200456796912327692824006355984695102492667153295392584461307438917751763118024910117909973188515361406215809367374669576500857616915113331895491632088149002555496154667518882725742360030743972379986952538084095169166333789329350012750426097374985867979809299456603751441019560292159630505935372957706879093955162475376221911665230388189774395365872312243208898645910998377454333497177964936867581851433735122353942461831852326257500083687044661523282608004739614309429552718196299504509799775184884732957452185539251284245209829491556469396117361758373648763792201506681788362583546846587271993093955863390548452612596113194401172560108736440390142878401129888430950530717635690182307689803335558566106317925039828152461100245004602761145778147272083640800305744389562982636743357334361344902260049720998173662466440158045749252503590175405380097170743370650665872974678289003733915171931321747508011498235276682205318019481457768463365356173071892459733323043212990283914314808178146198975823604548787343002207283141016017940839350833297538286336910097467670251317517814153973299962546174549554442625698702318135482084432643519328992386843766918193396713529361118649786846286658499246867245592257471164531746807584212418198776642953223432009184596642030526236419498281463694571724817805461756200278647515526578460015515280371797654792860604497822954583663877826230437852572706368350987099363387208024927067796335038150208006469206305659162363041116889026534517508604659300054606958762554563339709648961454807695356724112783444308925206480643198219616381124383244757979240872238260467357096017462637518280506408584823600010003017815612036475215995249762838919545683894282659953707900079477691755991116458564582327685633322488511141537470140742484608299780672337190623895404816637637623905993253412639594227115838757182065215359977783687179655315044973750252860659734865606455165482034752193986841818160286773306087761894399588566654745906157099726310468042247038042011777208986192011776907542997637014707460313220132863887087004278065689190876433043200438544159993191532973720593107367065944981835480448938756982143883172161337379420300547252681805694828884670861356374564092767433698065445480330826820529000679766239874785806554134027730918489403720110453433118711146537664118534490351024924189531729637270031584695569971518967415283607159897148807541787998016879779558340306204997149025399143676136822958476561720958427931392867422180579161571478974249581736920278391043156139606198135186477758825607416420760524980635790575679426400053531933233630798156181424131020459247699051881234342943105938026486759592737213666727745671632427101482316324930310713920432495996202234217788915694235790935132061982575795313833381240417366653032728053367095768675709379523317998793882937904496085769672708577293957684703813087227871159745910767348473491518427515435555065405751360882977686686973799460568345631882893061714806341627644535566370873767997291007546931620622427568639402884070380168767822169157711064128470364808852094622555722454901103572548502671203194531251012207133608142734036920732608248410656424484862115717798095934573614172463358952711439541402519329525815143223399047613043161992886320579246633783117869509739050475278466899052592461360049799239110490579450556979746123370384760364985851911726497080055180367360221562607956626199607674691077528646574904654451574788016497042943073244865535443659110149283454972882894672590179414906032096939191767142614566915041286316384501547843916899467284743954959295578873319434689481828635117930507874250608985685760677317370996951985528527586905047270448263075909409441594745487193815051152429843744944521860093880601255249465482608964290557574346593104183337949140186944571982453734850236964967910881568769906008088017737595670102505765914015694848

theorem mask26_eq : maskL 0 (tbl26.map Prod.fst) = mask26 := by decide +kernel

theorem cov26_1 : coverX 26 mask26 1 = true := by decide +kernel
theorem cov26_2 : coverX 26 mask26 2 = true := by decide +kernel
theorem cov26_3 : coverX 26 mask26 3 = true := by decide +kernel
theorem cov26_4 : coverX 26 mask26 4 = true := by decide +kernel
theorem cov26_5 : coverX 26 mask26 5 = true := by decide +kernel
theorem cov26_6 : coverX 26 mask26 6 = true := by decide +kernel
theorem cov26_7 : coverX 26 mask26 7 = true := by decide +kernel
theorem cov26_8 : coverX 26 mask26 8 = true := by decide +kernel
theorem cov26_9 : coverX 26 mask26 9 = true := by decide +kernel
theorem cov26_10 : coverX 26 mask26 10 = true := by decide +kernel
theorem cov26_11 : coverX 26 mask26 11 = true := by decide +kernel
theorem cov26_12 : coverX 26 mask26 12 = true := by decide +kernel
theorem cov26_13 : coverX 26 mask26 13 = true := by decide +kernel
theorem cov26_14 : coverX 26 mask26 14 = true := by decide +kernel
theorem cov26_15 : coverX 26 mask26 15 = true := by decide +kernel
theorem cov26_16 : coverX 26 mask26 16 = true := by decide +kernel
theorem cov26_17 : coverX 26 mask26 17 = true := by decide +kernel
theorem cov26_18 : coverX 26 mask26 18 = true := by decide +kernel
theorem cov26_19 : coverX 26 mask26 19 = true := by decide +kernel
theorem cov26_20 : coverX 26 mask26 20 = true := by decide +kernel
theorem cov26_21 : coverX 26 mask26 21 = true := by decide +kernel
theorem cov26_22 : coverX 26 mask26 22 = true := by decide +kernel
theorem cov26_23 : coverX 26 mask26 23 = true := by decide +kernel
theorem cov26_24 : coverX 26 mask26 24 = true := by decide +kernel
theorem cov26_25 : coverX 26 mask26 25 = true := by decide +kernel
theorem cov26_26 : coverX 26 mask26 26 = true := by decide +kernel

theorem cert26 : Cert 26 tbl26 := by
  refine ⟨by simp only [tbl26, tblOK_append, tbl26_0_ok, tbl26_1_ok, tbl26_2_ok, tbl26_3_ok, tbl26_4_ok, tbl26_5_ok, tbl26_6_ok, tbl26_7_ok, tbl26_8_ok, tbl26_9_ok, tbl26_10_ok, tbl26_11_ok, tbl26_12_ok, tbl26_13_ok, tbl26_14_ok, tbl26_15_ok, tbl26_16_ok, tbl26_17_ok, tbl26_18_ok, tbl26_19_ok, tbl26_20_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask26_eq]
  interval_cases x
  exacts [cov26_1, cov26_2, cov26_3, cov26_4, cov26_5, cov26_6, cov26_7, cov26_8, cov26_9, cov26_10, cov26_11, cov26_12, cov26_13, cov26_14, cov26_15, cov26_16, cov26_17, cov26_18, cov26_19, cov26_20, cov26_21, cov26_22, cov26_23, cov26_24, cov26_25, cov26_26]

/-! ### `N = 27`: 675 witness orderings -/

def tbl27_0 : List (Nat × Nat) := [
  (15649, 2484597335850597447432693663433253209052624),
  (15681, 2490041560964401150400142537435611678221579),
  (15713, 2495487721558825845975358268922220585526736),
  (15745, 2500931947352405617637681789574111138735437),
  (15777, 2506378107296695326583516253726790859204048),
  (23009, 5619696936395566051277470507669077631772113),
  (24033, 5619696936395566051167629592135413897171547),
  (25057, 4258226192416041258125418758222033807292113),
  (26081, 4258226192416041258125418758222034864256657),
  (27105, 4606685989416839543809102830897733130073681),
  (28129, 4606685633724305540426568937846351447758488),
  (16705, 5303573638803409382079926316165080713602513),
  (16737, 5303573638778056404247800633200473700640209),
  (16769, 5303573638762537549229692878406204688770513),
  (16801, 5303585249752740722416596568101534372013521),
  (16833, 2858898720180315471917864816107348357916111),
  (23041, 3910449302755721674232642641723950738515409),
  (24065, 3910449302755721674122801726190287003914843),
  (25089, 4258898446467243805691189569406354799006295),
  (26113, 4258898446467242567448919982324856728916696),
  (27137, 4606668502766196263980027992321413442507353),
  (28161, 4606668502771267218150239364256292259051025),
  (17729, 5303573287973445704145422923845781808817680),
  (17761, 5303573287974395179396770719112410646259216),
  (17793, 5303573291625046681541075137719146803701264),
  (17825, 5303562716457041727236954614036586581272080),
  (17857, 5620028290922336974584303857487702890722834),
  (24097, 3910449658478214003668084077629404294755858),
  (25121, 4258898802205255048282944005749289652139602),
  (26145, 4258898802205255048282944005749358371354130)]

theorem tbl27_0_ok : tblOK 27 tbl27_0 = true := by decide +kernel

def tbl27_1 : List (Nat × Nat) := [
  (27169, 4607347945932296034860649730208367491495506),
  (28193, 4607347940699915004542230527068366833205850),
  (18785, 5303573287974395179401492996649187650901520),
  (18817, 5303573291625046700883888127141273892886032),
  (18849, 5303562737226229161376265039212479257581072),
  (18881, 5620027997330260067460837153115527193638417),
  (24129, 3910449658478214119724888937615519069845009),
  (25153, 4258898802205255106311383382704142964045393),
  (26177, 4258898802205255106311383382704211683259921),
  (27201, 4607347945932296092889089107163220803401297),
  (28225, 4607347940704985606943143444674284926550554),
  (19809, 5303573287974474407564007260986781178074576),
  (19841, 5303573291949583980161311809263176704685780),
  (19873, 5303562737226230399316304324592754139928016),
  (19905, 5620027997233151311785356668523205396080081),
  (25185, 4258898801231699443220704345172165079680593),
  (26209, 4258898801231699449615902302064948313962132),
  (27233, 4607347944958740436202397900075078945715796),
  (28257, 4607347944958740436107206954062595797034641),
  (20865, 5303573291949583980161311811497380037359315),
  (20897, 5303562757995417833455032613354844279608784),
  (20929, 5620028018002338745924441335849602343839185),
  (25217, 4258898801231699445336103202354674919093841),
  (26241, 4258898801231699445337666874930046672942737),
  (27265, 4607347944958740431913833485772147179468369),
  (28289, 4607347944958740431913833120797050400171665),
  (21857, 5303573287972795844035750189795841619334608),
  (21889, 5303573285073040144253518292351033440540112),
  (21921, 5303562757995391895125158646988110018713040),
  (21953, 5620028018002312543113710129885449525208529)]

theorem tbl27_1_ok : tblOK 27 tbl27_1 = true := by decide +kernel

def tbl27_2 : List (Nat × Nat) := [
  (26273, 4258915952955279569767655910134884783203793),
  (27297, 4607347944958740431913808926813752741672529),
  (28321, 4607347589266206428531275033762371059357336),
  (22913, 5303573617993508575923876913054686584051152),
  (22945, 5303583921173782049326043137956066257081808),
  (22977, 5620028038771499875925741650744466073003473),
  (26305, 4258915952955279569762933543652015137990097),
  (27329, 4607347589590739774247574609179939521468117),
  (28353, 4607347589590739774247574609179939521468053),
  (23937, 5303573623597164217884905552252425753933329),
  (23969, 5303584276870921516981440320424814700213777),
  (24001, 5620028038771499875925226301275314442539611),
  (27361, 4607347589590741012185905015482203282429328),
  (28385, 4607347589590714828713263798003713638962244),
  (24993, 5303584276870921516982094026917924634965585),
  (25025, 4291565908456109537828587164668124667393617),
  (27393, 4607347589869995339516084891415629336438225),
  (28417, 4607347589869995339516084873401230826956241),
  (26017, 5303584276870921516982094026917993354180113),
  (26049, 4291565908456109537830150837243496421242513),
  (28449, 4607347589869916085004550231602446216226321),
  (27073, 4568978196472288386485388216295299641307862),
  (28097, 4291565722777238089795652159274477073806039),
  (16449, 7743057618043672505851355899303829841703511),
  (17473, 8091506761770713492437852649672515127145046),
  (18497, 8091506761770714730378234459445131448485263),
  (19521, 8440040975066407737278465734723387263878543),
  (20545, 8440040975441490049150663382590744304359120),
  (21569, 8788490391043208962661052231970903359559119),
  (22593, 8788490391043209081744581255964400290436559)]

theorem tbl27_2_ok : tblOK 27 tbl27_2 = true := by decide +kernel

def tbl27_3 : List (Nat × Nat) := [
  (23617, 9137028343491440243320174638384033606210139),
  (24641, 9137023276133984518112463781574341246658001),
  (25665, 9485472419861025504698959379584494074406353),
  (15650, 2484597335850597447432693663428855162541520),
  (15682, 2490041560964401150400142537431213631710475),
  (15714, 2495487721558825845975358268917822539015632),
  (15746, 2500931947352405617637681771559712629253453),
  (15778, 2505003729436870616875029002488355207321040),
  (15810, 7781610771659098126016302941814591932937745),
  (23010, 5619696936395566051277469354747573024925137),
  (24034, 5619696936395566051282219595099112374288987),
  (25058, 4258226187234046772726488465508614728857299),
  (26082, 4258226187234046772607153091974213148964499),
  (27106, 4606685654494771336186434341848512884421827),
  (27041, 5303584276870921516982094026917994427135569),
  (16706, 5303573638803409382079852529188785875396049),
  (16738, 5303573638778056404247799480278969093793233),
  (16770, 5303573312084924893344617954479754082592209),
  (16802, 5303564045767273459476273603542186700907985),
  (16834, 5348671601854135207205548727101066041701905),
  (23042, 3910449302755721674232641488802446131668433),
  (24066, 3910449302755721674237391729153985481032283),
  (25090, 4258898467354102665612560924892363553845975),
  (26114, 4258898467226288756898265251739392057872984),
  (27138, 4606668502766196263980027992039938465796697),
  (27009, 5303584091267631024097404669733026517562961),
  (17730, 5303573287973445704147207938751928799893208),
  (17762, 5303573287974395179396798593266929617712656),
  (17794, 5303573312394262822295575677294467791828499),
  (17826, 5303564045772106864016251046618179849532947)]

theorem tbl27_3_ok : tblOK 27 tbl27_3 = true := by decide +kernel

def tbl27_4 : List (Nat × Nat) := [
  (17858, 5353860916119699938045553911813986657613328),
  (24098, 3910449658478214003668084084454734208775698),
  (25122, 4258898467333821493383536181098488584222419),
  (26146, 4258898467333790310888241192955499367704016),
  (27170, 4607347609387636356737082054733101588611673),
  (26977, 5304094369433621164654543076560703544178258),
  (18786, 5303573287974395179401520959749730460612112),
  (18818, 5303573312394262764265889955891720825423379),
  (18850, 5303564066541294298150839194257294447457811),
  (18882, 5353351986328221020088582232826615981958872),
  (24130, 3910449658478214119724888944454043073066513),
  (25154, 4258898467333821435344380487436531237996115),
  (26178, 4258898467333790330231054200110549989660112),
  (27202, 4607347609712154910395508781516257592410649),
  (26945, 5304094369428550562253631311876221338207826),
  (19810, 5303573287974474407564035224082925958051280),
  (19842, 5303573312718771414410512894143621336176340),
  (19874, 5303564066546364899947289597523561924036308),
  (19906, 5358796339688014827635240360558994916665049),
  (25186, 4258898467333811531840021431871015018600148),
  (26210, 4258898467333811531720686056370700590085780),
  (27234, 4607347609712154910395508781533775687403088),
  (26913, 5304094365499234774771383753412725635593410),
  (20866, 5303573312718771414410512894143628835567315),
  (20898, 5303564087315552198686909503757589586687703),
  (20930, 5358796339668053429237972765687685149647707),
  (25218, 4258898467333811531840021431871022517991123),
  (26242, 4258898467333811531720686058336620938098323),
  (27266, 4607347610036673462231179723144807395144899),
  (26881, 5304094365499234774790050705493814827352409)]

theorem tbl27_4_ok : tblOK 27 tbl27_4 = true := by decide +kernel

def tbl27_5 : List (Nat × Nat) := [
  (21858, 5303573287972795844035676402819546781128144),
  (21890, 5303573313043210739787089983054789732300435),
  (21922, 5303564087320621563147753936618107125466775),
  (21954, 5364240849368763926824871019198129717720593),
  (26274, 4258915952960350172168568791131601542648407),
  (27298, 4607347610036672224291140437764532496020675),
  (26849, 5304094700421302924677289088829142079452753),
  (22914, 5303573618430381539569378638822565533021843),
  (22946, 5303583941944020743886513930198732803770007),
  (22978, 5342466765569811219910833755743677393221137),
  (26306, 4258915952960350172163846424648731897434711),
  (27330, 4607347610361270474609445450277429231236819),
  (26817, 5304094700096784254961984886019479561909842),
  (23938, 5303573618415169732485950020245535585056275),
  (23970, 5303583941943783059399000336551137017382616),
  (24002, 5342462786055844284435403766328696967030488),
  (27362, 4607347610361349234274595261725794919318166),
  (26785, 5304094700096625779293776657602920808236228),
  (24994, 5303583941948853661799913254157123830200023),
  (25026, 5342462786055844284435403766306717319149009),
  (27394, 4607347610751466543787637197618666783716055),
  (26753, 5304094699706588185781933536619100528989777),
  (26018, 5303583941948853661799884054791929455281815),
  (26050, 5342462777885823865163215044322496552187409),
  (26721, 5304094699701517581572572158238072197125715),
  (27074, 4568979524077766943712534641116724922749465),
  (17505, 5303658400103550807045218998707374961534480),
  (18529, 5303743470695281041661084717947293197473296),
  (19553, 5303743470695257283946228871371756527228368),
  (20577, 5303828541286989032423795689439165812643280)]

theorem tbl27_5_ok : tblOK 27 tbl27_5 = true := by decide +kernel

def tbl27_6 : List (Nat × Nat) := [
  (21601, 5303828541286989051761886436794759935235536),
  (22625, 5303913611954381892343372380048422301406672),
  (23649, 5303913611954403124660318606947524241331728),
  (24673, 5303998685472975108831106594556745907770071),
  (25697, 5303998685472975108831106594556813553242839),
  (27745, 5304094720588138637257172300542839989839115),
  (16707, 2838491142837776923629134778209515847873239),
  (16739, 2843936865285868070501893152308159333639631),
  (16771, 2849381091084543415829384592306646558791311),
  (16803, 2853452873162237736960841517864797654808014),
  (16835, 2858898720180315510603419108943780360295887),
  (16867, 2864429632389606393682920497984298851837393),
  (23043, 3909777043110873692566790181564440067511759),
  (24067, 3909777048688748990575628360432574765516504),
  (25091, 4258226187162257489830833314609231538271697),
  (26115, 4258226187162257489711656554569011447797199),
  (25986, 5303573618415169732366639886004605094557331),
  (25985, 5303573623597164217884905552252426809849489),
  (17731, 5652022431700486690841880899329802916705810),
  (17763, 5652022431700249006354338088302624948467219),
  (17795, 5652022451258669262088017948806234775074323),
  (17827, 5652016162727419232277428720081169453467352),
  (17859, 5658840481226422923229152449830923019597331),
  (17891, 5619357030784468067950128631638211896882706),
  (24099, 3910545051625101251396029942175059661842136),
  (25123, 4258994190175448414728117369885907121190483),
  (26147, 4258994190175448414608868573216043751257618),
  (25954, 5303998971373804614910308877853782847329744),
  (25953, 5303998971373804614910382664830077685536208),
  (18787, 5652022431700231443665679149666245561619983)]

theorem tbl27_6_ok : tblOK 27 tbl27_6 = true := by decide +kernel

def tbl27_7 : List (Nat × Nat) := [
  (18819, 5652022451186811717550223259137255685862929),
  (18851, 5652015868724326425977275889303457274598927),
  (18883, 5658840295961506088423824822540368784504339),
  (18915, 5619527172080289162896954690183499917407764),
  (24131, 3910545051625080053500414488327280105408216),
  (25155, 4258994190175448414728116216964402514343507),
  (26179, 4258994190175448414609237507815768087672337),
  (25922, 5303998971373822143404822967187770651551186),
  (25921, 5303998971373822143404822967469245628261842),
  (19811, 5652022431700231443967910604565504808785359),
  (19843, 5652022451186812955490254582153389393950161),
  (19875, 5652015868627117535957963924586806974723537),
  (19907, 5658925366543095118237864830980253100914258),
  (19939, 5619527192849238868450905547596721491367508),
  (25187, 4258994190175448472719145956935403240707796),
  (26211, 4258994190175448434031739278754168587503249),
  (25890, 5303998971373822143400100603202992498386386),
  (25889, 5303998971373822143400100603207390544897490),
  (20867, 5652022451191883557891093712783084572227025),
  (20899, 5652015889396281488201217618205296206321367),
  (20931, 5658925366517877175317026145466730662704725),
  (20963, 5619611865803862108361311199743412880324311),
  (25219, 4258994190175448472719145961988422466294491),
  (26243, 4258994190175448434031739385151709784127121),
  (25858, 5303998971373820905460061335837116108732051),
  (25857, 5303998971373820905460061335841514155243155),
  (21859, 5652022431700232971434743285362948223604175),
  (21891, 5652022451191884795409724783219482087200207),
  (21923, 5652015889396281507537451868399955870291407),
  (21955, 5659010428944284955546997985913287733749197)]

theorem tbl27_7_ok : tblOK 27 tbl27_7 = true := by decide +kernel

def tbl27_8 : List (Nat × Nat) := [
  (21987, 5619611865803863338697220810448739555157457),
  (26275, 4258994190175447985789651928384999332062673),
  (25826, 5303998971373820905445969104263894804821651),
  (25825, 5303998976555815390964234770511716520113809),
  (22915, 5652022762070421494086078288111734427817423),
  (22947, 5652015910251114296119179788660532149032399),
  (22979, 5659009099716289170631125082106227453404621),
  (23011, 5619696936395593553951821032148248069481937),
  (26307, 4258994195104463566652136343127737071924883),
  (25794, 5303998685472975132372022808303440677140115),
  (25793, 5303998976555736162801351534812081113900498),
  (23939, 5652022762070421436176815706649754132395537),
  (23971, 5652015910252558849998150878691633815656152),
  (24003, 5659094177175449488565509176664724734064147),
  (24035, 5619696936395594799207857612972276148881107),
  (25762, 5303998685472975132381467613313577718478483),
  (25761, 5303998685472975132381467613313578792220307),
  (24995, 4291660282722240972038742777201639738684881),
  (25027, 4254407214292177654519525336690123701597649),
  (25059, 4258226187234046772726488787814985337688795),
  (25730, 5303998685472975109133338050853211786262161),
  (25729, 5303998685472975109133338050857609832773265),
  (26019, 4291660282712099299387429009944777763394263),
  (26051, 4252263062691032974313858066842796338508376),
  (26083, 4258226187234046772607153164001023008798355),
  (17537, 5303658400103550807040496632224505316320784),
  (18561, 5303743470695281041656362351464423552259600),
  (19585, 5303743470695282279596401636844698434606544),
  (20609, 5303828541287012514211681078857650941572560),
  (21633, 5303828541286986575881807130500849498170832)]

theorem tbl27_8_ok : tblOK 27 tbl27_8 = true := by decide +kernel

def tbl27_9 : List (Nat × Nat) := [
  (22657, 5303913611954379416463293073754511864341968),
  (23681, 5303913611954403124055854943596916197668368),
  (24705, 5303998685472975109133338050857608775808721),
  (27777, 5304094720475775619922956084824282293884561),
  (17538, 5303658400103550807040496638953853331252752),
  (18562, 5303743470695281041656362787183211837502992),
  (19586, 5303743470695282279596402072563418017150416),
  (20610, 5303828541286989032425578360815511772370647),
  (21634, 5303828541286989051761812631804066587547088),
  (22658, 5303913611954381892343298575057728953718224),
  (23682, 5303913611954403124662101278323870201059032),
  (24706, 5303998685472975109133338050964464234424017),
  (26754, 5304094699706588185781859749642805690783313),
  (16708, 2838491142837776942995337223023364504360399),
  (16740, 2843936865285894302934388498451242214577809),
  (16772, 2849381091191809585564074919175855999374993),
  (16804, 2853452873163911603768478349823020710303183),
  (16836, 2858898720287599294644016398743461741541009),
  (16868, 2864429639254416049816675894699239374661073),
  (23044, 3909777043110873692868800293553611356050895),
  (24068, 3909777048688748990573849546676117726672401),
  (25092, 4258226187162257489716305570352910429918671),
  (24963, 5652022762070421436176815706649754132395473),
  (24962, 5303573618415169732485975259539006674450131),
  (24961, 5303573623597164217884905552252425752884945),
  (17732, 5652022431700486690727659833856318069577432),
  (17764, 5652022431700249006240264614796127114139352),
  (17796, 5652022451258668794817661050719598799562255),
  (17828, 5652016162727416756395637792672713389454866),
  (17860, 5658839978470022894237262762202263802689037)]

theorem tbl27_9_ok : tblOK 27 tbl27_9 = true := by decide +kernel

def tbl27_10 : List (Nat × Nat) := [
  (17892, 5619357030774326863148302796426239344981522),
  (24100, 3910545051625071381833084143075407648601618),
  (25124, 4258994190175448414613517152828899487200850),
  (24931, 5652448115100845603009818210946990411388631),
  (24930, 5303998971373804614912165336202026673018583),
  (24929, 5303998971373804614910382664825680713029072),
  (18788, 5652022431700231443665651586256775309760015),
  (18820, 5652022451186811717436123357127081674479119),
  (18852, 5652015868724326387289935285760360903939599),
  (18884, 5658840288085421028717927739351386494420499),
  (18916, 5619527171957787332380034483729955195532817),
  (24132, 3910545051625080046204433321122702717433361),
  (25156, 4258994190175448414613959874123718495909457),
  (24899, 5652448115100863087992010481777040839194327),
  (24898, 5303998971373822143404822974295491321312983),
  (24897, 5303998971373822143404822967469245611750866),
  (19812, 5652022431700231443967883041160363883959759),
  (19844, 5652022451186812955376162642507287854126543),
  (19876, 5652015868729396989690848203366278997284303),
  (19908, 5658925358677151264845016592061554565662290),
  (19940, 5619527192726983431769054341788235314538199),
  (25188, 4258994190175448004830165876530615224706513),
  (24867, 5652448115100863087689779026873383562557143),
  (24866, 5303998971373822143400100603313901165458898),
  (24865, 5303998971373822143400100603207390528386514),
  (20868, 5652022451191883557776565968526763463873999),
  (20900, 5652015889498584755094648607472526153332177),
  (20932, 5658925358677152502752073139557099706852941),
  (20964, 5619611865803862101061052727327310161417943),
  (25220, 4258994190175448005132391261972120378090961)]

theorem tbl27_10_ok : tblOK 27 tbl27_10 = true := by decide +kernel

def tbl27_11 : List (Nat × Nat) := [
  (24835, 5652448115100861849748476301732329962190289),
  (24834, 5303998971373820905460061335948048531215067),
  (24833, 5303998971373820905460061335841514138728147),
  (21860, 5652022431700232971434817054043369575617999),
  (21892, 5652022451191884795414373344711658384725455),
  (21924, 5652015889503654119555522239587327252997585),
  (21956, 5659010429268882737367938976189612368143821),
  (21988, 5619611865803863338999230904704987310925265),
  (24803, 5652448115029072609256144924909043842659793),
  (24802, 5303998971373820905565304477798296384714451),
  (24801, 5303998976555815390964234770511715463149265),
  (22916, 5652022762070421494090726849603910725342671),
  (22948, 5652015910252796495798210964894141880276431),
  (22980, 5659009100040886952452066072382552087799245),
  (23012, 5619696936395593554254051333848925779600849),
  (24771, 5652447824925582536043901778000335914673875),
  (24770, 5303998685472975132491358181837842257032915),
  (24769, 5303998976555736162801351534807751786870226),
  (23940, 5652022762070421436062287962393433024042511),
  (23972, 5652015910252558811312524651013747478738449),
  (24004, 5657035075412291418868029190914848952955483),
  (24036, 5619696936395564813342180309718837475160667),
  (24738, 5303998685472975132381467613313604528117459),
  (24737, 5303998685472975132381467613313578775705299),
  (24996, 4291660282599418419541785575918438398146001),
  (25028, 4252348133282764915923433577656705044771351),
  (25060, 4258226187234046772611874377668922423136987),
  (18593, 5303743470695281041656358928728706750682640),
  (19617, 5303743470695282279596398214108981633029584),
  (20641, 5303828541287012514211681832400944397882832)]

theorem tbl27_11_ok : tblOK 27 tbl27_11 = true := by decide +kernel

def tbl27_12 : List (Nat × Nat) := [
  (21665, 5303828541286986575881807866034210136987088),
  (22689, 5303913611954379416463293809287872503158224),
  (23713, 5303913611954403124055855697140209653978640),
  (27809, 5304094720867312479443703376490916595446552),
  (18594, 5303743470695281041656386891829249560393232),
  (19618, 5303743470695282279596426177205126413006288),
  (20642, 5303828541287012514213464503777290357872343),
  (21666, 5303828541286986575881734079057915298780624),
  (22690, 5303913611954379416463220022311577664951760),
  (23714, 5303913611954403124057638368516555613968088),
  (26786, 5304094700096704988113477808106447556887747),
  (17797, 2849466099368712585957766090738831402554962),
  (17829, 2853452893931266675990865258303761080940246),
  (17861, 2858898740939361694858328750136804526372239),
  (17893, 2864429659050047820293901067091289083553296),
  (17925, 8135643818519332483175629620376569220253203),
  (24101, 3909777042137290604386122996328464299701647),
  (23908, 5652022767323953923506327536726770969327121),
  (23907, 5652022767323953923508106350483228008171224),
  (23906, 5303573623597164218791599899337305692648977),
  (23905, 5303573623597164218791599899230336663238161),
  (18821, 6000471594913852313847734367187519593579919),
  (18853, 6000465012449770450537224820849925410108815),
  (18885, 6007281146833982589301834857007916497323539),
  (18917, 6011437790204012229733548211740314027509267),
  (18949, 6049041691702963787049908033166085454644755),
  (24133, 3910630115742039709877609716998995656390160),
  (23876, 5652363049690871147824272489733141549659665),
  (23875, 5652363049690901112959272519606192472901336),
  (23874, 5303913905964164795022132921977759750473432)]

theorem tbl27_12_ok : tblOK 27 tbl27_12 = true := by decide +kernel

def tbl27_13 : List (Nat × Nat) := [
  (23873, 5303573412665496806708697864219185547908624),
  (19845, 6000471594913853961305471354244998243878287),
  (19877, 6000465012456517204439856912686148951016847),
  (19909, 6007366658192338641601890527225891094107404),
  (19941, 6011437790210760030492697160819778471675474),
  (19973, 6055865759632595319333634727735972173010516),
  (23844, 5652363049690874861667559456429379349718545),
  (23843, 5652363049690874861669338394317467195328216),
  (23842, 5303913905964164385412412867896298678830808),
  (23841, 5303913905964164385412412431829395762390545),
  (20869, 6000471594918924563705874680264473853625743),
  (20901, 6000465033225704969843656163975602490938768),
  (20933, 6007366658192338641527087791619574915225171),
  (20965, 6011437810979947795570059859036706463921749),
  (20997, 6055866110461947704178391074039520041985621),
  (23812, 5652363049690874861667559456430545443862033),
  (23811, 5652363049690874861669338270187002482706136),
  (23810, 5303913905964085157250340907461867815646737),
  (23809, 5303913905964085157250340907354898786235921),
  (21861, 6000471994452259486489101100407689264571920),
  (21893, 6000471594918925801343682056274380851840399),
  (21925, 6000465033230774334304529796092043305526672),
  (21957, 6007451728784068876142925010642688413353491),
  (21989, 6011437810985018397970972776642666522584596),
  (22021, 6061310628332682719593805067648620296234644),
  (23779, 5652363049690874861971569725090659776382680),
  (23778, 5303913905964085157255063273944737460860433),
  (23777, 5303913905964085157255063273837768431449617),
  (22917, 3866492025072985818473924149636923539400144),
  (22949, 3900004478720640276786731812977231073445327)]

theorem tbl27_13_ok : tblOK 27 tbl27_13 = true := by decide +kernel

def tbl27_14 : List (Nat × Nat) := [
  (22981, 3904246213446463905974303820239219501367898),
  (23013, 3909777049662557382913428922654288047601299),
  (23045, 3909777049662300937729738909425278294500817),
  (23747, 5652362755682709405978169561623742897042963),
  (23746, 5303913611955668419400463836883466031314451),
  (23745, 5303913905964005928185485691155893861594642),
  (23941, 3866461240532311722315080814551119333483853),
  (23973, 3900004478718824238663782376452996358538639),
  (24005, 3904245731464296982454647095830936438501910),
  (24037, 3909777048689001721938148742368038426359315),
  (24069, 3909777048688745276753805477511587867768337),
  (6305, 6050154255247520523551911266536232487560720),
  (18625, 5303743806323990910290918765428180396099091),
  (19649, 5303743408392790579579383012084729296786896),
  (20673, 5303828499753708248333973721762960576943568),
  (21697, 5303828499753682310004099755396226316047824),
  (22721, 5303913900360579382503345538477798033827280),
  (27841, 5304094344728848149457269460115353941087896),
  (18626, 5303743470782350393515060179966461660214803),
  (19650, 5303743470787420995311510583232729136793300),
  (20674, 5303828541379151094527685818996629424617175),
  (21698, 5303828541384220458988530251857146963396247),
  (22722, 5303913611955905616047828269677605548524183),
  (26818, 5304094700096784254961984885738004585199186),
  (18627, 5652192614509391380092765904438657405007379),
  (19651, 5652192614514461981889216307691942268655316),
  (20675, 5652277685106192081105464177514822528710359),
  (21699, 5652277685111261445564478996269147831248337),
  (22723, 5652362755682946603847899395558849896846799),
  (25795, 5652447824925582528448779647950059305768399)]

theorem tbl27_14_ok : tblOK 27 tbl27_14 = true := by decide +kernel

def tbl27_15 : List (Nat × Nat) := [
  (17862, 2860356485143070232281558938911577651844822),
  (17894, 2864429659050127055446638491512729091229400),
  (17926, 8135645147747314830616479309749190182913555),
  (22885, 6000471912024546857248712497486062185686480),
  (22884, 5652022761746078625801278283604264598705615),
  (22883, 5652022761746078625499268171615093310166479),
  (22882, 5303573618008869013302508579865607260411344),
  (22881, 5303573618008869013302582366841902098617808),
  (18886, 6007281167603170029532922757887648252904979),
  (18918, 6011437790204091464896176255639756164908563),
  (18950, 6049126762254633222687318253002416081159699),
  (22853, 6000812194391467795376885672067529496405456),
  (22852, 5652363050664426808799834807018740091790801),
  (22851, 5652363050664425570859796674564367846024657),
  (22850, 5303913906937719969016511816171190217156049),
  (22849, 5303573412664128909023305771494521277322704),
  (19910, 6007366658192417869764404828155227031819860),
  (19942, 6011437790210760049944794496546907551544916),
  (19974, 6055865780401782751084913825302836924757588),
  (22820, 5652363044102858359462913606384281144858063),
  (22819, 5652363044102858359160903512128033389090255),
  (22818, 5303913900375789945359504152743361737463248),
  (22817, 5303913900375789945359504170757760246945232),
  (20934, 6007366658192417869689602055957098665956947),
  (20966, 6011437810979947795576470068508581317424725),
  (20998, 6055866110786466257836088340323049284392527),
  (22788, 5652363044102858359462915823281197717984719),
  (22787, 5652363044102858359160905711292026429445583),
  (22786, 5303913900375789945368948885427626051179984),
  (22785, 5303913900375789945368948903442024560661968)]

theorem tbl27_15_ok : tblOK 27 tbl27_15 = true := by decide +kernel

def tbl27_16 : List (Nat × Nat) := [
  (21862, 6000471533986440868692312704222367673025935),
  (21894, 6000471532611363498921101952697723580384655),
  (21958, 6005569268951734083019879137950447203591696),
  (21990, 6011437810872676655921904259998354575537682),
  (22022, 5940838482474625381562588513484944349668879),
  (22755, 5652363044112999563962731546222525078377935),
  (22754, 5303913900375789951765971954473039028622800),
  (22753, 5303913900375789951766045741449333866829264),
  (22918, 3850131681800852334436546022324590099650194),
  (22950, 3900004478703850116051868165255009145521615),
  (22982, 3903990581998425178924387673349590874654159),
  (23014, 3909777042548661932248116138502746726823571),
  (23046, 3909777042461836585249936727716653049648591),
  (7329, 6365936250129958519832233993581669391349264),
  (19681, 5303743408387719977178470094478742483965392),
  (20705, 5303828499748637645933060804156973764122064),
  (21729, 5303828499748611707603186837790239503226320),
  (27873, 5304094344728768921294755195777760397137560),
  (7362, 6365936250217267066772657709811580283995667),
  (19682, 5303743408387719977178470530197462066509264),
  (20706, 5303828499748637645934843475533319724111575),
  (21730, 5303828499748611707603113050813944665019856),
  (26850, 5304094365499234717054620599779921833800899),
  (19683, 5652192552114760963874333251517960356931287),
  (20707, 5652277643475678632629435822315505556952791),
  (21731, 5652277643475679870148362184385451803612623),
  (25827, 5652448115029072609136968164868823752185295),
  (18951, 3214242563680230839457451487115584734049809),
  (18983, 3214242169425840798323402266519043396417040),
  (21829, 6000471994447188884092910549284572113741328)]

theorem tbl27_16_ok : tblOK 27 tbl27_16 = true := by decide +kernel

def tbl27_17 : List (Nat × Nat) := [
  (21828, 5652022431700489166305487001616874136475087),
  (21827, 5652022431700489166300764653429877977454031),
  (21826, 5303573287973421003755515519858370838861264),
  (21825, 5303573287973421003755589306834665677067728),
  (19975, 6366713722584060036852751831087486927193679),
  (20007, 6321784925295307792239239449395855803373140),
  (21796, 5652277643475679870152565843996164447868367),
  (21795, 5652277643475679870148064838160704340563407),
  (21794, 5303828499748611296895739823753577533871568),
  (21793, 5303828499748611296895739841767976043353552),
  (20999, 3562776783262760091830427632420355942147797),
  (21031, 3562776803078851260346452824276467956954709),
  (21764, 5652277643475679870152568060893081020995023),
  (21763, 5652277643475679870148067037324697380918735),
  (21762, 5303828499748611297500202733279417144514000),
  (21761, 5303828499748611297500202751293815653995984),
  (21863, 3589487223210099040359140915094154187204244),
  (21895, 3544643186897580950745683430980643938199188),
  (22023, 3560987286971322308318327690761662318056911),
  (22055, 3560987286971322327661140804595729113351567),
  (8385, 6365936250215510251748799214487942088963600),
  (8417, 6398603398974562767421183045966511119078928),
  (19713, 5303573371040055473841465142010029605197264),
  (20737, 5303828499748637645933208341799291444860368),
  (27905, 5304094365499314297657596821509334819714710),
  (8386, 6365936250215510251748827153425754844116496),
  (8418, 6398603398974562767421183482248232266700304),
  (19714, 5303743827093258002447100347175612550506196),
  (20738, 5303828499748637645933208777518079746618832),
  (26882, 5304094365499234775394441702693093979783641)]

theorem tbl27_17_ok : tblOK 27 tbl27_17 = true := by decide +kernel

def tbl27_18 : List (Nat × Nat) := [
  (19715, 5652192970820073529203941113317575688738516),
  (20739, 5652277643475678632629435822315507687134935),
  (25859, 5652448115100861849748475847357252704745105),
  (19716, 5652192970820043584346698219626828040840657),
  (20740, 5652277643475678632516616707017218720569047),
  (24836, 5652448115100861849144012973685658257479377),
  (20805, 6000471973678001449953600489255849807689296),
  (20804, 5652022431700487928667679625994929135490511),
  (20803, 5652022431700487928781838291359931730794199),
  (20802, 5303573287973446942087245944577745897952983),
  (20801, 5303573287973446942085463273201399937963472),
  (20772, 5652277643475678632516616833116365396227538),
  (20771, 5652277643475678632629443892660696116213202),
  (20770, 5303828499748637645933206471675070533187024),
  (20769, 5303828499748637645933206036237757207877072),
  (9409, 6714385290103203699853357510722846307731026),
  (9441, 6719829807881798979348693792541990934132308),
  (27937, 5304094365499314293359587350932559287658000),
  (9410, 6714385290005993361533030928010196890240594),
  (9442, 6719829807881798979348693792646924596524628),
  (9474, 6719830226562233940848092977599772934563545),
  (26914, 5304094365499234775394439396850084766089753),
  (9475, 6719915294593298912542363742931723924362836),
  (25891, 5652448115100863087687924908984969095357905),
  (24868, 5652448115100863087083609573236937346328017),
  (10465, 6719829828650986413487989409076909385270864),
  (10497, 6719829828650986413487989391062510875788880),
  (10529, 6648469165812567107821087788983188433225296),
  (27969, 5304094363875442815304446340321559155087000),
  (10466, 6719829828650986413487989409078555062388304)]

theorem tbl27_18_ok : tblOK 27 tbl27_18 = true := by decide +kernel

def tbl27_19 : List (Nat × Nat) := [
  (10498, 6719829828650986413487989391064156552906320),
  (10530, 6648442355079150615608743866944026709939796),
  (26946, 5304094364525679056079340419430453772072131),
  (10499, 6719914899242716648103869409776608891483732),
  (10531, 6648442355079150618933362234810342191220303),
  (25923, 5652448115100863087990154130102936335361489),
  (24900, 5652448115100863087990227917186199129499089),
  (23877, 6000812186856316200747220601897119071929743),
  (11489, 7068278972378027400074485007082641987286608),
  (11521, 7068278972378027400074484989068243477804624),
  (11553, 7073723490248762024047113222370050150569424),
  (28001, 5304094363875457613141886838977245777311248),
  (11490, 7068278972378027400074485007084287664404048),
  (11522, 7068278972378027400074484989069889154922064),
  (11554, 7073723490248762024048905096276021763749328),
  (11586, 7073723889133772047280075326881914709962953),
  (26978, 5304094364525679056079339987955365465359001),
  (11523, 7068364042969757634690365007786739523237459),
  (11555, 7073808560840492708134218324993448617293266),
  (11587, 7073808956206286702404193334011974996476507),
  (25955, 5652448115100845603007961713227503038436815),
  (11588, 7073808956083397401132145668861861423330769),
  (24932, 5652448115100845603008035936762596994913743),
  (23909, 6000471904499536523905096584389248190887311),
  (17927, 8135645147747314830616479309186240246269459),
  (12545, 7029730117983900091271819681313517312730445),
  (12577, 7029730427818234270087444622192285103482189),
  (12609, 7073723511012482716144602893783816815318480),
  (12641, 7002507528630232403139914464366752369534285),
  (28033, 5303584085766188587331069999318198354716307)]

theorem tbl27_19_ok : tblOK 27 tbl27_19 = true := by decide +kernel

def tbl27_20 : List (Nat × Nat) := [
  (12546, 7029730111520179626460944678052781649389141),
  (12578, 7029730008242537554948986570599805936821845),
  (12610, 7030939836867020686647347874039938407478997),
  (12642, 7002507528630232403252666616162797498983757),
  (27010, 5303584086085636538579139003485204802270803),
  (12547, 7029730111520179626461534967692410851251791),
  (12579, 7029730008242537554948986316381330696627533),
  (12611, 7030939857635660951289294250084813136742101),
  (12643, 7002507528632066162627342111615746855515730),
  (25987, 5652022762070421436057638946609534041920975),
  (12612, 7030939857513787801666053614663091484431823),
  (12644, 7002507528630153603914446393767772518442581),
  (24964, 5652022762070421436062287962393433024042447),
  (16870, 2864429632065112886147416350991239757768145),
  (16838, 2860271414551339997361678932959783192958415),
  (16869, 2864429639254416049807452522099434645431761),
  (16837, 2858898720287599294644016398743393022064273),
  (16805, 2853452873163911603759033670337526994900431),
  (16773, 2849381507853013193799848727353494768002513),
  (13569, 7383631977163970605597520533177430515966550),
  (13601, 7383631977163970624940769451253033700226446),
  (13633, 7384493215995105253928574088652648515966416),
  (13665, 7384475727026312987210082083835092700558734),
  (28065, 5303583921178387513599560133866612744820376),
  (13570, 7383631977169305121033521738289758442714774),
  (13602, 7383631977169067436540066545773442417358222),
  (13634, 7384493215995105253928574070638250006484432),
  (13666, 7384475727026312987210082083553617723848078),
  (13698, 7427632005441898195761421914877838477846163),
  (27042, 5303583941948853309359425537868774181483715)]

theorem tbl27_20_ok : tblOK 27 tbl27_20 = true := by decide +kernel

def tbl27_21 : List (Nat × Nat) := [
  (13571, 7383631977169305121033521483840872300213646),
  (13603, 7383631977169067436540066527759043907876238),
  (13635, 7384493236764292784781950153350027160393167),
  (13667, 7384475727138674921615424574570417983399567),
  (13699, 7427702638563109709246335198739503094764247),
  (13636, 7384493236764292784781950171078552646653391),
  (13668, 7384475727138674921615498361265169125418639),
  (13700, 7427702638563108490653822158539742992770514),
  (13701, 7427787709154371174110852536920796492576403),
  (15814, 7781683569912482869031096743118277098157586),
  (15813, 7781684024907300864267208862993339195667986),
  (15781, 2505003729436870617172538019133023794566608),
  (15749, 2500932364126228652685763511160208420337299),
  (15812, 7781610751213953992584222645118305370187213),
  (15780, 2505003729436870617181982751817288108283344),
  (15748, 2500931947464768598988052440692075132712597),
  (15716, 2495487721558853316358366020248867605149333),
  (15684, 2490041999110735956408841625294708832540112),
  (15811, 7781610750889356210763281654841980735792589),
  (15779, 2505003729436870616879751315209504300799440),
  (15747, 2500931947464768598988051287774969646118549),
  (15715, 2495487721558853316358364867331762118555285),
  (15683, 2490041561077006440332246488920238626248144),
  (15651, 2484597335850597454172294275741573160965584),
  (14625, 2484512264929198809253266430647636524074383),
  (14657, 2489956490372670915784276693503235362759947),
  (14689, 2495402650642497714388345026655090473764239),
  (14721, 2500846876760675383021815945922253196686733),
  (14753, 2506271560381698181606659532790092968560015),
  (14626, 2484512264929198809253266430643238477563279)]

theorem tbl27_21_ok : tblOK 27 tbl27_21 = true := by decide +kernel

def tbl27_22 : List (Nat × Nat) := [
  (14658, 2489956490372670915784276693498837316248843),
  (14690, 2495402650642497714388343873733585866917263),
  (14722, 2500846876760675383021815927907854687204749),
  (14754, 2506272889722374866023784862288013298607503),
  (14627, 2484512264929198815991930815525120280954255),
  (14659, 2489956490485276186978038511692160673842575),
  (14691, 2495402650642525299921574082825001729095318),
  (14723, 2500846876873038345029388380554823306409622),
  (14755, 2506272889722374866023800948288195249665686),
  (14660, 2489956928195357752810684654453183655798417),
  (14692, 2495402650642525299921574100835001118324374),
  (14724, 2500846876873038345029388398564822695638678),
  (14756, 2506272889722374866023800966298194638894742),
  (14725, 2500847293225191658665041424927503908955795),
  (14757, 2506272889722374866022754222784053712061839)]

theorem tbl27_22_ok : tblOK 27 tbl27_22 = true := by decide +kernel

def tbl27 : List (Nat × Nat) := tbl27_0 ++ tbl27_1 ++ tbl27_2 ++ tbl27_3 ++ tbl27_4 ++ tbl27_5 ++ tbl27_6 ++ tbl27_7 ++ tbl27_8 ++ tbl27_9 ++ tbl27_10 ++ tbl27_11 ++ tbl27_12 ++ tbl27_13 ++ tbl27_14 ++ tbl27_15 ++ tbl27_16 ++ tbl27_17 ++ tbl27_18 ++ tbl27_19 ++ tbl27_20 ++ tbl27_21 ++ tbl27_22

def mask27 : Nat := 100541797352891707740738586265314203346524301073972334766427570985077998457009679655424264833717697150889645604524260979239130870349847513922192700434288987015434295972722103466344090223349241036933377557194557061266188426502752483858716354493692541697980568592645368091079170653478949189928890978292244471262321855570254843262931529325087399483004272321030930944184268036882745742982909684965867061028047871250404006250504785202641931574923814692894959786944828764886839676491411879668551053599246471868367075745580216569733008456554992236284484159479519709780274689942505863236321295637530800227269207920189601917871335361673035017116184489914136378549291255279765963597229899163991775668157082904186325389811056241219751665327496788545622744128939637070414146495910902792254046080407757388953034494886934312916081311791865163844543233281633958168271874353584897654422651200550533379240655278709511375182974701544995630719576516994422343509599880127286555982769705081565367538524898885470391252236020537265040284491810626931422470636620793119164439934405558881703935916071000050857178319884934682730506273421394425564066787706109005801455616845676946112379569319341890114801836911388725826688989302215657568214626298002968645112099967138436977617678380415549108535263506863134273405458084888469359842344109120866815682267913303973861284430891002743310749653827846115154414207946477159533013251668217873377397393106024334081090283539910238305463902546069747210637172664335082055618262992609964599378637513859170645221650148617632502713403707160058154911279927763869913783102719331570246121094140418293673762971559866624563774083603280618125874821067970159561556996244692857575543233555590813660223739328501627259704147553635451938626974894010153854099000088034166160676293563790073349210635886859741306222437311367639557639571956355605259795932158618515043475506766751716965342137920636024685894601245565767208465789769477467120265597672156697691698241495677489554145881250526487245813020309162114703058481960759369404358959105475628670717628265034026354350379452314675072642031100915791699048053125281426919244688848714968549918679843915681543128720317077596848199204607648914643649594241649083429703136772810458994380523972298310337034372282861180287039307247484724776779439514509262242392596986892237670992090955978589549300490984932289956487681486369776871609962456051385259261874303269657823543020195261571611860582933049162994511291598872379840134214420115503948678169783185917405323973091468601610048785039039468256643517738819400205897046769556509052258816661615660900941790706811712655533320523459888806010433540997355973592752018401538053505576768615743146758994568346128781896556720555573843394245232492499547840341009864931292397798260090782799668264020513178376053209386430651793616510143782102596775809818202780946942427685755906602513276392936378699091974178678661857990821517342892289292048106808276025642252172570035749950269862750513075378208422143057563517863544598464123764242374114945418963327003945366892357590888998272713065548446898052136819294789487925549015232314813081298033091194018859676530579929825319873353019802113528271863810214771114889914364985130501910780222520008798662627183972932559182779446381790492406859784764282469799737955576027757586072391966804785396898999651615817582200858887937968516682170009468434262761639281810045599709922898399016964006004861320130784829720298428043877492991907210181261029176139180172107145746522115509119452553744223843112854937948665488653669276990069541577700282649176331308549934336043604008955073365264506824660838268833025922565675105686256830104920699729054222484892727579746958685070640544230586990537398689282456274837328621564628841730149681629661457352894145618406414084500002857849589164433071690928288221568550136549136747652075036692728005789251024003087925354927704751161018420629890054701392668527304812327340235695357380220198305941075851522631933485007631675934330870676225310728703939195967545634116438273452967061316235474392410336434199877458281020860019491266057754473345272134421601204135678689207394012842477345143775667329110751161659031626811606114053367004459253171393907053250442958905889116535047499854564030438903630702166665062282907102437638719108994931295485209497032574474207633267761193124704477293532516365189185421596705165603088058067019232740499306678542471873005485650787993740034641020286250688676271887731394388822115789441441059431053898840766602815490141674592820577398164418105259945696183178816103483527459009145667197972264355966981916950680710661092755857640407335000333054396901295267661298442455480376031196452878957137814691669428691106282805489256610873535635534270406393051493973201597966130751566452518924637480117121326124732693663644626445441881692991360969590898138732120043198059470056429129073208899472879269066662995253798419677985512016112882464695394624568373863249874528151711623466317477947596494718164786108476949981635611888907289335069898517076979335599709036498661684100388864092964965009382235521763795520688133735034797932710479588955170313033989485986796626650588421389821177865257433026552177299941095006167491531602278210409981437893042400831768741370350720068564763781763421163042723408412447186408057433644233752223654540471116303467486857820361143742537403658842404327954913531342376058747055741654772999330531817586991320064127172215628199853115878910616223085840535970773251286055465525592999002724922730601218697916977378711957475610488736585914796305567294771150012687474039463139478045793762102707680712261362905136247612044673372409931063951998674772719752799442116544772998022597810468814460827667241070615461864531800311375986721009128741101284752183711218520594847036839635054055539278007561305106165555705901430320983733646219088600377448034875405627020148422925809780477139222127728511747214740361386580738937947031378947952187609151723872237432173107066643593746362825513228933629185671546329438883767921726960741485328815855547757254763584829924403057788937097679295043908708017398828336839833358350509997299821581251292795176453110065943953844669378446467269207837304481482536864035190046474867373504621089079617438763503883215874512402273883786243429783567304590167930592730830737103868445154330464044571688419321490537078132239994306866301263587878148519536197362833446512386714164523119721810898643278528831284656842591482886993412461273191724479850093284583919581748708671190270448238897748449705206892177428028462299429317374482422353393473453399096826277499926315465555305159387933324682246907479172983899554727501849687757430891719124988176161875257270775750801020468088209258299625128999546460902497615054511882005929768522494184481600907354882260337539204441601669179169170414618093765197326106648651335675516113134183272057785090314710758248315359314952359632838130101469646152083113229024426405440976953655408286988905982016405323317950309286742622501616169372225132080337109939947578023948228407814948835384161094455980952862842214008739793941644854248703319072135083819019014533160370771431128790014767907526908225991522802000093576725567430800542521282316635894103291929075773600517910549000549140780969239559676365963651459919628643369955500971609846202923375185796557050786332519223816381206365713287096808553874167027338143716632788736898102060368625368855999954236474798182853501412195748848753164261521805930714701797120477374358216819770109715081690962098666844267600121285987330993869453125129663087152202466050086537728273369012844908176057225884589466564147058700944197559216586332777208137683831087998547943132846881485331461401545174228734629950879054510286889072128141051141995692216861910548226818519654126961964081233543361157300708719151711635884737022569671593888985997176861264759731682979339071264434329663180990375955508171025118819971318718919471415769782070180577181688026630132967983858517537862830720485888251612272632742713194791523821594178273267196022294065248389347060071844608089425074253267255443304902330707732671064829039056338475467895845683087475836156357580930149504317385972438524115591725763770101604760238377081779607095213502692866254792667483541941646836391517541362879455762213415951098202658152301898629891919871792923400642120267364117441445780852739192225303490875116414662653923729640427225994502731456057314864910027351816803312776655617202990692482842812845842290991464846126325344445328177199255086305227894935637761193680465884602269972295112922914859615255383095266946751629707623345413090480637927266633313745683660265017004199714094055424

theorem mask27_eq : maskL 0 (tbl27.map Prod.fst) = mask27 := by decide +kernel

theorem cov27_1 : coverX 27 mask27 1 = true := by decide +kernel
theorem cov27_2 : coverX 27 mask27 2 = true := by decide +kernel
theorem cov27_3 : coverX 27 mask27 3 = true := by decide +kernel
theorem cov27_4 : coverX 27 mask27 4 = true := by decide +kernel
theorem cov27_5 : coverX 27 mask27 5 = true := by decide +kernel
theorem cov27_6 : coverX 27 mask27 6 = true := by decide +kernel
theorem cov27_7 : coverX 27 mask27 7 = true := by decide +kernel
theorem cov27_8 : coverX 27 mask27 8 = true := by decide +kernel
theorem cov27_9 : coverX 27 mask27 9 = true := by decide +kernel
theorem cov27_10 : coverX 27 mask27 10 = true := by decide +kernel
theorem cov27_11 : coverX 27 mask27 11 = true := by decide +kernel
theorem cov27_12 : coverX 27 mask27 12 = true := by decide +kernel
theorem cov27_13 : coverX 27 mask27 13 = true := by decide +kernel
theorem cov27_14 : coverX 27 mask27 14 = true := by decide +kernel
theorem cov27_15 : coverX 27 mask27 15 = true := by decide +kernel
theorem cov27_16 : coverX 27 mask27 16 = true := by decide +kernel
theorem cov27_17 : coverX 27 mask27 17 = true := by decide +kernel
theorem cov27_18 : coverX 27 mask27 18 = true := by decide +kernel
theorem cov27_19 : coverX 27 mask27 19 = true := by decide +kernel
theorem cov27_20 : coverX 27 mask27 20 = true := by decide +kernel
theorem cov27_21 : coverX 27 mask27 21 = true := by decide +kernel
theorem cov27_22 : coverX 27 mask27 22 = true := by decide +kernel
theorem cov27_23 : coverX 27 mask27 23 = true := by decide +kernel
theorem cov27_24 : coverX 27 mask27 24 = true := by decide +kernel
theorem cov27_25 : coverX 27 mask27 25 = true := by decide +kernel
theorem cov27_26 : coverX 27 mask27 26 = true := by decide +kernel
theorem cov27_27 : coverX 27 mask27 27 = true := by decide +kernel

theorem cert27 : Cert 27 tbl27 := by
  refine ⟨by simp only [tbl27, tblOK_append, tbl27_0_ok, tbl27_1_ok, tbl27_2_ok, tbl27_3_ok, tbl27_4_ok, tbl27_5_ok, tbl27_6_ok, tbl27_7_ok, tbl27_8_ok, tbl27_9_ok, tbl27_10_ok, tbl27_11_ok, tbl27_12_ok, tbl27_13_ok, tbl27_14_ok, tbl27_15_ok, tbl27_16_ok, tbl27_17_ok, tbl27_18_ok, tbl27_19_ok, tbl27_20_ok, tbl27_21_ok, tbl27_22_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask27_eq]
  interval_cases x
  exacts [cov27_1, cov27_2, cov27_3, cov27_4, cov27_5, cov27_6, cov27_7, cov27_8, cov27_9, cov27_10, cov27_11, cov27_12, cov27_13, cov27_14, cov27_15, cov27_16, cov27_17, cov27_18, cov27_19, cov27_20, cov27_21, cov27_22, cov27_23, cov27_24, cov27_25, cov27_26, cov27_27]

/-! ### `N = 28`: 763 witness orderings -/

def tbl28_0 : List (Nat × Nat) := [
  (15649, 159014210655229683257345822799900148711114320),
  (15681, 159362765037984992951345194414433726952748364),
  (15713, 159711195466052682674333750204774502226002715),
  (15745, 160059749723311847769245146496551462302979536),
  (15777, 160408178847438615278790859188568411865941454),
  (23009, 359660603929316227282071182644422418600109585),
  (24033, 359660626360368251416093285333110903215564305),
  (25057, 359666070904242310832478663880626595166799444),
  (26081, 359666070904242310832478663880626595166783252),
  (27105, 294826528587764684847066133093228432278971986),
  (28129, 294826527320514662201287911102451570967119308),
  (29153, 297303967965577939533175448710629573427803665),
  (16705, 339428714563770207755775187596121953681614353),
  (16737, 339428714563745250821744058577254192763446801),
  (16769, 339428714563730037834629719880558157811754513),
  (16801, 339429563588356883592814278158085596308645393),
  (16833, 182969519447023695471300219508019470867478031),
  (24065, 250268777807742728600942689354025663168587281),
  (25089, 272569523384363920332640652589204799325554259),
  (26113, 272569523384363920332640652589204799324505875),
  (27137, 294870268582894543474176370684242451583026899),
  (28161, 294870268582894543474176370684242451583026835),
  (29185, 315080306936230713389001112022997840198915796),
  (17729, 339428714563770207755775187596121953681614352),
  (17761, 339428714563745250821744058577254192763446800),
  (17793, 339428714563730037834629719880558157811754512),
  (17825, 339429563588356883592814278158085596308645392),
  (17857, 359681810247465962399267826429615249422104082),
  (24097, 250268777807742728600942689354025663168587280),
  (25121, 272569523382674697977729195650622225411814994)]

theorem tbl28_0_ok : tblOK 28 tbl28_0 = true := by decide +kernel

def tbl28_1 : List (Nat × Nat) := [
  (26145, 272569523382674697977729195650622225411814930),
  (27169, 294870268581205321116285100672584237760460306),
  (28193, 294870268581205321116285100677901749895111252),
  (29217, 315080306936230481937120972950453486131459668),
  (18785, 339428690430366339917497241298885005083219408),
  (18817, 339428690684681383214663813332304884881495504),
  (18849, 339428015182478745210150834503916563500963280),
  (18881, 359681791829467651066953017796946937779402321),
  (25153, 272569523006598106684541314591966081630410192),
  (26177, 272569523006598107094070093739247386447386064),
  (27201, 294870268205119080429545144042337881369155024),
  (28225, 294870268205119080429545172005429644157290263),
  (29249, 315428756079957499149005792417459856739219025),
  (19809, 339428690430366339917497241298885005066442192),
  (19841, 339428690684681383214663813332304884864718288),
  (19873, 339428015182478745210150834503916563484186064),
  (19905, 359681791829467651066953017796946937779398225),
  (25185, 272569523278828764366125078091023171353396817),
  (26209, 272569523278828764769325600574233321613117073),
  (27233, 294870268477359387910861245059905457000105553),
  (28257, 294870268477359387910861245060010664052999761),
  (29281, 315428756079942287341198591132282500978394705),
  (20865, 339428690705450649874580843036915223099413968),
  (20897, 339428016511706820220844426598211976682345936),
  (20929, 359681793152149760570404599325559303156344337),
  (26241, 272569523278828764501510604950703663637149329),
  (27265, 294870268477359387642485418070406300278273745),
  (28289, 294870268477359387642485418070406300278273681),
  (29313, 315777205217467690964167834308137019776210643),
  (21857, 339428690430371410536856172256194343071716816)]

theorem tbl28_1_ok : tblOK 28 tbl28_1 = true := by decide +kernel

def tbl28_2 : List (Nat × Nat) := [
  (21889, 339428690705450649874580843036633748122703312),
  (21921, 339428016511706820220844426597930501705635280),
  (21953, 359681793152149760570404599325559234436867601),
  (26273, 272569523278828764501510604950703663620372113),
  (27297, 294870268477359387642485418070124825301563089),
  (28321, 294870268477359387642485418070124825301563025),
  (29345, 315777205222371255351081910941271407980988113),
  (22913, 339428690244963911701920138574997146742928848),
  (22945, 339428017840893068071049198041724595672520144),
  (22977, 359681794481375992059247542075736745808045585),
  (27329, 294871451258260243134213457795915505906558481),
  (28353, 294871451258260243134213457795917145225373201),
  (29377, 316126763955018268307955638585577277486024405),
  (23937, 339428690244963911701920138574997146742908624),
  (23969, 339428017840893068071049198047314426955896336),
  (24001, 359681794487176768557651919962685351347955217),
  (27361, 294871451263828311656732713573357492040189651),
  (28385, 294871451263828311656732713573357492040189587),
  (29409, 316126763955018267918926598009543372111888987),
  (24993, 339428018984826010357997705035265260044248720),
  (25025, 359681795816502521991617947825551318681986641),
  (28417, 294871451263828311656732713733060634352895571),
  (29441, 316475298174904852825095442955653957003593299),
  (26017, 339428018984826010357997778822241554882455056),
  (26049, 359681795816502521991617947825551318681986577),
  (28449, 294871451263828311656732713738957040334751379),
  (29473, 316475298174904852825095442955653980887729875),
  (27073, 297309412483448674548590887256195739841279697),
  (29505, 316823747318631893811681936413595271191938643),
  (28097, 297309412483448674548590887256195739841279633)]

theorem tbl28_2_ok : tblOK 28 tbl28_2 = true := by decide +kernel

def tbl28_3 : List (Nat × Nat) := [
  (29537, 316823747318631893811681936630037726768931084),
  (17473, 339434137606627251323856258540449645695149584),
  (18497, 339439582124498065567433749859261503952197072),
  (19521, 339439582124498065567433749859261503935419856),
  (20545, 339445026642332096980609417919168946637963991),
  (21569, 339445026642332096980609417901154548128482007),
  (22593, 339450471160202831989395955212663568506618519),
  (23617, 339450471160202831989395955212637184522519192),
  (24641, 339450471036885781599198515672959629298566604),
  (25665, 339450471036885781599198515672959628224824780),
  (26689, 339451764520176762616978696705505039761343129),
  (27713, 339451765853643863695950119168066220922283671),
  (28737, 340163285521870657597765157985993113765483097),
  (16706, 181668954759265957748818674772047574031488722),
  (16738, 182017385182871017370623263542035927632037586),
  (16770, 182365939439713205919473418552723337462486543),
  (16802, 182620985206448946844574292538659017960781198),
  (16834, 182969519447023695509985773800860233270892047),
  (16866, 183323498173731485662881063925248880435602961),
  (24066, 388272415736100406444017436143724482710038229),
  (25090, 272526477618491015622176662414393261691880913),
  (26114, 272526477618491015622176662414111786715170257),
  (27138, 294826784197399712646825977984160851544577487),
  (28162, 294826784197399712646827834461038615043282711),
  (28065, 339428017717575908484359347647748293979080140),
  (17730, 361729459411176819052345607170969911255967247),
  (17762, 361729459410203263430055953218288576784836111),
  (17794, 361729436880575187852607370345814911726986767),
  (17826, 361729034037449138940137622194650481930610191),
  (17858, 359638764528045544193697977824848987749688847)]

theorem tbl28_3_ok : tblOK 28 tbl28_3 = true := by decide +kernel

def tbl28_4 : List (Nat × Nat) := [
  (17890, 359638849598642352380982274373422386955236882),
  (24098, 250274882951927368724362283747562160072242706),
  (25122, 272575628171229093540698657562709598701131540),
  (26146, 272575628171229093540584204417094095340380888),
  (27170, 294876373369697579205505045421284273646543641),
  (28194, 294875694093976784233913455181786538680592015),
  (28033, 339428017717575908484359347647748293979080141),
  (18786, 361729435628814812414252844015734644955747919),
  (18818, 361729436880884495103559312546993600343688788),
  (18850, 361729015598686580575316955752991219319948879),
  (18882, 362171315194986262960025478442515478978057809),
  (18914, 359649740361868040301506062563929760613385813),
  (25154, 272575628171228776647396134437286582220605012),
  (26178, 272575628171228776647396134850769054868477716),
  (27202, 294876373369810000273347543999021489077433873),
  (28226, 294876373369810000273347543897941460015452756),
  (28001, 339460761857721582409175870493883453427185303),
  (19810, 361729435628814812414252844015734576236271183),
  (19842, 361729436880884494929479233397803932698658388),
  (19874, 361729015598686580575316955752991150600472143),
  (19906, 362171309879047835481337267007636705918408273),
  (19938, 359649740361868040301506061411008256006538837),
  (25186, 272575628171228776647358872014257688926340692),
  (26210, 272575628171228776647358872427740161574213396),
  (27234, 294876373369810000273347543999021489077429777),
  (28258, 294876373369810000273347543897941459881497178),
  (27969, 339460769873649305716353106759242148290823628),
  (20866, 361729436876280628189002051662563388519466513),
  (20898, 361729016921362016502439990909475394396395288),
  (20930, 362176754395935032087300603514486951908066965)]

theorem tbl28_4_ok : tblOK 28 tbl28_4 = true := by decide +kernel

def tbl28_5 : List (Nat × Nat) := [
  (20962, 359655159411447255318376227930099269204256273),
  (26242, 272575628171228776646754409517932846986860309),
  (27266, 294876373369743317607050845674530848184804881),
  (28290, 294876373369743317607050845573468337103770202),
  (27937, 339460769853853519200079702843127954057790924),
  (21858, 361729435628814910191860137010747075464336911),
  (21890, 361729436876280628188699820207659731225789969),
  (21922, 361729016921362016502435268542992524751181592),
  (21954, 362176754395934873630975575111855517109151377),
  (21986, 359655159411447255318376227930094871157745169),
  (26274, 272575628171228776646754409517932846986860308),
  (27298, 294876373369743317607050845674530779465328145),
  (28322, 294876373369743317607050845573468337103508058),
  (27905, 339460769853853677637061918257969074350392780),
  (22914, 361729436876680891302571288279394364949336663),
  (22946, 361729018250559986013917412421420549288039887),
  (22978, 362182198370160264226650045103510804616787473),
  (23010, 359660603929316227282071181491500913993262609),
  (27330, 294876373369748388190076331634780380995593745),
  (28354, 294876373369748388190076331533717938633773658),
  (27873, 339460684824800318576851831610061743727379916),
  (23938, 361729458412613508168857541221208708669567576),
  (23970, 361729018256481948039999076808930736137377295),
  (24002, 362160675510452514868835986659590745277412881),
  (24034, 359660626360368251416093284180189398608717329),
  (27362, 294876373369748389428016370819076292020343387),
  (28386, 294876373369748389435648394519295373402220310),
  (27841, 339460684762497826884055242073073957167199895),
  (24994, 361729019792991582072039452188791082868053783),
  (25026, 362160420842332809789531158839849421273912913)]

theorem tbl28_5_ok : tblOK 28 tbl28_5 = true := by decide +kernel

def tbl28_6 : List (Nat × Nat) := [
  (25058, 359666070899009769979240414333398018649605716),
  (28418, 294876373369754485898606285977904137150992983),
  (27809, 339460514600343328113386930786981946971461072),
  (26018, 361729019792991582072039452188791014148577047),
  (26050, 362160420842322668584729333004655039946016405),
  (26082, 359666070899009769979240414746880491297478420),
  (28450, 294876373369754565126735815606098135417950808),
  (27777, 339460514600343328112782174693420412896347596),
  (27074, 297315517375832604513156314860601694005044753),
  (27106, 294826613616818043919700331323324208023929497),
  (27745, 339460428744330402210807005065552515492808140),
  (28098, 297315517375832604513156314759539251643224666),
  (28130, 294826612287265529581126023694336656541287884),
  (17505, 339434137606627251323856284962224234547717648),
  (18529, 339439582124498065567433676072285209113990608),
  (19553, 339439582124498065567433676072285209097213392),
  (20577, 339445026642367299307353258349398607180928464),
  (21601, 339445026642367299307353258349117132204217808),
  (22625, 339450471160208008074776114985798824878740944),
  (23649, 339450471160208008074776114991388656162117136),
  (24673, 339455915471472830307037527941606691457008279),
  (25697, 339455915471472830307037529094528191769412247),
  (26721, 339460428744330402523063877860719958247159377),
  (28769, 340163285521870657597765157986012277635397201),
  (16707, 181668954754388121282049346637856843638838040),
  (16739, 182017385182871017370623263542035927615260370),
  (16771, 182365939439713234686811652345999845692106449),
  (16803, 182620985206448946844574292520644619451299214),
  (16835, 182969519447023695509985773782845834761410063),
  (16867, 183323498173731485662881063924967405458892305)]

theorem tbl28_6_ok : tblOK 28 tbl28_6 = true := by decide +kernel

def tbl28_7 : List (Nat × Nat) := [
  (24067, 388272414406831217024996057291328555821389396),
  (25091, 272526477618491015622176662414393261691618769),
  (26115, 272526477618491015622176662414111786714908113),
  (27139, 294826784197399712646825977966146453035095503),
  (27042, 361729019792991582071433132802105936062518735),
  (27041, 339428018984825931130137569638525155290932818),
  (17731, 361729459411178661350948331982574154536527375),
  (17763, 361729459410205105689973199376177276151211535),
  (17795, 361729436880575187852607370345533436750276111),
  (17827, 361729034037449138940137622194369006953899535),
  (17859, 362166125345199688188450066802646650922546706),
  (17891, 359638849598642352380982274355407988445754898),
  (24099, 250274882951929203248694660136033679110387218),
  (25123, 272575628171229093540698657562709872505280276),
  (26147, 272575628171229093540584204417089697293869784),
  (27171, 294876373369697579205504971634307978808337177),
  (27010, 361762889912658628525573692719536531600131795),
  (27009, 339428017717575908484359347629733895469860365),
  (18787, 361729435628814812414252871561406793611548239),
  (18819, 361729436875956030407181185611340435196069457),
  (18851, 361729015598686580575318743915899362723087953),
  (18883, 362171308549819839694324677272535742345758293),
  (18915, 359649740361868040282172094628170876067075668),
  (25155, 272575628171228776647396134437304105686124116),
  (26179, 272575628171228776647396134850769328672626452),
  (27203, 294876373369738247004649938395994544810046993),
  (26978, 361762889701316498784186396335486539963119313),
  (26977, 339460771202877301501268987661446543752888985),
  (19811, 361729435628814812414252871561402395565037135),
  (19843, 361729436875956030407181184458418930589222481)]

theorem tbl28_7_ok : tblOK 28 tbl28_7 = true := by decide +kernel

def tbl28_8 : List (Nat × Nat) := [
  (19875, 361729015598686580575318743915617887746377297),
  (19907, 362171308549819839694324676119614237738911317),
  (19939, 359649740361868040262829281514336809271776852),
  (25187, 272575628171228776647358872014275212391859796),
  (26211, 272575628171228776647358872427740435378362132),
  (27235, 294876373369738247004649938395994544810042897),
  (26946, 361762889701316498784186397488408044569966289),
  (26945, 339460771202877301501268987661446543752889049),
  (20867, 361729436876280628189002051662563388519204369),
  (20899, 361729016921362016502439990909475394396133144),
  (20931, 362176753066382517746629587052585230393255243),
  (20963, 359655159411447255325678126143141142326195992),
  (26243, 272575628171228776646754409517933120791009045),
  (27267, 294876373369743317607050845674249373208094225),
  (26914, 361762889701315299111557010605112524775695889),
  (26913, 339460771183406033538654010472115505540432537),
  (21859, 361729435628814910191861919267184390310053393),
  (21891, 361729436876280628188699820207659731225527825),
  (21923, 361729016921362016502435268542992524750919448),
  (21955, 362176753066382359290304558523910050815264406),
  (21987, 359655159411447255325673403776658272680982296),
  (26275, 272575628171228776646754409517933120791009044),
  (27299, 294876373369743317607050845674249304488617489),
  (26882, 361762889701315299111557010605138569457378833),
  (26881, 339460771183406191975636225886956625833034393),
  (22915, 361729436876680891302571288280515842179970513),
  (22947, 361729018250559986013917412403406150778557903),
  (22979, 362182197040896723606269346733812500568815122),
  (23011, 359660603929318069541988427649389613359638033),
  (27331, 294876373369748388190076331634498906018883089)]

theorem tbl28_8_ok : tblOK 28 tbl28_8 = true := by decide +kernel

def tbl28_9 : List (Nat × Nat) := [
  (26850, 361761686900215992163925616764419385810818511),
  (26849, 339460686092050341222630053600838605039232594),
  (23939, 361729458412613508168857545808446055277991439),
  (23971, 361729018256481948039999076790916337627895311),
  (24003, 362160674181188974248455288289892441229440530),
  (24035, 359660626360370085078772858383667358759753432),
  (27363, 294876373369748389428016370801061893510861403),
  (26818, 361761686900215992163925616764700860787529167),
  (26817, 339460686092050341222630053600838605039236690),
  (24995, 361729019792991582072039452188791082867791639),
  (25027, 362160419512780295448860142377965301680686677),
  (25059, 359666070899009769979240414333415542115124820),
  (26786, 361761686900215992183268429878534927582827983),
  (26785, 339460515929571312529324223998157875193594393),
  (26019, 361729019792991582072039452188791014148314903),
  (26051, 362160419512770154244058316542753318431204683),
  (26083, 359666070899009769979240414746880765101627156),
  (26754, 361761686900323193184677483410616300017361627),
  (26753, 339460515929246793975665797271374719055626585),
  (27075, 297315517375832604513156314860320219028334097),
  (27107, 294826613616823110808583357839693027433054873),
  (18561, 339439582124498065548090862958451142318691792),
  (19585, 339439582124498065548090862958451142301914576),
  (20609, 339445026642368879789266966320501658863650256),
  (21633, 339445026642368879789266965167580154256803280),
  (22657, 339450471160197866869974288433063491076994512),
  (23681, 339450471160197866869974288433063353638041104),
  (24705, 339455915492763279925643404979484586372064912),
  (25729, 339455915492763279925945636434388243665741328),
  (28801, 340511734665597698584351653587372284400150233)]

theorem tbl28_9_ok : tblOK 28 tbl28_9 = true := by decide +kernel

def tbl28_10 : List (Nat × Nat) := [
  (18562, 361740327323028690298395757446736679133058639),
  (19586, 361740327323028690298395757446736678059316815),
  (20610, 361745771840897901159470518037273543206573583),
  (21634, 361745771840897901159470516884352038599726607),
  (22658, 361751216358753814319088574630600261034120655),
  (23682, 361751216364011718298220304597791395459962383),
  (24706, 361756660795242254805159791672580234187413271),
  (25730, 361756660795242254805159791672580165467936535),
  (27778, 361761686900323193184677483410616300017361626),
  (17732, 181668954754388121282054067959217291168392720),
  (17764, 182017385189975393008004338824004953288017423),
  (17796, 182365939439713234686811653498916951178700496),
  (17828, 182620985213640176412080595022789589773133328),
  (17860, 182969519447135966704206526879608405918295568),
  (17892, 183323498180922713934749679194428821758625490),
  (17924, 522076885618789214007398610838590079711921743),
  (24100, 250225732424538743747615515726657056259515920),
  (25124, 272526477618491015133388712403200062378067407),
  (26148, 272526477618491015133388712403195664331556303),
  (25987, 361729458412613508188319535504705232738829777),
  (25986, 361729458412613508188319535504705232739091921),
  (25985, 339428690244963881740513595244806996456465936),
  (18788, 384030180827345435555788561135461501838100047),
  (18820, 384030182074486653548598088620004962569930319),
  (18852, 384029760797217203678167047797971446161589839),
  (18884, 384471465705685897393416822525796509306406483),
  (18916, 384732018573487068552064725025519329927579219),
  (18948, 387600854072158669386322362269906022750565967),
  (25156, 272581072689099511175542419440248592067016272),
  (26180, 272581072689099511175542419440248592067016208)]

theorem tbl28_10_ok : tblOK 28 tbl28_10 = true := by decide +kernel

def tbl28_11 : List (Nat × Nat) := [
  (25955, 361756681001951729733146186837437583367194065),
  (25954, 361756681001951729725840760971084604357285327),
  (25953, 339455914203780782666170001011731246987961872),
  (19812, 384030180827345435555788561135461433118623311),
  (19844, 384030182074486653548598088620004893850453583),
  (19876, 384029760797217203678167047797971377442113103),
  (19908, 384471465705685897393416822525796509306406482),
  (19940, 384732018573487068552064725025519329927579218),
  (19972, 387573631316651653722919309240383210855450196),
  (25188, 272581072689099511175542419440248592067012176),
  (26212, 272581072689099511175542419440248592067012112),
  (25923, 361756681001951733773706257057810450299787027),
  (25922, 361756681001951733305772344304905247955949007),
  (25921, 339455914205078619196316165125851090438415888),
  (20868, 384030182074811251330418520019539132211906063),
  (20900, 384029762126769718347037974739999766982239760),
  (20932, 384476910223556711634883855576707935163721229),
  (20964, 384732019903039582890650111435745619401061906),
  (20996, 387923965283878354846745276961623816514655887),
  (26244, 272581072689099511175844644807952844360590864),
  (25891, 361756681001946900432338868997846122510190359),
  (25890, 361756681001946900432338868997846122510452503),
  (25889, 339455914184309435456049696441708468864352919),
  (21860, 384030180827345533333395781496419142115329551),
  (21892, 384030182074811251330116288564635474918229519),
  (21924, 384029762126769717109097935454619492083115536),
  (21956, 384476910223556711634883855576681890482038285),
  (21988, 384732019903039582890650111435464144424351250),
  (22020, 387923965283878354846745276961623816514651791),
  (26276, 272581072689099511175844644807948446314079760)]

theorem tbl28_11_ok : tblOK 28 tbl28_11 = true := by decide +kernel

def tbl28_12 : List (Nat × Nat) := [
  (25859, 361756681001946900432338868997846122510194455),
  (25858, 361756681001946900432338868997846122510456599),
  (25857, 339455914184309669414902122599890950859325784),
  (22916, 384030182075211514444107007688066911736804816),
  (22948, 384029763456312327927357952042613139998320336),
  (22980, 384482354741427513467086835133365044711858968),
  (23012, 384732021232592089818842492134911954903709202),
  (23044, 388272414427605475158184301202699911749781071),
  (25827, 361756681001967183265396605473299774195746257),
  (25826, 361756681001967183265396605473299774196008401),
  (25825, 339455912834317556817590665213401537913382416),
  (23940, 384030203611144131310397912642586593081493007),
  (23972, 384029763455014332940886759399818109477791248),
  (24004, 384460580657628560760172797869910592387359512),
  (24036, 384732021232587019216441579217305968090887698),
  (24068, 388272414427605475158184301202699910676039247),
  (25795, 361756660795242282230840687238826620950718231),
  (25794, 361756660795242282230840687238826620950980375),
  (25793, 339455912834317556817590665213401537930159632),
  (24996, 268365999437841357345369167353163829477189263),
  (25028, 272255010588221029973998304173767867397162576),
  (25060, 272526455957835922468430425267846386683549136),
  (25092, 272526477618491015133388712403200046345033167),
  (25762, 361756660795242252322276518692339056490694095),
  (25761, 339455915492773548387422411021015658474071568),
  (26020, 268365999437846427947770080270769816290010639),
  (26052, 272255010588221029973998304173767867397162512),
  (26084, 272526455957835922468732656722750059994768912),
  (26116, 272526477618491015133388712403195648298522063),
  (18593, 339439582124498065548076843432955123059463632)]

theorem tbl28_12_ok : tblOK 28 tbl28_12 = true := by decide +kernel

def tbl28_13 : List (Nat × Nat) := [
  (19617, 339439582124498065548076843432955123042686416),
  (20641, 339445026642368879789269976617162384251885008),
  (21665, 339445026642368879789269976616880909275174352),
  (22689, 339450471160197866869974289150586851253097936),
  (23713, 339450471160197866869974289156176682536474128),
  (24737, 339455915492773548387422337234039363635865232),
  (28833, 340511734665597698584351653587373719708280537),
  (18594, 361740327323028690298395783026896066797668121),
  (19618, 361740327323028690298395783024675053309560601),
  (20642, 361745771840899504541973543082574200832071183),
  (21666, 361745771840899504541671311627670543538394639),
  (22690, 361751216358753814319088574630318786057409999),
  (23714, 361751216364011718298220304597509920483251727),
  (24738, 361756660795242252322276518692343454537205199),
  (27810, 361761686900215992183270286355131216121599767),
  (17797, 182365939446539758025261289332573331073611282),
  (17829, 182620985213640176412080447448837068816197136),
  (17861, 182969519447135966704206526879604007871784464),
  (17893, 183323498180922713934749679194428753039148754),
  (17925, 522076885618794284609799523756187270431721039),
  (24101, 250225732424540419801077972514219392366360082),
  (25125, 272526477618491015133388712403200062377805263),
  (24964, 384030203611144130841067303766441869907969487),
  (24963, 361729458412613508188319535504986707715540433),
  (24962, 361729458412613508188319535504986707715802577),
  (24961, 339428690244963881740513521457830701618259600),
  (18821, 384030182074486653548598088620004962569668175),
  (18853, 384029760797217203678167046645049941554742863),
  (18885, 384471465705690967995819376337151401529525843),
  (18917, 384732018573487068552064651238543035089372755)]

theorem tbl28_13_ok : tblOK 28 tbl28_13 = true := by decide +kernel

def tbl28_14 : List (Nat × Nat) := [
  (18949, 387600854072158669347636736042237889176745551),
  (25157, 272581072689099511175542419440248592050239056),
  (24932, 384057426200482352867074247788833706599318991),
  (24931, 361756681001951729733146186837719058343904721),
  (24930, 361756681001951729725840760971089002403796431),
  (24929, 339455914203780782666169999858809726363571664),
  (19845, 384030182074486653548598088620004893850191439),
  (19877, 384029760797217203678167046645049872835266127),
  (19909, 384471465705690967995819376337151401529525842),
  (19941, 384732018573487068552064651238543035089372754),
  (19973, 387573631337420841157058104398561530780345940),
  (25189, 272581072689099511175542419440248592050234960),
  (24900, 384057426200482356427965249463723940696360399),
  (24899, 361756681001951733773706258210731954906634003),
  (24898, 361756681001951733305772344304909646002460111),
  (24897, 339455914205078619196316163972929569814025680),
  (20869, 384030182074811251330418520019539132211643919),
  (20901, 384029762126769718347037827166047177322604048),
  (20933, 384476910223561782239397304595207895949325842),
  (20965, 384732019903039582890638951173987878415971858),
  (20997, 387923965283883425449146215452304698278237839),
  (24868, 384057426200467382369072761435001104133555991),
  (24867, 361756681001946900432338868997846191229667095),
  (24866, 361756681001946900432338868997846191229929239),
  (24865, 339455914184309435456049695288786968551948951),
  (21861, 384030207644944607135302500642395399927142168),
  (21893, 384030182074811251330116288564635474917967375),
  (21925, 384029762126769717109097787880666902423479824),
  (21957, 384476910223561782239397304594926420972615186),
  (21989, 384732019903039582890638951173987809696495122)]

theorem tbl28_14_ok : tblOK 28 tbl28_14 = true := by decide +kernel

def tbl28_15 : List (Nat × Nat) := [
  (22021, 387923965283883425449146215452304698278233743),
  (24836, 384057426200467382369072761435001104133560087),
  (24835, 361756681001946900432338868997846191229671191),
  (24834, 361756681001946900432338868997846191229933335),
  (24833, 339455914184309669414902048812914587297228240),
  (22917, 384030182075211514444107007688066910663062992),
  (22949, 384029763456312327927357804468660619041384144),
  (22981, 384482354741432584119909578041726776672630290),
  (23013, 384732021232592087342962413582165803614942738),
  (23045, 388272414427610545760585214120297102469580367),
  (24803, 361756681001967183265396605473581249172456913),
  (24802, 361756681001967183265396605473581249172719057),
  (24801, 339455912834317556817590591426425243075176080),
  (23941, 384030203611144131310397912642305118104782351),
  (23973, 384029763455014332940886611825865588520855056),
  (24005, 384460580657633631412995540778272324348130834),
  (24037, 384732021232587016740561500664559816802121234),
  (24069, 388272414427610545760585214120297101395838543),
  (24771, 361756660795242282230840687256841019460200215),
  (24770, 361756660795242282230840687256841019460462359),
  (24769, 339455912834317556817590591426425243091953296),
  (24997, 268366084508433068757940056143718275265913303),
  (25029, 272255010588221029973888422703079128959100496),
  (25061, 272526455957825781263628599450648811567388112),
  (25093, 272526477618491015133388712403200046328255951),
  (6305, 407419920014214376633975944587226943821039184),
  (19649, 339439604928415856944297288871884629765854672),
  (20673, 339445023984237406773096657536331419711772112),
  (21697, 339445023984237406773096657536049944735061456),
  (22721, 339450468502066393853800970069755886712985040)]

theorem tbl28_15_ok : tblOK 28 tbl28_15 = true := by decide +kernel

def tbl28_16 : List (Nat × Nat) := [
  (23745, 339450468502066393853800970075345717996361232),
  (28865, 340860269195344216565607482849273899450701260),
  (19650, 361740327328930710481783176345536750829028948),
  (20674, 361745771847125964050857017066052145644422675),
  (21698, 361745771847125962812916977780671870745298451),
  (22722, 361751216365311312861552120314398828515899089),
  (23746, 361751216364013317875080927671603797995370001),
  (27842, 361761686900215992163927473241297149326300951),
  (19651, 361740327328930710481783176345549876248299092),
  (20675, 361745771847125964050857017066333414462965267),
  (21699, 361745771847125962812916977780953139563841043),
  (22723, 361751216365311312861552194173401999785932497),
  (23747, 361751216364013317875081001530606969265403409),
  (26819, 361761686900215992163925616746686462278047183),
  (18886, 205369113863478425643433418801797527245014481),
  (18918, 205624244701166159496861853304981862071445271),
  (18950, 205624244728120768804523006540742812851619412),
  (18982, 205624244728120768709942934112995494644270676),
  (23909, 384030203615724158650292282150109561402242578),
  (23908, 384030203615722482596829825362547225295398416),
  (23907, 361729458417191859455294033320941365507204625),
  (23906, 361729458417191859455186246671461272873936401),
  (23905, 339428690430258935238480887373686928810251792),
  (19910, 406772184444616770858342280187035417362646609),
  (19942, 407032953619220330320989426165581123748742740),
  (19974, 407467984707678317719596703291099931233834580),
  (20006, 404594235212364416423202889465628907805955668),
  (23877, 384051981687207098711949213452659315708868114),
  (23876, 384051981687207098711949361026607507338769938),
  (23875, 361751236488676457078977318640319784446404113)]

theorem tbl28_16_ok : tblOK 28 tbl28_16 = true := by decide +kernel

def tbl28_17 : List (Nat × Nat) := [
  (23874, 361751236488676457078972596327875712283125265),
  (23873, 339428698405302074481667641012395760295941648),
  (20934, 406777657067720753199596114949792525846664851),
  (20966, 407032935242760414649169164224259462509479573),
  (20998, 407475228978462053240136489674805955844466325),
  (21030, 404605125584195266032124161800041358746306197),
  (23844, 384051981687205422639148668221921932037924368),
  (23843, 361751236488674799497612876180593149179930129),
  (23842, 361751236488674799497505089531113056546661905),
  (23841, 339450468501741847794970959044468640934860304),
  (21862, 406330952864244523094575824534778105906161299),
  (21958, 406777657067720753199596114955122413924894355),
  (21990, 407032935242760412173289085934454919933576854),
  (22022, 407475228978462053240136489674805955844466324),
  (22054, 404605125584195266032114717065136080944481942),
  (23812, 384051981687205422639148668223588791665632784),
  (23811, 361751236488674799497612876181982931877438993),
  (23810, 361751236488674799497505089532502839244170769),
  (23809, 339450468501741847833656585272137197490628304),
  (22918, 252376376627677364777810760609009019248248271),
  (22950, 249506359654029617350965224192684172283827923),
  (22982, 249954096578061304107467444143051688105555665),
  (23014, 250225706984263273948336401643323176747079120),
  (23046, 250225706984263273952548455220056317969118929),
  (23078, 250225706984263273913862828866296534486824466),
  (23779, 361751236488674799516955689295816998672737809),
  (23778, 361751236488674799516847902646336906039469585),
  (23777, 339450468501741875300142543348562561975784976),
  (23942, 252376376627677364776904066244298048440960527),
  (23974, 249506359654029617350965223039762667676980947)]

theorem tbl28_17_ok : tblOK 28 tbl28_17 = true := by decide +kernel

def tbl28_18 : List (Nat × Nat) := [
  (24006, 249954096578061304107467444143051688073049617),
  (24038, 250225706984263273954734612276694418274989585),
  (24070, 250225732424538610240714832610976165689898513),
  (24102, 250225732424538610202028837466441231295657490),
  (7329, 407419920008317449469304027966390316643202640),
  (19681, 339439604928415856924954475758050562970555856),
  (20705, 339445023983912888219438230809548263691195856),
  (21729, 339445023983912888219438230809266788714485200),
  (22753, 339450468501741875300142543342972730692408784),
  (28897, 340860269195344216623636288765784201674700369),
  (7362, 409864512520666111647507259224435454342710868),
  (19682, 361740350153576653859236566655778448119809617),
  (20706, 361745769182443512972141797274960080271382031),
  (21730, 361745769182443512971839565820056422977705487),
  (22754, 361751213700297822749256828822704665496720847),
  (27874, 361761686900215992163927473241297149309523735),
  (19683, 361740350153576653866533600363394061758219860),
  (20707, 361745769182443512972255891318631915039307281),
  (21731, 361745769182443512971953659863728257745630737),
  (22755, 361751213700297851453682752379520034498483663),
  (26851, 361761686900215992163925616746404987301336527),
  (18951, 205716970316888518585510137026096847680743193),
  (18983, 205716970192273163723925773291017779834603091),
  (22885, 384030208932636062561793259696062367806600722),
  (22884, 384030180827345534533556888445973184190940623),
  (22883, 361729435628814911392021096404644401332950479),
  (22882, 361729435628814882687595172847829032331187663),
  (22881, 339428690430258935238480887368097097526875600),
  (19975, 407467984707678317719596703290818456257123924),
  (20007, 404594235212349204616000150713373897320912468)]

theorem tbl28_18_ok : tblOK 28 tbl28_18 = true := by decide +kernel

def tbl28_19 : List (Nat × Nat) := [
  (22853, 384051987004119002623450190998612122113226258),
  (22852, 384051987004119002623450338572560313743128082),
  (22851, 361751241805588360990478579717986954217596433),
  (22850, 361751241805588360990473565577704735589308119),
  (22849, 339428698405302074481667641006805929012565456),
  (20999, 407475228978462053240136489674243005907822229),
  (21031, 404605125584195265967394198135867881813005971),
  (22820, 384051958898920615689117899251544224188970448),
  (22819, 361751213700389992547582179826255834126595537),
  (22818, 361751213700272470931089833894666880112465359),
  (22817, 339450468501741847794970959038878809651484112),
  (21863, 406429122832703388060832801021612718506493590),
  (22023, 407475228978462053240136489674243005907822228),
  (22055, 404605125584195265967394198141193441621165715),
  (22788, 384051958898920615689117899253765237677077968),
  (22787, 361751213700389992547582179828199770684503505),
  (22786, 361751213700272470975192303520899431261869519),
  (22785, 339450468501741847833656585266265468265371088),
  (22919, 252376376627672294175409847691403032435426767),
  (22951, 249506359654029617350965224192402697307117267),
  (23047, 250203931564678855622680849066526960637515215),
  (23079, 250203931564678855622680849066526960637511119),
  (8385, 430069134104023331994852307623344979590583760),
  (8417, 430069134104023331994852306470423474983736784),
  (20737, 339445023983912888220042544992481483995289040),
  (21761, 339445023983912888220042544992200009018578384),
  (28929, 341208547923999863287274302527288759094457808),
  (8386, 430074578849336187612973119878217527528080977),
  (8418, 430074578849336187612670888423313870234404433),
  (20738, 361745769182443512972141502127054918042633743)]

theorem tbl28_19_ok : tblOK 28 tbl28_19 = true := by decide +kernel

def tbl28_20 : List (Nat × Nat) := [
  (21762, 361745769182443512971839270672151260748957199),
  (27906, 361762889701315299111557039702016196445324817),
  (20739, 361745769182443512972255955889338531776599832),
  (21763, 361745769182443512971953724434434874482923288),
  (26883, 361762889701315299111557010605138500737902097),
  (20740, 384046514380974136113674206499868379899008792),
  (21764, 384046514380974136113371975044964722605332248),
  (25860, 384057426200467382369072761435001035414083351),
  (20040, 536678229452773237393556183413799466625484368),
  (21829, 384030207644944607135604732097299057220818712),
  (21828, 384030180827361931067124319745065189947541007),
  (21827, 361729435628831307925707417882571532871480849),
  (21826, 361729435628831307925593323838899698103555599),
  (21825, 339428690430300683173191988828110063840335312),
  (21064, 227908630884035365268370414990428131362932175),
  (21796, 384046514380974136113371975044964722605328152),
  (21795, 361745769182443512971953724434434874482919192),
  (21794, 361745769182443512971839268026256244178228751),
  (21793, 339445023983912888220033101412155774334997968),
  (21864, 224452401745226091719077490732833271392052880),
  (22088, 227908630884035365268068183535524474069255631),
  (9409, 430069134104023173538527280247591297109530064),
  (9441, 430069134104023094310364765983253703565579728),
  (20769, 339445023983912888220033101412437249311708624),
  (28961, 341208548197872585333183851391313260678301265),
  (9410, 430074557545017646265649860070003462318704207),
  (9442, 430074557545017646265649860070003462318442063),
  (9474, 432165257724059370558801940979306934202840857),
  (20770, 361745769182443512972141499481159901471905295),
  (27938, 361762889701315299111557039702016196345972241)]

theorem tbl28_20_ok : tblOK 28 tbl28_20 = true := by decide +kernel

def tbl28_21 : List (Nat × Nat) := [
  (9475, 432165257724059355838996419380808604508562137),
  (20771, 361745769182443512972255955889338531776595736),
  (26915, 361762889701315299111557010605108126729184785),
  (20772, 384046514380974136113674206499868379899004696),
  (25892, 384057426200467382369072761435001035414079255),
  (10465, 452369854232193834065401020891265295148717520),
  (10497, 452718303375920875051987664026917743461209552),
  (10529, 452718303375920875051987661721356209224226256),
  (28993, 341556997335397988956153094567167779476117203),
  (10466, 452375302737097918736209862429811284679968403),
  (10498, 452723747893791610092522150172795467071575697),
  (10530, 452723747893791610092522150177816939963963025),
  (27970, 361762889701316498791786169924907398805362455),
  (10499, 452723747893791610092522178020784461445187221),
  (10531, 452723747893791610092522178020784460371445397),
  (26947, 361762889701316498784186766422977394897663697),
  (25924, 384057426200482356427965249463719542649849295),
  (24901, 384057426200467144640105323824740063119525327),
  (11489, 452369854232193834065392158383659382316013008),
  (11521, 452718303375920875051978656251202250165786064),
  (11553, 452718303375920875051969209248703773657339344),
  (29025, 341556997335372635948666571139286965387560663),
  (11490, 452375302737097915970494615807571119372527386),
  (11522, 452723747893791610092522150172864058773034641),
  (11554, 452723747893791610092522150177816740180874897),
  (11586, 454814452273649364141238833858892891752351251),
  (28002, 361762889701316498791786169924907398788585239),
  (11523, 452723747893791610092522178020784461329319573),
  (11555, 452723747893791610092522178020784460255577749),
  (11587, 454814452066317034628975695904727301429249555)]

theorem tbl28_21_ok : tblOK 28 tbl28_21 = true := by decide +kernel

def tbl28_22 : List (Nat × Nat) := [
  (26979, 361762889701316498784186765270055890290816721),
  (11588, 454819896584187754492853444539675610149107216),
  (25956, 384057426200482352867074247788829308552807887),
  (24933, 384057426200467141060173740490919419520861647),
  (12545, 472204743181954703068645187999415852719465869),
  (12577, 472204743512305415025145096565511389898155664),
  (12609, 475367499047056637189539313355196344598336976),
  (12641, 475367499047056637170196500241362277803038160),
  (29057, 341905446479196483745100887534822040281835219),
  (12546, 472204743175171535873289496971930189421946511),
  (12578, 472204743071888901226169255503723340073117071),
  (12610, 472259628439604959438991606864521548802672147),
  (12642, 475372943564926034262875589204779518617785871),
  (28034, 361762889912658659711090018097856623370105436),
  (12547, 472204743175171535873289496971930120702469775),
  (12579, 472204743071888901226169255503723271353640335),
  (12611, 472259628439604959438991606864802817637729811),
  (12643, 475372943564926034270194883636523161288295953),
  (27011, 361762889707562902611644420565244716696539864),
  (12612, 472259629760708479579112636558188503346038287),
  (12644, 475378388082796769277988771743594769598711311),
  (25988, 384030203611144130841067303766437471861458383),
  (24965, 384030203611144130841067303766441869907707343),
  (17927, 514023578587430491805699763544092752682493455),
  (17926, 514023578587430493043639802829473027581617679),
  (17894, 183323498173408642315566561062052838859191826),
  (17862, 183062924147077067755046794948943738204661264),
  (13569, 472552427020959688661518420251284211742859862),
  (13601, 472552427020959688680767377484474292659352974),
  (13633, 472530648949476986303593264302611440125670798)]

theorem tbl28_22_ok : tblOK 28 tbl28_22 = true := by decide +kernel

def tbl28_23 : List (Nat × Nat) := [
  (13665, 472530145172066583820477433759735593875076494),
  (29089, 341905458362639185816246885255926296439764497),
  (13570, 472552426581349739612782311278289629669303951),
  (13602, 472552426580376183949993716155499250032944527),
  (13634, 472530648949476986311205496428169451855738254),
  (13666, 472530145172066583828089665885293605605143950),
  (13698, 477115212071356301117556842206823841232908892),
  (28066, 361729019792991582071434989278983699561223959),
  (13571, 472552426581349739612782311278289560949827215),
  (13603, 472552426580376183949993716155499248959202703),
  (13635, 472530648949599410066346994764290346777142931),
  (13667, 472530145172189007583231164221414500526548627),
  (13699, 477115211927594581846873802134384273298571996),
  (27043, 361729019792991582071433132784091537553036751),
  (13636, 472530648949471944391466901139498267131618703),
  (13668, 472530145172061541908351070596622420881024399),
  (13700, 477120656445408248750132401757512092825965276),
  (13701, 477120656445408248750022597191235185654445586),
  (16870, 183323498173408642315576011469554108636444177),
  (16838, 183062924147077067755046794948943738204661265),
  (16869, 183323498180922716699548778669108573589833428),
  (16837, 182969519447135966704206526879604007871784465),
  (16805, 182620985213640176412080447448837068816197137),
  (16773, 182365939446539762028010239473764254080919250),
  (16868, 183323498180922716699548778669108574663575252),
  (16836, 182969519447135966704206526879608405918295569),
  (16804, 182620985213640176412080595022789589773133329),
  (16772, 182365939439713234686811653498916951178700497),
  (16740, 182017385189975393008004338824004953288021519),
  (16708, 181668954754388121282054067959217291168392721)]

theorem tbl28_23_ok : tblOK 28 tbl28_23 = true := by decide +kernel

def tbl28_24 : List (Nat × Nat) := [
  (14625, 159014210655229683257959732748796455230985812),
  (14657, 159362765017210734914790803883257145887667663),
  (14689, 159711195466052682674333750241366706696861004),
  (14721, 160059749702507483011607954221460698711262671),
  (14753, 160408178847438615278790859188568411865941455),
  (29121, 297309412483448674548590862704348481719186961),
  (14626, 159014210655229683257950285691693064788985423),
  (14658, 159362765017210737390670882184936095075861967),
  (14690, 159711195466052682674333750240798901198451483),
  (14722, 160059749702507483011607954203446300201780687),
  (14754, 160408180176784363759658732463183033893979599),
  (14627, 159014211136769169137060849975309271523198415),
  (14659, 159362765017210737390670882184936026356385231),
  (14691, 159711195473573483971635981920131572347008725),
  (14723, 160059749702507511791181922962292363980768719),
  (14755, 160408180176784363759663451371182864695363023),
  (14660, 159362765017212505070198167904431185447728592),
  (14692, 159711195473573483971673735489972616273155792),
  (14724, 160059749702507511791186644175572254042424783),
  (14756, 160408180176784363759965681672883542405481935),
  (14725, 160059749709383789626017046194930160653924051),
  (14757, 160408180176784363759956236940199278091765199),
  (15814, 491722746975497600854102998654447590465934800),
  (15813, 499770020654246535541300895039609846713923090),
  (15781, 160408180176784363763577849328629583029540304),
  (15749, 160059749730152978293884192687022200873645779),
  (15812, 499770020654241464888478152131248114753151768),
  (15780, 160408180176784363763577996902300697729242576),
  (15748, 160059749723311876529482298305691182347130320),
  (15716, 159711195473573480257853765207784381252196048)]

theorem tbl28_24_ok : tblOK 28 tbl28_24 = true := by decide +kernel

def tbl28_25 : List (Nat × Nat) := [
  (15684, 159362765037986763164766904464638265573603029),
  (15811, 499765163634370563153780968010625023824705042),
  (15779, 160408180176784363763573275689020807667586512),
  (15747, 160059749723311876529477575957504186188109264),
  (15715, 159711195473573480257853781346434257632982741),
  (15683, 159362765037985003686913873787499903181764048),
  (15651, 159014211136753957329858111222491311084738000),
  (15810, 499765164963634103774161666380323327872677393),
  (15778, 160408180176784363759658732463183033893979598),
  (15746, 160059749723311847769245072709575167464773072),
  (15714, 159711195466052682674333750204770104179491611),
  (15682, 159362765037985003686913873787499904255505872),
  (15650, 159014210655229683257345822781885750201632336)]

theorem tbl28_25_ok : tblOK 28 tbl28_25 = true := by decide +kernel

def tbl28 : List (Nat × Nat) := tbl28_0 ++ tbl28_1 ++ tbl28_2 ++ tbl28_3 ++ tbl28_4 ++ tbl28_5 ++ tbl28_6 ++ tbl28_7 ++ tbl28_8 ++ tbl28_9 ++ tbl28_10 ++ tbl28_11 ++ tbl28_12 ++ tbl28_13 ++ tbl28_14 ++ tbl28_15 ++ tbl28_16 ++ tbl28_17 ++ tbl28_18 ++ tbl28_19 ++ tbl28_20 ++ tbl28_21 ++ tbl28_22 ++ tbl28_23 ++ tbl28_24 ++ tbl28_25

def mask28 : Nat := 333412537725620709401091444812462392137193130263193081869390956717666684780641154637726636172142716754901043807108907640240808042746912734671424509600112174678060192409937890112361488186910265575501821492443239695105742572073793867112318415573226906894714101509312873316702168701083452525569335372370452434927876677506988065768912929184537404251645880742488229632599709983369339904538242349190014022969322092259868474583594891035403797979985115575137315216151924997693255976715894801943541696900833520486642358745153697382756505863886928910908878972774497746587034558218610425844084220241529015634408689804625179372554403852591662383970551887952609007473175229181385302035209511718781406174613317681373306160151131168108484790691969146162819037711408523596842307914101985805303389888309722438567238868416570263780224282020918828993687710233357190190159953985750725680662479682346518343243234456767944078662186589081181837157013211089829323935019827297694623643822733223306564850061311977656907946831586492973236641434603635767335199084571610728295273726510917958432645434586065846149057783407147699290392287312594990223421773757689448758008921833434505197433507747724259488313751486742683529809186475422291083189842149282636450375148928729419493182114998348123426717910266682043496138177049493764965115624222289059329781818885962951247807723826218647611269108550596998464045581674773237375671226238358555970539546462575352480433105436082988658898872687850997403782878328295882516168676277491432845574894310514371205735957361999889449456770459094311822950318157762130416237466520223218220125464200765528882502028660545712100443425555369575301442216103005265458304836604798837563883867965055799278384874001909713724468248299252915780474206841660293730320395882594483295795459362781280356627566932104478891766135875190858515588500634468097968074242479647378990764274928909955313870253315991174226656263817228081128017364840058957561059995555376974400630860146175906487669464443505585649269257157583659710368240843728648143127699904192057855473394591036524539585538161731167407919641987944685698784742061582305525182038353462864791261959807050928957528300580347492445780801178241599709518555926162218613808117413373198377744613066492256752487656118048367620599231542751998777235200315247894694442213281342224717794971742615269624067011304320231071832579061207570549728254743253648379479328470675678524843043882709243434300198141106079736832226755915604212440417411182760214938337523914533502835041122668195515654227375254431207956169942175353165557935654025256309566535064225449526305318110304397327592204207147764766259504822441986947669479750528577753583358029490416153281170923745442184600316125123271420308433747319715002297557066247952964524843395073375968967080646113223392599318870159566697164464845371176108532069411771447484754927577104894411006719975297111826503985543334392381264789896739577102088535821451309765103670149481572860949770655894967884414594832006696562703726604385973300953569137626460604761679718234838512497918922414989582110355242642617193799363597910740273834451190329983358061694231524319981289901396100656069886460202119873787935303104938835941358250328556778403625347463714965166643250093780685471999390402661755930021571748366264020405128630533115088209418159670728030447815272454187373411302782845024385680212062873312938051115791463089974266579569587335174896131679121603606391305759706390967645591935071183947025054460391060265724611723404301446273583324577661500314647905104503311123680761826969015644493859723748970799165323833101381678039948022087970446907416467088801727023713684052240615242300186656985181671320272811680719029326504165220878980022424792983990604556128212082004405752448095828188274052178901131434734977855019274214518797593845073932502755045340147178656133363915764207588012576439136791901438207297216469070583043433418627938009160321496170043914901134240520908646758488407733964088631242996217332948798748299158752168714101581802268294962218187017521741095534838286416265847576392202929356843705778017318305902303378469447867747922580370485353025788790831346972662934327894075368587744348419641946234467571668348407556987694883113243497780827599483669235124460153325060818505932368957548199018489613655273418080391605224491751830092352676491364777932164167773433370468022733629570872345556944403940009411212256941918164352166321228703187002079853891647259600276538347938468464364912249108907882223222705852983616090489200334358787717895290622408300872391130014293696378638049500633898004688241500083325750289850893352556972926186862032442992522975028575662501824765227107499320610036225890587273224871764024526579740160574819461904921635778834226907578140705655905019074635644129374617793807338030111758238915041773252620256811678587612080429262032588744501004615037031618451292153472126672715493878667723971040228481226354659658811404891294765040381222363990098664558482896015589484639738241369401166994780139034722000475295962246026544721893517306188471763403310250040157821634395516423254919758976465229518512160862253641661860473549352223074002630715789328207632937969507155042771414430221443422804442303175604076511324903900038171061012099275998741606527819529819049670844156853400556555300301340838405661001754748571227545769584550032263083714834021359388389568897685459880232831682970095558249631101100424032015261780886342598970367439047220257409347979686222292681908347932393600010501608500597442988818140469527431157574587688893184268227058951237042934030510473658676519922481110991317193326319243878308961309425836232893604162948150725522517522952309496841479366742651216237667204322693044165348170905836406819627255653194684407545445625301812608623687492378668487575179362216494179657277746818060575715797573367568392326147997716615508637124734477045311843523477012100826571217693443003227280541080088835711139316712345678723227589500989512768273613412075255731308793764784682916897301193784966886923053357637809436757148534455747794595387956897423490775208780109069386649208972425039839697464589132044083364330911863881252194542486910591748280046468271517662900637799816040659356181403422001172552337265891880323756934996064361575598177006660223151820514281233497977390173141892288137457735440246557728440959626944413062289437554699853710522740099767954468141335867747185271231152091960288672006526297967662803261264005641717854591471337818757000039773089173775689198558291820365227279713046225447613746073679887698591613772762553361427758626281754778928634282009840571533992026893627967192259852131399776300428049578800807860129717090897441039258226160321798900824824464853270393870637651471631009068848159960752803124982008803321977168131325574471543931226762517793194294278980397054925242818264856345993012706651490947882181638889665645973011663063736982735586477658870481129831959461625017763501402268763616891341262178472901866661625598350538218377348971031108040501515783909587960239595915746682228894547858416171084730045584759712524293434058617901620020688442518506750312281114602052245754616952143227031150086989776759769271855182034749492865463385505128091940756100168399793750082472937460922559056680167031767275620434726336630207157212539694907007087893015846288795883269225698248539962341935636291035161725395253157218178160550114352716041365004827803421013908140580892650388654507267753043457536705580759677326793451070810750875511333282291609174464932138417460986060186810109315049780763463492090443336484132365328455726507698354967153595780486845582026721742758907236884764918761809599664574725935548908767126325164883403953554538862652408647942474972966422773489807064551784331975682219775265597141697523269441280953069514351512336482957809902003275962946705708491245225866583533140644399464535213293103005879368088576010328051448563591245126424663707512807357053846875962763730817071543955138977439984389949486303432591732307245148408287395919919390101818140478059039508159022027337430400873163627247912111219912095501217899500461726329346003845966614229778536421697385694227435902678449365235613383352263574059142836566136406024452978118737758726589046405645905312817936860569275801861431445318315898624327790600039233318741278702503640455336032990385803830664426850406386710993551306134495623187048859637049192579171777183374376187842551007892845358856839002244174543659171192271457553028570814725911658930802975905051038637285799277726557662904533941851478784769214141071616188862443382348722544351610688588364646352090478098901705637458783833970195410441237292044158680486126776102064841646347783917273598704616498127340561549208277657057100232044957333688987125979418073066107406573320991622608055272078356708810543242169465745877424202585939277186382228241438596575879319019510646342722799229565666873432356405614342412946321993930039409256396896256745261641224176195003839235703101576216268691734528

theorem mask28_eq : maskL 0 (tbl28.map Prod.fst) = mask28 := by decide +kernel

theorem cov28_1 : coverX 28 mask28 1 = true := by decide +kernel
theorem cov28_2 : coverX 28 mask28 2 = true := by decide +kernel
theorem cov28_3 : coverX 28 mask28 3 = true := by decide +kernel
theorem cov28_4 : coverX 28 mask28 4 = true := by decide +kernel
theorem cov28_5 : coverX 28 mask28 5 = true := by decide +kernel
theorem cov28_6 : coverX 28 mask28 6 = true := by decide +kernel
theorem cov28_7 : coverX 28 mask28 7 = true := by decide +kernel
theorem cov28_8 : coverX 28 mask28 8 = true := by decide +kernel
theorem cov28_9 : coverX 28 mask28 9 = true := by decide +kernel
theorem cov28_10 : coverX 28 mask28 10 = true := by decide +kernel
theorem cov28_11 : coverX 28 mask28 11 = true := by decide +kernel
theorem cov28_12 : coverX 28 mask28 12 = true := by decide +kernel
theorem cov28_13 : coverX 28 mask28 13 = true := by decide +kernel
theorem cov28_14 : coverX 28 mask28 14 = true := by decide +kernel
theorem cov28_15 : coverX 28 mask28 15 = true := by decide +kernel
theorem cov28_16 : coverX 28 mask28 16 = true := by decide +kernel
theorem cov28_17 : coverX 28 mask28 17 = true := by decide +kernel
theorem cov28_18 : coverX 28 mask28 18 = true := by decide +kernel
theorem cov28_19 : coverX 28 mask28 19 = true := by decide +kernel
theorem cov28_20 : coverX 28 mask28 20 = true := by decide +kernel
theorem cov28_21 : coverX 28 mask28 21 = true := by decide +kernel
theorem cov28_22 : coverX 28 mask28 22 = true := by decide +kernel
theorem cov28_23 : coverX 28 mask28 23 = true := by decide +kernel
theorem cov28_24 : coverX 28 mask28 24 = true := by decide +kernel
theorem cov28_25 : coverX 28 mask28 25 = true := by decide +kernel
theorem cov28_26 : coverX 28 mask28 26 = true := by decide +kernel
theorem cov28_27 : coverX 28 mask28 27 = true := by decide +kernel
theorem cov28_28 : coverX 28 mask28 28 = true := by decide +kernel

theorem cert28 : Cert 28 tbl28 := by
  refine ⟨by simp only [tbl28, tblOK_append, tbl28_0_ok, tbl28_1_ok, tbl28_2_ok, tbl28_3_ok, tbl28_4_ok, tbl28_5_ok, tbl28_6_ok, tbl28_7_ok, tbl28_8_ok, tbl28_9_ok, tbl28_10_ok, tbl28_11_ok, tbl28_12_ok, tbl28_13_ok, tbl28_14_ok, tbl28_15_ok, tbl28_16_ok, tbl28_17_ok, tbl28_18_ok, tbl28_19_ok, tbl28_20_ok, tbl28_21_ok, tbl28_22_ok, tbl28_23_ok, tbl28_24_ok, tbl28_25_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask28_eq]
  interval_cases x
  exacts [cov28_1, cov28_2, cov28_3, cov28_4, cov28_5, cov28_6, cov28_7, cov28_8, cov28_9, cov28_10, cov28_11, cov28_12, cov28_13, cov28_14, cov28_15, cov28_16, cov28_17, cov28_18, cov28_19, cov28_20, cov28_21, cov28_22, cov28_23, cov28_24, cov28_25, cov28_26, cov28_27, cov28_28]

/-! ### `N = 29`: 852 witness orderings -/

def tbl29_0 : List (Nat × Nat) := [
  (16705, 11937950286350267047674747783728684614250735121),
  (16737, 11649119380272652645719140063460159242735003153),
  (16769, 11671418842723128642733517850199346555926988173),
  (16801, 11693726400278950144851913585521904873580340753),
  (16833, 11716025864059500607686470665199218425738937871),
  (16865, 11732703859338409377164697128332834429507544593),
  (24065, 25897127878365073537479754194641240296111818323),
  (25089, 17463999300403640068956874594962288867961541209),
  (26113, 17463999300403640068467873647424474286146785880),
  (27137, 18891246986649733382717029651888374401986269785),
  (28161, 18891246986649728310876693423202276832995775194),
  (29185, 20164525254421290300690528472847922694154692113),
  (30209, 20164525254421290300690528472847922694154429969),
  (17729, 23172991700903519972155382589184087027696612946),
  (17761, 23172991700902546416494407311309580568848578130),
  (17793, 23172991700902515992976715899373114981948143186),
  (17825, 23172991700902515845507108719502189734589970002),
  (17857, 23016881040350268026168752964790891418672510546),
  (17889, 23016886484493036422723789351135031254066476626),
  (25121, 17467097488027152346290015854783324829254760018),
  (26145, 17467097488033724500498836288931338096479651474),
  (27169, 18894345180739683018719645799601898843863856722),
  (28193, 18894345180739683018719645799601903240836363858),
  (29217, 20165531140111459591973572464148391782635348629),
  (30241, 20165531140132228779407711774664756629521647250),
  (18785, 23172991700902546416488912335195549556154644049),
  (18817, 23172991700902531204776912504737946593177712209),
  (18849, 23172991700902531057307305324867021345819539025),
  (18881, 23016879749714109754699274598575393857153865295),
  (18913, 23016885195561117770489979547802573127902377553)]

theorem tbl29_0_ok : tblOK 29 tbl29_0 = true := by decide +kernel

def tbl29_1 : List (Nat × Nat) := [
  (25153, 17467097488027167558097218593535298364763092561),
  (26177, 17467097488033724498022956210360577546681403027),
  (27201, 18894345180739683022433465917457195243631097425),
  (28225, 18894345180739683022433465917457199640603604561),
  (29249, 20187831885309980072672366317300447895616565909),
  (30273, 20187831885330750859680061499411216032801080981),
  (19809, 23172990071291157555982345944395707820304311825),
  (19841, 23172990071689229087130135260091353217036002833),
  (19873, 23172990064707325139416701795791865397984437777),
  (19905, 23016879749734878942133412047593873592200533519),
  (19937, 23016885195581886957924116995668412833335682577),
  (26209, 17467097488027167558097216730887016084879517201),
  (27233, 18894345180740007540987124344183978401798628881),
  (28257, 18894345180740007540987124344183982796624176657),
  (29281, 20187831885330749260106505627816812742503122578),
  (30305, 20187831885330749260106505627816812742502860434),
  (20865, 23172990071689229088368056921807950058777552401),
  (20897, 23172990064728094326850822728737203950143743505),
  (20929, 23017924756485201091019996494327427191480325647),
  (20961, 23017930202332624317007859032451726041326888465),
  (26241, 17467097488027172628698692575329892180474275345),
  (27265, 18894345180739992329162996490617995588939884049),
  (28289, 18894345180739992329162996490617999983765431825),
  (29313, 20210132630110307829034147380843280767214720856),
  (30337, 20210132630110307829034147380843280767214720792),
  (21889, 23172990071709998275802196232322071974301214225),
  (21921, 23172990064728099397453223641654809867163346449),
  (21953, 23017924756485206161622397407244751702242694671),
  (21985, 23017930202332629387610259945369331958346491409),
  (27297, 18894345180733132362287371364908461999705630225)]

theorem tbl29_1_ok : tblOK 29 tbl29_1 = true := by decide +kernel

def tbl29_2 : List (Nat × Nat) := [
  (28321, 18894345180733132362738286012822307663483315729),
  (29345, 20210132630424460469941350917223236984225760982),
  (30369, 20210132630424460469934659918824853768513873490),
  (22913, 23172990071709998276945216707607333914642032145),
  (22945, 23172990064748868584792443388168813517921920529),
  (22977, 23018273205633785587264871481837629270157235727),
  (23009, 23018278651476356428521264967714574951586801169),
  (27329, 18894345180733136799124913728866569838459692561),
  (28353, 18894345180733138632763471835172626120072832529),
  (29377, 20232433375643760280510334873824649420233795410),
  (30401, 20232433375643760280510334873824649420233795346),
  (23937, 23172990071227479593190018472843344184924513809),
  (23969, 23172990064748750623133979996003569495637566993),
  (24001, 23018274642524603488675513204853774641437677071),
  (24033, 23018278651476238546071621276699834456051099153),
  (28385, 18894427604520390503653696026957883191761913426),
  (29409, 20232434648957148682682480356015674774784599890),
  (30433, 20232434648957148682682480356015674774784599826),
  (24993, 23172990064767613026380888506621752887269724761),
  (25025, 23018623115906960561130118667114422140687951441),
  (25057, 23018627185647436597138760899788358045892940377),
  (28417, 18894427604526596107408887433549643713243858514),
  (29441, 20254735394155679280894233532904280957209589593),
  (30465, 20254735394155679280894233532904280957209589529),
  (26017, 23172990064767613025891887559083938305454969432),
  (26049, 23018623115906960561130118666671371731252618769),
  (26081, 23018627185647436597131233158573639746783613528),
  (29473, 20254735394155776508606598283720453100082317140),
  (30497, 20254735394155776508606598283720453100082317076),
  (27073, 23019020639833210062358900531952629302305302033)]

theorem tbl29_2_ok : tblOK 29 tbl29_2 = true := by decide +kernel

def tbl29_3 : List (Nat × Nat) := [
  (27105, 23018975622994265175526691283303283723123626585),
  (29505, 20277036120496142969125895754744762913271911001),
  (30529, 20277036120496142969125895754744481438295200345),
  (28097, 23019020639833210062807100411739915338051036689),
  (28129, 23018975622994260103629233309640394925628265178),
  (30561, 20277036120496142264698906407993786753991119642),
  (29153, 23019286470914375036852207774852817800777717464),
  (30177, 19049754781395338480809597017356861028479084049),
  (17473, 34592725004255298685100153277656720154328905298),
  (18497, 34592725004255298685100153713461048895717062225),
  (19521, 36019972696961258566158439682928549634516526609),
  (20545, 36019972696961258573585754075353513278374749713),
  (21569, 37447568838809917504032308486560323738006791697),
  (22593, 37447568838810242022452380610219408895245624849),
  (23617, 38874816531826435152764376662181616503892289041),
  (24641, 38874816531826435698695935235331326746542805593),
  (25665, 40302412671022250852394984031409508859709310674),
  (26689, 40302412672346894624955890137616358373899178585),
  (27713, 41729660365052853957606422527599374171331433242),
  (16706, 11626813786216659158659424982890662668402758360),
  (16738, 11649119380272657716328583199502573913412847121),
  (16770, 11671418842743897830167657156086014773381130001),
  (16802, 11693726400278950144851913585521623398603630097),
  (16834, 11716025864059510748891272490748152644128282127),
  (16866, 11732703859338419518798965026393755330655888913),
  (24066, 24871735352308901185804021882156344333564991123),
  (25090, 24782548705068390898284125251046907612415219347),
  (26114, 24782532407658751755928687735174855084714350227),
  (27138, 18891247071727522213186304348017092803188004692),
  (28162, 18891247071718697522646285490090116407838454362)]

theorem tbl29_3_ok : tblOK 29 tbl29_3 = true := by decide +kernel

def tbl29_4 : List (Nat × Nat) := [
  (29186, 20316371911529922025040675168151830179460486669),
  (29121, 23019020639833210062807100411746912966920185361),
  (17730, 23172991700903519972155382515397110732858406482),
  (17762, 23172991700902546416494407237522604274010371666),
  (17794, 23172990156739174423620965119404696114451002962),
  (17826, 23172990150093034444754418916593645883080390226),
  (17858, 23016881040350268026168752964772877020163028562),
  (17890, 23016886484493036425206373257833039377502123602),
  (25122, 17467097488027152346290015854765310430745278034),
  (26146, 17467097488033724500498836288931453928157300370),
  (27170, 18894345180739683018719645800073646429151024722),
  (28194, 18894345180739683018719645799583888842326881874),
  (29218, 20324114551793683856046019008825918803357828821),
  (29089, 23172957987815870846952267747569004325069239822),
  (18786, 23172991700902546416488912335177535157645162065),
  (18818, 23172990156739174423620965119511093655647630929),
  (18850, 23172990150093034444754418916700043424277018193),
  (18882, 23178964591177766320770638934581258588494317137),
  (18914, 23017583383261775924619670569651124701987161683),
  (25154, 17467097488027167558097218593517283966253610577),
  (26178, 17467097488033724498022956210360693378359051923),
  (27202, 18894345180739683022433465917929787234610132561),
  (28226, 18894345180739683022433465917439185242094122577),
  (29250, 20321681357404255040057527433365375513953112725),
  (29057, 23175391097126859431983401281262076918215022093),
  (19810, 23172990071291157555982347883591378201656763921),
  (19842, 23172990156759948714041364597635701960262588052),
  (19874, 23172990150113808735116785228524683888803485332),
  (19906, 23179312282772258884102337579034865628964509530),
  (19938, 23017583468353138921084072613847309509100595032)]

theorem tbl29_4_ok : tblOK 29 tbl29_4 = true := by decide +kernel

def tbl29_5 : List (Nat × Nat) := [
  (26210, 17467097488027167558097218667776843457051829777),
  (27234, 18894345180740007540987124344656455109647869457),
  (28258, 18894345180740007540987124344165968398114694673),
  (29282, 20321680851079111765751739561042362999521204058),
  (29025, 23175391688531094132639793327345379688355534349),
  (20866, 23172990156759948704137860313520065070418925397),
  (20898, 23172990149798686088253724507822228950601185109),
  (20930, 23179312282670055425968724240446907462014523226),
  (20962, 23017930202332624317007859062320980092431705617),
  (26242, 17467097488027172631182507576043147543985297240),
  (27266, 18894345180739992329162996491090753703046358545),
  (28290, 18894345180739992329162996490599985585255949841),
  (29314, 20321680850976908307618126222454404832571217754),
  (28993, 23175391688633297590773406665933337855305520653),
  (21890, 23172990156780717891571999550247210760897599316),
  (21922, 23172990149798691158854009874342767106171123544),
  (21954, 23179660731813111467707597609162733891897099990),
  (21986, 23017930202332629387610259975238581612478539281),
  (27298, 18894345180733132362333991912125422037218662232),
  (28322, 18894345180733132362333385514427042168424179217),
  (29346, 20321680852305465304155328968476028192085608150),
  (28961, 23175391687304089398431658351395696414380856845),
  (22914, 23172990156780717812343837035982873167353648980),
  (22946, 23172990149819460346270921844353146561095313236),
  (22978, 23179660731813111467707597609286864356626499285),
  (23010, 23018278651476356428521388661059352608872977937),
  (27330, 18894345180733136957581348285946417083111560721),
  (28354, 18894345180733136957581338811034847996380522001),
  (29378, 20321680852305465304155328968600158656815007445),
  (28929, 23175391687304089398842957802761356331319580376)]

theorem tbl29_5_ok : tblOK 29 tbl29_5 = true := by decide +kernel

def tbl29_6 : List (Nat × Nat) := [
  (23938, 23172990156801152340019392035040095334377555732),
  (23970, 23172990149819465335161350189168390391666386449),
  (24002, 23180003733780511782108936945083541458422957845),
  (24034, 23018278651476238546071621275546912951444252177),
  (28386, 18894427604520390477306099106063301885304059474),
  (29410, 20321675407787594569139913554606439748523624149),
  (28897, 23175397131821960133858373216755075239610963672),
  (24994, 23172990149845077258579341287345175236053419604),
  (25026, 23180003729784979132388356087692510410950395473),
  (25058, 23018627185647436597138760899770343647383458393),
  (28418, 18894427604526596107408887433549639315197347410),
  (29442, 20321675403792061919419332697213552518289756821),
  (28865, 23175397131823258290487633225734021964224075277),
  (26018, 23172990149845401777132999714071958392073979604),
  (26050, 23180352178937205869491535354115110066896623121),
  (26082, 23018627185647436597139063131225247304676872792),
  (29474, 20321675403800561615535925468039998226348758545),
  (28833, 23175397135809644282856211883257551771820430861),
  (27074, 23180352178936554835740775821970130408230454997),
  (27106, 23018975626988821744505015329141293405405222740),
  (29506, 20321675403799910581785165935895018567682590421),
  (28801, 23175397135809644121213120835466496420451997400),
  (28098, 23170867382033527218434819262523899308764115546),
  (28130, 23018975626979997053964996471214317010055672410),
  (28769, 23175397135810293319963528736711118083861583373),
  (29154, 20477786068695179666146078996508697187356870357),
  (18529, 23173688599649792196852019886602098014587799123),
  (19553, 23173688684199257750476254765228214775964833293),
  (20577, 23174037133342984791424138509083949856994924376),
  (21601, 23174037218789642902249923015763491475072291547)]

theorem tbl29_6_ok : tblOK 29 tbl29_6 = true := by decide +kernel

def tbl29_7 : List (Nat × Nat) := [
  (22625, 23174385667954139130670648821875632384983241369),
  (23649, 23174385751695625422440321806588948681268234004),
  (24673, 23174734200839352463426908302258998745049167636),
  (25697, 23174732055254018383586165370987556124079990616),
  (26721, 23175080504418524837403733345155263158237860441),
  (27745, 23175080504418519760599817310655263359116325466),
  (29793, 23220036419114063634220161162748325739902387730),
  (17731, 11627162235360376058556917223808699860637516569),
  (17763, 11649467829561774137364608676789326387829130832),
  (17795, 11671767291887624871154243655142508693051242262),
  (17827, 11687743139963706414319000955711869146427880910),
  (17859, 11710049329329278281268649686045614892163073487),
  (17891, 11732703969890238428745549390579718906893641296),
  (17923, 34773282468936937392648164152581760884965201556),
  (25123, 17464000844013759523816108724323565532196456018),
  (26147, 17464000844013759525061950473487944685624514392),
  (27171, 18891248536405612375088544425880093422766281501),
  (28195, 18891248536405612216624327208871034416201278992),
  (28066, 23172990149836577165821143398438601816986694234),
  (28065, 23172990064767607954051551331550762242144015066),
  (18787, 24600239369829379988871706778960501880248153680),
  (18819, 24600237849446412096485792227559301620878620240),
  (18851, 24600237842483872021990522684898796878513124944),
  (18883, 24606174173216254892401396315896256072227309139),
  (18915, 24622849188697057418054895790805305430346122835),
  (18947, 24807963629415809277199314889115158834463200916),
  (25155, 17467494844394386951700627189079801201746331219),
  (26179, 17467494844394386952946487765834543448810083037),
  (27203, 18894742537100346497380611482867852524734460633),
  (28227, 18894742537098753692714551755577249982945769102)]

theorem tbl29_7_ok : tblOK 29 tbl29_7 = true := by decide +kernel

def tbl29_8 : List (Nat × Nat) := [
  (28034, 23175010151017740478500213699938443034029528654),
  (28033, 23172990741158384396458281241208037149660484314),
  (19811, 24600237763997117541304190135487972550617192084),
  (19843, 24600237849466207761843552822632923359606036116),
  (19875, 24600237842483876854916644715933662071085119322),
  (19907, 24606522367713610772272355961708537234102212442),
  (19939, 24622849188724372020123576050774062965384075098),
  (19971, 24827134571953637677575857641917070883133970069),
  (26211, 17467494844812680889275983817343291405386700634),
  (27235, 18894742537518640770334270222597115283157600089),
  (28259, 18894742537518640770326061108858063534710408786),
  (28002, 23175080843143521984055823070554995794256147034),
  (28001, 23175080840526604609963651668154872521501250330),
  (20867, 24600237849466207750702396610981018068736923285),
  (20899, 24600237842504646042350775097751355443270473362),
  (20931, 24606522367507901107328907236029570258100606810),
  (20963, 24622849273794963750351198602727835523921335954),
  (20995, 24827133813108538322213235680534960736193074837),
  (26243, 17467494844812756549612758411640078573298636434),
  (27267, 18894742537518716430671044378778119274044413650),
  (28291, 18894742537518716430671042371235822045081196178),
  (27970, 23175080843369681309253991078674569993896407642),
  (27969, 23175080840713167363328603159896282919186797274),
  (21891, 24600237849486976938136535921495140054053803604),
  (21923, 24600237842504651112950758233289005407484295001),
  (21955, 24606870816651593055595371341465480326905410269),
  (21987, 24622849273355150466923469504472275070126249554),
  (22019, 24849434558265530570486492777779365127065294548),
  (27299, 18894742537518716430671044381089292234687895122),
  (28323, 18894742537518716430671042371235822046154933842)]

theorem tbl29_8_ok : tblOK 29 tbl29_8 = true := by decide +kernel

def tbl29_9 : List (Nat × Nat) := [
  (27938, 23175080843369711416044635168795669281019597530),
  (27937, 23175080839383974460783373364725705785464394458),
  (22915, 24600237849486976858908373407230802460509853268),
  (22947, 24600237842525420300367972508069249219638412882),
  (22979, 24606870816651593050239499912526026442336753235),
  (23011, 24622849358425742197447618742699314640032450130),
  (23043, 24849434558162227813087464305128809069743822551),
  (27331, 18894742537518716430695557584914506566600255321),
  (28355, 18894742537518716430687363164968773325486638674),
  (27906, 23175080843369711415955746499122855540597535322),
  (27905, 23175080839383974465619983337548933456170128090),
  (23939, 24600237849507112221034189442257834468748379922),
  (23971, 24600237842525425216219636158617604053072422416),
  (24003, 24607219264457267251897412143267758047082137171),
  (24035, 24622849358425742197466954828063118600789112402),
  (24067, 24871735267235728512760058997544731651435746964),
  (28387, 18894742537518391912133704738241990169466062418),
  (27874, 23175080844698939411740662372026662600877879898),
  (27873, 23175080759629970199971070305138823026035200730),
  (24995, 24600239307229451820085633600933352556349957712),
  (25027, 24605825723094134278654913758406673098314171987),
  (25059, 24622849443888032997690878965393608290329507410),
  (25091, 24782548619995218225240162366435294930285975188),
  (28419, 18894742537539162615911349377185697639064229524),
  (27842, 23175080759630294718505385918751772115260478170),
  (27841, 23175080759630294718524728731865606182055776986),
  (26019, 24600239307229451899321688377465050263135474461),
  (26051, 24605825467891183931494824552828188996553201498),
  (26083, 24622849443894605121977573353496368000691197586),
  (26115, 24782532322567390838105822777297942740045256341)]

theorem tbl29_9_ok : tblOK 29 tbl29_9 = true := by decide +kernel

def tbl29_10 : List (Nat × Nat) := [
  (27810, 23175080674559703225954955364246229380656599770),
  (27809, 23175080589489111495739984542971315246803522266),
  (27075, 18714540251839047358192111980646736521515320912),
  (27107, 18874136412981238515693433726927348937377797844),
  (27139, 18891247071727522213186304348022427571194450653),
  (27778, 23175080589489111495720943961312384837301899994),
  (27777, 23175080589489111495740286774426218904097198810),
  (28099, 18714540215714233941950088352058801671967928922),
  (28131, 18874136412981238513217553648356588387579549460),
  (28163, 18891247071718697527571481901131254161672573658),
  (18561, 23173688599149435207675779900058257030019880525),
  (19585, 23173688684220026937910393928168384171605300749),
  (20609, 23174037133363753978859475610520372395761800717),
  (21633, 23174037218789323445710465484899875531343078171),
  (22657, 23174385667953819674111848477898182104949531416),
  (23681, 23174383698164285311711783216548656525274583832),
  (24705, 23174732147308012353107860132861859318815855321),
  (25729, 23174732146784162229043338237974418685766215185),
  (26753, 23175080589489116567637744748089107701592560217),
  (29825, 23220036419114062899794808126863787910503974549),
  (18562, 23173688599149435207675779900057975555043169869),
  (19586, 23173688684220026937910395839695882878224504333),
  (20610, 23174037133363753978859599638446578048116839953),
  (21634, 23174037218789323478055247678276981653633573723),
  (22658, 23174385667953819706476668841271580054057670488),
  (23682, 23174383698164285311692440403434822458479285016),
  (24706, 23174732147308012353107855410495376449170641625),
  (25730, 23174732147328781540541994721009498434487259864),
  (26754, 23175080589489116567645574793374770049717178969),
  (28802, 23175397135810293082298384007031939370025031181)]

theorem tbl29_10_ok : tblOK 29 tbl29_10 = true := by decide +kernel

def tbl29_11 : List (Nat × Nat) := [
  (17732, 11627162235360376059794904116646934327021610576),
  (17764, 11649467829561774166222857724969151250958763602),
  (17796, 11671767292368844909082200967766406270314440466),
  (17828, 11687743139971216789583047626991175576553866834),
  (17860, 11710049329810286161022893205964681950591534674),
  (17892, 11732703969897743779428908667746455518962599506),
  (17924, 34773282470266489913172778963396310550277342862),
  (25124, 17464000844013759523816410955778183316466910802),
  (26148, 17464000844013759492696563105029944697329931922),
  (27172, 18891248536405610303700182641738481182400914960),
  (27043, 24600239307229451899321688303678073968297267997),
  (27042, 23172990149845401856361162256365578212336244564),
  (27041, 23172990064767613025891887560236859811134509657),
  (18788, 24600239369829379988872009010397109664055637584),
  (18820, 24600237849446412097723732193039691202430056016),
  (18852, 24600237842483872021990824842548709842459113040),
  (18884, 24606174173237029150437936539327139619426879059),
  (18916, 24622849188704576229889462590137108839722468947),
  (18948, 24807963630745361797723929699929708499775342222),
  (25156, 17467494844874978312841847889355487698092115539),
  (26180, 17467494844352848546854101195609765054552027800),
  (27204, 18894742537058808122024838351425318930798949081),
  (27011, 24602330002552990422616464529710952996634933080),
  (27010, 23175158446469913599639905488831164140121266007),
  (27009, 23172990741158389468298617469894134718650978905),
  (19812, 24600237763997117541296270055919613163685095056),
  (19844, 24600237849466207729496896223864347187161147024),
  (19876, 24600237842483876854908738213164186516116022928),
  (19908, 24606522367499365763825896153634241295251003029),
  (19940, 24622849188724371861659651529594242856431994514)]

theorem tbl29_11_ok : tblOK 29 tbl29_11 = true := by decide +kernel

def tbl29_12 : List (Nat × Nat) := [
  (19972, 24827132341151148967778189668067760930330891924),
  (26212, 17467494844812670748063582498856934509896877714),
  (27236, 18894742537518630629121863745939946776634410578),
  (26979, 24602330002091575269797327703949147401655702301),
  (26978, 23175080843378536106141804559755206676746932825),
  (26977, 23175080840713167364566538475664774501364470361),
  (20868, 24600237849466207750694489607862719636355503762),
  (20900, 24600237842504646042342877517573371843572999824),
  (20932, 24606522367499365763472843211132675487599810195),
  (20964, 24622849273794963591894873574199160336850212498),
  (20996, 24827133778168214710211045410923273416854562453),
  (26244, 17467494844812756391156431521991936017190704786),
  (27268, 18894742537518716272214717490288500852873582290),
  (26947, 24602330002091489626704473959600593227905812312),
  (26946, 23175080843378536106513898039253970625593414233),
  (26945, 23175080840713207523457469772083896629726089817),
  (21892, 24600237849486976938128628918376841621672379986),
  (21924, 24600237842504651112950756299513533007243060816),
  (21956, 24606870816643092804459429706730404143143663181),
  (21988, 24622849273815734215146010168992122596787775314),
  (22020, 24849434523366745339548983530034888209465698004),
  (27300, 18894742537518716272214717490288509648966600274),
  (26915, 24602330002091489626704473959600588829876340568),
  (26914, 23175080843378536106513898039201356767347963473),
  (26913, 23175080839383979531385769554126423079555764889),
  (22916, 24600237849486976858900466404112504028128429650),
  (22948, 24600237842525420300360037665468232457566627408),
  (22980, 24606870816643092804477562461564781136251799123),
  (23012, 24622849358886326024608788475313134083857794642),
  (23044, 24849434523366750410151384465902530037319063252)]

theorem tbl29_12_ok : tblOK 29 tbl29_12 = true := by decide +kernel

def tbl29_13 : List (Nat × Nat) := [
  (27332, 18894742537518716272231642599350019659052435026),
  (26883, 24602330002091489626687548850539351596167877405),
  (26882, 23175080843378536106495765357049831935947085652),
  (26881, 23175080839383979537517441311211822253665489497),
  (23940, 24600237849507112221034491599925757433157338898),
  (23972, 24600237842525425216219933667705743365744174608),
  (24004, 24607219264457591849679233084258865602507130451),
  (24036, 24622849358907090141440526872901945076724352594),
  (24068, 24871735268565281033284673808359281316747888270),
  (26851, 24602330002091814145241207277266134752188453661),
  (26850, 23175080844707764102280681229953638996227430228),
  (26849, 23175080759629975271811406533824920595025695321),
  (24996, 24600239307229451820085935832369960340157441616),
  (25028, 24605825723094458876436734699397780653739165267),
  (25060, 24622849443895578677599863007171994699288364626),
  (25092, 24782548621324770745764777177249844595598116494),
  (26819, 24602330002071043283046518254198378465615456084),
  (26818, 23175080759630299790873413441263992260087583321),
  (26817, 23175080759630299790365064960551703751046271577),
  (26020, 24600239307229449827933326519536461796651378192),
  (26052, 24605825467882683685732886520794505362174985875),
  (26084, 24622849443894605121938887726814436224566380178),
  (26116, 24782532287771158534530374887295578276250343060),
  (26786, 23175080674559708298323285118195338784267899481),
  (26785, 23175080589489116567580320771657412815794016857),
  (27076, 18714540217043469089275494572087389675298550289),
  (27108, 18874136412981238483193508685219418318180796114),
  (27140, 18891247071719027038802265832542250869769179737),
  (19617, 23173688684220026937909487381377625789400684045),
  (20641, 23174037133363753978859475536733396100923594253)]

theorem tbl29_13_ok : tblOK 29 tbl29_13 = true := by decide +kernel

def tbl29_14 : List (Nat × Nat) := [
  (21665, 23174037218789718563809289515564902645463855899),
  (22689, 23174385667954214792230010599310552029073847065),
  (23713, 23174383698164285311711783216548375050297873176),
  (24737, 23174732147308012353107860132861859250096378585),
  (25761, 23174732146784162229036112727730753644444586584),
  (29857, 23242337145454429390312593138208087869957944977),
  (19618, 23173688684240796628187014607006474096167424413),
  (20642, 23174037133384523669173601102509090328496690705),
  (21666, 23174035334070715394351321319667994607067149083),
  (22690, 23174383783214442514566676186410623269061908051),
  (23714, 23174383783234877042234420423553446972228711193),
  (24738, 23174732232378604083221006919151557841178445395),
  (25762, 23174732232399373270655146229665679826495309523),
  (28834, 23175397135809644282836869070143717705025132045),
  (18821, 13099016862981267922054335454660528033194120784),
  (18853, 13114990832677181741243725064625566390754031185),
  (18885, 13137297022516251112683580089322588392106571345),
  (18917, 13159951662603708731089897781566784643731109457),
  (18949, 13182257852422333512916101473477992205689116435),
  (18981, 13182257857654129662320278690051378109133964883),
  (25157, 17464000844013759501362145146998507537173657169),
  (26181, 17464000844013759501362143303934787298300081809),
  (25988, 24600239307543558897987992952277420379243665042),
  (25987, 24600239307543558930353380320735420367538247512),
  (25986, 23172990156821921527453639448068692974306162388),
  (25985, 23172990071227479592701017525222454831677772376),
  (19845, 26027485542172167610572713475035608393104086676),
  (19877, 26027485536855255627471740332014531155218519700),
  (19909, 26033770051899577998933926592564302137876141717),
  (19941, 26050109144843904763098291358081833459474847380)]

theorem tbl29_14_ok : tblOK 29 tbl29_14 = true := by decide +kernel

def tbl29_15 : List (Nat × Nat) := [
  (19973, 26078413216295722337910546127346582828141078159),
  (20005, 25894036584943517993338855943163243018986018452),
  (26213, 17467843293642051961650435260121780230775195281),
  (25956, 24601981553262194023651659591474796159713007250),
  (25955, 24601981553262194056210474942684301680777384797),
  (25954, 23174732402057879978328647548044172594063938136),
  (25953, 23174732402057879977820303788545445450060993112),
  (20869, 26027485542172167631752776013116543514109630097),
  (20901, 26027485536539833919186079386659750466815035226),
  (20933, 26033770051899577976431846195293357827337574035),
  (20965, 26050107855536664942983688140181110808133318289),
  (20997, 26078414653292343411596809530104435731716204181),
  (21029, 25894733483230972075312028934359263280249525907),
  (26245, 17467843293642051961785834876148391274125538961),
  (25924, 24601981553262194023654077289775465305351771794),
  (25923, 24601981553262194056075075326639962014465939288),
  (25922, 23174732402057920169175089954835297984691638872),
  (25921, 23174732402057920136711235084964567578422612568),
  (21893, 26027485542192936819186915323630665499426506321),
  (21925, 26027485536539838989793877944993711669357086553),
  (21957, 26034118501043305017420515254510396351569581651),
  (21989, 26050107855557435545230659646905223280242013777),
  (22021, 26078763102436070458779798426541412293469890260),
  (22053, 25894733568301563817925105442126709707813017171),
  (25892, 24601981553262194023692762916003133419737659026),
  (25891, 24601981553262194056075075326639962083185416024),
  (25890, 23174732402037150959129813159133786380674627089),
  (25889, 23174732402037150959121983186482178822781367825),
  (22917, 26027485542192936739958752809366327905882555985),
  (22949, 26027485536560608177203239534536601080345691993)]

theorem tbl29_15_ok : tblOK 29 tbl29_15 = true := by decide +kernel

def tbl29_16 : List (Nat × Nat) := [
  (22981, 26034118501043305018658455293795412004018931283),
  (23013, 26050107940628027377225056979148960418206345049),
  (23045, 26078763102436075529382199362409054121323255508),
  (23077, 25895082017445290858911691937724355283674023507),
  (25860, 24601981553262194023692762916003133438942369426),
  (25859, 24601981553262194056058150284461133427236951896),
  (25858, 23174732402037150959129813159133785835218735704),
  (25857, 23174732402037150959121983186482178277325476440),
  (23941, 26027485542213072102092778005179581242208765713),
  (23973, 26027485536560613093063135505359257876269438480),
  (24005, 26034466950187032059645039778387130969660409427),
  (24037, 26050107940648791494056795376254839284973553235),
  (24069, 26079111551579802570360539482190604219974764174),
  (24101, 25895082102515882589146305793714918887456327251),
  (25827, 24601981553262194135286312798725471020780902232),
  (25826, 23174732402540556732386571926058743627548817108),
  (25825, 23174732316946114797633950003212505484920427096),
  (24997, 17601644032652652902776452636174273869404784211),
  (25029, 17426406013500297604014787865648524136622929489),
  (25061, 17446964513973899424364035217901829645665384017),
  (25093, 17463999385977312815781747814710278557470377553),
  (25125, 17464000844013759523816410955778183247747434066),
  (25795, 24601981553262189064681234304012077945131923288),
  (25794, 23174732316946114877370456276975570222467322456),
  (25793, 23174732316946114876862112517476843078464377432),
  (26021, 17601643777440877712072605038651018766837958291),
  (26053, 17417617953925556218228977269122205986918822423),
  (26085, 17446964513973899424356407129917859246252570257),
  (26117, 17463999385453462374092206419459718522143052376),
  (26149, 17464000844013759492696563131528262799665256082)]

theorem tbl29_16_ok : tblOK 29 tbl29_16 = true := by decide +kernel

def tbl29_17 : List (Nat × Nat) := [
  (6305, 26231334247166407661270956558685800147539015249),
  (19649, 23173688684240796596941669188853792275042739729),
  (20673, 23174035419120410451410217761639418947888817681),
  (21697, 23174035419141179638844357072153540863412479505),
  (22721, 23174383868284906442148845542398588778930578961),
  (23745, 23174383867803650495199736353096706837483431441),
  (24769, 23174732316946114877351113465014657660279132761),
  (29889, 23242337145454526618024957916978379813372909203),
  (19650, 23173688684240796599424559118910350116187318100),
  (20674, 23174035419120410451418143240199652911510230872),
  (21698, 23174035419141179638852282549560848994173753176),
  (22722, 23174383868284906442148969235743366436216755729),
  (23746, 23174383867803650495199736353096425362506720785),
  (24770, 23174732316946114877351113463861736155672285785),
  (28866, 23175397135808995240823395883409197736440181339),
  (19651, 24600936378672180676849033985331497143220164244),
  (20675, 24601283111826797142189642103648552411212666517),
  (21699, 24601283111847566171167456413179118297291978582),
  (22723, 24601631560991293291382205395496346318381373012),
  (23747, 24601631561011428653507979519521124470901261907),
  (24771, 24601981553262189063443170210535533548373919316),
  (27843, 24602330002071043283007709155676690496214869520),
  (18886, 13143621750860979831276143087839948748084020687),
  (18918, 13159951662595875545684074186136328088375117395),
  (18950, 13182257851920262459891205337886123647170590289),
  (18982, 13182257825523351112930137843410786641289229904),
  (25158, 17464000844013744289554942407111068343661049425),
  (24965, 26027487000249518787711860963695478355470136913),
  (24964, 24600239307543558929107840803025658998380643922),
  (24963, 24600239307543558929107538571571041214110189138)]

theorem tbl29_17_ok : tblOK 29 tbl29_17 = true := by decide +kernel

def tbl29_18 : List (Nat × Nat) := [
  (24962, 23172990156801152340019392035040095334377551636),
  (24961, 23172990071227479593190018472760269413492527705),
  (19910, 26033770051920347186368065903078424122119018133),
  (19942, 26050109144843909833708310688639537674615875220),
  (19974, 26078413301366196819188344779182214292729865614),
  (20006, 25894036584943842543021484693562528753174042262),
  (24933, 26029229245968153935543882514078075544967132753),
  (24932, 24601981553262194054485568212735548190159353426),
  (24931, 24601981553262194054466230121988478467985978962),
  (24930, 23174732402057879978309304734930338527268901465),
  (24929, 23174732402057879978309304736083260031875748441),
  (20934, 26033770051920347163872681746431360078244534106),
  (20966, 26050107855536665022211850654445448331884050065),
  (20998, 26078414654621571407388437052226738478501947029),
  (21030, 25894733483231296624994657610935543922613933718),
  (24901, 26029229245968153935895414669046896779419035417),
  (24900, 24601981553262194054837133421963884512698279705),
  (24899, 24601981553262194054837133348194927014416066329),
  (24898, 23174732402057920167937149915549917709792776793),
  (24897, 23174732402057920167937149989336894004630983257),
  (21958, 26034118501064074204854758092673227782810621523),
  (21990, 26050107855557435546468599686190603485347919441),
  (22022, 26078763103765298454557709880816807837510756052),
  (22054, 25894733568301888336486399860384313422754993747),
  (24868, 24601981553262194054837133421964165987674990361),
  (24867, 24601981553262194054837133348195208489392776985),
  (24866, 23174732402037150959129510927678882585941997329),
  (24865, 23174732402037150959129510927696896984451479313),
  (22918, 26027487258119734758179012592730429692591781721),
  (22982, 26034118501064074206092698131935263367345030739)]

theorem tbl29_18_ok : tblOK 29 tbl29_18 = true := by decide +kernel

def tbl29_19 : List (Nat × Nat) := [
  (23014, 26050107940628027377225359210603864074426275673),
  (23046, 26078763103765303525160110793734413814794114772),
  (23078, 25895082017445615377472986354487977508255123027),
  (24836, 24601981553262194054812610766751372058079348306),
  (24835, 24601981553262194054812308535296754273808893522),
  (24834, 23174732402037150959129510927678882177925321305),
  (24833, 23174732402037150959129510927696896576434803289),
  (23942, 26027485287001296908912747735605613481490990675),
  (23974, 26027485281348837902358990403315538736203240976),
  (24006, 26026064947920724814953392607345670429091108368),
  (24038, 26050107940146669316457540450261201806383199825),
  (24070, 26070666441039311540913185703564151108523869779),
  (24102, 25895080057813820963331870758491511313489016400),
  (24803, 24601981553262194134040471049561091867352843858),
  (24802, 23174732402519787544952324513030145987620206356),
  (24801, 23174732316946114798122950950750320066735182425),
  (24998, 17601641987971041254571494665883165944840275539),
  (25030, 17417966431219046067787909573397910851677415188),
  (25062, 17446964513972925868703059937703747323864102481),
  (25094, 17463999130765537625082400559782935329786656532),
  (25126, 17464000844013744312008905985570747571757991506),
  (7329, 27524778588076776024076004513975518884919019156),
  (20705, 23174035418722338678998009322122783136140305937),
  (21729, 23174035418722343749600410235040389053159908881),
  (22753, 23174383867866070790531357808736947548923962897),
  (23777, 23174383867865952987290533818872710580136912401),
  (29921, 23264637890653057216229413922801533258476627473),
  (7362, 27524778588076888478664914196427801244026103445),
  (20706, 23174035418722338679005934800683017099761719128),
  (21730, 23174035418722343749608335712447697183921182552)]

theorem tbl29_19_ok : tblOK 29 tbl29_19 = true := by decide +kernel

def tbl29_20 : List (Nat × Nat) := [
  (22754, 23174383867866070790531481502081725206210139665),
  (23778, 23174383867865952987290533817719789075530065425),
  (28898, 23175397131822609094943636388320518189183997453),
  (20707, 24601283111428298664263940177549037203388225173),
  (21731, 24601283111428303734863923238852716298197055321),
  (22755, 24601631560572030775833584772950819253938411092),
  (23779, 24601631560572035691685267973122148007255549456),
  (27875, 24602330002091813986776990060257075745623451152),
  (19975, 13188577134922879178655680112708134217716377428),
  (20007, 13188540825542111933569937423198358262711375706),
  (20039, 36223396385690416196551637990421609868648867477),
  (23909, 26027487340531987825045101429795388460855543379),
  (23908, 24600237763997127527739224221031808162371544592),
  (23907, 24600237763997127527738921990730107484661425680),
  (23906, 23172990071291044823344187835327748552935941649),
  (23905, 23172990071291044823344187836480670057542788625),
  (20999, 27505628326964318718610537557691095283756525205),
  (21031, 27522300044592072971344102950401450611773367957),
  (21063, 27676325625130206996559893834639418525840926357),
  (23877, 26028881137106895988972099434021283281157310035),
  (23876, 24601633444400936365309813165662079234655749907),
  (23875, 24601633444400934846357129967371997038446196306),
  (23874, 23174385751801290688521114129135814060905158419),
  (23873, 23172990581693825879810869213734258078762739217),
  (22023, 27505978667929503053303434873925300452624529110),
  (22055, 27522300044612955285254607033263696317326677718),
  (22087, 27704630901008205572882049877247572414714705622),
  (23844, 24601631560572035691685565480950686799147116048),
  (23843, 24601631560572035691685263250666719044969768464),
  (23842, 23174383867865952908062371303366505389345547793)]

theorem tbl29_20_ok : tblOK 29 tbl29_20 = true := by decide +kernel

def tbl29_21 : List (Nat × Nat) := [
  (23841, 23174383867865952908062371304519426893952394769),
  (22919, 16286247321479915498037404546871648659536168657),
  (23047, 16043411449358750065107779165223710816983369563),
  (23079, 16043384657774814047757529456809277326762731351),
  (23111, 16043384652122355278881228214115280377750046291),
  (23812, 24601631560572035691685565481057365815320454672),
  (23811, 24601631560572035691685263250755665137610335760),
  (23810, 23174383867865952908062371303455451481986115089),
  (23809, 23174383867865952908062371304608372986592962065),
  (23943, 15770139371335850605728873751462186074529420944),
  (23975, 15974772409905889695995824655903771017050396176),
  (24007, 15990745422536975804513117923667325440518874896),
  (24071, 16035357811186460077442860191641096143770822161),
  (24103, 16035357811186460077442860191641096143770822160),
  (24135, 16035357811186460077442864913918632920775464464),
  (8385, 27524778588076765887823264929897714707338712724),
  (8417, 27680882685379525757982362475084324352717825553),
  (20737, 23174035418722338678998609060360264571868751377),
  (21761, 23174035418722343749601009973277870488888354321),
  (22785, 23174383867866070790512014995623113482128664081),
  (29953, 23264637805582465485994798056957881400534574609),
  (8386, 27524778588076765887823266862593731299630208660),
  (8418, 27680882685379525757982364411974151724890138129),
  (20738, 23174035418722338678998609090229518622973568529),
  (21762, 23174035418722343749601010003147120143020402193),
  (22786, 23174383867866070790512138688967891139414840849),
  (28930, 23175391687304738359928220974326799280892614157),
  (20739, 24601283111428298664263940177549032805341714069),
  (21763, 24601283111428303734863923238852716229477578585),
  (22787, 24601631560572030775833584772950814855891899988)]

theorem tbl29_21_ok : tblOK 29 tbl29_21 = true := by decide +kernel

def tbl29_22 : List (Nat × Nat) := [
  (27907, 24602330002091489468223331633530292589602874896),
  (20740, 24601283111428298664256045124284756408237070170),
  (21764, 24601283111428303734863923238378832489268164441),
  (22788, 24601631560572030775825669510143827855010469721),
  (26884, 24602330002091487555299187066397739355802510864),
  (20040, 36223401830208286929090567297364799959936099989),
  (22885, 26027487258119729687615177833415841031648523857),
  (22884, 24600237763997122611879328250118270202061559641),
  (22883, 24600237763997122611887238790558778731344287316),
  (22882, 23172990071291162626585135519689684683616015889),
  (22881, 23172990071291162626585011826344907026329839121),
  (21064, 27676674074273933852892385345373177734032090773),
  (22853, 26028881054694637764905737018787227342302386009),
  (22852, 24601633361988677883845343160663880426277119565),
  (22851, 24601633361988810779434380990536656241296688983),
  (22850, 23174385668101598656047251889946003629238661981),
  (22849, 23172990581693943820517492567224696014596548113),
  (22088, 27210476768986563358657260366993724641849468628),
  (22820, 24601631560572030775825669510146044470452062041),
  (22819, 24601631560572030775833589495317297724562462291),
  (22818, 23174383867866070790512138688969553600913200657),
  (22817, 23174383867866070790512014631299918026365019665),
  (22920, 15792440115205153233085493698612086878414657232),
  (23112, 16035706260330182202569857668995968408186812249),
  (9409, 28952024991602686847824508713557014542835585882),
  (9441, 28974325736794672026302759476625649349738964497),
  (21793, 23174035418722343749601009463686565452661990929),
  (29985, 23286938552110224104921321674420721098660562712),
  (9410, 28952024991225283510858413745053336501413566099),
  (9442, 28974325736794672028778749740950258024074827281)]

theorem tbl29_22_ok : tblOK 29 tbl29_22 = true := by decide +kernel

def tbl29_23 : List (Nat × Nat) := [
  (9474, 28974325736802517375092675096524133014177146517),
  (21794, 23174035418722343749601011398270263961852171793),
  (28962, 23175391687304738356310208227675117818290705933),
  (9475, 28974674185946248622657543523185819451361945237),
  (21795, 24601283111428303734863965740125755359538304595),
  (27939, 24602330002091489468248146996165908894958601746),
  (21796, 24601283111428303734863842141201240614903777113),
  (26916, 24602330002091487555299188460385976068536915472),
  (21829, 26027487258098960500181038524054640688377443921),
  (21828, 24600237763997122611904163751585083572299282265),
  (21827, 24600237763997122611904163752058685906251462489),
  (21826, 23172990071291162626648576225653666791975589720),
  (21825, 23172990071291162626640650748246358661214316049),
  (10465, 28974325566653488565833528254529650670081222161),
  (10497, 28974325311070853804989131822345866532233750033),
  (10529, 28659382926813018976378963762745816550110221969),
  (30017, 23286938569220079740592903511272734393742956312),
  (10466, 28974325566653488568309518009262954308290074129),
  (10498, 28974325311070853804989255663302015220366562833),
  (10530, 28659382926813018977617018122627326240739382929),
  (28994, 23175391688633297590754063852819503788510221837),
  (10499, 28974673760214582841867281471861979931598771861),
  (10531, 28659382926833788165051157437681076649371981456),
  (27971, 24602330002091489468248146997316609385003599378),
  (26948, 24602330002091487555343389735581020822023477080),
  (25925, 26029229245968153904712363285723278544152417937),
  (11489, 30401573258926288141629578149366155350329075217),
  (11521, 30401573003776820513228148409590589437615351313),
  (11553, 30423873748975351136369986354707018387924264465),
  (30049, 23309239314417636887610189346963978920160994833)]

theorem tbl29_23_ok : tblOK 29 tbl29_23 = true := by decide +kernel

def tbl29_24 : List (Nat × Nat) := [
  (11490, 30401573258926180608084492339277507835603002897),
  (11522, 30401573003776820513228148410063347551721825809),
  (11554, 30423873748975351136369986355179213689516271121),
  (11586, 30423875550290506671236538891495631633801115350),
  (29026, 23175391688531094132620450514231545621560235533),
  (11523, 30401921452920547555843480885223043959115339476),
  (11555, 30424222198119078178984109909130976950693779158),
  (11587, 30424223987637335249631997015072354103387846358),
  (28003, 24602330002091565128584619069624212823191144210),
  (11588, 30424223987637333174981388447783678025938593491),
  (26980, 24602330002091442395246553935725311035750819344),
  (25957, 26029229245968153904711758802079760630909580945),
  (12545, 30221022258654466404418141041511584691178247003),
  (12577, 30221023696980716697773739311983130827134678737),
  (12609, 30423873834004308232379471111571557860500121105),
  (12641, 30109518532661808693480060483380222494751667921),
  (30081, 23309239314417635288043928300640019583450859025),
  (12546, 30221022229534473534347603816191201251341727446),
  (12578, 30221021806468047735869689021734732275037599446),
  (12610, 30226679693697981797237935661302610848442078934),
  (12642, 30109518532661808693480060483380337776807720657),
  (29058, 23175391182196802120185201147257374740776825435),
  (12547, 30221022229534473534351230666205590130612070096),
  (12579, 30221021806468047735869689612030441552055461584),
  (12611, 30226679778520026865115822085327432964562577107),
  (12643, 30109518532661808694718000914985702088125830867),
  (28035, 24602330002511449972512206591022567315616105176),
  (12612, 30226679778516462865337228263207176176158496464),
  (12644, 30109518532661808694717999002308694958292457171),
  (27012, 24602330002008370714932486006642551006782891536)]

theorem tbl29_24_ok : tblOK 29 tbl29_24 = true := by decide +kernel

def tbl29_25 : List (Nat × Nat) := [
  (25989, 26027487000249518787711859120631758116596561553),
  (24966, 26027487000249503575904658223808039161957529169),
  (18983, 13188190570166373032761709777721094575343355475),
  (18951, 13188228685779152137668789454076562191472997969),
  (13569, 31671005896561593388190622441189892060761650897),
  (13601, 31671005896561511292823243853028671131617129934),
  (13633, 31674485885486239366747071999809115824187057681),
  (13665, 31674408720230796504923520931792711362978575822),
  (30113, 23018672190856250062946198824006822848258713105),
  (13570, 31671005896101137228159646448321911751039092439),
  (13602, 31671005896100163672481443975211772410997339859),
  (13634, 31674485885486239366747073937056877318715024913),
  (13666, 31674408720230796504923645030961268069334054350),
  (13698, 31873423992182681084031069293740966565341861719),
  (29090, 23172957987816519808037530919134447274644280846),
  (13571, 31671005896101137228159647112397964725159310800),
  (13603, 31671005896100163672481444565501134895639770832),
  (13635, 31671007696147799889576469362759550044825024211),
  (13667, 31674408720230798495745798290202592386817029843),
  (13699, 31873772425604133237374197730150036786875225943),
  (28067, 24600239307229451740857471086669014961732265488),
  (13636, 31671007696147667871527465161987229097022305744),
  (13668, 31674408720230796426164795351388928820947285715),
  (13700, 31873772425058565796162522973529381198071453266),
  (27044, 24600239307229449827933326519536461727931901456),
  (13701, 31874120874202292837265166200236443120543544913),
  (17927, 34773580566823264135385321067060869100744038036),
  (17926, 34773150963160893374248234518246716408666867283),
  (17894, 11732703969889915664601577316961023962297476688),
  (17862, 11716374058155019950217858459113913437274572239)]

theorem tbl29_25_ok : tblOK 29 tbl29_25 = true := by decide +kernel

def tbl29_26 : List (Nat × Nat) := [
  (17925, 34773282470266814431726437390122530756344497806),
  (17893, 11732703969897743779428908667746451120916088402),
  (17861, 11710049329810286161022893205964681881872057938),
  (17829, 11687743139971216789583038182258209905982916178),
  (17797, 11671769170275308040996049485299978989451945552),
  (14625, 31693257635452024463203274800537639807492097487),
  (14657, 31691515899158305102233487679428868617943188943),
  (14689, 31691515391062617260148253771042092994339341775),
  (14721, 31873422345078639711525922009625236756164322833),
  (14753, 31559453164260840730447056066492446418265769423),
  (30145, 23019020639833210062807100411746912966919923217),
  (14626, 31693257635452024463203396997421838641958553039),
  (14658, 31693335238561957052337805831074933040513119955),
  (14690, 31691515391062617260654892192332582234113246671),
  (14722, 31698534338433013616510982329065675850111054423),
  (14754, 31559453164260840730953694487782935658039674319),
  (29122, 23170867296941841787157247107050820452225979917),
  (14627, 31693257635452026464065674310514824623276504784),
  (14659, 31693259442244749771281596735188087748429690575),
  (14691, 31691515391062619254801605549111501424022369744),
  (14723, 31698534406452102463317224255935084910454290263),
  (14755, 31559453164260842725100407844561854847948797392),
  (14660, 31693259441700135916578233449786670412450301391),
  (14692, 31691515391062617181426729678068240242522785231),
  (14724, 31698534405906509198836575393879820700833142352),
  (14756, 31559453164260840651725531973518593666449212879),
  (14725, 31698534490977101008292015590090126316523345488),
  (14757, 31559454970508987355481672703314425721140348367),
  (16870, 11732703858009304363602001656128826839443514897),
  (16838, 11716025608847735558187424893217192672255612431)]

theorem tbl29_26_ok : tblOK 29 tbl29_26 = true := by decide +kernel

def tbl29_27 : List (Nat × Nat) := [
  (16869, 11732703890143740246858063256452211112215402260),
  (16837, 11716025864540194110130543645972710429758146321),
  (16805, 11693726400279068285318789584336642418921260817),
  (16773, 11671420721131596211816665728454786818168137233),
  (16868, 11732703890143740245753709520234247362195052308),
  (16836, 11716025864540194110135053358368827834479511316),
  (16804, 11693726400279068285323299296733041229899859732),
  (16772, 11671418843225117868095612911094980916091627025),
  (16740, 11649119380272775386356165519800307844151346966),
  (16708, 11626813786216659160013119446884136169998722577),
  (16867, 11732703859338419518798965026393473855679178257),
  (16835, 11716025864059510748891272490748148246081771023),
  (16803, 11693726400278950144859265694169404676460586513),
  (16771, 11671418842743897830167657156086014704661653265),
  (16739, 11649119380272657716328583199502573913396069905),
  (16707, 11626813786216659158775132554045901703614632728),
  (15649, 10177264666376236651016143448825510492235699728),
  (15681, 10199564127371785047754797648701207228068242763),
  (15713, 10221871686237140171390980131384912294221780496),
  (15745, 10244171150017051188341780307402604447780111196),
  (15777, 10266478706219454112376133011925686798116787728),
  (15650, 10177264666376236651016143448807496093726217744),
  (15682, 10199564127371785047754792926334724358423029067),
  (15714, 10221871686237140171390980131366897895712298512),
  (15746, 10244171150017051188341780307402600049733600092),
  (15778, 10266478706248057947474067323928823418325403412),
  (15810, 33323037081120301535732314377529029047967123221),
  (15651, 10177264666376236681021860615182645654071612944),
  (15683, 10199564127874884109723743675896972057963992592),
  (15715, 10221871686237262990959264439694548690156226326)]

theorem tbl29_27_ok : tblOK 29 tbl29_27 = true := by decide +kernel

def tbl29_28 : List (Nat × Nat) := [
  (15747, 10244171150519157908040944015060420766773643030),
  (15779, 10266478706248057948521299315241772055680878356),
  (15811, 33323326406181682357538885594756331568656364252),
  (15684, 10199566092180431839580779779479264219288901136),
  (15716, 10221871686237262990959264440847465796699784982),
  (15748, 10244171150519157908040944015078430766162872086),
  (15780, 10266478706248057948521304036455051945742534420),
  (15812, 33323326406181677366183947757093149174376256348),
  (15749, 10244173027099004265718405054566463013887493905),
  (15781, 10266478706248057959655539243112449268019971857),
  (15813, 33323674843528505944598748737415145861437276956),
  (15814, 33323672789513882365750602472128275803599652435)]

theorem tbl29_28_ok : tblOK 29 tbl29_28 = true := by decide +kernel

def tbl29 : List (Nat × Nat) := tbl29_0 ++ tbl29_1 ++ tbl29_2 ++ tbl29_3 ++ tbl29_4 ++ tbl29_5 ++ tbl29_6 ++ tbl29_7 ++ tbl29_8 ++ tbl29_9 ++ tbl29_10 ++ tbl29_11 ++ tbl29_12 ++ tbl29_13 ++ tbl29_14 ++ tbl29_15 ++ tbl29_16 ++ tbl29_17 ++ tbl29_18 ++ tbl29_19 ++ tbl29_20 ++ tbl29_21 ++ tbl29_22 ++ tbl29_23 ++ tbl29_24 ++ tbl29_25 ++ tbl29_26 ++ tbl29_27 ++ tbl29_28

def mask29 : Nat := 59937343014637126029575117604812587410319599155124425006796411998004188380808042038646400227095052904765963511879288457735083135182663409723296576798318392491005840412815078337058611470058801534113941550186791528777864442738103684774101188855798829160806058864762369264372447469583808904247385373281856496947634475573714986073311708558017055287344080218984171025611918826214286537068149303936400394076723693521480677120159926406239144895654462038584327225164273929522055685797084057382747522743891657031230802718748945465852998381184360175058142288050474298403042029142519757045874905688131291741682022056549918887519424626891757934447661173861543276330885361192538137269295702334093606336431397214452398701012543995624089850289280946281411684584948431000723369699968718470995423484113131375693133583251843720568269696575235797470257842022620160449193781405790062316151441445643612227935166963971614292137950698214488742304753705224735562589064867972250622016747565326676592544933846612275551034025163601301744530121183547400133132557697001654760512912456062929973459925439089452582360062077399880361454530818220006186747634719835398825061629988470905886597103624009414031097632714100001023717604057493918164334513984466951276824783211311009827598746523633651766975436943914201607526207929556092273562826470325477305973940640606168454526550020438906582889752301424345767530065375883516071994387454640322982095135737912453444574228288830921636832610576045596016055118627699131093322344789464395849077193037663561249125642147166396225799449402173643673574494417852332188122128461787111732376426657012461648649674002219420161727989527854222725363798566679243508036582791562718321406501614262484669923936443048070265481195332814795730685824297800619540225553478513412410797063490081197427658031244777034012667538580043785105450471930007447972158270964547072422329007615848314074448517567342457020027838094376116770196638752420699016204521075633825751899017108982624902054148156846851043860369082310256444277035678114819517185254910993634228921002926588860865061305708814721661163732285043110386907277540402022165425646760595755263189889780912153628405746005868460300427357273493663060462146022249860272035784651590841619782952458736182917738450428451545174504951866325834748966359204053492174693632241299965183703365063638651322810082508402824758294392223996192279552348243745030303863347387623678446168376798118849281956916579409835128143298117823029292292873520055756508390417462996207013573412617427255552478015181363647095391037181129590912608759548744815107960633384080061489954223543174157932023310682791891399002652711832445267580234561328652927202211184550882340580643866618966295500841756938535143414325093079836322452154316558803422907237921382589851991819398698894078349930708111014147035188898082419272976780438533785119248228103179307728508189223591302061573813492868873905997577872397310080671709374107710415088961159728972110878723280861410791305298571977384500077290237962887965961822482739317496839603723614425229631580726261380234829906253854754645104111964515589583951896797710866593408278173531514358154905424074172508373345861208312354094926394642889941112423233208483700189301437109942680242856819427109831958250938267563175141268429736350338261374595854403170672115014950687374314241607464425877041746602790528710326711343328581222461141820659693354475201186274162384941646814595281871819942802444335307170200445160128621982852392254010670553882956934961252722319946007659543111279407246441971220319448036290221923006127243061799952518787911421748101254582342239661798357853950987511970728611068398613911749251350968187697708259665388205339635409804085086943666884312439717349047863646803980209611465045684682831541724870553065485645994606636744001603070969864962192540977044883668732189804784791503352784482952650183838481638141769437498676641265161804370084441113013279233308967390483071593959485445782145163230220377153865408817462653969457872510394351858413348923449809500015863289552281863409647019822647323327888012515262138711173216057192890423731106130681745192330310371604555740359586295440936956525437774889164626729311434778981955253178981711748023126550601791633292006228359711357374926004459742417601346478748078017443407370040120819804589547362187455503919090490931350707892908335131982783387993157723035551673851843025210266076762210101397787887366134468301917089929378739842856405923394979560989351605877748674318025438730649096473682374186128067027771832664059641618029544885226405514108591837463996182287605201098379257182930033390592192275266679753067753908890335787872167194084929184949905121214627160741301291692758399321131968218617896592170834383666837434011789046140198218735130629838881309915073014333213785136600672525049067840089740800263514694977475463086646477233065847468074237137549291559953073549094733787921598144927108132535119770759073490803761706157388819164543413445376430544147110436071078544843662652923920302082318390269159637676972199429544225914921104744567145737184934275693891534006395393395640030349413304154332148443369469544423836563791233567148354195765743660494569222883528066336025244380605673349386129854001632878761958753645421586361968967604726851189622808940732733424907694503060092963470317596444996152195590216041067471467655833292134907008402491325025934238999619823309881307747081345805016591150324156143457581205904713208139774283712478625059952289092255401574040819866581879335832806786150460909148748451867595554012837730534964574410488182035407164661730861344894516809041461722420073617525141574274073669910824042345080855547201188783503412782489367059443170313954109918872177654563894498014567473305050908352497031378080243114242412792446637918074727230733172652854101325650915583272298737572383335668163144947634873108261881246586700457816538763044323723480585478402563247432250994408750228312385578803511872183146784867636842428784518709844067421108137303021052070267149588797390523455575981316070232181117122817136762901014144166469928702193471018215117069433366231893057874073522131179152277705382514493851346560660396366213358011819713944647965651389159160997112306669110302395234277740756246959625796989708303921175704345902879294460403408435895321649438194094091859036792083326895361286104035334405051723642165596558770583486884664686063956109972383031406345473754256332449463235888597542675747979513623936436765440918508591896683236039388414528104917351277197343137606455111407072323551865494557293073428670855329293340291995376170026246215778707551167851534353221386741797996610411772802487435509361310044441306813624112585463057692588609982002662612334534575817718980054185357799721595718358831893225589181745090331392677145828407083702296581741282985833776159182879529220344272178013988335006385983472457812480316465973303504406529233037499097848129379893887333829710667259753579352463162787215891811622390897212714958009054609443945632006431724095641480899548642472689850785356114307356322730024974669355907236613236784787965195509854876969242277019223146551331181463352349366054724130511584157829000135152779921745196714281436650213760536059145236826937319191625404013182962167398036923836606144738888336538867196614823878482614959825541252822111203637637679061012116848615967598509955662226243937550596635783860407799742978448689448391221791194849444024129406374183969458667467756269457167700319345500192475613284536379127178281915657013956038678871841528689643436059072417298457039486042885418365332489261691296158140850234750562156101789819113269402707267271874044259147884471549902363684587418788039779155123950567037780113413924351402381519856141341306908457173323795842083422525198035594447241511910897301148170424723236534834346887948097912009305519621993120871316363872701363342296888349673211917081712721616871672456441523563326159586620887157249630185205177620866764794257498098151069005166966992527641691175747664413113935079709607723480354081994477999357953471346620623835232162578852575195582599368111577601214018503063066365864590783956087425877626467836040919840145193852027672319372042044568603172321538250245201478413711978472082226129028698240371322020944386119694692767234508340249907592800353026169372144661818494460739968693162232288623455991078253785981941374527254105330194611543507007245859426602094420859110694829133102114067211090070445531500265202044838244679871033299604382377890952106980724439523677297183877861965342209111234420161651404064276829196531977838811154516725301817781920412775839772079910987155787731122783170834730183225679840908314102979027700915958751372119483159216914794115351557836848805028691128917632762279260528080656119507230372382007386322948802774074020572932735099220332608526696331727175213251775462313526175107363041530509388999252375448627039955930861466598211068365732544966102440165125959389086588076685227752220760553329048766392824751355592157643792607530594924949575230740522087226138776642518409428360417224598337636039960463105999011053837091669935399730368100399249223333061134943854796348182159077768881189297418456861529417745634716483159615156220477477281414604179693187212221607941157381302733472116698703921049347562375794389296349184

theorem mask29_eq : maskL 0 (tbl29.map Prod.fst) = mask29 := by decide +kernel

theorem cov29_1 : coverX 29 mask29 1 = true := by decide +kernel
theorem cov29_2 : coverX 29 mask29 2 = true := by decide +kernel
theorem cov29_3 : coverX 29 mask29 3 = true := by decide +kernel
theorem cov29_4 : coverX 29 mask29 4 = true := by decide +kernel
theorem cov29_5 : coverX 29 mask29 5 = true := by decide +kernel
theorem cov29_6 : coverX 29 mask29 6 = true := by decide +kernel
theorem cov29_7 : coverX 29 mask29 7 = true := by decide +kernel
theorem cov29_8 : coverX 29 mask29 8 = true := by decide +kernel
theorem cov29_9 : coverX 29 mask29 9 = true := by decide +kernel
theorem cov29_10 : coverX 29 mask29 10 = true := by decide +kernel
theorem cov29_11 : coverX 29 mask29 11 = true := by decide +kernel
theorem cov29_12 : coverX 29 mask29 12 = true := by decide +kernel
theorem cov29_13 : coverX 29 mask29 13 = true := by decide +kernel
theorem cov29_14 : coverX 29 mask29 14 = true := by decide +kernel
theorem cov29_15 : coverX 29 mask29 15 = true := by decide +kernel
theorem cov29_16 : coverX 29 mask29 16 = true := by decide +kernel
theorem cov29_17 : coverX 29 mask29 17 = true := by decide +kernel
theorem cov29_18 : coverX 29 mask29 18 = true := by decide +kernel
theorem cov29_19 : coverX 29 mask29 19 = true := by decide +kernel
theorem cov29_20 : coverX 29 mask29 20 = true := by decide +kernel
theorem cov29_21 : coverX 29 mask29 21 = true := by decide +kernel
theorem cov29_22 : coverX 29 mask29 22 = true := by decide +kernel
theorem cov29_23 : coverX 29 mask29 23 = true := by decide +kernel
theorem cov29_24 : coverX 29 mask29 24 = true := by decide +kernel
theorem cov29_25 : coverX 29 mask29 25 = true := by decide +kernel
theorem cov29_26 : coverX 29 mask29 26 = true := by decide +kernel
theorem cov29_27 : coverX 29 mask29 27 = true := by decide +kernel
theorem cov29_28 : coverX 29 mask29 28 = true := by decide +kernel
theorem cov29_29 : coverX 29 mask29 29 = true := by decide +kernel

theorem cert29 : Cert 29 tbl29 := by
  refine ⟨by simp only [tbl29, tblOK_append, tbl29_0_ok, tbl29_1_ok, tbl29_2_ok, tbl29_3_ok, tbl29_4_ok, tbl29_5_ok, tbl29_6_ok, tbl29_7_ok, tbl29_8_ok, tbl29_9_ok, tbl29_10_ok, tbl29_11_ok, tbl29_12_ok, tbl29_13_ok, tbl29_14_ok, tbl29_15_ok, tbl29_16_ok, tbl29_17_ok, tbl29_18_ok, tbl29_19_ok, tbl29_20_ok, tbl29_21_ok, tbl29_22_ok, tbl29_23_ok, tbl29_24_ok, tbl29_25_ok, tbl29_26_ok, tbl29_27_ok, tbl29_28_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask29_eq]
  interval_cases x
  exacts [cov29_1, cov29_2, cov29_3, cov29_4, cov29_5, cov29_6, cov29_7, cov29_8, cov29_9, cov29_10, cov29_11, cov29_12, cov29_13, cov29_14, cov29_15, cov29_16, cov29_17, cov29_18, cov29_19, cov29_20, cov29_21, cov29_22, cov29_23, cov29_24, cov29_25, cov29_26, cov29_27, cov29_28, cov29_29]

/-! ### `N = 30`: 948 witness orderings -/

def tbl30_0 : List (Nat × Nat) := [
  (16705, 765478372208840380606779279476505126398984529489),
  (16737, 745565858902094584862926074278952035627331556121),
  (16769, 746993542669016830918136063618445976560901367377),
  (16801, 748420708352259064454098104618679624804672533966),
  (16833, 749848391949213477454946713433979133331397486161),
  (16865, 750893054049194853734455172526301154093697410641),
  (25089, 1657416189659883550446866583474182450462357538451),
  (26113, 1657416189686261072602021087956712361589111867027),
  (27137, 1209399471905694704751118353421366537026346235474),
  (28161, 1209399471905694704751118353421366537025272493650),
  (29185, 1290529959287588435521480201039413418123309950609),
  (30209, 1290529959287588435521480201039431432521819170385),
  (31233, 1381896030367641591651650921279360070226831263577),
  (17729, 1483071467335898764262722345056750043128743147090),
  (17761, 1483071467335898764025037857516262873357324990034),
  (17793, 1483071467330581852279582681567440657896835462738),
  (17825, 1483071467330438415078865656954202502935740757586),
  (17857, 1473080384952598964496851183519545911609321137743),
  (17889, 1473080733401886453336355958745317002290474071634),
  (25121, 1657307494539475899473313958534894050568440202899),
  (26145, 1657307496073198940719105441684148264270157923987),
  (27169, 1209238091541707286037036100857850835310871938642),
  (28193, 1209238091541707286037016758045889922204300288666),
  (29217, 1290593991335835754912152602835525020021273207579),
  (30241, 1290591236408463934998567487473801048030371194447),
  (31265, 1381896079042222569666693328451425551763399628370),
  (18785, 1483071474411213926346156623682962273596911990417),
  (18817, 1483071474411213911768115181461708698847924270737),
  (18849, 1483071474411213911766877241422423318573025146513),
  (18881, 1473080303983053436728541895177670417262673467023)]

theorem tbl30_0_ok : tblOK 30 tbl30_0 = true := by decide +kernel

def tbl30_1 : List (Nat × Nat) := [
  (18913, 1473080652517267664784753471201441732553440835217),
  (26177, 1117894239235460924036338560568281742081776760465),
  (27201, 1209238091568642356422830920637346806359161124433),
  (28225, 1209238091568642356422830920637346806358087382609),
  (29249, 1292021240743204336881476506967891362332007544401),
  (30273, 1292021240743204336881476506968363378199222150737),
  (31297, 1383362343594861048086422024946303018240569366097),
  (19809, 1483071474411213926346156623682962273596911986321),
  (19841, 1483071474411213911768115181461708698847924266641),
  (19873, 1483071474411213911766877241422423318573025142417),
  (19905, 1473080303983053436728541895177670417262656689807),
  (19937, 1473080652517267664784753471201441732553440831121),
  (26209, 1117894239235460924036338560568281742081776756369),
  (27233, 1209238091568642356422830920637346806359161120337),
  (28257, 1209238091568642356422830920637346806358087378513),
  (29281, 1292021240743204336881476506967891362332007540305),
  (30305, 1292021240743204336881476506968363378198148408913),
  (31329, 1383362343594861048086422024946303018239495624273),
  (20865, 1483071364589467123697276378629705491885690791505),
  (20897, 1483071364142598368082403225498274332977688815185),
  (20929, 1473147184415053199517164036930459552326599906895),
  (20961, 1473147532949288287452453251426915326025761629777),
  (27265, 1209238091568642361493432396481789682454755878481),
  (28289, 1209238091568642361493432396481789682453682136657),
  (29313, 1293448488436223745795093208494346788425942263637),
  (30337, 1293448488436223745795093208494346788425942263573),
  (31361, 1384789591287880456999591665491739322034483975826),
  (21889, 1483071364589467123697276378629705491816971314769),
  (21921, 1483071364142598368082403225498274332908969338449),
  (21953, 1473147184415053199517164036930459270851623196239)]

theorem tbl30_1_ok : tblOK 30 tbl30_1 = true := by decide +kernel

def tbl30_2 : List (Nat × Nat) := [
  (21985, 1473147532949288287452453251426915325957042153041),
  (27297, 1209238091568647599891238156809855105854802847634),
  (28321, 1209238091568647599891238156809855105852705695506),
  (29345, 1293448488436223745795093209741769606531435325270),
  (30369, 1293448488436223745795093209741769606531435325206),
  (31393, 1384789591287880456999591665491739322034483971730),
  (22945, 1483071364143927920596646880233904804789638211153),
  (22977, 1473169485160583382870922660336006930520973321809),
  (23009, 1473169833694487142594072864098661990336086746705),
  (28353, 1209238091568647599891238157390927544176636942226),
  (29377, 1294875736126271249684581663965411483149210871639),
  (30401, 1294875736126271249684581663965411483149210871575),
  (31425, 1386221732136160157928802397896170255446807963479),
  (23937, 1483071364590796027175650656551167777660498159185),
  (23969, 1483071364143927920517418717719640467196094260817),
  (24001, 1473169485160582631530253160325583236937230128655),
  (24033, 1473169833694487142514844701584397652742542796369),
  (28385, 1209243366689304990389127603393457998494730630738),
  (29409, 1294875736126271249684581663965411483149210871638),
  (30433, 1294875736126271249684581663965411483149210871574),
  (31457, 1386221732136160157928802397896170255446807963478),
  (24993, 1483431028905239001914309261494392971871162545746),
  (25025, 1473191884757327491700893176454180073726813001297),
  (25057, 1473192231842868959666872959269313307852640953937),
  (29441, 1296302983905377029265331739481584736884097369746),
  (30465, 1296302983905377029265331739481483955847993041564),
  (31489, 1387649328277550909330745654945324586807306081874),
  (26017, 1483431028905239001914309261490934207358415746706),
  (26049, 1473191884757327491700893176454180073726813001233),
  (26081, 1473192233398214318950447886351774686323265582738)]

theorem tbl30_2_ok : tblOK 30 tbl30_2 = true := by decide +kernel

def tbl30_3 : List (Nat × Nat) := [
  (29473, 1296302982192149139468308962475847544309357548120),
  (30497, 1296302982192149139468309086508275678338941491096),
  (31521, 1387649328277550909330745654945324586807677428317),
  (27073, 1473217663953951300296940805127777877269371496017),
  (27105, 1473214534143412849573589421995794042177015330386),
  (30529, 1297730229877913040533219790973112990323991450194),
  (31553, 1389076575970256869034392255764487152668738921115),
  (28097, 1473217663953951300296940805127777877268297754193),
  (28129, 1473214534143412849573589421995794042175941588562),
  (30561, 1297730229877913038616137869133429304428818178314),
  (31585, 1389076575970256869034392255764487152668738921114),
  (29153, 1473239882700823024039381223324127643509867521881),
  (31617, 1389073733761928996227911527958101498331973838548),
  (30177, 1473239882700823024039381223324127758955327047577),
  (31649, 1389076581426824210729930352384413608760278000014),
  (18497, 1483115628407831805012928813150063515329233229454),
  (19521, 1483115628407831805012928813150063515329216452238),
  (20545, 1483137929153030660154623402493067544504670132121),
  (21569, 1483137929153030660154623402493049530106160650137),
  (22593, 1483160229898161588087030207425431949078395656089),
  (23617, 1483160229898161588086985516273744888344379692824),
  (24641, 1483182618607681525725077459480621355671133427278),
  (25665, 1483182618607681525725077459480621355671133427214),
  (26689, 1483203111864952850063569935993059264816986789390),
  (27713, 1483203111864952850063569935993041250418477307406),
  (28737, 1483225423492314565520691044238711422070641993297),
  (29761, 1483225423492314565520691044238711413274549233233),
  (30785, 1487529814410564933490106939284517376181384066641),
  (17730, 744138693399255116272047172228343484211810088530),
  (17762, 745565858903423812858711037005408410599159051856)]

theorem tbl30_3_ok : tblOK 30 tbl30_3 = true := by decide +kernel

def tbl30_4 : List (Nat × Nat) := [
  (17794, 746993542669016830918136063617293055056294520400),
  (17826, 748420708352259715304901548100200420534420600656),
  (17858, 749848391949275892234175486680595240434428139090),
  (17890, 750893054049194863876108783236322987557034206800),
  (17922, 2232625625021890657257478474422124471695273449107),
  (25122, 1657307440778837004351455903097245092659359725136),
  (26146, 1657307538948846017523543399150182694672076232341),
  (27170, 1209397326872368667397535313526874412336845972254),
  (28194, 1209397326872368667397535313526874412268126495518),
  (29218, 1300744028298153812599153006016589799129176696661),
  (30242, 1300744028298153950556755036246924429586574147998),
  (30145, 1473217663953951300296940805128966809978810738257),
  (18786, 1574415326744622825956355231093573232492761400979),
  (18818, 1574415222365837326705726889538729171673003935379),
  (18850, 1574415221940484368054552634341409599346242307731),
  (18882, 1574820214095252802022697919057307747500365797012),
  (18914, 1575862348078353683367192370675103475643228440211),
  (18946, 1589071765430125115762000475996832085747636197011),
  (26178, 1117919670067618609662702540259884995316632864403),
  (27202, 1209263522401240780165387186985081883024393103061),
  (28226, 1209263522401240780165387186985081883024393102997),
  (29250, 1300610251049551982535380868776922503501597730645),
  (30274, 1300610251049552120492982899007257133958995181982),
  (30113, 1483230617667539937035342272266853837767642834578),
  (19810, 1574415326744622825956355231093573232492761400978),
  (19842, 1574415222365837326705726889538729171673003935378),
  (19874, 1574415221940484368054552634341409599346242307730),
  (19906, 1574820186877980360330760505478954381200030258836),
  (19938, 1575862348078353683367192370675103475643228440210),
  (19970, 1589071765430125175965639148262344688672250881749)]

theorem tbl30_4_ok : tblOK 30 tbl30_4 = true := by decide +kernel

def tbl30_5 : List (Nat × Nat) := [
  (26210, 1117919670067618609662702540259884995316632864402),
  (27234, 1209263522401240779988456699455422661701479782100),
  (28258, 1209263522401240779988456699455422661701479782036),
  (29282, 1300610223661636042991733466000939172548668905108),
  (30306, 1300610223661636042991733466000939260302465516182),
  (30081, 1483230617667539937035342207914234215127265175186),
  (20866, 1574415222367166559534957178484997063639589021397),
  (20898, 1574415221920297671237555470413648335822849324949),
  (20930, 1574842487703435996574283859942836901988582155990),
  (20962, 1575862353524200782880370811544079024256876668498),
  (20994, 1590364187480584562921327899466971920276060206803),
  (27266, 1209263522400800366726204890474340451022167991890),
  (28290, 1209263522401261533964083631747539058944539977493),
  (29314, 1300610223741893010685730151121290606570261276373),
  (30338, 1300610223741893148612115284746549044975714821846),
  (30049, 1483230617666210709065885032460983625473909712662),
  (21890, 1574415222367166559534957178484997063639589021396),
  (21922, 1574415221920297671237553052563198056866123659161),
  (21954, 1574842487703435023177079209691185227707608327894),
  (21986, 1575862353524200782880370811544079019858830157394),
  (22018, 1590364165706500763968620985429708465823735707347),
  (27298, 1209263522400800366726204890474340446624121480786),
  (28322, 1209263522401260560408422656024637133182509610774),
  (29346, 1300610223741892037130069175841108849732684707542),
  (30370, 1300610223741892175214910634494897370694740993750),
  (30017, 1483230616549764742028313176250219181912495506206),
  (22946, 1574415221921627223751872284049696798617119795097),
  (22978, 1574864788448633553673000659799119227000764826014),
  (23010, 1575862358939247500637887329858552986131961259929),
  (23042, 1591791413395178150524563562012961917006371481367)]

theorem tbl30_5_ok : tblOK 30 tbl30_5 = true := by decide +kernel

def tbl30_6 : List (Nat × Nat) := [
  (28354, 1209263522400800691244763961093882775058326005657),
  (29378, 1300610223826962628860303791706953908960140818261),
  (30402, 1300610223826962766817925164750402373484333564318),
  (29985, 1483230616549764743206789225110273943435029563289),
  (23938, 1574415222368495463012188435931174087564446176916),
  (23970, 1574415221921627223672644121535432461023575844761),
  (24002, 1574864788448633553672981316986005392933969527198),
  (24034, 1575862358939247500637887325136186503262316046233),
  (24066, 1591791413395177501487456221990397794115133237016),
  (28386, 1209263522401177483658686099217238522099090613022),
  (29410, 1300610223826962628860303791706953908960140814165),
  (30434, 1300610223826962766817905821937288539417538265502),
  (29953, 1483230616549764743206789225110274224910006273945),
  (24994, 1574772736178339099232032579931645991235632838226),
  (25026, 1574776979094273017926290258133284905837258172245),
  (25058, 1575862364383765650624669825502030650356169782866),
  (25090, 1593218658689620630543366360108750650595802961555),
  (29442, 1300610570049315969206573859533117016053306967699),
  (30466, 1300610570049315969206573859532998502162389086876),
  (29921, 1483225423515142472908887059163841565266725590930),
  (26018, 1574772736205094396948456521705944765977561257621),
  (26050, 1574775585382266387101337770550793856235896919700),
  (26082, 1575862364383765650624669825502036522085395040082),
  (26114, 1593219007138764393067389597714364195954228541135),
  (29474, 1300610918498459696247562528592215435885064303261),
  (30498, 1300610920810362213047379882354472676351616308749),
  (29889, 1483225423515142472909295945092948333803377797013),
  (27074, 1574775585467839431149198277507838607436002485974),
  (27106, 1575862369828140084158968518534246989827324347986),
  (27138, 1594646603280614369024951468047937380897765012249)]

theorem tbl30_6_ok : tblOK 30 tbl30_6 = true := by decide +kernel

def tbl30_7 : List (Nat × Nat) := [
  (30530, 1300611266947603423288566370614941851768043156121),
  (29857, 1483225423492314565548257637283468429581781870489),
  (28098, 1574775585467839431180415174112914799487945605534),
  (28130, 1575862369828140084158949175794920131510984057498),
  (28162, 1594646951729758135987125155484532080074646418755),
  (30562, 1300611615396747150329552919774813989001971418371),
  (29825, 1483225423492314565548257637283468327286682986393),
  (29154, 1280497057479090433654645319983036430414344159899),
  (29186, 1300744028298153812599153006379902217943572375381),
  (29793, 1483225423492314565520729829921218338970984814489),
  (30178, 1280497062942324603854831327511519043720533520988),
  (30210, 1300744028298153950556755036246924429586574152094),
  (18529, 1483116075901866657900478621380955144758188394131),
  (19553, 1483116075901866657900478621380955144758188394130),
  (20577, 1483138382091574652438661494343787349630747485773),
  (21601, 1483138382091574652438661494343787349562028009037),
  (22625, 1483160688278653366834361525324998973181404451481),
  (23649, 1483160688278653366834361525324998968783357940377),
  (24673, 1483182967587400177615006739184446436545607849620),
  (25697, 1483182967247118135212621934147674481805164369556),
  (26721, 1483205267992308173134996324636120958683466764953),
  (27745, 1483205267992308173134996324636120958682393023129),
  (28769, 1483225423492314565520729829891040017082532308561),
  (30817, 1487532663524292620553424197500965567933634332505),
  (17731, 744138693399255116272047172228343202736833377874),
  (17763, 745565858903423812858711037005390396200649569872),
  (17795, 746993542669016832923847927682972332165253682770),
  (17827, 748420708352259715304901548100200420465701123920),
  (17859, 749848391949275892234175486680667267244287972946),
  (17891, 750893054049194863876108783236322706082057496144)]

theorem tbl30_7_ok : tblOK 30 tbl30_7 = true := by decide +kernel

def tbl30_8 : List (Nat × Nat) := [
  (17923, 2232625619577206430749799600128752888301298738900),
  (25123, 1657307440778837004351455903097227078260850243152),
  (26147, 1657307538948839481995786311329618598062122682003),
  (27171, 1209397326872368667397543257746097326386610464665),
  (28195, 1209397326872368667397543257672310350091772258201),
  (29219, 1300741273370781992676979681627800446767539237594),
  (29122, 1574775585297698109762343912150892865314664048469),
  (29121, 1473217663953951300296940805128948795580301518481),
  (18787, 1574415326744622827923555824014830901357345851027),
  (18819, 1574415222365837326705726889833750984858883409555),
  (18851, 1574415221918968118721970757141056860906159683216),
  (18883, 1574817431951937733235578480970164838763616093843),
  (18915, 1575862348078353685360179047701097494643180127891),
  (18947, 1589071759985440889254321601703460502353661486804),
  (26179, 1117919670067618611655689217285879014316584552083),
  (27203, 1209263522401240780165387311106232564597233575835),
  (28227, 1209263522401240780165387311106232564597233575834),
  (29251, 1300607468735593415896551441492149630112254740115),
  (29090, 1574574470000655508891343662462953142331931711314),
  (29089, 1483230617667539937035342272266381167227036845714),
  (19811, 1574415326744622827923555824014830901357345851026),
  (19843, 1574415222365837326705726889833750984858883409554),
  (19875, 1574415221918968118721970757141056860906159679120),
  (19907, 1574817431951937733235578480970164838763616093842),
  (19939, 1575862348078353685360179047701097494643180127890),
  (19971, 1588937982736839059190549464463793206726082520788),
  (26211, 1117919670067618611655689217285879014316584552082),
  (27235, 1209263522401240779988464601681792082939701913499),
  (28259, 1209263522401240779988464601681792082939701913498),
  (29283, 1300607468735593415896551441492149630112254740114)]

theorem tbl30_8_ok : tblOK 30 tbl30_8 = true := by decide +kernel

def tbl30_9 : List (Nat × Nat) := [
  (29058, 1574574470000655508891343662463095287195170592594),
  (29057, 1483230617667539937035342207913761544586659186322),
  (20867, 1574415222367166559534957178484998185141382244053),
  (20899, 1574415221920297671237555470413648335822849320853),
  (20931, 1574839732776064176660696647872153971876598769366),
  (20963, 1575862353524200782880370811544079024256859891282),
  (20995, 1590364160261982893223742549815015179374258415319),
  (27267, 1209263522400800366726204890474340451022151214674),
  (28291, 1209263522401261533964091561422663943543775094684),
  (29315, 1300607468814521190763556826732501254208623031003),
  (29026, 1574574469999325956377010329471285322826097727318),
  (29025, 1483230617666210709065885032460983625473909712726),
  (21891, 1574415222367166559534957178484998185141382244052),
  (21923, 1574415221920297671237553052563198056866123397017),
  (21955, 1574839732776063203263491997620502297595624941270),
  (21987, 1575862353524200782880370811544079019858813380178),
  (22019, 1590364160261982893223742549741228203079420208855),
  (27299, 1209263522400800366726204890474340446624104703570),
  (28323, 1209263522401260560408430584580347580481621554966),
  (29347, 1300607468814520217207895851452320933748671866579),
  (28994, 1574574468882946174416042807942482372810514974546),
  (28993, 1483230616549764742028313176250211787886251579220),
  (22947, 1574415221921627223751872284049696798617119532953),
  (22979, 1574862033521261733759415543933496478048781152990),
  (23011, 1575862358939247500637887329858552986131960997785),
  (23043, 1591791407949331051783900210525274738305637934871),
  (28355, 1209263522400800691244763961093882775058325743513),
  (29379, 1300607468899590808938130467318164556599577096922),
  (28962, 1574574468882946175590554452965749660366677554770),
  (28961, 1483230616549764743206789225110273827989570037593)]

theorem tbl30_9_ok : tblOK 30 tbl30_9 = true := by decide +kernel

def tbl30_10 : List (Nat × Nat) := [
  (23939, 1574415222368495463012188435931175209108002920084),
  (23971, 1574415221921627223672644121535432461023575582617),
  (24003, 1574862033521261733759396201120382643981985854174),
  (24035, 1575862358939247500637887325136186503262315784089),
  (24067, 1591791407949330402746792864690833310691284346648),
  (28387, 1209263522401177483658694043362674459922736375705),
  (29411, 1300607468899590808938130467318164556598503355098),
  (28930, 1574574468882946175590554452965749660435397031506),
  (28929, 1483230616549764743206789225110274109464546748249),
  (24995, 1574772736178339099263410120438718131841497642578),
  (25027, 1574772852148397772780232249418078388586192122586),
  (25059, 1575862364383765778367926374562976510672456988242),
  (25091, 1593218653244936404035687485815379067201828251348),
  (29443, 1300607463455072938203115051904170837690211971802),
  (28898, 1574569275848323889057397981251029376591788848722),
  (28897, 1483225423515142472908887059163841449479865980754),
  (26019, 1574772736205094396948464034923983498477686347413),
  (26051, 1574772830454894532010370830169100506739202410131),
  (26083, 1575862364383765778367926374562982382401682245458),
  (26115, 1593219001694080368834197338454876168408865785551),
  (29475, 1300607463455093707390549191223764216524307772120),
  (28866, 1574569275825495997935987939162233069909461030482),
  (28865, 1483225423515142472909295945092948333775527974741),
  (27075, 1574772830540467611235611065437155677324019099350),
  (27107, 1575862369828140216972827166276655552473130698322),
  (27139, 1594646597835930142597719329819627069444985013839),
  (28834, 1574569275825495997935987939164573815816860587602),
  (28833, 1483225423492314565548257637283468314066512619353),
  (28099, 1574772830540467611266830058247292050535961932510),
  (28131, 1575862369828140216974065106314788010699039777434)]

theorem tbl30_10_ok : tblOK 30 tbl30_10 = true := by decide +kernel

def tbl30_11 : List (Nat × Nat) := [
  (28163, 1594646946285074111911093252922035383655295436431),
  (28802, 1574569275825495997908460131934654502831444534864),
  (28801, 1483225423492314565548257637283468327258504669017),
  (29155, 1280531843970093681276281663757475754488197359312),
  (29187, 1300744022852306713859764465694628495454687802074),
  (19585, 1483116075901883862475277978036433035523345700500),
  (20609, 1483138382091600263801422852006516669059511694171),
  (21633, 1483138382091600263801422852006516669059494916955),
  (22657, 1483160688278658209167971285762567555666842789655),
  (23681, 1483160688278658209167971285762567555666842789654),
  (24705, 1483182965441915815864401264492337059255247251025),
  (25729, 1483182967247114484878886229305084830931402180243),
  (26753, 1483205267992313015469977309628113493023732090579),
  (27777, 1483205267992313015469977309628113493023732090515),
  (30849, 1487529821315964747746974625007785555349372425053),
  (19586, 1574459928235019238799356177620548751672120526482),
  (20610, 1574482234424735640157511315533571029902126818893),
  (21634, 1574482234424735640157511315533571025504080307789),
  (22658, 1574504540611793586960346717734415843110313341788),
  (23682, 1574504540611793586960346717734415843110313079644),
  (24706, 1574526817775097248252131566537104466508766324304),
  (25730, 1574526819580249862559975827222744442632181986138),
  (26754, 1574549120325448393262353771507342990774765930393),
  (27778, 1574549120325448393262353766784976507905120716697),
  (29826, 1574569275825495997908460131965986027698389817241),
  (18788, 836932013619140648757847116107840644513963251216),
  (18820, 838359695747396795934719765447165304885765330449),
  (18852, 839359418745037482083851022084539581837541472083),
  (18884, 840787014964127778089341715331247468350174213777),
  (18916, 842236911859026753556472845221453264311041742483)]

theorem tbl30_11_ok : tblOK 30 tbl30_11 = true := by decide +kernel

def tbl30_12 : List (Nat × Nat) := [
  (18948, 843664508079425510433345739791131949242634294931),
  (18980, 843664508079178800752648389625003428048971056787),
  (26180, 1118053474519085283411585841637973796023040292497),
  (27204, 1209397326852265742243655168401416191188594669265),
  (28228, 1209397326852265742243655168401416191188594669201),
  (28067, 1574772736205094396948464465851381105005755393945),
  (28066, 1574772736205094396948456521705945167182109631262),
  (28065, 1483431028905239001914309259555669603210759845458),
  (19812, 1665759177446779627487731437453355828048339211792),
  (19844, 1665759074699101830772610714189863931786095314577),
  (19876, 1665759074358819463851672260172375211598224377489),
  (19908, 1666161305128764141772219684332140976809608304276),
  (19940, 1667206985611621499823311123128024774780088833684),
  (19972, 1669019958829854064650443401409065592293919377038),
  (20004, 1657218341442157338434185888590556629452335699604),
  (26212, 1117941970793092630352843059482633429377585858193),
  (27236, 1209285823126265517909130031728893902599002302363),
  (28260, 1209285823126265517909130031728893902599002302362),
  (28035, 1574549120325723361103288981792796035684758578837),
  (28034, 1574552250252135049928599632910517175016273340053),
  (28033, 1483431028905239651185367901020946207411940177490),
  (20868, 1665759074700368623403811993590053676250350872080),
  (20900, 1665759074338549700392478016286237541320156636688),
  (20932, 1666183589540409060201468475684928177872477705939),
  (20964, 1667206902755696983821240025413991246300957980369),
  (20996, 1669041187005031467215478612317704858090272581333),
  (21028, 1657262833843921433237829818656421178021431600851),
  (27268, 1209285823126273089185047781068272425794868426449),
  (28292, 1209285823126273089185047781068272425794868426385),
  (28003, 1574549120325449361748669586616402248857023727513)]

theorem tbl30_12_ok : tblOK 30 tbl30_12 = true := by decide +kernel

def tbl30_13 : List (Nat × Nat) := [
  (28002, 1574549120325449361748669586622166856106255619988),
  (28001, 1483205267992375338007618938529712265592967870034),
  (21892, 1665759074700368623403811993590053394775374161424),
  (21924, 1665759074338549700392478016286237259845179926032),
  (21956, 1666183589540409060201468475684928177872477701843),
  (21988, 1667206902755696985254581133101449563599529404115),
  (22020, 1669041187005031467215478612318045438542897239963),
  (22052, 1657262833843921433237829818656420896546454890195),
  (27300, 1209285823126273089207175615135681234444872136401),
  (28324, 1209285823126273089207175615135681234444872136337),
  (27971, 1574549120325449361748669586616402248857040504729),
  (27970, 1574549120325449361748669586622166856115012514590),
  (27969, 1483205267992375338007621039977068563859072693842),
  (22948, 1665759074339879252906663963699988581554847868432),
  (22980, 1666205890285607590825847951437533914212094002835),
  (23012, 1667206908201544073844176662488725011955083666270),
  (23044, 1669063487750230322357173806461891948555800172442),
  (23076, 1657285134589120288379893988470625057129016936083),
  (28356, 1209285823126273089207175652324317286974608717457),
  (27939, 1574549120325449361747431646583239811007557423902),
  (27938, 1574549120325449361747431646582880354681866957598),
  (27937, 1483205267992354568740997423781940226655644104274),
  (23940, 1665759074701697526882128564189636530447900075536),
  (23972, 1665759074339879252827435801185724243961303918096),
  (24004, 1666205890285607590825847951437533909814047491731),
  (24036, 1667206908201544073844176662488725011886364189534),
  (24068, 1669063487750230322357173778496627932812119922586),
  (24100, 1657285134589120288378656048431339676854117811859),
  (28388, 1209285823126273089127947489810052949381064767121),
  (27907, 1574549120325449361747431646583239815405603935006)]

theorem tbl30_13_ok : tblOK 30 tbl30_13 = true := by decide +kernel

def tbl30_14 : List (Nat × Nat) := [
  (27906, 1574549120325449361747431646582880354681867219742),
  (27905, 1483205267992354568740997423781940508130620814930),
  (24996, 1666116588518173892949774856644179824848772871761),
  (25028, 1666116703642836020380964616994697669987764885140),
  (25060, 1667206913647350612826372393577698853134136596307),
  (25092, 1669085788495429121721831172007120912445034808974),
  (25124, 1657307440778837004351474943678867994271842383440),
  (27875, 1574549120325449366818034047496157421392416756510),
  (27874, 1574549120325449366818034047495797960668680041246),
  (27873, 1483205267992333794803567992027526449110286157458),
  (26020, 1666116588518173877737967653905427006889408149137),
  (26052, 1666116703638367080538328054806416626572382783123),
  (26084, 1667206913642034025361786388512633078813725906579),
  (26116, 1668997630862066180352224788620824349390956480142),
  (26148, 1657307538948839481995805654067792534329472927379),
  (27843, 1574549120325449042299477413978188372613011350302),
  (27842, 1574549120325449040228111777533984173659642521170),
  (27841, 1483205267992333794799854190799136239764169639570),
  (27076, 1219276208355863376617966655018133025931260978704),
  (27108, 1207609809459578516164535898190751014253648483856),
  (27140, 1209399478199669396165991383309227670183498827475),
  (27172, 1209397326872368667395059433448303651787047723806),
  (27810, 1574549120325448717780907392551598441738278822686),
  (27809, 1483205267992313015469977309628113211548755379859),
  (28100, 1219276208355863376617966655018133025862541501968),
  (28132, 1207609809459578516165773838230036460635588470416),
  (28164, 1209399478199669396165991383309227670183498827411),
  (28196, 1209397326872368667395059433448303651718328247070),
  (19617, 1483116075901883862475277978036432754048368989844),
  (20641, 1483138382091600263801422852006498654661002212187)]

theorem tbl30_14_ok : tblOK 30 tbl30_14 = true := by decide +kernel

def tbl30_15 : List (Nat × Nat) := [
  (21665, 1483138382091600263801422852006498654660985434971),
  (22689, 1483160688278658209167971285761414634162235942679),
  (23713, 1483160688278658209167971285761414634162235942678),
  (24737, 1483182965441915815864850073377676883724541961809),
  (25761, 1483182967247114484878886229305084826533355669139),
  (26785, 1483205267992313015469977309628113211548755379923),
  (30881, 1487529821315964747746974625007785555349372420957),
  (19618, 1574459928235019563317909944215200322323913983634),
  (20642, 1574482234424735964676200186151299130502295623577),
  (21666, 1574482234424735964676200186151298849027318912921),
  (22690, 1574504414460254127909250297374285829486050666067),
  (23714, 1574504414460253803390696638947559046330030089811),
  (24738, 1574526817860167839982814991287135021331396240976),
  (25762, 1574526819580250187078529485649472904264743736979),
  (26786, 1574549120325448717780907392625385418033117029150),
  (29858, 1574569275825495997935987939164581490954198886297),
  (18821, 838359695778017413059016435959216330081583081303),
  (18853, 839359418745037482083851022084503553040539285331),
  (18885, 840787014964127778089341715331176255181066417809),
  (18917, 842236911859026753556472845221453264242322265747),
  (18949, 843664508079425510433345739791113934844124812947),
  (18981, 843664508079178800752648389551216451754132850323),
  (26181, 1118053474519085283411585841637955781624530810513),
  (27205, 1209397326852265742243655168401398176790085187281),
  (27044, 1666116588518172904182306678625254634831073588945),
  (27043, 1574772736205094396948464465925168081300593600409),
  (27042, 1574772736205094396948456521705945167250829107998),
  (27041, 1483431028905239001914309259555669603211833587282),
  (19845, 1665759074699101830772610714189863927388048803473),
  (19877, 1665759074358819463851672260172375207200177866385)]

theorem tbl30_15_ok : tblOK 30 tbl30_15 = true := by decide +kernel

def tbl30_16 : List (Nat × Nat) := [
  (19909, 1666161305128764146842833207764738437250456250004),
  (19941, 1667206985611621499823311123128006760381579351700),
  (19973, 1669019958829874833917104491371671023867906516628),
  (20005, 1657218341442157338434185888590538615053826217620),
  (26213, 1117941970793092630352843059408846453082747651729),
  (27237, 1209285823126265517909130031728893902599002040219),
  (27012, 1665892972743700085716195796312090525138576553681),
  (27011, 1574549120325723361103288981792796035684758578901),
  (27010, 1574552250252135049928599632910517175016273340117),
  (27009, 1483431028905239651185367901020946207413013919314),
  (20869, 1665759074700368623403812106417131287548921939864),
  (20901, 1665759074338549700392478129113315152618727704472),
  (20933, 1666183589540409065272070878382549857616180893395),
  (20965, 1667206902755696983821239723182536342643664303825),
  (20997, 1669041187005052236402912751628218980419052889813),
  (21029, 1657262948373084586428112671884632213790112962259),
  (27269, 1209285823126273089185047781067119504290261579473),
  (26980, 1665892971107613908228796224384701841344410423646),
  (26979, 1574549120325449361748669586690189225151861933977),
  (26978, 1574549120325449361748669586695953832401093826452),
  (26977, 1483205267992375338007618938529712265594041611858),
  (21893, 1665759074700368623403812106417113273150412457880),
  (21925, 1665759074338549700392478129113297138220218222488),
  (21957, 1666183589540409065272070878382549940496224872147),
  (21989, 1667206902755696985254580830869994659942235727571),
  (22021, 1669041187005052236402912751628559560528214112155),
  (22053, 1657262948373084586428112671884632297899524405147),
  (27301, 1209285823126273089207175615135663220046362654417),
  (26948, 1665892971107319914922009054238314174491080300436),
  (26947, 1574549120325449361748669586690189225151878711193)]

theorem tbl30_16_ok : tblOK 30 tbl30_16 = true := by decide +kernel

def tbl30_17 : List (Nat × Nat) := [
  (26946, 1574549120325449361748669586695953832409850721054),
  (26945, 1483205267992375338007621039977068563860146435666),
  (22949, 1665759074339879252906664076454414405139654805400),
  (22981, 1666205890285607595896450354140107687657636488851),
  (23013, 1667206908201544073844176360257270108297789989726),
  (23045, 1669063487750251091544607945772406070541117044634),
  (23077, 1657285254562807220109861656703619940225307142039),
  (26916, 1665892971107319914921964550732691302499439732240),
  (26915, 1574549120325449361747431646657026787302395630366),
  (26914, 1574549120325449361747431646656667330976705164062),
  (26913, 1483205267992354568740997423781940226656717846098),
  (23941, 1665759074701697526882128676944062354032707012504),
  (23973, 1665759074339879252827435913940150067546110855064),
  (24005, 1666205890285607595896450354138954766153029641875),
  (24037, 1667206908201544073844176360257270108229070512990),
  (24069, 1669063487750251091544607917807142054797436794778),
  (24101, 1657285254562807220109861656703619940225307142038),
  (26884, 1665892971109978370913534382478498951254616434192),
  (26883, 1574549120325449361747431646657026791700442141470),
  (26882, 1574549120325449361747431646656667330976705426206),
  (26881, 1483205267992354568740997423781940508131694556754),
  (24997, 1666116588518173892949774856644161810450263389777),
  (25029, 1666116703642836020382202557033983041466570987156),
  (25061, 1667206913647350612826372393577698853065417119571),
  (25093, 1669085788495449890988492261969726344019021948564),
  (25125, 1657307440778837004351474943383774132288018003536),
  (26851, 1574549120325449366818034047569944397687254962974),
  (26850, 1574549120325449366818034047569584936963518247710),
  (26849, 1483205267992333794803567992027526449110286157522),
  (26021, 1666116588518173877737967653905408992490898667153)]

theorem tbl30_17_ok : tblOK 30 tbl30_17 = true := by decide +kernel

def tbl30_18 : List (Nat × Nat) := [
  (26053, 1666116703638367085608930455424186890329796200083),
  (26085, 1667206913642034025361786388512633078745006429843),
  (26117, 1668997630862086949618885878583429780964943619732),
  (26149, 1657307538948839481995805654067792252854496216723),
  (26819, 1574549120325449042299477414051975348907849556766),
  (26818, 1574549120325449040228111777533984178057689032274),
  (26817, 1483205267992333794799854190799136239764169639634),
  (27077, 1219276208355863376617966767772558849516067915672),
  (27109, 1207609809459536977789667619643509746577852929552),
  (27141, 1209399478199669396165991081077772766526205150931),
  (27173, 1209397326872368667395059433447150730282440876830),
  (6305, 1761585827843889923862419672958458972641701480081),
  (20673, 1483138266825062715806783387137560875467374405201),
  (21697, 1483138266825062715806783387137560875398654928465),
  (22721, 1483160567571590566337999725510014353635631798164),
  (23745, 1483160567571590241819446067083287570479611221908),
  (24769, 1483182965612056999087634817566571174659794216529),
  (25793, 1483182967247135264176712655184483990667487692434),
  (30913, 1488957069008191002743566828680855513101255169617),
  (20674, 1574482119158244148194521916963950888062146353045),
  (21698, 1574482119158244148194521916963950888062146353044),
  (22722, 1574504419904771998722984840730699558345515733470),
  (23746, 1574504419904771674204431182303972775189495157214),
  (24770, 1574526817945238431475365119610185941883683153488),
  (25794, 1574526819580250509604970537318897210414084249234),
  (29890, 1574569275825495997935987939193761890880851847065),
  (20675, 1574482119158244280669364287662203505514296993493),
  (21699, 1574482119158244280669364287662203505514296993492),
  (22723, 1574504419904771998723490890794472113003639633812),
  (23747, 1574504419904771674204937232367745329847619057556)]

theorem tbl30_18_ok : tblOK 30 tbl30_18 = true := by decide +kernel

def tbl30_19 : List (Nat × Nat) := [
  (24771, 1574526817945238433470904784689512439229248251472),
  (25795, 1574526819580250511597107586963329106495876748949),
  (28867, 1574569275825495997935987939162233069908387288658),
  (19910, 841214545023668171257653891198750500621348603730),
  (19942, 842236911825565056915484334967970429535028610898),
  (19974, 843664508078903336804976227025302956106085947026),
  (20006, 843664508079170718451652642484931879465643230866),
  (20038, 2288150981015907434789800116382688544338539271828),
  (26214, 1118053474519077115151822842419896045768728192657),
  (25989, 1666116588518173877737967653906561913995505514129),
  (25988, 1666116588518173877737967653906579928394014996113),
  (25987, 1574772736205094396948464034923983498546405824149),
  (25986, 1574772736205094396948456521705944766046280734357),
  (25985, 1483431028905239001922858784887248864881937823378),
  (20934, 1757527441873921201951345490360248468715473561301),
  (20966, 1758550755088878416288198187741568444486220543899),
  (20998, 1760382632946405395643596708000147931244036450005),
  (21030, 1761427202855229031862791254019696493032459822805),
  (21062, 1773200253801819527195590980240253073320394188501),
  (25957, 1665870670362168100178715581339720816268308203345),
  (25956, 1665870670362168100178715581487294768789265139537),
  (25955, 1574526819580250831046291679275085948342330803858),
  (25954, 1574526819580250831046291679270474266996827834002),
  (25953, 1483182967247176807384477402885692909740291864210),
  (21958, 1757527441873921201951345476193040920414231230166),
  (21990, 1758550755088878417642330475727876182736436291282),
  (22022, 1760382632946405395643596708000147931244036450004),
  (22054, 1761427202855229031862791254019696493032459822804),
  (22086, 1773088749480332732205944821017696106246804436694),
  (25925, 1665870670362168100178715581339723591435656709969)]

theorem tbl30_19_ok : tblOK 30 tbl30_19 = true := by decide +kernel

def tbl30_20 : List (Nat × Nat) := [
  (25924, 1665870670362168100178715581487297543956613646161),
  (25923, 1574526819580250831046291679277301719633874994834),
  (25922, 1574526819580250831046291679277301724031921505938),
  (25921, 1483182967247176807384479504362521326917862635154),
  (22982, 1757549742619119732574487013768597505327920064407),
  (23014, 1758550760534725506231926005115151631092007064414),
  (23046, 1760404933691604250785291902145147362752033543828),
  (23078, 1761427208301076130593591585306594018991502087828),
  (23110, 1774524071218702470558856669950112029415969490711),
  (25892, 1665870670362168100177477641300456225627986548561),
  (25891, 1574526819580250831045053739680720182454617724562),
  (25890, 1574526819580250831045053720791272269978751293074),
  (25889, 1483182967247156038117855888137921147879898298002),
  (23942, 1757103042383762147373460302191241789031979542162),
  (23974, 1757103042383762147373767350972972295591778633624),
  (24006, 1757549742619119732574487013768597505327920064406),
  (24038, 1758550760534725506231926005115151631023287587678),
  (24070, 1760404933691604250785291902145147081277056833172),
  (24102, 1761427208301076130593591585306576004592992605844),
  (24134, 1774524071218702470558856669950112029415969490710),
  (25860, 1665870670364826556168716874332275693134208636432),
  (25859, 1574526819580250831045053744403086665324262938258),
  (25858, 1574526819580250831045053720791272270047470769810),
  (25857, 1483182967247156038117855888137921152277944809106),
  (24998, 1100655078374812861426011616450823340511357920980),
  (25030, 1115179183454068775769007315185861809812605847186),
  (25062, 1116268349496659051486711964973093092242354423442),
  (25094, 1118055631311006159032320323088103514814566188690),
  (25126, 1118053474511109930649009647948759783463174100818),
  (25158, 1118053474519077115155536662537752186592351827537)]

theorem tbl30_20_ok : tblOK 30 tbl30_20 = true := by decide +kernel

def tbl30_21 : List (Nat × Nat) := [
  (25827, 1574526819580250836115656145316004271311075759762),
  (25826, 1574526819580250836115656121704189876034283591314),
  (25825, 1483182967247135264180426456412874200013604210322),
  (26022, 1100655078374812861426011314219368436854064244436),
  (26054, 1115179183454068775769450102785680772807404111506),
  (26086, 1116268349496659056557314365886010677947239834269),
  (26118, 1118055631311006159032320432311255492053385729682),
  (26150, 1118053474539187233827594118904240083211241477778),
  (26182, 1118053474519077115151822842419896045768728196753),
  (7329, 1761585827843889923862419370727004068984407803537),
  (20705, 1483138266798230006619860653474824310544712410705),
  (21729, 1483138266798230006619860653474824310475992933969),
  (22753, 1483160567543428861761500208697922290357561271889),
  (23777, 1483160567543428861682272046183657952764017321553),
  (24801, 1483182965612056674569081159139844391503773640273),
  (30945, 1488957069008191002743566823958489030231609955921),
  (7362, 1771598792589741602362717396408897949874246723216),
  (20706, 1574482119131411439007599183301214323139484358549),
  (21730, 1574482119131411439007599183301214323139484358548),
  (22754, 1574504419876610294149230639159536146733983635353),
  (23778, 1574504419876610294070002476645271809140439685017),
  (24802, 1574526818030315895785532250476554081942114752338),
  (29922, 1574569275848323889057397981251037050556618499666),
  (20707, 1574482119131411439039995400410155675765755889557),
  (21731, 1574482119131411439039995400410155758853927748318),
  (22755, 1574504419876610294181671251740888434800052159134),
  (23779, 1574504419876610294102443089226624097206508208798),
  (24803, 1574526818030315895785532250481165763287617722194),
  (28899, 1574569275848323889057397981103455705477089146450),
  (19975, 844069394472903558959939190161340437847659071122)]

theorem tbl30_21_ok : tblOK 30 tbl30_21 = true := by decide +kernel

def tbl30_22 : List (Nat × Nat) := [
  (20007, 844066611140010286295865747990450244312334943890),
  (20039, 2288150981015845127227498302914055985697175983764),
  (24966, 1757460440851347141869648776851126007691822310993),
  (24965, 1666116588518173892949774857371655279857183831633),
  (24964, 1666116588518173892949774857371673294255693313617),
  (24963, 1574772736178339110670924568751040046596235802194),
  (24962, 1574772736178339108670087439443385207066555922002),
  (24961, 1483431028905239001922858784890707629394684622418),
  (20999, 1760382632946405395643596703277781448374391236309),
  (21031, 1761427202855229031862791254019696492963740346069),
  (21063, 1773200253801819527194353040200967693045495064277),
  (24933, 1665870670362168100178715581339720816268308465489),
  (24932, 1665870670362168100178715581487294768789265401681),
  (24931, 1574526818028986667790985274720036748270091192146),
  (24930, 1574526818028986667790985274646303815102061954898),
  (24929, 1483182965693139866661836291081684245410112415313),
  (22023, 1760382632946405395643596703277781448374391236308),
  (22055, 1761427202855229031862791254019696492963740346068),
  (22087, 1773088749480332732233493192727181975170196272854),
  (24901, 1665870670362168100178715581339723591435656972113),
  (24900, 1665870670362168100178715581487297543956613908305),
  (24899, 1574526818028986667790985274720037285175362930514),
  (24898, 1574526818028986667790985274646304347678006658898),
  (24897, 1483182965693139906852683031070197846378619938385),
  (23047, 1760404933691604250785291897422780879882388330132),
  (23079, 1761427208301076130593591585306594018922782611092),
  (23111, 1774524071218702470558856669950057986220474599191),
  (24868, 1665870670362168100177477641300456225627986810705),
  (24867, 1574526818028986667789747334607109034722730530642),
  (24866, 1574526818028986667789747334603650274813114931026)]

theorem tbl30_22_ok : tblOK 30 tbl30_22 = true := by decide +kernel

def tbl30_23 : List (Nat × Nat) := [
  (24865, 1483182965691810678834286675480580813802758809169),
  (23943, 1757549742619119732574485200527442035963197941658),
  (23975, 1757549742619119732574485200527442035963181164442),
  (24071, 1760404933691604250785291897422780598407411619476),
  (24103, 1761427208301076130593591585306576004524273129108),
  (24135, 1774524071218702470558856669950057986220474599190),
  (24836, 1665870670364826556168716874332275693134208636496),
  (24835, 1574526818028986667789747334608261956227337377618),
  (24834, 1574526818028986667789747334603650274881834407762),
  (24833, 1483182965691810678834280961055459773807320180305),
  (24999, 1100655078374812861426011616450805326112848438996),
  (25031, 1115179183454048006581573175875347687827288966802),
  (25063, 1116179162849418541199192068341983655521204651666),
  (25095, 1118055631305689571567734318024440035633970628242),
  (25127, 1118053452734360465792211396871226727320591349330),
  (25159, 1118053452741005956734028659382291351885021787729),
  (8385, 1854356847156628336650511871284840776868698871506),
  (8417, 1854356847156628336650511870907908434766979474267),
  (21761, 1483138266798230006619861253213061791911721379409),
  (22785, 1483160567543428861761480865884808456290765973073),
  (23809, 1483160567543428861682252703370544118697222022737),
  (30977, 1490384665150061458853045835656464591851619690065),
  (8386, 1854379147876322964861464951685928662313913411285),
  (8418, 1854379147901826830750881008484918263815054382802),
  (21762, 1574482119131411439007591555288833914612668245584),
  (22786, 1574504419876610294149211296346422312667188336537),
  (23810, 1574504419876610294069983133832157975073644386201),
  (29954, 1574574468882946175590554452966238121262104496025),
  (21763, 1574482119131411439039995660141465717982081628057),
  (22787, 1574504419876610294181671511473351033957836171161)]

theorem tbl30_23_ok : tblOK 30 tbl30_23 = true := by decide +kernel

def tbl30_24 : List (Nat × Nat) := [
  (23811, 1574504419876610294102443348959086696364292220825),
  (28931, 1574574468882946175590554452965749656037350520402),
  (21764, 1665825971464592876464693946220622762558870034328),
  (22788, 1665848272209791731606344744891051834710980065176),
  (23812, 1665848272209791731527116582376787497117436114840),
  (27908, 1665892971109978370913534382478498946856569923088),
  (21064, 935432770874998186429045662940706714070325745363),
  (21096, 935432770875288620005866983105124268569823635157),
  (23909, 1665759190049251162472621412619620761804262160017),
  (23908, 1665759069228997609034550439503694964132900800408),
  (23907, 1574415216895816171609876946353533503760484287134),
  (23906, 1574415216895816171577436333772181215694415763353),
  (23905, 1483071364562634739189705903310567359317993399889),
  (22088, 1854576020884904749439924480954384402394188134294),
  (22120, 1841355599958587775073864739680214328047253939921),
  (23877, 1665848393030045279419217205272752887503111186068),
  (23876, 1665848393030045279419217205272752817616499328657),
  (23875, 1574504540611802114847930400084265156680319362836),
  (23874, 1574504540612071134288127388398961701115718599260),
  (23873, 1483071397228412735603972404777957865533392627281),
  (23112, 1026285200661131990530241880549769475080967714712),
  (23144, 1026285200661131990530241880549767254067479607192),
  (23844, 1665848272209791731527077896750557889445334124440),
  (23843, 1574504419876610294102443348959086696364275443609),
  (23842, 1574504419876610294069983133832157975073644382105),
  (23841, 1483160567543428861682252703006220923241458378321),
  (23944, 1035205841828925424503998692645994182311853233680),
  (23976, 1022000349974525086790039475611064230440367887888),
  (24136, 1026285200661131990451013718035505137487423764376),
  (24168, 1026285200661131990451013718035502916473935656856)]

theorem tbl30_24_ok : tblOK 30 tbl30_24 = true := by decide +kernel

def tbl30_25 : List (Nat × Nat) := [
  (9409, 1854356847156628336650511871284840772470652360402),
  (9441, 1854356847156628336650511870907890420368469992283),
  (21793, 1483138266798230006619861252703470486875495016017),
  (22817, 1483160567543428861761480865520485260835002328657),
  (31009, 1490384665150061458853045835656804886301290649169),
  (9410, 1854379147876322964861464951685928662312839669461),
  (9442, 1854379147901826830750881008484918263815037605586),
  (9474, 1864369898081623792272308751065529493415443313438),
  (21794, 1574482119131411439007591556756608820169301681744),
  (22818, 1574504419876610294149211296346422312667188332441),
  (29986, 1574574468882946175590554452966238121262087718809),
  (9475, 1864369898081623792272308751065529774890352923422),
  (21795, 1574482119131411439039995660141465717982064850841),
  (22819, 1574504419876610294181671511473351033957819393945),
  (28963, 1574574468882946175590554452965749655968631043666),
  (21796, 1665825971464592876464693946220622762558870030232),
  (22820, 1665848272209791731606306059264822227038878074776),
  (27940, 1665892971107319914921964550732691302430720255504),
  (22885, 1665759190049251162472621412619621043279238870673),
  (22884, 1665759069228997609113778602017959301726444750744),
  (22883, 1574415216895816171689105108867797841354028237470),
  (22882, 1574415216895816171656664496286445553287959713689),
  (22881, 1483071364562634739268934065824831696911537350225),
  (22853, 1665848393030045279419217205273905809007718033044),
  (22852, 1665848393030045279419217205273905739121106175633),
  (22851, 1574504540611802114847930400084011332216594974483),
  (22850, 1574504540612071134288127388472748677410556805724),
  (22849, 1483071397228412735683200567292222203126936577617),
  (10465, 1945700688600774027568211342124688685678875714395),
  (10497, 1947127919934422360306646683072249261206747555409)]

theorem tbl30_25_ok : tblOK 30 tbl30_25 = true := by decide +kernel

def tbl30_26 : List (Nat × Nat) := [
  (10529, 1947127919934422360306646659755564752037874312785),
  (31041, 1491810867495628917455821577482178808901683988114),
  (10466, 1945722989345972521668580479701698598768732845979),
  (10498, 1947150220679620890929796451276064020075209856921),
  (10530, 1947150220679620890929796451276064020075209852825),
  (30018, 1574574468882946174416042807942972773175735142297),
  (10499, 1947150220679621023737392637866369228671116396438),
  (10531, 1947150220679621023737392637866369228602396919702),
  (28995, 1574574468882946174416042798497767421469734029138),
  (27972, 1665892971107319914922009054238296160092570818452),
  (26949, 1665892971107319914921970368611909177122162251668),
  (11489, 1945700688600774027568210737891157503288345708242),
  (11521, 1947127919934422360306627340259135427139952256593),
  (11553, 1947127919934422360306627316942450917971079013969),
  (31073, 1491810867495628917455820973019263948459171202706),
  (11490, 1945722989345972521668580479701698598768732841883),
  (11522, 1947150220679620890929777108462950186008414558105),
  (11554, 1947150220679620890929777108462950186008414554009),
  (11586, 1955713750414805224660039053109144542112144175902),
  (30050, 1574574469999325956377010329471285322826097727254),
  (11523, 1947150220679621023737392637866369228671099619222),
  (11555, 1947150220679621023737392637866369228602380142486),
  (11587, 1955713750414805224660039053109144542180813325086),
  (29027, 1574574469999325956377010329323711370237495056214),
  (11588, 1955736051161324168895571067137325832210255484820),
  (28004, 1665892971107613908228796224384701841275690946910),
  (26981, 1665892971107613908228796224384701841344410423582),
  (12545, 2038471777708127849030800384805755194397745555025),
  (12577, 2038471777708127849030800384805630782458039445073),
  (12609, 2039899025402163124292533386095599214204642469457)]

theorem tbl30_26_ok : tblOK 30 tbl30_26 = true := by decide +kernel

def tbl30_27 : List (Nat × Nat) := [
  (12641, 2039899025402163124292533386093435516058667656785),
  (31105, 1493238115188334877310999185259945006771393910418),
  (12546, 2038494078457320636166884814454217559645278787346),
  (12578, 2038494078457320636166884814454217559644205045522),
  (12610, 2039921326150026596047943100423719690602306422546),
  (12642, 2039921326150026596047943100423719682280807286546),
  (30082, 1574574470000655508891351890022024522486272766814),
  (12547, 2038494078457320636166884814454289617166302271250),
  (12579, 2038494078457320636166884814454271602767792789266),
  (12611, 2039921326150026596047943100424871767750702614290),
  (12643, 2039921326150026596047943100424871759361557743378),
  (29059, 1574574470000655508891343686074927415395495532370),
  (12612, 2039943626895225126750312671452141012544041076497),
  (12644, 2039943626895225126750312671452145956566794848017),
  (28036, 1665892972743700085716195796312090525138576553617),
  (27013, 1665892972743700085716195791589724042268931339985),
  (25990, 1757460440851347141865934956733269866868198680209),
  (20040, 2289578185009251963394522735925418565477250455188),
  (13569, 2026938830855910556941713914021188090084023940881),
  (13601, 2026938830855910556941713914021063678144317830929),
  (13633, 2026827321685275093448273891336089905102520940305),
  (13665, 2026827327129917579307874799800053958904775264017),
  (31137, 1493238115188334877310999249612564629411771569810),
  (13570, 2026938828883357345802243093788318860568933820179),
  (13602, 2026938828879369661802510154702585033774923347728),
  (13634, 2026827321685275093527505963460323997078678767383),
  (13666, 2026827327129917579387106871924288609433996064532),
  (13698, 2048484910507173008887220717193529388527446779541),
  (30114, 1574574470000655508891351890022024522486272766750),
  (13571, 2026938828883357345802243093788318860568917042963)]

theorem tbl30_27_ok : tblOK 30 tbl30_27 = true := by decide +kernel

def tbl30_28 : List (Nat × Nat) := [
  (13603, 2026938828879369661802510154702585033706203870992),
  (13635, 2026946556536154454126604252626157417734099781395),
  (13667, 2026827327129917579387106995951993202897025857300),
  (13699, 2048484910507173008887220717193619179044999653013),
  (29091, 1574574470000655508891343686074767537608723879762),
  (13636, 2026946556537484006237066386469301225887003920147),
  (13668, 2026827327129917580020486703403708643335595955728),
  (13700, 2048507216690113355467099790119386354913725769363),
  (28068, 1666116588518172904182306678625254634831073588881),
  (13701, 2048507216690113355467099790119386354913725507219),
  (27045, 1666116588518172904182306678625236620432564106961),
  (18983, 844066611140010286295865747990450244312334943891),
  (18951, 844069394472903558959939190161340437847659071123),
  (18982, 843664508079170718451652642484931879465643230867),
  (18950, 843664508078903336804976227025302956106085947027),
  (18918, 842236911825565056915484334967970429535028610899),
  (18886, 841214545023668171257653891198750500621348603731),
  (14625, 2119712433468197028114886975804670705074489591311),
  (14657, 2119960845891169164656483127989920443842060953169),
  (14689, 2119960845891169164426226880417618429632731752017),
  (14721, 2132670130110920340116363376560781717789180765777),
  (14753, 2132670130110885574881594100001566149122014651985),
  (31169, 1473217675280342334269256067685732231886073615953),
  (14626, 2119712433468197028114887102651269317589860419087),
  (14658, 2119715914401395425277016269023828100481234061075),
  (14690, 2119960851335728706250987623687461463317588576020),
  (14722, 2119962942146584054590007963617101598350247323285),
  (14754, 2132692430941154829801195695088008513343055038226),
  (30146, 1574775585297698247719945942381227495772061499806),
  (14627, 2119712433468197030194861447685236390559437395736)]

theorem tbl30_28_ok : tblOK 30 tbl30_28 = true := by decide +kernel

def tbl30_29 : List (Nat × Nat) := [
  (14659, 2119712435360079811986739531834457126182941963855),
  (14691, 2119960851335728706250987623687462584819381798676),
  (14723, 2119962942061513462859773347310932004059103749781),
  (14755, 2132692430941154829801195695088080540152914872082),
  (29123, 1574772830370326289840170587762103512953026589402),
  (14660, 2119712435359515406779942896542751018062273644047),
  (14692, 2119960856780246439279751441295128845874185180688),
  (14724, 2119962947469784136744926897670088538940424447504),
  (14756, 2132714731687682450779581484828154393410259772944),
  (14725, 2119962947469784136744934132048318435129566463896),
  (14757, 2132714731687682450779588719206384289599401789336),
  (17927, 2196807079506730782508677944455406693856998405714),
  (17926, 2196807079510725580861518830377123959105087944274),
  (17894, 750893054047865753792738626953941992035578402386),
  (17862, 749848391945288208246820739061955846063446939218),
  (17925, 2232625619662318737775099862719550439275147060884),
  (17893, 750893054081327450436511274397646853360428095317),
  (17861, 749848391949275892234175486753301317635399079506),
  (17829, 748420708384394545365647042110709961737054271058),
  (17797, 746993542699637464792010466086208780196451555159),
  (17924, 2232625619662297968508438772756945007701159921294),
  (17892, 750893054081327450436511274397646853361501837141),
  (17860, 749848391949275892234175486753301317636472821330),
  (17828, 748420708384394545365647042258283909928684172882),
  (17796, 746993542669016832923847927684124972193810077266),
  (17764, 745565858935161022273347203318282265994684868176),
  (17732, 744138693399255116272066515037998553764784846418),
  (15649, 2121139937649088417530676309551792843591051712016),
  (15681, 2121050767334072291133068503243270121058699646480),
  (15713, 2121050734668294295035673576689268965043407492624)]

theorem tbl30_29_ok : tblOK 30 tbl30_29 = true := by decide +kernel

def tbl30_30 : List (Nat × Nat) := [
  (15745, 2121050735965118793789832557551351239887477392912),
  (15777, 2121047979742251703117873377208447197447967544848),
  (31201, 1473239882700823024039381223324127758955327047513),
  (15650, 2121139937649088417530684530969194124439014413840),
  (15682, 2121140058299165893932688402405731096765128853267),
  (15714, 2121050734668294295069336772246605188522903160592),
  (15746, 2121050741410179366601452746526125341407059941012),
  (15778, 2121048328219207735776813798663038218631115302676),
  (15810, 2139831867308208360340647203705278983326477386142),
  (15651, 2121139937649088550257892552581146982949408315160),
  (15683, 2121140058299165893932688402406883173913525045011),
  (15715, 2121050734668294427764223869359415207735141697300),
  (15747, 2121050741410179366601452746526126462950616684180),
  (15779, 2121048328219207735776813798663038499899950360340),
  (15811, 2139829112380836540427062087839656234374493713118),
  (15684, 2121140058298601509399960043631044286769295070736),
  (15716, 2121050734668294289998734371333401581928550831632),
  (15748, 2121050741409615900441691155983416145281748637200),
  (15780, 2121048328219198891936967329330804317643089188368),
  (15812, 2139851417557199495728925071830312459839565547155),
  (15749, 2121050741409615890300486354157866933915662501648),
  (15781, 2121048328219198881795762527505255106277003052816),
  (15813, 2139851417557199500799527474531733316178547697299),
  (15814, 2139873718302728735712975367834881014986448316310),
  (16870, 750893054047865753792738625850687560394332251729),
  (16838, 749848391945288208246824016384294957597225244242),
  (16869, 750893054081327464932963219747474379030330447701),
  (16837, 749848391949275892234178769903550266953015338841),
  (16805, 748420708384394545365648025390226630377773569879),
  (16773, 746993542699717606376010357377350440114990978903)]

theorem tbl30_30_ok : tblOK 30 tbl30_30 = true := by decide +kernel

def tbl30_31 : List (Nat × Nat) := [
  (16868, 750893054081327464932963219747474379031404189525),
  (16836, 749848391949275892234178769903550266954089080665),
  (16804, 748420708384394545365648025390262659173718792023),
  (16772, 746993542669016832923847927831701141398928086609),
  (16740, 745565858935161022273347203318282265994684868177),
  (16708, 744138693399255116254795800631267120102350595665),
  (16867, 750893054049194863876108783236322706082057496145),
  (16835, 749848391949275892234178764003006378778066277970),
  (16803, 748420708352259715304901548100200420465701123921),
  (16771, 746993542669016832923847927848886318957086746457),
  (16739, 745565858903423812858711037005390396200649569873),
  (16707, 744138693399255116253557860595422489942762530385),
  (16866, 750893054049194863876108783236322987557034206801),
  (16834, 749848391949275892234178764002934351968206444114),
  (16802, 748420708352259715304901548100200420534420600657),
  (16770, 746993542669016830918136063617293055056294520401),
  (16738, 745565858903423812858711037005408410599159051857),
  (16706, 744138693399255116253557860595440504341272012369)]

theorem tbl30_31_ok : tblOK 30 tbl30_31 = true := by decide +kernel

def tbl30 : List (Nat × Nat) := tbl30_0 ++ tbl30_1 ++ tbl30_2 ++ tbl30_3 ++ tbl30_4 ++ tbl30_5 ++ tbl30_6 ++ tbl30_7 ++ tbl30_8 ++ tbl30_9 ++ tbl30_10 ++ tbl30_11 ++ tbl30_12 ++ tbl30_13 ++ tbl30_14 ++ tbl30_15 ++ tbl30_16 ++ tbl30_17 ++ tbl30_18 ++ tbl30_19 ++ tbl30_20 ++ tbl30_21 ++ tbl30_22 ++ tbl30_23 ++ tbl30_24 ++ tbl30_25 ++ tbl30_26 ++ tbl30_27 ++ tbl30_28 ++ tbl30_29 ++ tbl30_30 ++ tbl30_31

def mask30 : Nat := 198761730595483619001380064283882898050169631315867861884930637797282379257078658401866999004733461017969291545032703671801160633274156510602965198594962826588499326428190758405417393556017772217186073921226023796405896784246734364595637515886752338552199508101180624975645637221559675610394891308693971849274980664289733412974951065766233974469133151295951694419003670541437365307167765647120111356420295740228487299013657211809242572478836620093616498328394511804354866668188237956020022106060410894098382480194196690075898905455189252333818286160265081817497967748060735611941864315403326909234761924393552259560549393704983042863375727498906385757423862214473570206645212207964371470608165565605242841783290853577421330671900534965201449666018132461925664464209823600754965556747874019095603874181761721014139489355956244226154387995105239623881538642835895495762620649930693724752402613663058216113330969083546711975887376672646311491222003603993620753796447978594902954248392602522511119737162152232047143431343038372411508311110219430789085286155558876245117586699575929761723155109533256235389160287555108535864392996853367924966120174848086293711944819108294710383666398056781981578364662221474301097316218678117656520136831409484312240525593954407467230240021633261806106586318481205585205790298443657476621458788755064783233729488514744896073256330902818342065036856961158135921421023833050078410456400221434573831089886678673183538451038211580434922409151673169633227280203178145148578997451863480643729960154593218471509514057048373267905115307345642883633643357870575411922550975109351649140851588356461741571851281780578141493169324209914383714463959011181725821798126595022127748524036161484935656580881589349618046329774125874082216879285956728081072043478015375895665256754973125236584011586978812213350488645177748515994184481038012208160966256345210950238239837338418378169159032348089130206255529069362962954330751910629185169011933240346800192416144731596396978268216229784472007760968926342283342861796194037797917035063090650658809953732169074458396456990660863763536406739420835691421700044625492107511135448683829334120474201535834494598610053636098346382576457618051457210471050097548997398048002351119965620058488592826195603062509329562155340010040549376358634213529868119621829470517404759168011415843720821472307564947279410738395519846969351004903347959347836917637266502096020574053798914456430049558984021690960622538103811504290385453382936331151623880486315508231937514065990257236080096790581879028362709550320100174884478247272235224112010017598116930644882240892329033779996557649516653863151321559094515644721219621914943933705360503853095824384341515243944417808082650561865043031434125364541310838884544773790449827448951989400232583713494695011999149172055372815879476837500192862599208979811432707036850303644908259497282695092425527239685306658198127580811739195479639678866730762622775385932581850683603254651091173390009188996372801529910987062758980609921659705213759883079233334189184384083081485123806816379249941091176022489545591348377978594152116835568891576262545708125392628526770058543519571468821666529774533604047590751717768896496461910756690318654215418157028038057379431195797992925104080303262479587901015924861185966079956939748173899864451353839192730574391950899340741919334084878447172524935661824024725781888528904860043758044296523529175185060752690015155238646179874551766513807781121976852067255961891631377439766381269084418608369969786267997793083049699983963832376805799096846421170113113561354711877237375009855196423557413675578553726064304630525349088652294949741399072086803625157133641200191755140319098941952454382162927098751688366475275066077241497338393422471363760100435874246188305497900025964261555805044601279020930369003467927254056250646931645150418693445707548695444841443445591257322807994043897328355993833791898492330037223737230198793987376062633250908383945952975712072610949054302589786753347120737577759347830278969205165925463164897364548707452722088963022586359842075168364788193252849425268849297876232341577399705613399335680553391763867785023180857853980186623468826517288056083258991267006739144914846023859417833188027455140367144263951419104783979484792259654954903114959219431300153487732652492506616363272857237999227678545674898820163364297308097072706532848687693003100528400895016595867218343042162505020884283881093203407052699089614033234861435270989239459057123964257041843600485844860966162190841900392319035362067587548349434114797098489138302245357735603716956168964668347752299234443054241431995502672035278111732831035301043236232391208584778571977606657287016293307400108830078713033371845097607262090496785368964740529567662367304143082866928882511326438401939003365256530349810261531245706554480711938322689501050836271745970681217258948561036308053646842886872452810671060243981690350867111138032854479562563314161245361196238997405296284396543418359727406267184314063786622333332047573597753419128054642695258597905214592770597515939687721010288801341082818939989445331777154725475483098043092980663180358502100001059424597017864758650161415564922963926478997694676738431755800925029614401921397915221070898920278027404070963612511563147823992767302812872217204517564031015184022502817206810884560482361877700980313326500563563030877349821591570086085366051783757273981344504045648901974954180213256250044528224102064610735699422947799538806039725232325096779846738268848727429191659865695618718148296764346056741970847501194563518713427804481337076567048321904021520582897674250800225800173349571732089204421136329481020454906954215954559639405242317480009264040817196771330811683300818005551276747495103964392784904439230467167139724017775297440997041865758993162046546975839971498266986327014041799074825228859669962685778303657537459420195609974311643837658635639822298299323645472785343278923049259877188849543747683868615122469899198358239084539790630717369274801589037932038980819315561823045649073633984591565952685956517543893449749449774234806434884915323964359618092395745733256571294495404570382595755068989905544193686921634834346743378453707262107170016620786103512130416743394693034715816030675128963709000617114891183461523359628662009438910030097886449364155061485145521998931548447092252166151363916606781226039389580535045870660445684479071045128609207489390297280771122126925906838202765352163044747037339052108242439897811778094366069264948831032613377038561935558908872978284668949217279092686630923890845321269332395680413028864581796579839063217533530227671069979557677779356566771089351465300693876918283889474370023728636878550236232572281426671695305366037436514164367411205414772466851620330684194495277778568412901977724996640007287928797256147784757063310277418736952996023996920232919173153489905972957184181092978881169854743531958710143196139135511003345952486191313329905846013673384541606765832644604913281072899370108606710460879094463013377828317064736854240087821795092227001841251954430615373581936916028409975452665770061305772250994334494208977326653062132404879312380499741337465282504811566162166813048728325993028358749427021911172176552235311455720395205143265064178780430720488166048261006110904363085621351105075392156080808176645229272425800358487041340622564519270046934063356149753150638989474820587067128041444846535034430529482162261335585986345829374011051407049762498368475112200407998581965710911199478381458538564999339373561597556669858630449933022336001639238672514348879268977094473995928487098036503329367579608082050126258680892998004466291130065333440660657960607154910284826854946041522241076676218790731156113059849150436347897748257489168089325545563069338656580142352285120124695167415103852115900183184039250061848038170038955910499685095136470850024482618039781567116175123063060971029353537537940949225653954584795856434218388254377263078232720093142554482660815841195330626120746151361376840472800664250297309630095149306858763943782668238951557049164029293731001512204153431940870557378282860123711509186996754593800920644363462684536799144117089495323117260670285083561298515963939005298926253700458113573898405055020823759505701604729742728894766691409003558705250685199600162095246712031092228174987780192747801641068494664844300914000659787862062811085197711019899465923451386761105611124714084561644139724422144477539569165994703674725043686455067903774693136624874200669368102615968459463763070471854961705275257039930251374955137312249524252414602179119642552234360525821814532171002924820884475837733434404154182214779824640703317237766864198465294178868272146401168588586948475605092602897167946567078205930981938151529703179410674937193894874933582845618779033807356927462716552896219040399720199171999029730233354650008956392429530727270819476683748667264040822630511569679490812137737918763893961975128268345023597347429920409438467450504514713359239809033262001972627678339697441103531789287528347445037608111931477827446753198794190012458793436834087585516509436551524101200346549170980339534365944344364996448159774205263129284982958847219851850903537163498400991032749421834902212382833740805629379809048250917030778071960349557377116041853664365362829751250620331289241303043150284277204007294424203152199961239018607271327582839655534979462572303416888229816692009299139796925794359250806373277374068788602598994900216747756816830881363878667205182398064888411263102052633174009972554967476086053908659620132362911744

theorem mask30_eq : maskL 0 (tbl30.map Prod.fst) = mask30 := by decide +kernel

theorem cov30_1 : coverX 30 mask30 1 = true := by decide +kernel
theorem cov30_2 : coverX 30 mask30 2 = true := by decide +kernel
theorem cov30_3 : coverX 30 mask30 3 = true := by decide +kernel
theorem cov30_4 : coverX 30 mask30 4 = true := by decide +kernel
theorem cov30_5 : coverX 30 mask30 5 = true := by decide +kernel
theorem cov30_6 : coverX 30 mask30 6 = true := by decide +kernel
theorem cov30_7 : coverX 30 mask30 7 = true := by decide +kernel
theorem cov30_8 : coverX 30 mask30 8 = true := by decide +kernel
theorem cov30_9 : coverX 30 mask30 9 = true := by decide +kernel
theorem cov30_10 : coverX 30 mask30 10 = true := by decide +kernel
theorem cov30_11 : coverX 30 mask30 11 = true := by decide +kernel
theorem cov30_12 : coverX 30 mask30 12 = true := by decide +kernel
theorem cov30_13 : coverX 30 mask30 13 = true := by decide +kernel
theorem cov30_14 : coverX 30 mask30 14 = true := by decide +kernel
theorem cov30_15 : coverX 30 mask30 15 = true := by decide +kernel
theorem cov30_16 : coverX 30 mask30 16 = true := by decide +kernel
theorem cov30_17 : coverX 30 mask30 17 = true := by decide +kernel
theorem cov30_18 : coverX 30 mask30 18 = true := by decide +kernel
theorem cov30_19 : coverX 30 mask30 19 = true := by decide +kernel
theorem cov30_20 : coverX 30 mask30 20 = true := by decide +kernel
theorem cov30_21 : coverX 30 mask30 21 = true := by decide +kernel
theorem cov30_22 : coverX 30 mask30 22 = true := by decide +kernel
theorem cov30_23 : coverX 30 mask30 23 = true := by decide +kernel
theorem cov30_24 : coverX 30 mask30 24 = true := by decide +kernel
theorem cov30_25 : coverX 30 mask30 25 = true := by decide +kernel
theorem cov30_26 : coverX 30 mask30 26 = true := by decide +kernel
theorem cov30_27 : coverX 30 mask30 27 = true := by decide +kernel
theorem cov30_28 : coverX 30 mask30 28 = true := by decide +kernel
theorem cov30_29 : coverX 30 mask30 29 = true := by decide +kernel
theorem cov30_30 : coverX 30 mask30 30 = true := by decide +kernel

theorem cert30 : Cert 30 tbl30 := by
  refine ⟨by simp only [tbl30, tblOK_append, tbl30_0_ok, tbl30_1_ok, tbl30_2_ok, tbl30_3_ok, tbl30_4_ok, tbl30_5_ok, tbl30_6_ok, tbl30_7_ok, tbl30_8_ok, tbl30_9_ok, tbl30_10_ok, tbl30_11_ok, tbl30_12_ok, tbl30_13_ok, tbl30_14_ok, tbl30_15_ok, tbl30_16_ok, tbl30_17_ok, tbl30_18_ok, tbl30_19_ok, tbl30_20_ok, tbl30_21_ok, tbl30_22_ok, tbl30_23_ok, tbl30_24_ok, tbl30_25_ok, tbl30_26_ok, tbl30_27_ok, tbl30_28_ok, tbl30_29_ok, tbl30_30_ok, tbl30_31_ok, Bool.and_self], fun x h1 h2 => ?_⟩
  rw [mask30_eq]
  interval_cases x
  exacts [cov30_1, cov30_2, cov30_3, cov30_4, cov30_5, cov30_6, cov30_7, cov30_8, cov30_9, cov30_10, cov30_11, cov30_12, cov30_13, cov30_14, cov30_15, cov30_16, cov30_17, cov30_18, cov30_19, cov30_20, cov30_21, cov30_22, cov30_23, cov30_24, cov30_25, cov30_26, cov30_27, cov30_28, cov30_29, cov30_30]

/-! ## The 3-prefix analogue of Conjecture C for `N ≤ 30`, `N ≠ 7` -/

theorem cert_le_30 {N : Nat} (h3 : 3 ≤ N) (hN : N ≤ 30) (h7 : N ≠ 7) :
    ∃ tbl, Cert N tbl := by
  interval_cases N
  exacts [⟨_, cert3⟩, ⟨_, cert4⟩, ⟨_, cert5⟩, ⟨_, cert6⟩, absurd rfl h7, ⟨_, cert8⟩,
    ⟨_, cert9⟩, ⟨_, cert10⟩, ⟨_, cert11⟩, ⟨_, cert12⟩, ⟨_, cert13⟩, ⟨_, cert14⟩, ⟨_, cert15⟩,
    ⟨_, cert16⟩, ⟨_, cert17⟩, ⟨_, cert18⟩, ⟨_, cert19⟩, ⟨_, cert20⟩, ⟨_, cert21⟩, ⟨_, cert22⟩,
    ⟨_, cert23⟩, ⟨_, cert24⟩, ⟨_, cert25⟩, ⟨_, cert26⟩, ⟨_, cert27⟩, ⟨_, cert28⟩, ⟨_, cert29⟩,
    ⟨_, cert30⟩]

/-- **The 3-prefix analogue of Conjecture C for `N ≤ 30` (`N ≠ 7`).**  A valid 3-prefix
`(x, y, z)` extends to a full semi-symmetric fold sequence iff its set is not one of the dead
3-sets `D_j = {1, 2j, 2j+1}` (`2 ≤ j`, `4j ≤ N + 3`), their mirror images, and (odd `N ≥ 7`)
the 3-subsets of `{1, 2, N-1, N}`.  (For `N = 7` the set `{1, 4, 7}`, through the sporadic dead
pair `{1, 7}`, is dead as well.) -/
theorem extends3_iff_le_30 {N x y z : Nat} (hN : N ≤ 30) (h7 : N ≠ 7) (hx : 1 ≤ x ∧ x ≤ N)
    (hy : 1 ≤ y ∧ y ≤ N) (hz : 1 ≤ z ∧ z ≤ N) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hv : SemiSymmetric N [x, y, z]) : Extends N [x, y, z] ↔ ¬ Dead3 N {x, y, z} := by
  obtain ⟨tbl, hc⟩ := cert_le_30 (by omega) hN h7
  exact extends3_iff_of_cert (by omega) hc hx hy hz hxy hxz hyz hv

end Live3p
end Folds
