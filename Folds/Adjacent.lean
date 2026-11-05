import Folds.Live4

/-!
# The Adjacent Lemma: every interval is co-reachable

`experiments/adjacent/PROOFS.txt`.

* `greedy`: **the centre greedy.**  Fix a centre `c = c2 / 2`.  Starting from any list `S` of
  placed panels, repeatedly place, among the unplaced panels of a target set `U` whose step is
  valid, one closest to `c`.  If every unplaced panel `m` left of `c` has at most as many
  placed panels in its left arm as in its right arm, and every unplaced panel right of `c` at
  least as many (the sign invariant `Inv`), and every panel of the strip is placed or in `U`,
  then this never gets stuck: the outermost unplaced panel on either side has one arm full,
  which together with the invariant makes it valid; and placing the panel `x` closest to `c`
  keeps the invariant, because a panel `m` whose arm count moves the wrong way lies between `x`
  and `c`, so it is closer to `c` than `x` and hence was not valid (strict sign).
* `coReach_of_inward` (**Theorem G**): a set `B` is co-reachable as soon as the panels outside
  `B` that `B` pulls to the right (more of `B` in the right arm) all lie left of the panels
  that `B` pulls to the left.  Proof: run the greedy on the background `B` and read the
  resulting order backwards (`semiStep_compl`).
* `coReach_interval`, `coReach_adjacent`: every interval `[a, b]`, in particular every adjacent
  pair `{r, r + 1}` (the **Adjacent Lemma**), is co-reachable; `extends_interval`: every valid
  prefix whose set is an interval is live.
* `coReach_mult`: a mirror-symmetric set that pulls no panel of the left half to the left
  satisfies Theorem G (`inward_of_symm`); so the multiples of `q` are co-reachable whenever
  `q ∣ N + 1` (for `q` not a power of 2 these are exceptional classes of live2/live3, which have
  no residue chain), and `coReach_mult_transfer` transfers co-reachability through them.
* `Cov3`: the closure of `Live4.Cov2` and of all sets satisfying the criterion of Theorem G
  under residue transfers through good classes and through the multiples of `q` (`q ∣ N + 1`),
  and the mirror; `Cov3.coReach`, `Cov3.extends`.  `experiments/adjacent/covlean5.py` computes
  the family (see PROOFS.txt section 3 for the numbers).
-/

namespace Folds
namespace Adjacent

open Live2 Live4

/-! ## Arm counts under appending one panel -/

theorem leftCount_le_reach (N : Nat) (S : List Nat) (m : Nat) :
    leftCount N S m ≤ reach N m := by
  unfold leftCount
  exact (List.countP_le_length).trans (by simp)

theorem rightCount_le_reach (N : Nat) (S : List Nat) (m : Nat) :
    rightCount N S m ≤ reach N m := by
  unfold rightCount
  exact (List.countP_le_length).trans (by simp)

theorem leftCount_full {N m : Nat} {S : List Nat}
    (h : ∀ d, 1 ≤ d → d ≤ reach N m → m - d ∈ S) : leftCount N S m = reach N m := by
  unfold leftCount
  rw [List.countP_eq_length.2]
  · simp
  · intro d hd
    rw [List.mem_range'_1] at hd
    simpa using h d hd.1 (by omega)

theorem rightCount_full {N m : Nat} {S : List Nat}
    (h : ∀ d, 1 ≤ d → d ≤ reach N m → m + d ∈ S) : rightCount N S m = reach N m := by
  unfold rightCount
  rw [List.countP_eq_length.2]
  · simp
  · intro d hd
    rw [List.mem_range'_1] at hd
    simpa using h d hd.1 (by omega)

section concat
variable {N m x : Nat} {S : List Nat}

theorem leftCount_concat_ge (hnd : (S ++ [x]).Nodup) :
    leftCount N S m ≤ leftCount N (S ++ [x]) m := by
  rw [leftCount_eq hnd, leftCount_eq (List.nodup_append.1 hnd).1, List.countP_append]
  omega

theorem leftCount_concat_le (hnd : (S ++ [x]).Nodup) :
    leftCount N (S ++ [x]) m ≤ leftCount N S m + 1 := by
  rw [leftCount_eq hnd, leftCount_eq (List.nodup_append.1 hnd).1, List.countP_append]
  have : List.countP (fun y => decide (m - reach N m ≤ y ∧ y < m)) [x] ≤ 1 :=
    (List.countP_le_length).trans (by simp)
  omega

theorem leftCount_concat_of_le (hnd : (S ++ [x]).Nodup) (hx : m ≤ x) :
    leftCount N (S ++ [x]) m = leftCount N S m := by
  rw [leftCount_eq hnd, leftCount_eq (List.nodup_append.1 hnd).1, List.countP_append]
  have : List.countP (fun y => decide (m - reach N m ≤ y ∧ y < m)) [x] = 0 := by
    rw [List.countP_eq_zero]; intro y hy; simp at hy; subst hy; simp; omega
  omega

theorem rightCount_concat_ge (hnd : (S ++ [x]).Nodup) :
    rightCount N S m ≤ rightCount N (S ++ [x]) m := by
  rw [rightCount_eq hnd, rightCount_eq (List.nodup_append.1 hnd).1, List.countP_append]
  omega

theorem rightCount_concat_le (hnd : (S ++ [x]).Nodup) :
    rightCount N (S ++ [x]) m ≤ rightCount N S m + 1 := by
  rw [rightCount_eq hnd, rightCount_eq (List.nodup_append.1 hnd).1, List.countP_append]
  have : List.countP (fun y => decide (m < y ∧ y ≤ m + reach N m)) [x] ≤ 1 :=
    (List.countP_le_length).trans (by simp)
  omega

theorem rightCount_concat_of_le (hnd : (S ++ [x]).Nodup) (hx : x ≤ m) :
    rightCount N (S ++ [x]) m = rightCount N S m := by
  rw [rightCount_eq hnd, rightCount_eq (List.nodup_append.1 hnd).1, List.countP_append]
  have : List.countP (fun y => decide (m < y ∧ y ≤ m + reach N m)) [x] = 0 := by
    rw [List.countP_eq_zero]; intro y hy; simp at hy; subst hy; simp; omega
  omega

end concat

/-! ## The centre greedy -/

/-- Twice the distance from `x` to the centre `c2 / 2`. -/
def dist2 (c2 x : Nat) : Nat := if 2 * x ≤ c2 then c2 - 2 * x else 2 * x - c2

/-- The sign invariant: unplaced panels left of the centre are not heavier on the left,
unplaced panels right of the centre are not heavier on the right. -/
def Inv (N c2 : Nat) (S : List Nat) (U : Finset Nat) : Prop :=
  ∀ m ∈ U, (2 * m < c2 → leftCount N S m ≤ rightCount N S m) ∧
    (c2 < 2 * m → rightCount N S m ≤ leftCount N S m)

/-- **The centre greedy never gets stuck.**  If every panel of the strip is placed (in `S`) or
still to be placed (in `U`), no panel of `U` sits exactly at the centre, and the sign
invariant holds, then `U` can be appended to `S` with every step valid. -/
theorem greedy (N c2 : Nat) : ∀ (n : Nat) (S : List Nat) (U : Finset Nat), U.card = n →
    S.Nodup → (∀ m ∈ U, m ∉ S) → (∀ m ∈ U, 1 ≤ m ∧ m ≤ N) →
    (∀ z, 1 ≤ z → z ≤ N → z ∈ S ∨ z ∈ U) → (∀ m ∈ U, 2 * m ≠ c2) → Inv N c2 S U →
    ∃ l : List Nat, l.Nodup ∧ l.toFinset = U ∧
      ∀ k (hk : k < l.length), SemiStep N (S ++ l.take k) l[k] := by
  intro n
  induction n with
  | zero =>
    intro S U hc _ _ _ _ _ _
    rw [Finset.card_eq_zero] at hc
    subst hc
    exact ⟨[], List.nodup_nil, by simp, fun k hk => absurd hk (by simp)⟩
  | succ n ih =>
    intro S U hc hS hUS hUN hcov hc2 hinv
    have hne : U.Nonempty := by rw [← Finset.card_pos, hc]; omega
    -- a valid panel exists: the outermost unplaced panel on one side
    have hV : (U.filter (fun m => SemiStep N S m)).Nonempty := by
      by_cases hA : ∃ y ∈ U, c2 < 2 * y
      · have hF : (U.filter (fun y => c2 < 2 * y)).Nonempty := by
          obtain ⟨y, hy, hy2⟩ := hA
          exact ⟨y, Finset.mem_filter.2 ⟨hy, hy2⟩⟩
        have hM := Finset.max'_mem _ hF
        have hMmax : ∀ y ∈ U, c2 < 2 * y → y ≤ (U.filter (fun y => c2 < 2 * y)).max' hF :=
          fun y hy hy2 => Finset.le_max' _ y (Finset.mem_filter.2 ⟨hy, hy2⟩)
        rw [Finset.mem_filter] at hM
        refine ⟨_, Finset.mem_filter.2 ⟨hM.1, ?_⟩⟩
        have hr := rightCount_full (N := N) (S := S)
          (m := (U.filter (fun y => c2 < 2 * y)).max' hF) (fun d hd1 hd2 => by
            have hMN := hUN _ hM.1
            have h' : (U.filter (fun y => c2 < 2 * y)).max' hF + d ≤ N := by
              unfold reach at hd2; omega
            rcases hcov _ (by omega) h' with h | h
            · exact h
            · have := hMmax _ h (by omega); omega)
        have hl := leftCount_le_reach N S ((U.filter (fun y => c2 < 2 * y)).max' hF)
        have := (hinv _ hM.1).2 hM.2
        unfold SemiStep; omega
      · push Not at hA
        have hm0 := Finset.min'_mem U hne
        have hmin : ∀ y ∈ U, U.min' hne ≤ y := fun y hy => Finset.min'_le U y hy
        refine ⟨_, Finset.mem_filter.2 ⟨hm0, ?_⟩⟩
        have hlt : 2 * U.min' hne < c2 := by
          have := hA _ hm0; have := hc2 _ hm0; omega
        have hl := leftCount_full (N := N) (S := S) (m := U.min' hne) (fun d hd1 hd2 => by
          have hmN := hUN _ hm0
          have h' : 1 ≤ U.min' hne - d := by unfold reach at hd2; omega
          rcases hcov _ h' (by omega) with h | h
          · exact h
          · have := hmin _ h; omega)
        have hr := rightCount_le_reach N S (U.min' hne)
        have := (hinv _ hm0).1 hlt
        unfold SemiStep; omega
    -- the valid panel closest to the centre
    obtain ⟨x, hxV, hxmin⟩ := Finset.exists_min_image _ (dist2 c2) hV
    rw [Finset.mem_filter] at hxV
    obtain ⟨hxU, hxv⟩ := hxV
    have hxS : x ∉ S := hUS x hxU
    have hS' : (S ++ [x]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hS, List.nodup_singleton x, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      intro hab; subst hab; exact hxS ha
    have hinv' : Inv N c2 (S ++ [x]) (U.erase x) := by
      intro m hm
      rw [Finset.mem_erase] at hm
      obtain ⟨hmx, hmU⟩ := hm
      constructor
      · intro hlt
        have h0 := (hinv m hmU).1 hlt
        have hR1 := rightCount_concat_ge (N := N) (m := m) hS'
        by_cases hxm : x < m
        · have hnv : ¬ SemiStep N S m := by
            intro hv
            have := hxmin m (Finset.mem_filter.2 ⟨hmU, hv⟩)
            unfold dist2 at this; split_ifs at this <;> omega
          unfold SemiStep at hnv
          have hL2 := leftCount_concat_le (N := N) (m := m) hS'
          omega
        · have hL3 := leftCount_concat_of_le (N := N) (m := m) hS' (by omega)
          omega
      · intro hgt
        have h0 := (hinv m hmU).2 hgt
        have hL1 := leftCount_concat_ge (N := N) (m := m) hS'
        by_cases hxm : m < x
        · have hnv : ¬ SemiStep N S m := by
            intro hv
            have := hxmin m (Finset.mem_filter.2 ⟨hmU, hv⟩)
            unfold dist2 at this; split_ifs at this <;> omega
          unfold SemiStep at hnv
          have hR2 := rightCount_concat_le (N := N) (m := m) hS'
          omega
        · have hR3 := rightCount_concat_of_le (N := N) (m := m) hS' (by omega)
          omega
    obtain ⟨l, hl1, hl2, hl3⟩ := ih (S ++ [x]) (U.erase x)
      (by rw [Finset.card_erase_of_mem hxU, hc]; rfl) hS'
      (fun m hm => by
        rw [Finset.mem_erase] at hm
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hUS m hm.2, hm.1⟩)
      (fun m hm => hUN m (Finset.mem_of_mem_erase hm))
      (fun z hz1 hz2 => by
        rcases hcov z hz1 hz2 with h | h
        · left; simp [h]
        · by_cases hzx : z = x
          · left; simp [hzx]
          · right; exact Finset.mem_erase.2 ⟨hzx, h⟩)
      (fun m hm => hc2 m (Finset.mem_of_mem_erase hm)) hinv'
    refine ⟨x :: l, ?_, ?_, ?_⟩
    · rw [List.nodup_cons]
      refine ⟨fun h => ?_, hl1⟩
      have := List.mem_toFinset.2 h
      rw [hl2] at this
      simp at this
    · rw [List.toFinset_cons, hl2, Finset.insert_erase hxU]
    · intro k hk
      cases k with
      | zero => simpa using hxv
      | succ k =>
        have := hl3 k (by simp at hk; omega)
        simpa [List.take_succ_cons, List.append_assoc] using this

/-! ## Reading a sequence on a background backwards -/

/-- If `B ++ l` is a complete sequence and every step of `l` is valid after `B` and the
earlier steps of `l`, then `l` read backwards is valid from scratch (whatever `B` is). -/
theorem semiSymmetric_reverse_of_bg {N : Nat} {B l : List Nat} (hf : IsFoldSeq N (B ++ l))
    (h : ∀ k (hk : k < l.length), SemiStep N (B ++ l.take k) l[k]) :
    SemiSymmetric N l.reverse := by
  intro j hj
  have hjl : j < l.length := by simpa using hj
  have hil : l.length - 1 - j < l.length := by omega
  have e : B ++ l = (B ++ l.take (l.length - 1 - j)) ++ [l[l.length - 1 - j]] ++
      l.drop (l.length - 1 - j + 1) := by
    simp only [List.append_assoc, List.singleton_append]
    rw [← List.drop_eq_getElem_cons hil, List.take_append_drop]
  rw [e] at hf
  have h1 := (semiStep_compl hf).1 (h _ hil)
  rw [List.take_reverse, List.getElem_reverse]
  rw [show l.length - j = l.length - 1 - j + 1 by omega]
  exact (semiStep_congr fun x => by simp).1 h1

/-! ## Theorem G and the Adjacent Lemma -/

/-- The criterion of Theorem G for a set `B` and a centre `c2 / 2`. -/
def Inward (N c2 : Nat) (B : Finset Nat) : Prop :=
  ∀ m, 1 ≤ m → m ≤ N → m ∉ B → 2 * m ≠ c2 ∧
    (2 * m < c2 → leftCount N B.toList m ≤ rightCount N B.toList m) ∧
    (c2 < 2 * m → rightCount N B.toList m ≤ leftCount N B.toList m)

/-- **Theorem G.**  If every panel outside `B` that `B` pulls to the right lies left of the
centre and every panel that `B` pulls to the left lies right of it, then `B` is
co-reachable. -/
theorem coReach_of_inward {N c2 : Nat} {B : Finset Nat} (hB : B ⊆ Finset.Icc 1 N)
    (h : Inward N c2 B) : CoReach N B := by
  obtain ⟨l, hl1, hl2, hl3⟩ := greedy N c2 _ B.toList (Finset.Icc 1 N \ B) rfl
    (Finset.nodup_toList B)
    (fun m hm => by rw [Finset.mem_sdiff] at hm; simpa using hm.2)
    (fun m hm => by rw [Finset.mem_sdiff, Finset.mem_Icc] at hm; exact hm.1)
    (fun z hz1 hz2 => by
      by_cases hz : z ∈ B
      · left; simpa using hz
      · right; simp only [Finset.mem_sdiff, Finset.mem_Icc]; exact ⟨⟨hz1, hz2⟩, hz⟩)
    (fun m hm => by
      rw [Finset.mem_sdiff, Finset.mem_Icc] at hm; exact (h m hm.1.1 hm.1.2 hm.2).1)
    (fun m hm => by
      rw [Finset.mem_sdiff, Finset.mem_Icc] at hm; exact (h m hm.1.1 hm.1.2 hm.2).2)
  have hf : IsFoldSeq N (B.toList ++ l) := by
    unfold IsFoldSeq
    have hnd : (B.toList ++ l).Nodup := by
      rw [List.nodup_append]
      refine ⟨Finset.nodup_toList B, hl1, ?_⟩
      intro a ha b hb hab
      subst hab
      have := List.mem_toFinset.2 hb
      rw [hl2, Finset.mem_sdiff] at this
      exact this.2 (Finset.mem_toList.1 ha)
    rw [List.perm_ext_iff_of_nodup hnd List.nodup_range']
    intro x
    rw [List.mem_append, Finset.mem_toList, List.mem_range'_1, ← List.mem_toFinset, hl2,
      Finset.mem_sdiff, Finset.mem_Icc]
    constructor
    · rintro (hx | hx)
      · have := Finset.mem_Icc.1 (hB hx); omega
      · omega
    · intro hx
      by_cases hxB : x ∈ B
      · left; exact hxB
      · right; exact ⟨⟨hx.1, by omega⟩, hxB⟩
  unfold CoReach g
  rw [Finset.card_pos]
  exact ⟨l.reverse, mem_semiOrders.2 ⟨⟨List.nodup_reverse.2 hl1, by
    rw [List.toFinset_reverse, hl2]⟩, semiSymmetric_reverse_of_bg hf hl3⟩⟩

/-- Every interval satisfies the criterion of Theorem G, with the centre of the interval. -/
theorem inward_interval {N a b : Nat} (hab : a ≤ b) : Inward N (a + b) (Finset.Icc a b) := by
  intro m _ _ hmB
  rw [Finset.mem_Icc] at hmB
  have hnd := Finset.nodup_toList (Finset.Icc a b)
  refine ⟨by omega, fun hlt => ?_, fun hgt => ?_⟩
  · have : leftCount N (Finset.Icc a b).toList m = 0 := by
      rw [leftCount_eq hnd, List.countP_eq_zero]
      intro x hx
      simp only [Finset.mem_toList, Finset.mem_Icc] at hx
      simp only [decide_eq_true_eq, not_and, not_lt]
      intro _; omega
    omega
  · have : rightCount N (Finset.Icc a b).toList m = 0 := by
      rw [rightCount_eq hnd, List.countP_eq_zero]
      intro x hx
      simp only [Finset.mem_toList, Finset.mem_Icc] at hx
      simp only [decide_eq_true_eq, not_and, not_le]
      intro _; omega
    omega

/-- **Every interval is co-reachable**: `[1, N] \ [a, b]` has a semi-symmetric ordering. -/
theorem coReach_interval {N a b : Nat} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ N) :
    CoReach N (Finset.Icc a b) :=
  coReach_of_inward (fun x hx => by rw [Finset.mem_Icc] at *; omega) (inward_interval hab)

/-- **The Adjacent Lemma**: `[1, N] \ {r, r + 1}` has a semi-symmetric ordering. -/
theorem coReach_adjacent {N r : Nat} (hr : 1 ≤ r) (hrN : r + 1 ≤ N) :
    CoReach N {r, r + 1} := by
  have : ({r, r + 1} : Finset Nat) = Finset.Icc r (r + 1) := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc]; omega
  rw [this]
  exact coReach_interval hr (by omega) hrN

/-- Every valid prefix whose panels form an interval is live. -/
theorem extends_interval {N a b : Nat} {p : List Nat} (hnd : p.Nodup)
    (hv : SemiSymmetric N p) (hp : p.toFinset = Finset.Icc a b) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ N) :
    Extends N p := by
  rw [extends_iff_coReach hnd (fun x hx => by
    have := List.mem_toFinset.2 hx; rw [hp, Finset.mem_Icc] at this; omega) hv, hp]
  exact coReach_interval ha hab hb

/-! ## Mirror-symmetric sets; the multiples of `q` when `q ∣ N + 1` -/

theorem leftCount_mirror {N m : Nat} {L : List Nat} (hnd : L.Nodup)
    (hL : ∀ x ∈ L, 1 ≤ x ∧ x ≤ N) (hsym : ∀ x ∈ L, N + 1 - x ∈ L) (hm1 : 1 ≤ m)
    (hmN : m ≤ N) : leftCount N L m = rightCount N L (N + 1 - m) := by
  have hreach : reach N (N + 1 - m) = reach N m := by unfold reach; omega
  rw [leftCount_eq hnd, rightCount_eq hnd, hreach]
  have hperm : (L.map (N + 1 - ·)).Perm L := by
    rw [List.perm_ext_iff_of_nodup (nodup_map_of_injOn hnd fun a ha b hb e => by
      have := hL a ha; have := hL b hb; omega) hnd]
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hsym y hy
    · intro hx
      exact List.mem_map.2 ⟨N + 1 - x, hsym x hx, by have := hL x hx; omega⟩
  rw [← hperm.countP_eq, List.countP_map]
  apply List.countP_congr
  intro x hx
  have := hL x hx
  simp only [Function.comp_apply, decide_eq_true_eq]
  omega

/-- A mirror-symmetric set whose imbalance is `≤ 0` at every panel of the left half satisfies
the criterion of Theorem G (centre: the middle of the strip). -/
theorem inward_of_symm {N : Nat} {B : Finset Nat} (hB : B ⊆ Finset.Icc 1 N)
    (hsym : ∀ x ∈ B, N + 1 - x ∈ B)
    (hleft : ∀ m, 1 ≤ m → 2 * m ≤ N + 1 → m ∉ B →
      leftCount N B.toList m ≤ rightCount N B.toList m) :
    Inward N (2 * ((N + 1) / 2) + 1) B := by
  have hL : ∀ x ∈ B.toList, 1 ≤ x ∧ x ≤ N := fun x hx => by
    have := hB (Finset.mem_toList.1 hx); rwa [Finset.mem_Icc] at this
  have hs : ∀ x ∈ B.toList, N + 1 - x ∈ B.toList := fun x hx =>
    Finset.mem_toList.2 (hsym x (Finset.mem_toList.1 hx))
  have hnd := Finset.nodup_toList B
  intro m hm1 hmN hmB
  refine ⟨by omega, fun hlt => hleft m hm1 (by omega) hmB, fun hgt => ?_⟩
  have hm' : N + 1 - m ∉ B := fun h => hmB (by
    have := hsym _ h; rwa [show N + 1 - (N + 1 - m) = m by omega] at this)
  have h := hleft (N + 1 - m) (by omega) (by omega) hm'
  rw [leftCount_mirror hnd hL hs (by omega) (by omega),
    show N + 1 - (N + 1 - m) = m by omega] at h
  rw [leftCount_mirror hnd hL hs hm1 hmN]
  exact h

theorem mod_class_q {q x : Nat} (hq : 0 < q) (hx : 1 ≤ x) :
    (x - 1) % q + 1 = q ↔ x % q = 0 := by
  have hlt := Nat.mod_lt (x - 1) hq
  have e : x % q = ((x - 1) % q + 1) % q := by
    conv_lhs => rw [show x = (x - 1) + 1 by omega]
    rw [Nat.add_mod]
    rcases Nat.lt_or_ge 1 q with h1 | h1
    · rw [Nat.mod_eq_of_lt h1]
    · have : q = 1 := by omega
      subst this; simp
  rw [e]
  constructor
  · intro h; rw [h, Nat.mod_self]
  · intro h
    rcases Nat.lt_or_ge ((x - 1) % q + 1) q with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h; omega
    · omega

/-- **The multiples of `q` are co-reachable when `q ∣ N + 1`** (for `q` not a power of 2 these
are the exceptional classes `C_q`, `N ≡ -1 (mod q)`, of live2/live3): they are mirror-symmetric,
and at a panel `m` of the left half `⌊(m-1)/q⌋ ≤ ⌊(m mod q + m - 1)/q⌋` multiples lie left vs
right. -/
theorem coReach_mult {q N : Nat} (hq : 0 < q) (hN : (N + 1) % q = 0) :
    CoReach N (rPanels q N q).toFinset := by
  have hmem : ∀ x, x ∈ rPanels q N q ↔ 1 ≤ x ∧ x ≤ N ∧ x % q = 0 := by
    intro x
    rw [mem_rPanels_iff hq (by omega) le_rfl]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (mod_class_q hq h1).1 h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (mod_class_q hq h1).2 h3⟩
  have hnodup : (rPanels q N q).Nodup := by
    unfold rPanels classPanels
    refine nodup_map_of_injOn List.nodup_range' fun a ha b hb e => ?_
    rw [List.mem_range'_1] at ha hb
    unfold cls at e
    have : (a - 1) * q = (b - 1) * q := by omega
    have := Nat.eq_of_mul_eq_mul_right hq this
    omega
  have hperm : (rPanels q N q).toFinset.toList.Perm (rPanels q N q) := by
    rw [List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hnodup]
    intro x; rw [Finset.mem_toList, List.mem_toFinset]
  have hB : (rPanels q N q).toFinset ⊆ Finset.Icc 1 N := by
    intro x hx
    rw [List.mem_toFinset, hmem] at hx
    rw [Finset.mem_Icc]; exact ⟨hx.1, hx.2.1⟩
  refine coReach_of_inward hB (inward_of_symm hB ?_ ?_)
  · intro x hx
    rw [List.mem_toFinset, hmem] at hx ⊢
    refine ⟨by omega, by omega, ?_⟩
    exact Nat.sub_mod_eq_zero_of_mod_eq (by rw [hN, hx.2.2])
  · intro m hm1 hm2 _
    have hnd := Finset.nodup_toList (rPanels q N q).toFinset
    have hr : reach N m = m - 1 := by unfold reach; omega
    rw [leftCount_eq hnd, rightCount_eq hnd, hperm.countP_eq, hperm.countP_eq, hr,
      countP_left_rPanels hq (by omega) le_rfl (by omega) (by omega),
      countP_right_rPanels hq (by omega) le_rfl hm1 (by omega)]
    apply Nat.div_le_div_right
    rw [show m - (m - 1) - 1 + q - q = 0 by omega, Nat.zero_mod]
    omega

/-- **Transfer through the multiples of `q` when `q ∣ N + 1`** (a window copy with reachable
complement): co-reachable sets of its strip stay co-reachable. -/
theorem coReach_mult_transfer {q N : Nat} (hq : 0 < q) (hqN : q ≤ N) (hN : (N + 1) % q = 0)
    {D : Finset Nat} (hDs : D ⊆ Finset.Icc 1 (ccount q q N)) (hD : CoReach (ccount q q N) D) :
    CoReach N (D.image (cls q q)) := by
  refine coReach_winEmb (winEmb_res hq (by omega) le_rfl hqN) ?_ hDs hD
  have e : (Finset.Icc 1 (ccount q q N)).image (cls q q) = (rPanels q N q).toFinset := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Icc, List.mem_toFinset, rPanels, classPanels,
      List.mem_map, List.mem_range'_1]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, ⟨hy.1, by omega⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, ⟨hy.1, by omega⟩, rfl⟩
  rw [e]
  exact coReach_mult hq hN

/-! ## The enlarged proven family -/

/-- `Cov3`: the closure of `Cov2` and of the sets satisfying Theorem G (in particular every
interval and every adjacent pair) under residue transfers through good classes, through the
multiples of `q` when `q ∣ N + 1` (`coReach_mult_transfer`), and the mirror. -/
inductive Cov3 : Nat → Finset Nat → Prop
  | cov2 {N : Nat} {D : Finset Nat} : Cov2 N D → Cov3 N D
  | inward {N c2 : Nat} {D : Finset Nat} : D ⊆ Finset.Icc 1 N → Inward N c2 D → Cov3 N D
  | res {q N s : Nat} {D : Finset Nat} : 2 ≤ q → q ≤ N → Good q (N % q) s →
      D ⊆ Finset.Icc 1 (ccount q s N) → Cov3 (ccount q s N) D → Cov3 N (D.image (cls q s))
  | mult {q N : Nat} {D : Finset Nat} : 2 ≤ q → q ≤ N → (N + 1) % q = 0 →
      D ⊆ Finset.Icc 1 (ccount q q N) → Cov3 (ccount q q N) D → Cov3 N (D.image (cls q q))
  | mirror {N : Nat} {D : Finset Nat} : Cov3 N D → Cov3 N (D.image (N + 1 - ·))

theorem Cov3.coReach {N : Nat} {D : Finset Nat} (h : Cov3 N D) : CoReach N D := by
  induction h with
  | cov2 h => exact h.coReach
  | inward hD hi => exact coReach_of_inward hD hi
  | res hq2 hqN hg hDs _ ih => exact coReach_good (by omega) hqN hg hDs ih
  | mult hq2 hqN hN hDs _ ih => exact coReach_mult_transfer (by omega) hqN hN hDs ih
  | mirror _ ih => exact coReach_mirror ih

theorem Cov3.adjacent {N r : Nat} (hr : 1 ≤ r) (hrN : r + 1 ≤ N) : Cov3 N {r, r + 1} := by
  have : ({r, r + 1} : Finset Nat) = Finset.Icc r (r + 1) := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc]; omega
  rw [this]
  exact Cov3.inward (fun x hx => by rw [Finset.mem_Icc] at *; omega) (inward_interval (by omega))

/-- Every valid 2-prefix whose set is in the family is live. -/
theorem Cov3.extends {N u v : Nat} (h : Cov3 N {u, v}) (hu : 1 ≤ u ∧ u ≤ N)
    (hv : 1 ≤ v ∧ v ≤ N) (huv : u ≠ v) (hval : SemiSymmetric N [u, v]) :
    Extends N [u, v] := by
  rw [extends_iff_coReach (by simp [huv]) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption) hval]
  convert h.coReach using 2
  ext x; simp

end Adjacent
end Folds
