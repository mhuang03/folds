import Folds.Live3p

/-!
# Live 3-prefixes, part 2: induction on `N` through copies

`experiments/live3q/PROOFS.txt`.

* `Good3 N`: every valid (`valid3B`), non-dead (`dead3B`) sorted triple of `[N]` is
  co-reachable; `extends3_iff_of_good3` turns it into the liveness iff for 3-prefixes;
  `good3_le_30` from the certificates of `Live3p`.
* `stepsB`, `coReach_of_stepsB`: Theorem G after an explicit list of valid steps.
* `copyF`, `copyOK`, `transfers_of_copyOK`, `trB`, `coReach_of_trB`: transfers of valid
  non-dead triples of a smaller strip through six copy families (centred and right-aligned
  Beatty, residue classes, multiples of `q ∣ N + 1`, swapped Beatty, `{1, 4, 6, …, N}`).
* `Covered3S`, `Residual3`, `good3_of_residual`: **reduction for all `N`**: the 3-prefix
  property for every `N ≠ 7` follows from the co-reachability of the residual triples (not
  settled by Theorem G, Theorem G after ≤ 2 steps, or a transfer from a smaller strip, for the
  triple or its mirror image) above the certified range.
* `Hint`, `decH`, `chkR`, `good3_of_cov`: packed per-triple certificates.
* `extends3_iff_le_50`: **the 3-prefix analogue of Conjecture C for every `N ≤ 50`, `N ≠ 7`**;
  `extends3_iff_of_residual`: for all `N ≠ 7`, modulo `Residual3 N` for `N > 50`.
-/

namespace Folds
namespace Live3q

open Live2 Live4 Adjacent Live5 Live6 Live7 Live3p

/-! ## Valid 3-sets -/

/-- Some ordering of `{a, b, c}` is a valid 3-prefix. -/
def valid3B (N a b c : Nat) : Bool :=
  (step2B N a a b && step2B N a b c) || (step2B N a a c && step2B N a c b) ||
  (step2B N b b a && step2B N b a c) || (step2B N b b c && step2B N b c a) ||
  (step2B N c c a && step2B N c a b) || (step2B N c c b && step2B N c b a)

theorem semiSymmetric3 {N x y z : Nat} (h1 : SemiStep N [x] y) (h2 : SemiStep N [x, y] z) :
    SemiSymmetric N [x, y, z] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  interval_cases k
  · simp [SemiStep, leftCount, rightCount]
  · simpa using h1
  · simpa using h2

/-- A valid ordering of a sorted triple, as one of the six permutations. -/
theorem valid3_of_B {N a b c : Nat} (hab : a < b) (hbc : b < c) (h : valid3B N a b c = true) :
    ∃ x y z, ((x = a ∧ y = b ∧ z = c) ∨ (x = a ∧ y = c ∧ z = b) ∨ (x = b ∧ y = a ∧ z = c) ∨
      (x = b ∧ y = c ∧ z = a) ∨ (x = c ∧ y = a ∧ z = b) ∨ (x = c ∧ y = b ∧ z = a)) ∧
      SemiStep N [x] y ∧ SemiStep N [x, y] z := by
  unfold valid3B at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (((((h | h) | h) | h) | h) | h)
  · exact ⟨a, b, c, by omega, step1B_iff.1 h.1, (step2B_iff (by omega)).1 h.2⟩
  · exact ⟨a, c, b, by omega, step1B_iff.1 h.1, (step2B_iff (by omega)).1 h.2⟩
  · exact ⟨b, a, c, by omega, step1B_iff.1 h.1, (step2B_iff (by omega)).1 h.2⟩
  · exact ⟨b, c, a, by omega, step1B_iff.1 h.1, (step2B_iff (by omega)).1 h.2⟩
  · exact ⟨c, a, b, by omega, step1B_iff.1 h.1, (step2B_iff (by omega)).1 h.2⟩
  · exact ⟨c, b, a, by omega, step1B_iff.1 h.1, (step2B_iff (by omega)).1 h.2⟩

/-- Conversely, every valid 3-prefix has a sorted set with `valid3B`. -/
theorem valid3B_of {N x y z : Nat} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h1 : SemiStep N [x] y) (h2 : SemiStep N [x, y] z) :
    valid3B N (min x (min y z)) (x + y + z - min x (min y z) - max x (max y z))
      (max x (max y z)) = true := by
  have e1 := step1B_iff.2 h1
  have e2 := (step2B_iff hxy).2 h2
  rcases Nat.lt_or_gt_of_ne hxy with h | h <;> rcases Nat.lt_or_gt_of_ne hxz with h' | h' <;>
    rcases Nat.lt_or_gt_of_ne hyz with h'' | h''
  · rw [show min x (min y z) = x by omega, show max x (max y z) = z by omega,
      show x + y + z - x - z = y by omega]; simp [valid3B, e1, e2]
  · rw [show min x (min y z) = x by omega, show max x (max y z) = y by omega,
      show x + y + z - x - y = z by omega]; simp [valid3B, e1, e2]
  · omega
  · rw [show min x (min y z) = z by omega, show max x (max y z) = y by omega,
      show x + y + z - z - y = x by omega]; simp [valid3B, e1, e2]
  · rw [show min x (min y z) = y by omega, show max x (max y z) = z by omega,
      show x + y + z - y - z = x by omega]; simp [valid3B, e1, e2]
  · omega
  · rw [show min x (min y z) = y by omega, show max x (max y z) = x by omega,
      show x + y + z - y - x = z by omega]; simp [valid3B, e1, e2]
  · rw [show min x (min y z) = z by omega, show max x (max y z) = x by omega,
      show x + y + z - z - x = y by omega]; simp [valid3B, e1, e2]

/-- **The 3-prefix property of a strip**: every valid, non-dead sorted triple is
co-reachable. -/
def Good3 (N : Nat) : Prop :=
  ∀ a b c, 1 ≤ a → a < b → b < c → c ≤ N → valid3B N a b c = true → dead3B N a b c = false →
    CoReach N {a, b, c}

/-! ## The certificates of `Live3p` give `Good3` for `N ≤ 30`, `N ≠ 7` -/

theorem ok3_of_cert {N : Nat} {tbl : List (Nat × Nat)} (hc : Cert N tbl)
    {x y z : Nat} (hx : 1 ≤ x ∧ x ≤ N) (hy : 1 ≤ y ∧ y ≤ N) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hz : 1 ≤ z ∧ z ≤ N) (h1 : SemiStep N [x] y) (h2 : SemiStep N [x, y] z) :
    ok3 N (maskL 0 (tbl.map Prod.fst)) (min x (min y z))
      (x + y + z - min x (min y z) - max x (max y z)) (max x (max y z)) = true := by
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
  · exact h

theorem good3_of_cert {N : Nat} {tbl : List (Nat × Nat)} (hN : N < 32) (hc : Cert N tbl) :
    Good3 N := by
  intro a b c ha hab hbc hcN hv hd
  obtain ⟨x, y, z, hp, h1, h2⟩ := valid3_of_B hab hbc hv
  have hok := ok3_of_cert hc (x := x) (y := y) (z := z) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) h1 h2
  rw [show min x (min y z) = a by omega, show max x (max y z) = c by omega,
    show x + y + z - a - c = b by omega] at hok
  unfold ok3 at hok
  simp only [Bool.or_eq_true] at hok
  rcases hok with ((h | h) | h) | h
  · rw [hd] at h; exact absurd h (by decide)
  · exact coReach3_of_F ha hab hbc hcN (f3S_of_f3SB h)
  · exact coReach_of_tbl hc.1 (by omega) (by omega) h
  · exact coReach3_of_mirror (by omega) (by omega) hcN
      (coReach_of_tbl hc.1 (by omega) (by omega) h)

theorem good3_le_30 {N : Nat} (hN : N ≤ 30) (h7 : N ≠ 7) : Good3 N := by
  by_cases h3 : 3 ≤ N
  · obtain ⟨tbl, hc⟩ := cert_le_30 h3 hN h7
    exact good3_of_cert (by omega) hc
  · intro a b c ha hab hbc hcN; omega

/-! ## Theorem G after explicit valid steps (elements given as a list) -/

/-- Elements of `xs` in the left arm of `m`. -/
def lcB (N m : Nat) (xs : List Nat) : Nat :=
  xs.countP fun x => decide (m - reach N m ≤ x ∧ x < m)

/-- Elements of `xs` in the right arm of `m`. -/
def rcB (N m : Nat) (xs : List Nat) : Nat :=
  xs.countP fun x => decide (m < x ∧ x ≤ m + reach N m)

theorem toList_perm_of_nodup {xs : List Nat} (h : xs.Nodup) : xs.toFinset.toList.Perm xs := by
  rw [List.perm_ext_iff_of_nodup (Finset.nodup_toList _) h]; intro x; simp

theorem leftCount_toFinset {N m : Nat} {xs : List Nat} (h : xs.Nodup) :
    leftCount N xs.toFinset.toList m = lcB N m xs := by
  rw [leftCount_eq (Finset.nodup_toList _), (toList_perm_of_nodup h).countP_eq]; rfl

theorem rightCount_toFinset {N m : Nat} {xs : List Nat} (h : xs.Nodup) :
    rightCount N xs.toFinset.toList m = rcB N m xs := by
  rw [rightCount_eq (Finset.nodup_toList _), (toList_perm_of_nodup h).countP_eq]; rfl

/-- The criterion of Theorem G for the set of `xs` and the centre `c2 / 2`. -/
def inwB (N c2 : Nat) (xs : List Nat) : Bool :=
  (List.range' 1 N).all fun m => xs.contains m ||
    (2 * m != c2 && (if 2 * m < c2 then decide (lcB N m xs ≤ rcB N m xs)
      else decide (rcB N m xs ≤ lcB N m xs)))

theorem inward_of_inwB {N c2 : Nat} {xs : List Nat} (hnd : xs.Nodup) (h : inwB N c2 xs = true) :
    Inward N c2 xs.toFinset := by
  intro m hm1 hmN hmB
  unfold inwB at h
  rw [List.all_eq_true] at h
  have hm := h m (List.mem_range'_1.2 ⟨hm1, by omega⟩)
  have hx : m ∉ xs := by simpa using hmB
  rw [leftCount_toFinset hnd, rightCount_toFinset hnd]
  simp only [Bool.or_eq_true, List.contains_iff_mem, hx, false_or, Bool.and_eq_true,
    bne_iff_ne, ne_eq] at hm
  obtain ⟨h1, h2⟩ := hm
  split_ifs at h2 with h3
  · simp only [decide_eq_true_eq] at h2; exact ⟨h1, fun _ => h2, fun _ => by omega⟩
  · simp only [decide_eq_true_eq] at h2; exact ⟨h1, fun _ => by omega, fun _ => h2⟩

/-- Valid steps `ms` after the background `xs`, then Theorem G with the centre `c2 / 2`. -/
def stepsB (N : Nat) : List Nat → List Nat → Nat → Bool
  | xs, [], c2 => inwB N c2 xs
  | xs, m :: ms, c2 => decide (1 ≤ m) && decide (m ≤ N) && !xs.contains m &&
      (lcB N m xs == rcB N m xs) && stepsB N (m :: xs) ms c2

/-- **Theorem G after explicit valid steps** (`coReach_of_step` iterated). -/
theorem coReach_of_stepsB {N c2 : Nat} : ∀ (ms xs : List Nat), xs.Nodup →
    (∀ x ∈ xs, 1 ≤ x ∧ x ≤ N) → stepsB N xs ms c2 = true → CoReach N xs.toFinset
  | [], xs, hnd, hb, h => by
      refine coReach_of_inward (fun x hx => ?_) (inward_of_inwB hnd h)
      rw [List.mem_toFinset] at hx; rw [Finset.mem_Icc]; exact hb x hx
  | m :: ms, xs, hnd, hb, h => by
      simp only [stepsB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        beq_iff_eq] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      have hm : m ∉ xs := by
        intro hc; rw [← List.contains_iff_mem, h3] at hc; exact absurd hc (by decide)
      have ih := coReach_of_stepsB ms (m :: xs) (List.nodup_cons.2 ⟨hm, hnd⟩)
        (fun x hx => by
          rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ⟨h1, h2⟩
          · exact hb x hx) h5
      rw [List.toFinset_cons] at ih
      refine coReach_of_step (D := xs.toFinset) (fun x hx => ?_) h1 h2 (by simpa using hm) ?_ ih
      · rw [List.mem_toFinset] at hx; rw [Finset.mem_Icc]; exact hb x hx
      · unfold SemiStep; rw [leftCount_toFinset hnd, rightCount_toFinset hnd]; exact h4

theorem coReach3_of_stepsB {N a b c c2 : Nat} {ms : List Nat} (ha : 1 ≤ a) (hab : a < b)
    (hbc : b < c) (hcN : c ≤ N) (h : stepsB N [a, b, c] ms c2 = true) :
    CoReach N {a, b, c} := by
  have := coReach_of_stepsB ms [a, b, c] (by simp; omega) (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega) h
  simpa using this

/-! ## Copies and transfers -/

/-- The transfer property of a map `[p] → [N]`. -/
def Transfers (N p : Nat) (φ : Nat → Nat) : Prop :=
  ∀ D : Finset Nat, D ⊆ Finset.Icc 1 p → CoReach p D → CoReach N (D.image φ)

/-- The copies with proven transfers: `0` centred Beatty `Z(N, p)`; `1` right-aligned Beatty
`X(N, p, u)`; `2` residue class `v mod u`; `3` multiples of `u` (`u ∣ N + 1`); `4` swapped
Beatty `(p, h = u, c = v)`; `5` the copy `{1, 4, 6, …, N}`. -/
def copyF (k N p u v : Nat) : Nat → Nat :=
  match k with
  | 0 => zF N p
  | 1 => beatty N p u
  | 2 => cls u v
  | 3 => cls u u
  | 4 => swapF N p u v
  | _ => chiY

/-- The hypotheses of the transfer for each copy. -/
def copyOK (k N p u v : Nat) : Bool :=
  match k with
  | 0 => decide (1 ≤ p) && decide (2 * p ≤ N)
  | 1 => decide (1 ≤ p) && decide (u + 2 * p ≤ N + 1) && decide (u ≤ 1)
  | 2 => decide (2 ≤ u) && decide (u ≤ 12) && decide (u ≤ N) && decide (1 ≤ v) &&
      decide (v ≤ u) && !excB u (N % u) v && p == ccount u v N
  | 3 => decide (2 ≤ u) && decide (u ≤ N) && (N + 1) % u == 0 && p == ccount u u N
  | 4 => decide (3 ≤ p) && p % 2 == 1 && decide (u ≤ 1) && decide (2 ≤ v) &&
      decide (2 * v * p + 1 ≤ N + u)
  | 5 => N == 2 * p && p % 2 == 0 && decide (4 ≤ p)
  | _ => false

theorem transfers_of_copyOK {k N p u v : Nat} (h : copyOK k N p u v = true) :
    Transfers N p (copyF k N p u v) := by
  intro D hDs hD
  rcases k with _ | _ | _ | _ | _ | _ | k
  · simp only [copyOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact coReach_z_transfer h.1 h.2 hDs hD
  · simp only [copyOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact coReach_beatty_transfer h.1.1 h.1.2 h.2 hDs hD
  · simp only [copyOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, rfl⟩ := h
    exact coReach_mod h1 h2 h3 h4 h5 h6 hDs hD
  · simp only [copyOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, rfl⟩ := h
    exact coReach_mult_transfer (by omega) h2 h3 hDs hD
  · simp only [copyOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact coReach_swap_transfer ⟨h1, h2, h3, h4, h5⟩ hDs hD
  · simp only [copyOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨rfl, h2⟩, h3⟩ := h
    exact coReach_chiY_transfer h3 h2 hDs hD
  · simp [copyOK] at h

/-- A transfer hint: the sorted triple `(a, b, c)` of `[N]` is the image of the valid,
non-dead sorted triple `(i, j, l)` of a smaller strip `[p]` (`p ≠ 7`) under a copy. -/
def trB (N a b c k p u v i j l : Nat) : Bool :=
  copyOK k N p u v && decide (p < N) && p != 7 && decide (1 ≤ i) && decide (i < j) &&
    decide (j < l) && decide (l ≤ p) && copyF k N p u v i == a && copyF k N p u v j == b &&
    copyF k N p u v l == c && valid3B p i j l && !dead3B p i j l

theorem coReach_of_trB {N a b c k p u v i j l : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (h : trB N a b c k p u v i j l = true) : CoReach N {a, b, c} := by
  unfold trB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, hp⟩, hp7⟩, hi⟩, hij⟩, hjl⟩, hl⟩, ea⟩, eb⟩, ec⟩, hv⟩, hd⟩ := h
  have hD := IH p hp hp7 i j l hi hij hjl hl hv hd
  have := transfers_of_copyOK hc {i, j, l} (fun x hx => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Icc]; omega) hD
  simpa [Finset.image_insert, ea, eb, ec] using this

/-! ## The covering rules and the reduction for all `N` -/

/-- The rules that settle a sorted triple given the smaller strips: Theorem G in closed form,
Theorem G after at most two explicit valid steps, or a transfer of a valid non-dead triple of
a smaller strip through one of the copies. -/
def Covered3 (N a b c : Nat) : Prop :=
  f3SB N a b c = true ∨ (∃ ms c2, ms.length ≤ 2 ∧ stepsB N [a, b, c] ms c2 = true) ∨
    ∃ k p u v i j l, trB N a b c k p u v i j l = true

/-- `Covered3` for the triple or its mirror image. -/
def Covered3S (N a b c : Nat) : Prop :=
  Covered3 N a b c ∨ Covered3 N (N + 1 - c) (N + 1 - b) (N + 1 - a)

theorem coReach_of_covered3 {N a b c : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcN : c ≤ N) (h : Covered3 N a b c) :
    CoReach N {a, b, c} := by
  rcases h with h | ⟨ms, c2, -, h⟩ | ⟨k, p, u, v, i, j, l, h⟩
  · exact coReach3_of_F ha hab hbc hcN (f3S_of_f3SB h)
  · exact coReach3_of_stepsB ha hab hbc hcN h
  · exact coReach_of_trB IH h

theorem coReach_of_covered3S {N a b c : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcN : c ≤ N) (h : Covered3S N a b c) :
    CoReach N {a, b, c} := by
  rcases h with h | h
  · exact coReach_of_covered3 IH ha hab hbc hcN h
  · exact coReach3_of_mirror (by omega) (by omega) hcN
      (coReach_of_covered3 IH (by omega) (by omega) (by omega) (by omega) h)

/-- **The residual statement for `N`**: every valid, non-dead sorted triple of `[N]` that is
not settled by the rules `Covered3S` is co-reachable. -/
def Residual3 (N : Nat) : Prop :=
  ∀ a b c, 1 ≤ a → a < b → b < c → c ≤ N → valid3B N a b c = true → dead3B N a b c = false →
    ¬ Covered3S N a b c → CoReach N {a, b, c}

/-- **Reduction**: the 3-prefix property for all `N ≠ 7` follows from the base strips and
the residual statements above them. -/
theorem good3_of_residual {M : Nat} (hbase : ∀ N, N ≤ M → N ≠ 7 → Good3 N)
    (hres : ∀ N, M < N → Residual3 N) : ∀ N, N ≠ 7 → Good3 N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro h7
    by_cases hN : N ≤ M
    · exact hbase N hN h7
    intro a b c ha hab hbc hcN hv hd
    by_cases hc : Covered3S N a b c
    · exact coReach_of_covered3S ih ha hab hbc hcN hc
    · exact hres N (by omega) a b c ha hab hbc hcN hv hd hc

/-- From `Good3` to the liveness iff for a valid 3-prefix. -/
theorem extends3_iff_of_good3 {N x y z : Nat} (hG : Good3 N) (hx : 1 ≤ x ∧ x ≤ N)
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
    rw [extends_iff_coReach hnd hp hv, hfs]
    have h1 : SemiStep N [x] y := by simpa using hv 1 (by simp)
    have h2 : SemiStep N [x, y] z := by simpa using hv 2 (by simp)
    have hval := valid3B_of hxy hxz hyz h1 h2
    have hS : ({x, y, z} : Finset Nat) = {min x (min y z),
        x + y + z - min x (min y z) - max x (max y z), max x (max y z)} := by
      ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hS] at hd ⊢
    refine hG _ _ _ (by omega) (by omega) (by omega) (by omega) hval ?_
    by_contra hb
    exact hd (dead3_of_dead3B (by simpa using hb))


/-! ## Certificates: one hint per sorted triple

For `31 ≤ N ≤ 63` the base strips are extended by kernel-checked certificates that list, for
every valid, non-dead sorted triple failing `F3S` (in lexicographic order, grouped by the
smallest element `a`), one hint: a transfer through a copy (using the strips below `N`),
Theorem G after explicit valid steps, or a witness ordering; each possibly for the mirror
image. -/

/-- A hint for a sorted triple. -/
inductive Hint where
  /-- An ordering of `[N] \ {a, b, c}` from scratch. -/
  | wit (w : List Nat)
  /-- Theorem G (centre `c2 / 2`) after the valid steps `ms`. -/
  | st (c2 : Nat) (ms : List Nat)
  /-- A transfer through the copy `k` with parameters `p u v` of the triple `(i, j, l)`. -/
  | tr (k p u v i j l : Nat)

def hintB (N a b c : Nat) : Hint → Bool
  | .wit w => witB3 N a b c w
  | .st c2 ms => stepsB N [a, b, c] ms c2
  | .tr k p u v i j l => trB N a b c k p u v i j l

/-- A hint for the triple (`false`) or for its mirror image (`true`). -/
def hintOK (N a b c : Nat) (h : Bool × Hint) : Bool :=
  if h.1 then hintB N (N + 1 - c) (N + 1 - b) (N + 1 - a) h.2 else hintB N a b c h.2

theorem coReach_of_hintB {N a b c : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q) (ha : 1 ≤ a)
    (hab : a < b) (hbc : b < c) (hcN : c ≤ N) {h : Hint} (hh : hintB N a b c h = true) :
    CoReach N {a, b, c} := by
  cases h with
  | wit w => exact coReach_of_witB3 hh
  | st c2 ms => exact coReach3_of_stepsB ha hab hbc hcN hh
  | tr k p u v i j l => exact coReach_of_trB IH hh

theorem coReach_of_hintOK {N a b c : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q) (ha : 1 ≤ a)
    (hab : a < b) (hbc : b < c) (hcN : c ≤ N) {h : Bool × Hint}
    (hh : hintOK N a b c h = true) : CoReach N {a, b, c} := by
  unfold hintOK at hh
  split_ifs at hh
  · exact coReach3_of_mirror (by omega) (by omega) hcN
      (coReach_of_hintB IH (by omega) (by omega) (by omega) (by omega) hh)
  · exact coReach_of_hintB IH ha hab hbc hcN hh

/-- Reading `k` base-128 digits. -/
def rdList : Nat → Nat → List Nat × Nat
  | 0, n => ([], n)
  | k + 1, n => let r := rdList k (n / 128); (n % 128 :: r.1, r.2)

/-- **Decoding a packed hint list** (base-128 digits, at most `f` hints).  Each hint starts
with a tag `2 * kind + mirror + 1`; a witness is followed by its length and its panels, a
step hint by `c2`, the number of steps and the steps, a transfer by `k p u v i j l`.  (The
decoding needs no proof: every decoded hint is checked.) -/
def decH : Nat → Nat → List (Bool × Hint)
  | 0, _ => []
  | f + 1, n =>
    if n = 0 then [] else
    let t := n % 128 - 1
    let m := t % 2 == 1
    let n := n / 128
    if t / 2 = 0 then
      let r := rdList (n % 128) (n / 128)
      (m, .wit r.1) :: decH f r.2
    else if t / 2 = 1 then
      let n' := n / 128
      let r := rdList (n' % 128) (n' / 128)
      (m, .st (n % 128) r.1) :: decH f r.2
    else
      let r := rdList 7 n
      (m, .tr (r.1.getD 0 0) (r.1.getD 1 0) (r.1.getD 2 0) (r.1.getD 3 0) (r.1.getD 4 0)
        (r.1.getD 5 0) (r.1.getD 6 0)) :: decH f r.2

/-- The triples that need a hint. -/
def need (N a b c : Nat) : Bool := valid3B N a b c && !dead3B N a b c && !f3SB N a b c

/-- The pairs `(b, c)`, `b₀ ≤ b < b₁`, `b < c ≤ N`, whose triple `(a, b, c)` needs a hint, in
lexicographic order. -/
def neededR (N a b₀ b₁ : Nat) : List (Nat × Nat) :=
  ((List.range' b₀ (b₁ - b₀)).flatMap fun b =>
    (List.range' (b + 1) (N - b)).map fun c => (b, c)).filter fun t => need N a t.1 t.2

/-- The hints match the needed triples one by one. -/
def all2 (N a : Nat) : List (Nat × Nat) → List (Bool × Hint) → Bool
  | [], [] => true
  | t :: ts, h :: hs => hintOK N a t.1 t.2 h && all2 N a ts hs
  | _, _ => false

theorem all2_sound {N a : Nat} : ∀ (ts : List (Nat × Nat)) (hs : List (Bool × Hint)),
    all2 N a ts hs = true → ∀ t ∈ ts, ∃ h, hintOK N a t.1 t.2 h = true
  | [], [], _ => fun t ht => absurd ht (List.not_mem_nil)
  | t :: ts, h :: hs, e => by
      simp only [all2, Bool.and_eq_true] at e
      intro t' ht'
      rw [List.mem_cons] at ht'
      rcases ht' with rfl | ht'
      · exact ⟨h, e.1⟩
      · exact all2_sound ts hs e.2 t' ht'
  | [], _ :: _, e => by simp [all2] at e
  | _ :: _, [], e => by simp [all2] at e

/-- The certificate check for the triples `(a, b, c)` with `b₀ ≤ b < b₁`. -/
def chkR (N a b₀ b₁ : Nat) (hs : List (Bool × Hint)) : Bool := all2 N a (neededR N a b₀ b₁) hs

theorem chkR_sound {N a b₀ b₁ : Nat} {hs : List (Bool × Hint)} (hc : chkR N a b₀ b₁ hs = true)
    (b c : Nat) (h0 : b₀ ≤ b) (h1 : b < b₁) (hbc : b < c) (hcN : c ≤ N)
    (hn : need N a b c = true) : ∃ h, hintOK N a b c h = true := by
  have hmem : (b, c) ∈ neededR N a b₀ b₁ := by
    unfold neededR
    rw [List.mem_filter, List.mem_flatMap]
    exact ⟨⟨b, List.mem_range'_1.2 ⟨h0, by omega⟩, List.mem_map.2
      ⟨c, List.mem_range'_1.2 ⟨by omega, by omega⟩, rfl⟩⟩, hn⟩
  exact all2_sound _ _ hc _ hmem

/-- A hint for every needed triple of `[N]`. -/
def CovQ (N : Nat) : Prop :=
  ∀ a b c, 1 ≤ a → a < b → b < c → c ≤ N → need N a b c = true → ∃ h, hintOK N a b c h = true

/-- Hints for the needed triples `(a, b, c)` with `b₀ ≤ b < b₁`. -/
def CovB (N a b₀ b₁ : Nat) : Prop :=
  ∀ b c, b₀ ≤ b → b < b₁ → b < c → c ≤ N → need N a b c = true → ∃ h, hintOK N a b c h = true

theorem CovB.of_chk {N a b₀ b₁ : Nat} {hs : List (Bool × Hint)}
    (hc : chkR N a b₀ b₁ hs = true) : CovB N a b₀ b₁ :=
  fun b c h0 h1 h2 h3 hn => chkR_sound hc b c h0 h1 h2 h3 hn

theorem CovB.trans {N a b₀ b₁ b₂ : Nat} (h₁ : CovB N a b₀ b₁) (h₂ : CovB N a b₁ b₂) :
    CovB N a b₀ b₂ := fun b c h0 h1 h2 h3 hn => by
  by_cases hb : b < b₁
  · exact h₁ b c h0 hb h2 h3 hn
  · exact h₂ b c (by omega) h1 h2 h3 hn

/-- Hints for the needed triples with smallest element `a₀ ≤ a < a₁`. -/
def CovA (N a₀ a₁ : Nat) : Prop := ∀ a, a₀ ≤ a → a < a₁ → CovB N a (a + 1) (N + 1)

theorem CovA.one {N a : Nat} (h : CovB N a (a + 1) (N + 1)) : CovA N a (a + 1) :=
  fun a' h0 h1 => by rw [show a' = a by omega]; exact h

theorem CovA.trans {N a₀ a₁ a₂ : Nat} (h₁ : CovA N a₀ a₁) (h₂ : CovA N a₁ a₂) :
    CovA N a₀ a₂ := fun a h0 h1 => by
  by_cases ha : a < a₁
  · exact h₁ a h0 ha
  · exact h₂ a (by omega) h1

theorem CovQ.of_covA {N : Nat} (h : CovA N 1 (N - 1)) : CovQ N :=
  fun a b c h0 h1 h2 h3 hn => h a h0 (by omega) b c (by omega) (by omega) h2 h3 hn

/-- **Soundness of the certificates**: given the strips below `N`, hints for all needed
triples give `Good3 N`. -/
theorem good3_of_cov {N : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q) (h : CovQ N) :
    Good3 N := by
  intro a b c ha hab hbc hcN hv hd
  by_cases hf : f3SB N a b c = true
  · exact coReach3_of_F ha hab hbc hcN (f3S_of_f3SB hf)
  obtain ⟨h', hh⟩ := h a b c ha hab hbc hcN (by simp only [need, hv, hd]; simpa using hf)
  exact coReach_of_hintOK IH ha hab hbc hcN hh

end Live3q
end Folds
