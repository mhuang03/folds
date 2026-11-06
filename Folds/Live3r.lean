import Folds.Live3p
import Folds.ThinCover

/-!
# Live 3-prefixes, part 3: near copies

`experiments/live3r/PROOFS.txt`.

* The definitions `valid3B`, `Good3`, `stepsB`, `copyF`, `trB`, `Covered3`, `Covered3S`,
  `Residual3` of `Folds/Live3q.lean` are restated here verbatim (namespace `Live3r`), so that
  this file does not import the 2.3 MB certificate file; `Live3q.Residual3 N` and
  `Live3r.Residual3 N` are the same statement.
* `NearEmb`, `coReach_nearEmb`: **near copies**, maps `[p] → [N]` that preserve the window
  relation around every panel outside the transferred set (not necessarily around the
  others); with an ordering of the complement of the image from scratch they transfer
  co-reachable sets.
* `nearTrB`, `nearTrP`: decidable near-copy rules (a copy `copyF` with up to two panels moved
  by one; the complement of the image by Theorem G after explicit steps, or through a second
  near copy whose two irregular panels form a live 2-prefix, `ThinCover.conjectureC`).
* `coReach_X_odd`, `coReach_chiX_transfer`, `chiXB`: the copy `X_N = {1, 4, 6, …, N - 3, N}`
  is co-reachable for every odd `N ≥ 17` (Live5: `N ≡ 3 mod 4`), so it transfers.
* Families for all `N`: `coReach_one_even_N` (`{1, 2k, N}`, `N` odd) and
  `coReach_one_two_odd` (`{1, 2, c}`, `N ≡ 1 mod 4`, `c` odd), by closed-form (near) copies.
* `Covered3R`, `Residual3R`, `residual3_of_residual3R`, `good3_of_residual3R`,
  `residual3_all_of_residual3R`: the reduction of Live3q with the enlarged rules; numerically
  (`experiments/live3r`, N = 51..70) the residual of `Covered3R` is the family `{1, 2, c}`
  (and its mirror) only.
-/

namespace Folds
namespace Live3r

open Live2 Live4 Adjacent Live5 Live6 Live7 Live3p

/-! ## The definitions of `Live3q` (verbatim) -/


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


/-! ## Near copies -/

/-- A **near copy**: an injective map `[p] → [N]` that preserves the window relation around
every *regular* panel `j` (`R j`): for regular `j` and every `y`, `φ y` lies in the left
(right) arm of `φ j` iff `y` lies in the left (right) arm of `j`.  Around irregular panels
nothing is required. -/
structure NearEmb (N p : Nat) (φ : Nat → Nat) (R : Nat → Prop) : Prop where
  bound : ∀ y, 1 ≤ y → y ≤ p → 1 ≤ φ y ∧ φ y ≤ N
  inj : ∀ x y, 1 ≤ x → x ≤ p → 1 ≤ y → y ≤ p → φ x = φ y → x = y
  left : ∀ j y, 1 ≤ j → j ≤ p → R j → 1 ≤ y → y ≤ p →
    ((φ j - reach N (φ j) ≤ φ y ∧ φ y < φ j) ↔ (j - reach p j ≤ y ∧ y < j))
  right : ∀ j y, 1 ≤ j → j ≤ p → R j → 1 ≤ y → y ≤ p →
    ((φ j < φ y ∧ φ y ≤ φ j + reach N (φ j)) ↔ (j < y ∧ y ≤ j + reach p j))

theorem NearEmb.nodup_map {N p : Nat} {φ : Nat → Nat} {R : Nat → Prop} (hφ : NearEmb N p φ R)
    {σ : List Nat} (hnd : σ.Nodup) (hσ : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ p) : (σ.map φ).Nodup :=
  nodup_map_of_injOn hnd fun x hx y hy e =>
    hφ.inj x y (hσ x hx).1 (hσ x hx).2 (hσ y hy).1 (hσ y hy).2 e

/-- Around a regular panel the image of the whole strip is balanced. -/
theorem NearEmb.balanced_self {N p : Nat} {φ : Nat → Nat} {R : Nat → Prop}
    (hφ : NearEmb N p φ R) {j : Nat} (hj1 : 1 ≤ j) (hjp : j ≤ p) (hR : R j) :
    Balanced N ((List.range' 1 p).map φ) (φ j) := by
  unfold Balanced
  rw [List.countP_map, List.countP_map]
  have L : (List.range' 1 p).countP
        ((fun x => decide (φ j - reach N (φ j) ≤ x ∧ x < φ j)) ∘ φ) =
      (List.range' 1 p).countP (fun y => decide (j - reach p j ≤ y ∧ y ≤ j - 1)) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    rw [hφ.left j y hj1 hjp hR hy.1 (by omega)]; omega
  have R' : (List.range' 1 p).countP
        ((fun x => decide (φ j < x ∧ x ≤ φ j + reach N (φ j))) ∘ φ) =
      (List.range' 1 p).countP (fun y => decide (j + 1 ≤ y ∧ y ≤ j + reach p j)) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    rw [hφ.right j y hj1 hjp hR hy.1 (by omega)]; omega
  rw [L, R', countP_range'_interval, countP_range'_interval]
  unfold reach; omega

/-- An ordering of the complement of the image is balanced around every regular panel. -/
theorem NearEmb.balanced_compl {N p : Nat} {φ : Nat → Nat} {R : Nat → Prop}
    (hφ : NearEmb N p φ R) {l : List Nat} (hnd : l.Nodup)
    (hl : l.toFinset = Finset.Icc 1 N \ (Finset.Icc 1 p).image φ) {j : Nat} (hj1 : 1 ≤ j)
    (hjp : j ≤ p) (hR : R j) : Balanced N l (φ j) := by
  have hX : ((List.range' 1 p).map φ).Nodup := hφ.nodup_map (List.nodup_range' ..)
    fun y hy => by rw [List.mem_range'_1] at hy; omega
  have hmem : ∀ x, x ∈ l ↔ (1 ≤ x ∧ x ≤ N) ∧ ¬ ∃ y, (1 ≤ y ∧ y ≤ p) ∧ φ y = x := by
    intro x
    rw [← List.mem_toFinset, hl]
    simp
  have hp : (l ++ (List.range' 1 p).map φ).Perm (List.range' 1 N) := by
    refine perm_of_mem_iff (List.nodup_append.2 ⟨hnd, hX, ?_⟩) (List.nodup_range' ..) ?_
    · intro a ha b hb e
      subst e
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
      rw [List.mem_range'_1] at hy
      exact ((hmem _).1 ha).2 ⟨y, by omega, rfl⟩
    · intro x
      rw [List.mem_append, hmem, List.mem_map, List.mem_range'_1]
      constructor
      · rintro (⟨h, -⟩ | ⟨y, hy, rfl⟩)
        · omega
        · rw [List.mem_range'_1] at hy
          have := hφ.bound y hy.1 (by omega); omega
      · intro hx
        by_cases h : ∃ y, (1 ≤ y ∧ y ≤ p) ∧ φ y = x
        · obtain ⟨y, hy, rfl⟩ := h
          exact Or.inr ⟨y, List.mem_range'_1.2 ⟨hy.1, by omega⟩, rfl⟩
        · exact Or.inl ⟨by omega, h⟩
  exact Balanced.of_append (Balanced.perm balanced_full hp.symm) (hφ.balanced_self hj1 hjp hR)

/-- A step at a regular panel, after a balanced background. -/
theorem NearEmb.semiStep_iff {N p : Nat} {φ : Nat → Nat} {R : Nat → Prop}
    (hφ : NearEmb N p φ R) {U T : List Nat} {j : Nat} (hnd : (U ++ T.map φ).Nodup)
    (hT : ∀ y ∈ T, 1 ≤ y ∧ y ≤ p) (hj1 : 1 ≤ j) (hjp : j ≤ p) (hR : R j)
    (hU : Balanced N U (φ j)) :
    SemiStep N (U ++ T.map φ) (φ j) ↔ SemiStep p T j := by
  have hndT : T.Nodup := (List.nodup_append.1 hnd).2.1.of_map φ
  unfold SemiStep
  rw [leftCount_eq hnd, rightCount_eq hnd, leftCount_eq hndT, rightCount_eq hndT,
    List.countP_append, List.countP_append, List.countP_map, List.countP_map]
  have L : T.countP ((fun x => decide (φ j - reach N (φ j) ≤ x ∧ x < φ j)) ∘ φ) =
      T.countP (fun y => decide (j - reach p j ≤ y ∧ y < j)) := by
    apply List.countP_congr; intro y hy; have := hT y hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    exact hφ.left j y hj1 hjp hR this.1 this.2
  have R' : T.countP ((fun x => decide (φ j < x ∧ x ≤ φ j + reach N (φ j))) ∘ φ) =
      T.countP (fun y => decide (j < y ∧ y ≤ j + reach p j)) := by
    apply List.countP_congr; intro y hy; have := hT y hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    exact hφ.right j y hj1 hjp hR this.1 this.2
  unfold Balanced at hU
  rw [L, R']; omega

/-- **Transfer through a near copy.**  If the complement of the image of `φ` has an ordering
from scratch and every panel of `[p]` outside `D` is regular, co-reachable sets `D` of the
`p`-strip map to co-reachable sets.  (Order the complement of the image first, then the
image of an ordering of `[p] \ D`: around a regular panel the complement is balanced, and
the arms of the image are the images of the arms.) -/
theorem coReach_nearEmb {N p : Nat} {φ : Nat → Nat} {R : Nat → Prop} (hφ : NearEmb N p φ R)
    (hY : CoReach N ((Finset.Icc 1 p).image φ)) {D : Finset Nat}
    (hDs : D ⊆ Finset.Icc 1 p) (hR : ∀ j, 1 ≤ j → j ≤ p → j ∉ D → R j) (hD : CoReach p D) :
    CoReach N (D.image φ) := by
  unfold CoReach g at *
  rw [Finset.card_pos] at hY hD ⊢
  obtain ⟨l1, h1⟩ := hY
  obtain ⟨l2, h2⟩ := hD
  rw [mem_semiOrders] at h1 h2
  obtain ⟨⟨hnd1, hs1⟩, hv1⟩ := h1
  obtain ⟨⟨hnd2, hs2⟩, hv2⟩ := h2
  have m2 : ∀ y, y ∈ l2 ↔ (1 ≤ y ∧ y ≤ p) ∧ y ∉ D := by
    intro y; rw [← List.mem_toFinset, hs2]; simp
  have m1 : ∀ x, x ∈ l1 ↔ (1 ≤ x ∧ x ≤ N) ∧ ¬ ∃ y, (1 ≤ y ∧ y ≤ p) ∧ φ y = x := by
    intro x; rw [← List.mem_toFinset, hs1]; simp
  have b2 : ∀ y ∈ l2, 1 ≤ y ∧ y ≤ p := fun y hy => ((m2 y).1 hy).1
  have hnd2' := hφ.nodup_map hnd2 b2
  have hnd : (l1 ++ l2.map φ).Nodup := by
    refine List.nodup_append.2 ⟨hnd1, hnd2', fun a ha b hb e => ?_⟩
    subst e
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact ((m1 _).1 ha).2 ⟨y, b2 y hy, rfl⟩
  refine ⟨l1 ++ l2.map φ, mem_semiOrders.2 ⟨⟨hnd, ?_⟩, ?_⟩⟩
  · ext x
    simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset, Finset.mem_sdiff,
      Finset.mem_Icc, Finset.mem_image, List.mem_map]
    constructor
    · rintro (hx | ⟨y, hy, rfl⟩)
      · obtain ⟨hx1, hx2⟩ := (m1 x).1 hx
        refine ⟨hx1, fun ⟨d, hd, e⟩ => hx2 ⟨d, ?_, e⟩⟩
        have := hDs hd; simpa using this
      · obtain ⟨hy1, hy2⟩ := (m2 y).1 hy
        refine ⟨hφ.bound y hy1.1 hy1.2, fun ⟨d, hd, e⟩ => hy2 ?_⟩
        have hd' : 1 ≤ d ∧ d ≤ p := by have := hDs hd; simpa using this
        rwa [← hφ.inj d y hd'.1 hd'.2 hy1.1 hy1.2 e]
    · rintro ⟨hx, hxD⟩
      by_cases h : ∃ y, (1 ≤ y ∧ y ≤ p) ∧ φ y = x
      · obtain ⟨y, hy, rfl⟩ := h
        exact Or.inr ⟨y, (m2 y).2 ⟨hy, fun hyD => hxD ⟨y, hyD, rfl⟩⟩, rfl⟩
      · exact Or.inl ((m1 x).2 ⟨hx, h⟩)
  · rw [semiSymmetric_append_iff]
    refine ⟨hv1, fun k hk => ?_⟩
    simp only [List.length_map] at hk
    rw [List.getElem_map, ← List.map_take]
    have hmem := (m2 _).1 (List.getElem_mem hk)
    have hj := hmem.1
    have hRj := hR _ hj.1 hj.2 hmem.2
    have hbal : Balanced N l1 (φ l2[k]) := hφ.balanced_compl hnd1 hs1 hj.1 hj.2 hRj
    refine (hφ.semiStep_iff ?_ (fun y hy => b2 y (List.mem_of_mem_take hy)) hj.1 hj.2 hRj
      hbal).2 (hv2 k hk)
    refine hnd.sublist (List.Sublist.append_left ?_ _)
    rw [List.map_take]; exact List.take_sublist _ _

/-- A window copy is a near copy with every panel regular. -/
theorem nearEmb_of_winEmb {N p : Nat} {φ : Nat → Nat} (h : WinEmb N p φ) :
    NearEmb N p φ (fun _ => True) :=
  ⟨h.bound, h.inj, fun j y hj1 hjp _ hy1 hyp => h.left j y hj1 hjp hy1 hyp,
    fun j y hj1 hjp _ hy1 hyp => h.right j y hj1 hjp hy1 hyp⟩

/-! ## A decidable near-copy rule -/

/-- Move the panel `y₀` of a map by `+1` (`e = 1`) or `-1` (`e = 2`). -/
def mvF (f : Nat → Nat) (y₀ e : Nat) (y : Nat) : Nat :=
  if y = y₀ then (if e = 1 then f y + 1 else if e = 2 then f y - 1 else f y) else f y

/-- The near maps: a copy `copyF k N p u v` with up to two panels moved by one. -/
def nearF (k N p u v y₁ e₁ y₂ e₂ : Nat) : Nat → Nat :=
  mvF (mvF (copyF k N p u v) y₁ e₁) y₂ e₂

/-- The window relation of `y` to `j` is preserved by `φ`. -/
def agreeB (N p : Nat) (φ : Nat → Nat) (j y : Nat) : Bool :=
  (decide (φ j - reach N (φ j) ≤ φ y ∧ φ y < φ j) == decide (j - reach p j ≤ y ∧ y < j)) &&
  (decide (φ j < φ y ∧ φ y ≤ φ j + reach N (φ j)) == decide (j < y ∧ y ≤ j + reach p j))

/-- `j` is a regular panel of `φ`. -/
def regB (N p : Nat) (φ : Nat → Nat) (j : Nat) : Bool :=
  (List.range' 1 p).all fun y => agreeB N p φ j y

/-- `φ` maps `[p]` increasingly into `[N]`. -/
def incB (N p : Nat) (φ : Nat → Nat) : Bool :=
  (List.range' 1 p).all fun y => decide (1 ≤ φ y) && decide (φ y ≤ N) &&
    (y == p || decide (φ y < φ (y + 1)))

theorem lt_of_incB {N p : Nat} {φ : Nat → Nat} (h : incB N p φ = true) :
    ∀ x y, 1 ≤ x → x < y → y ≤ p → φ x < φ y := by
  intro x y hx hxy hy
  induction y, hxy using Nat.le_induction with
  | base =>
    unfold incB at h; rw [List.all_eq_true] at h
    have := h x (List.mem_range'_1.2 ⟨hx, by omega⟩)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at this
    rcases this.2 with h' | h'
    · omega
    · exact h'
  | succ y hxy ih =>
    have h1 := ih (by omega)
    unfold incB at h; rw [List.all_eq_true] at h
    have := h y (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at this
    rcases this.2 with h' | h'
    · omega
    · omega

theorem nearEmb_of_B {N p : Nat} {φ : Nat → Nat} (hi : incB N p φ = true) :
    NearEmb N p φ (fun j => regB N p φ j = true) := by
  have hlt := lt_of_incB hi
  refine ⟨fun y h1 h2 => ?_, fun x y hx1 hxp hy1 hyp e => ?_, fun j y hj1 hjp hR hy1 hyp => ?_,
    fun j y hj1 hjp hR hy1 hyp => ?_⟩
  · unfold incB at hi; rw [List.all_eq_true] at hi
    have := hi y (List.mem_range'_1.2 ⟨h1, by omega⟩)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2⟩
  · rcases Nat.lt_trichotomy x y with h | h | h
    · have := hlt x y hx1 h hyp; omega
    · exact h
    · have := hlt y x hy1 h hxp; omega
  · unfold regB at hR; rw [List.all_eq_true] at hR
    have := hR y (List.mem_range'_1.2 ⟨hy1, by omega⟩)
    unfold agreeB at this
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_decide] at this
    exact this.1
  · unfold regB at hR; rw [List.all_eq_true] at hR
    have := hR y (List.mem_range'_1.2 ⟨hy1, by omega⟩)
    unfold agreeB at this
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_decide] at this
    exact this.2

/-- **The near-copy rule** for a sorted triple: `(a, b, c)` is the image under the near map
of the valid non-dead triple `(i, j, l)` of a smaller strip `[p]`, `p ≠ 7`; every panel of
`[p]` outside `{i, j, l}` is regular; and the image of the near map satisfies Theorem G after
the explicit valid steps `ms` (centre `c2 / 2`), so its complement has an ordering from
scratch. -/
def nearTrB (N a b c k p u v y₁ e₁ y₂ e₂ i j l c2 : Nat) (ms : List Nat) : Bool :=
  let φ := nearF k N p u v y₁ e₁ y₂ e₂
  decide (p < N) && p != 7 && decide (1 ≤ i) && decide (i < j) && decide (j < l) &&
    decide (l ≤ p) && φ i == a && φ j == b && φ l == c && valid3B p i j l &&
    !dead3B p i j l && incB N p φ &&
    (List.range' 1 p).all (fun x => x == i || x == j || x == l || regB N p φ x) &&
    stepsB N ((List.range' 1 p).map φ) ms c2

theorem coReach_of_nearTrB {N a b c k p u v y₁ e₁ y₂ e₂ i j l c2 : Nat} {ms : List Nat}
    (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (h : nearTrB N a b c k p u v y₁ e₁ y₂ e₂ i j l c2 ms = true) : CoReach N {a, b, c} := by
  unfold nearTrB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, hp7⟩, hi⟩, hij⟩, hjl⟩, hl⟩, ea⟩, eb⟩, ec⟩, hv⟩, hd⟩, hinc⟩,
    hreg⟩, hst⟩ := h
  set φ := nearF k N p u v y₁ e₁ y₂ e₂ with hφdef
  have hφ := nearEmb_of_B hinc
  have hlt := lt_of_incB hinc
  have hD := IH p hp hp7 i j l hi hij hjl hl hv hd
  have hbd : ∀ x ∈ (List.range' 1 p).map φ, 1 ≤ x ∧ x ≤ N := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range'_1] at hy
    exact hφ.bound y hy.1 (by omega)
  have hnd : ((List.range' 1 p).map φ).Nodup := hφ.nodup_map (List.nodup_range' ..)
    (fun y hy => by rw [List.mem_range'_1] at hy; omega)
  have hY := coReach_of_stepsB ms _ hnd hbd hst
  have himg : ((List.range' 1 p).map φ).toFinset = (Finset.Icc 1 p).image φ := by
    ext x; simp only [List.mem_toFinset, List.mem_map, List.mem_range'_1, Finset.mem_image,
      Finset.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, ⟨hy.1, by omega⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, ⟨hy.1, by omega⟩, rfl⟩
  rw [himg] at hY
  have := coReach_nearEmb hφ hY (D := {i, j, l}) (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]; omega)
    (fun x hx1 hxp hx => by
      rw [List.all_eq_true] at hreg
      have := hreg x (List.mem_range'_1.2 ⟨hx1, by omega⟩)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      rcases this with ((h | h) | h) | h
      · exact absurd h hx.1
      · exact absurd h hx.2.1
      · exact absurd h hx.2.2
      · exact h) hD
  simpa [Finset.image_insert, ea, eb, ec] using this

/-! ## The copy `X_N = {1, 4, 6, …, N - 3, N}` for every odd `N`

Live5 proved `X_N` co-reachable for `N = 2n - 1`, `n` even.  For `n` odd the same near-copy
argument works with the full sequence `[1, n] ++ σ.reverse` of `[n]`, `σ` an ordering of
`[n] \ {1, n}` from scratch (`{1, n}` is co-reachable for odd `n ≠ 7`): it places `1` before
`2` and `n` before `n - 1`, as `psiX` requires. -/

theorem semiSymmetric_one_n (n : Nat) : SemiSymmetric n [1, n] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  interval_cases k
  · simp [SemiStep, leftCount, rightCount]
  · simp [SemiStep, leftCount, rightCount, reach]

/-- **`X_N` is co-reachable** for `N = 2n - 1`, `n` odd, `n ≥ 9`. -/
theorem coReach_X_odd {n : Nat} (hn : 9 ≤ n) (ho : n % 2 = 1) :
    0 < g (2 * n - 1) (Finset.Icc 1 (2 * n - 1) \ (Finset.Icc 1 (n - 1)).image (chiX n)) := by
  have hn6 : 6 ≤ n := by omega
  obtain ⟨σ, hσn, hσs, hσv⟩ := coReach_list (coReach_one_N n ho (by omega))
  have hσm : ∀ x, x ∈ σ ↔ 2 ≤ x ∧ x ≤ n - 1 := fun x => by
    rw [← List.mem_toFinset, hσs, Finset.mem_sdiff, Finset.mem_Icc]
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = [1, n] ++ σ.reverse := ⟨_, rfl⟩
  have hρn : ρ.Nodup := by
    rw [hρ, List.nodup_append]
    refine ⟨by simp; omega, List.nodup_reverse.2 hσn, fun a ha b hb e => ?_⟩
    subst e
    rw [List.mem_reverse, hσm] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    omega
  have hρs : ρ.toFinset = Finset.Icc 1 n := by
    ext x
    rw [List.mem_toFinset, hρ, List.mem_append, List.mem_reverse, hσm, Finset.mem_Icc]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hρb : ∀ x ∈ ρ, 1 ≤ x ∧ x ≤ n := fun x hx => by
    have := List.mem_toFinset.2 hx; rw [hρs, Finset.mem_Icc] at this; exact this
  have hρf := isFoldSeq_of_toFinset hρn hρs
  have hρv : SemiSymmetric n ρ := by
    subst hρ
    exact semiSymmetric_append_rev hρf (semiSymmetric_one_n n)
      (by rw [List.reverse_reverse]; exact hσv)
  -- `1` and `n` come first
  have hprec : Prec (excX n) ρ := by
    intro p hp j hj hex
    subst hρ
    rcases hex with ⟨ha, rfl⟩ | ⟨ha, rfl⟩
    · -- `ρ[p] = 1`: `p = 0`
      have hp0 : p = 0 := by
        by_contra hne
        rcases Nat.lt_or_ge p 2 with hlt | hge
        · have : p = 1 := by omega
          subst this; simp at ha; omega
        · have : ([1, n] ++ σ.reverse)[p] ∈ σ.reverse := by
            rw [List.getElem_append_right (by simpa using hge)]; exact List.getElem_mem _
          rw [ha, List.mem_reverse, hσm] at this; omega
      subst hp0; simp at hj
    · -- `ρ[p] = n`: `p = 1`
      have hp1 : p = 1 := by
        by_contra hne
        rcases Nat.lt_or_ge p 2 with hlt | hge
        · have : p = 0 := by omega
          subst this; simp at ha; omega
        · have : ([1, n] ++ σ.reverse)[p] ∈ σ.reverse := by
            rw [List.getElem_append_right (by simpa using hge)]; exact List.getElem_mem _
          rw [ha, List.mem_reverse, hσm] at this; omega
      subst hp1; simp at hj; omega
  have hmap : SemiSymmetric (2 * n - 1) (ρ.map (psiX n)) :=
    semiSymmetric_near hρb hρn hρv hprec
      (fun a b ha1 han hb1 hbn e => psiX_inj hn6 ha1 han hb1 hbn e)
      (fun _ _ hi1 hin hj1 hjn hij he' => agree_psiX hn6 hi1 hin hj1 hjn hij he')
  unfold g
  rw [Finset.card_pos]
  refine ⟨ρ.map (psiX n), mem_semiOrders.2 ⟨⟨nodup_map_of_injOn hρn fun a ha b hb e =>
    psiX_inj hn6 (hρb a ha).1 (hρb a ha).2 (hρb b hb).1 (hρb b hb).2 e, ?_⟩, hmap⟩⟩
  ext x
  have hx : x ∈ ρ.map (psiX n) ↔ x ∈ (Finset.Icc 1 n).image (psiX n) := by
    rw [List.mem_map, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, e⟩
      exact ⟨a, by rw [← hρs, List.mem_toFinset]; exact ha, e⟩
    · rintro ⟨a, ha, e⟩
      exact ⟨a, by rw [← List.mem_toFinset, hρs]; exact ha, e⟩
  rw [List.mem_toFinset, hx, mem_image_psiX hn6, Finset.mem_sdiff, mem_image_chiX hn6,
    Finset.mem_Icc]
  omega

/-- **Transfer through `X_N`** for every `N = 2n - 1` with `n ≥ 6`, `n ≠ 7`. -/
theorem coReach_chiX_transfer {n : Nat} (hn : 6 ≤ n) (h7 : n ≠ 7) {D : Finset Nat}
    (hDs : D ⊆ Finset.Icc 1 (n - 1)) (hD : CoReach (n - 1) D) :
    CoReach (2 * n - 1) (D.image (chiX n)) := by
  refine coReach_winEmb (winEmb_chiX hn) ?_ hDs hD
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact coReach_X hn (by omega)
  · exact coReach_X_odd (by omega) (by omega)

/-- The `chiX` rule: `N = 2n - 1` odd, `(a, b, c)` the image of a valid non-dead triple of
`[n - 1]`. -/
def chiXB (N a b c i j l : Nat) : Bool :=
  N % 2 == 1 && decide (11 ≤ N) && N != 13 && N != 15 && decide (1 ≤ i) && decide (i < j) &&
    decide (j < l) && decide (l ≤ (N + 1) / 2 - 1) && chiX ((N + 1) / 2) i == a &&
    chiX ((N + 1) / 2) j == b && chiX ((N + 1) / 2) l == c &&
    valid3B ((N + 1) / 2 - 1) i j l && !dead3B ((N + 1) / 2 - 1) i j l

theorem coReach_of_chiXB {N a b c i j l : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (h : chiXB N a b c i j l = true) : CoReach N {a, b, c} := by
  unfold chiXB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hodd, h11⟩, h13⟩, h15⟩, hi⟩, hij⟩, hjl⟩, hl⟩, ea⟩, eb⟩, ec⟩, hv⟩, hd⟩ := h
  have hD := IH ((N + 1) / 2 - 1) (by omega) (by omega) i j l hi hij hjl hl hv hd
  have := coReach_chiX_transfer (n := (N + 1) / 2) (by omega) (by omega) (D := {i, j, l})
    (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]; omega) hD
  rw [show 2 * ((N + 1) / 2) - 1 = N by omega] at this
  simpa [Finset.image_insert, ea, eb, ec] using this

/-- **The family `{1, 2k, N}` for odd `N`** (`4 ≤ 2k ≤ N - 3`): the image under `chiX` of
`{1, k, (N - 1)/2}`, which is valid and, except for `k = 2` and `k = (N - 3)/2` when
`N ≡ 3 (mod 4)` (the dead sets `{1, 2, q}`, `{1, q - 1, q}` of the odd strip `q`), not dead. -/
theorem coReach_one_even_N {N k : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q) (hodd : N % 2 = 1)
    (h17 : 17 ≤ N) (hk2 : 2 ≤ k) (hk : 2 * k + 3 ≤ N)
    (hdead : N % 4 = 1 ∨ (3 ≤ k ∧ 2 * k + 5 ≤ N)) : CoReach N {1, 2 * k, N} := by
  refine coReach_of_chiXB (i := 1) (j := k) (l := (N + 1) / 2 - 1) IH ?_
  have e1 : chiX ((N + 1) / 2) 1 = 1 := by simp [chiX]
  have e2 : chiX ((N + 1) / 2) k = 2 * k := by unfold chiX; split_ifs <;> omega
  have e3 : chiX ((N + 1) / 2) ((N + 1) / 2 - 1) = N := by unfold chiX; split_ifs <;> omega
  have hv : valid3B ((N + 1) / 2 - 1) 1 k ((N + 1) / 2 - 1) = true := by
    unfold valid3B
    have h1 : step2B ((N + 1) / 2 - 1) k k 1 = true := by
      unfold step2B reach; simp only [beq_iff_eq]; split_ifs <;> omega
    have h2 : step2B ((N + 1) / 2 - 1) k 1 ((N + 1) / 2 - 1) = true := by
      unfold step2B reach; simp only [beq_iff_eq]; split_ifs <;> omega
    simp [h1, h2]
  have hd : dead3B ((N + 1) / 2 - 1) 1 k ((N + 1) / 2 - 1) = false := by
    simp only [dead3B, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      decide_eq_false_iff_not, ne_eq]
    omega
  simp only [chiXB, e1, e2, e3, hv, hd, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq, Bool.not_false]
  simp only [and_true, le_refl]; omega

/-! ## The complement of a near copy through a second near copy

The complement `Y` of the image of a near map is co-reachable as soon as `Y` is itself the
image of a near copy `ψ` of a strip `[q]` that is regular at every panel except two panels
`i₁, i₂` forming a live 2-prefix `[i₁, i₂]` of `[q]` (Conjecture C, `ThinCover.conjectureC`)
whose image `[ψ i₁, ψ i₂]` is a valid 2-prefix of `[N]`: the image of a completion
`[i₁, i₂, …]` orders `Y` from scratch. -/

/-- The image of a full sequence of `[q]` that starts with the irregular panels. -/
theorem coReach_compl_nearEmb {N q : Nat} {ψ : Nat → Nat} {R : Nat → Prop}
    (hψ : NearEmb N q ψ R) {i₁ i₂ : Nat}
    (hreg : ∀ x, 1 ≤ x → x ≤ q → x ≠ i₁ → x ≠ i₂ → R x) (hext : Extends q [i₁, i₂])
    (hst : SemiStep N [ψ i₁] (ψ i₂)) :
    CoReach N (Finset.Icc 1 N \ (Finset.Icc 1 q).image ψ) := by
  obtain ⟨a, hf, hv, hpre⟩ := hext
  have hnd : a.Nodup := (List.Perm.nodup_iff hf).2 (List.nodup_range' ..)
  have hb : ∀ y ∈ a, 1 ≤ y ∧ y ≤ q := fun y hy => by
    have := hf.subset hy; rw [List.mem_range'_1] at this; omega
  obtain ⟨t, rfl⟩ := hpre
  have hnd' := hnd
  rw [List.nodup_append] at hnd'
  have hi12 : i₁ ≠ i₂ := by
    have := hnd'.1; simp at this; exact this
  have hmap : SemiSymmetric N (([i₁, i₂] ++ t).map ψ) := by
    intro k hk
    simp only [List.length_map] at hk
    rw [List.getElem_map, ← List.map_take]
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · simp [SemiStep, leftCount, rightCount]
      · simpa using hst
    · have hS := take_nodup hnd k
      have hx : ([i₁, i₂] ++ t)[k] ∈ t := by
        rw [List.getElem_append_right (by simpa using hk2)]; exact List.getElem_mem _
      have hxb := hb _ (List.getElem_mem hk)
      have hx1 : ([i₁, i₂] ++ t)[k] ≠ i₁ := fun e => hnd'.2.2 i₁ (by simp) _ hx e.symm
      have hx2 : ([i₁, i₂] ++ t)[k] ≠ i₂ := fun e => hnd'.2.2 i₂ (by simp) _ hx e.symm
      have hR := hreg _ hxb.1 hxb.2 hx1 hx2
      refine (near_step hS (fun x hx' y hy e => ?_) (fun y hy => ?_)).2 (hv k hk)
      · have := hb x (List.mem_of_mem_take hx'); have := hb y (List.mem_of_mem_take hy)
        exact hψ.inj x y (by omega) (by omega) (by omega) (by omega) e
      · have := hb y (List.mem_of_mem_take hy)
        exact ⟨hψ.left _ y hxb.1 hxb.2 hR this.1 this.2, hψ.right _ y hxb.1 hxb.2 hR this.1 this.2⟩
  have hsub : (Finset.Icc 1 q).image ψ ⊆ Finset.Icc 1 N := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_Icc] at hy ⊢
    exact hψ.bound y hy.1 hy.2
  unfold CoReach g
  rw [Finset.card_pos, Finset.sdiff_sdiff_eq_self hsub]
  refine ⟨_, mem_semiOrders.2 ⟨⟨hψ.nodup_map hnd hb, ?_⟩, hmap⟩⟩
  ext x
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hb y hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hf.symm.subset ?_, rfl⟩
    rw [List.mem_range'_1]; omega

/-- The panels of `[N]` outside `xs`, in increasing order. -/
def cmpL (N : Nat) (xs : List Nat) : List Nat := (List.range' 1 N).filter fun x => !xs.contains x

/-- The increasing enumeration of a list. -/
def enumF (l : List Nat) (y : Nat) : Nat := l.getD (y - 1) 0

theorem map_enumF (l : List Nat) : (List.range' 1 l.length).map (enumF l) = l := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_map, List.getElem_range', enumF]
  rw [show 1 + 1 * n - 1 = n by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rfl

/-- **The near-copy rule with the complement through a second near copy.**  As `nearTrB`, but
the complement `Y` of the image of `φ` is shown co-reachable by its own increasing
enumeration `ψ : [q] → Y`, regular except at `i₁, i₂`, with `[i₁, i₂]` a valid non-dead
2-prefix of `[q]` and `[ψ i₁, ψ i₂]` a valid 2-prefix of `[N]`. -/
def nearTrP (N a b c k p u v y₁ e₁ y₂ e₂ i j l i₁ i₂ : Nat) : Bool :=
  let φ := nearF k N p u v y₁ e₁ y₂ e₂
  let ys := cmpL N ((List.range' 1 p).map φ)
  let ψ := enumF ys
  decide (p < N) && p != 7 && decide (1 ≤ i) && decide (i < j) && decide (j < l) &&
    decide (l ≤ p) && φ i == a && φ j == b && φ l == c && valid3B p i j l &&
    !dead3B p i j l && incB N p φ &&
    (List.range' 1 p).all (fun x => x == i || x == j || x == l || regB N p φ x) &&
    incB N ys.length ψ &&
    (List.range' 1 ys.length).all (fun x => x == i₁ || x == i₂ || regB N ys.length ψ x) &&
    decide (1 ≤ i₁) && decide (i₁ ≤ ys.length) && decide (1 ≤ i₂) && decide (i₂ ≤ ys.length) &&
    i₁ != i₂ && step2B ys.length i₁ i₁ i₂ && step2B N (ψ i₁) (ψ i₁) (ψ i₂) &&
    !deadB ys.length (min i₁ i₂) (max i₁ i₂)

theorem coReach_of_nearTrP {N a b c k p u v y₁ e₁ y₂ e₂ i j l i₁ i₂ : Nat}
    (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (h : nearTrP N a b c k p u v y₁ e₁ y₂ e₂ i j l i₁ i₂ = true) : CoReach N {a, b, c} := by
  unfold nearTrP at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, hp7⟩, hi⟩, hij⟩, hjl⟩, hl⟩, ea⟩, eb⟩, ec⟩, hv⟩, hd⟩, hinc⟩,
    hreg⟩, hinc2⟩, hreg2⟩, h11⟩, h12⟩, h21⟩, h22⟩, hne⟩, hs1⟩, hs2⟩, hdd⟩ := h
  set φ := nearF k N p u v y₁ e₁ y₂ e₂ with hφdef
  set ys := cmpL N ((List.range' 1 p).map φ) with hys
  have hφ := nearEmb_of_B hinc
  have hψ := nearEmb_of_B hinc2
  have hD := IH p hp hp7 i j l hi hij hjl hl hv hd
  -- the 2-prefix `[i₁, i₂]` of `[ys.length]` extends (Conjecture C)
  have hval : SemiSymmetric ys.length [i₁, i₂] := by
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · simp [SemiStep, leftCount, rightCount]
    · simpa using step1B_iff.1 hs1
  have hext : Extends ys.length [i₁, i₂] :=
    (ThinCover.conjectureC ⟨h11, h12⟩ ⟨h21, h22⟩ hne hval).2 hdd
  have hY := coReach_compl_nearEmb hψ (i₁ := i₁) (i₂ := i₂) (fun x hx1 hxq hx1' hx2' => by
      rw [List.all_eq_true] at hreg2
      have := hreg2 x (List.mem_range'_1.2 ⟨hx1, by omega⟩)
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      rcases this with (h | h) | h
      · exact absurd h hx1'
      · exact absurd h hx2'
      · exact h) hext (step1B_iff.1 hs2)
  -- the image of `ψ` is the complement of the image of `φ`
  have hlt := lt_of_incB hinc
  have himg : (Finset.Icc 1 ys.length).image (enumF ys) =
      Finset.Icc 1 N \ (Finset.Icc 1 p).image φ := by
    ext x
    have e1 : x ∈ (Finset.Icc 1 ys.length).image (enumF ys) ↔ x ∈ ys := by
      rw [← map_enumF ys, List.mem_map, Finset.mem_image]
      simp only [Finset.mem_Icc, List.mem_range'_1, map_enumF]
      constructor
      · rintro ⟨y, hy, e⟩; exact ⟨y, ⟨hy.1, by omega⟩, e⟩
      · rintro ⟨y, hy, e⟩; exact ⟨y, ⟨hy.1, by omega⟩, e⟩
    have e2 : x ∈ (List.range' 1 p).map φ ↔ ∃ y, (1 ≤ y ∧ y ≤ p) ∧ φ y = x := by
      rw [List.mem_map]
      constructor
      · rintro ⟨y, hy, e⟩; rw [List.mem_range'_1] at hy; exact ⟨y, ⟨hy.1, by omega⟩, e⟩
      · rintro ⟨y, hy, e⟩; exact ⟨y, List.mem_range'_1.2 ⟨hy.1, by omega⟩, e⟩
    rw [e1, hys, cmpL, List.mem_filter, List.mem_range'_1, Finset.mem_sdiff, Finset.mem_Icc,
      Finset.mem_image, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem, e2]
    simp only [Finset.mem_Icc]
    constructor
    · rintro ⟨hx, hn⟩; exact ⟨⟨hx.1, by omega⟩, hn⟩
    · rintro ⟨hx, hn⟩; exact ⟨⟨hx.1, by omega⟩, hn⟩
  have hsub : (Finset.Icc 1 p).image φ ⊆ Finset.Icc 1 N := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_Icc] at hy ⊢
    exact hφ.bound y hy.1 hy.2
  rw [himg, Finset.sdiff_sdiff_eq_self hsub] at hY
  have := coReach_nearEmb hφ hY (D := {i, j, l}) (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]; omega)
    (fun x hx1 hxp hx => by
      rw [List.all_eq_true] at hreg
      have := hreg x (List.mem_range'_1.2 ⟨hx1, by omega⟩)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      rcases this with ((h | h) | h) | h
      · exact absurd h hx.1
      · exact absurd h hx.2.1
      · exact absurd h hx.2.2
      · exact h) hD
  simpa [Finset.image_insert, ea, eb, ec] using this

/-! ## A closed-form near copy: `{1, 2, c}` for `N ≡ 1 (mod 4)` and odd `c`

`phi12 : [p] → [N]` (`N = 2p - 1`, `p` odd) is the odd class with the panel `3` moved to `2`:
`1 ↦ 1`, `2 ↦ 2`, `y ↦ 2y - 1`.  It preserves the window relation around every panel except
`2` (for even `p` the panel `(p + 2)/2` would be irregular as well).  Its image
`{1, 2, 5, 7, …, N}` is co-reachable: `4` is a valid step, and `{1, 2, 4, 5, 7, …, N}` pulls no
panel to the left (Theorem G with the centre `1/2`).  So `{1, 2, c}` (`c` odd) is the image of
`{1, 2, (c + 1)/2}`, co-reachable in `[p]` by induction. -/

/-- The odd class with `3` moved to `2`. -/
def phi12 (y : Nat) : Nat := if y = 2 then 2 else 2 * y - 1

theorem nearEmb_phi12 {p : Nat} (hp : 3 ≤ p) (ho : p % 2 = 1) :
    NearEmb (2 * p - 1) p phi12 (fun j => j ≠ 2) := by
  refine ⟨fun y h1 h2 => ?_, fun x y hx1 hxp hy1 hyp e => ?_, fun j y hj1 hjp hR hy1 hyp => ?_,
    fun j y hj1 hjp hR hy1 hyp => ?_⟩
  · unfold phi12; split_ifs <;> omega
  · unfold phi12 at e; split_ifs at e <;> omega
  · unfold phi12 reach; split_ifs <;> omega
  · unfold phi12 reach; split_ifs <;> omega

theorem mem_image_phi12 {p x : Nat} (hp : 3 ≤ p) :
    x ∈ (Finset.Icc 1 p).image phi12 ↔
      x = 1 ∨ x = 2 ∨ (x % 2 = 1 ∧ 5 ≤ x ∧ x ≤ 2 * p - 1) := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rw [Finset.mem_Icc] at hy; unfold phi12; split_ifs <;> omega
  · intro h
    rcases h with rfl | rfl | h
    · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, by simp [phi12]⟩
    · exact ⟨2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by simp [phi12]⟩
    · exact ⟨(x + 1) / 2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by
        unfold phi12; split_ifs <;> omega⟩

/-- `#({1, 2, 4} ∪ {odd ≥ 5}) ∩ [0, t)`. -/
def F12 (t : Nat) : Nat := if 5 ≤ t then t / 2 + 1 else if 3 ≤ t then 2 else t - 1

theorem countP_F12 : ∀ n lo, (List.range' lo n).countP
    (fun x => decide (x = 1 ∨ x = 2 ∨ x = 4 ∨ (x % 2 = 1 ∧ 5 ≤ x))) = F12 (lo + n) - F12 lo
  | 0, lo => by simp
  | n + 1, lo => by
    rw [List.range'_succ, List.countP_cons, countP_F12 n (lo + 1),
      show lo + (n + 1) = lo + 1 + n by omega]
    have hm : F12 (lo + 1) ≤ F12 (lo + 1 + n) := by unfold F12; split_ifs <;> omega
    have key : F12 (lo + 1) =
        F12 lo + (if lo = 1 ∨ lo = 2 ∨ lo = 4 ∨ (lo % 2 = 1 ∧ 5 ≤ lo) then 1 else 0) := by
      unfold F12; split_ifs <;> omega
    simp only [decide_eq_true_eq]
    split_ifs at key ⊢ <;> omega

theorem countP_sub_range' (P : Nat → Prop) [DecidablePred P] (m : Nat) :
    ∀ r, r < m → (List.range' 1 r).countP (fun d => decide (P (m - d))) =
      (List.range' (m - r) r).countP (fun x => decide (P x))
  | 0, _ => by simp
  | r + 1, h => by
    have e : List.range' (m - (r + 1)) (r + 1) = (m - (r + 1)) :: List.range' (m - r) r := by
      rw [List.range'_succ, show m - (r + 1) + 1 = m - r by omega]
    rw [List.range'_concat, List.countP_append, countP_sub_range' P m r (by omega), e,
      List.countP_cons, show 1 + 1 * r = r + 1 by omega]
    simp only [List.countP_cons, List.countP_nil]
    omega

theorem countP_add_range' (P : Nat → Prop) [DecidablePred P] (m : Nat) :
    ∀ r, (List.range' 1 r).countP (fun d => decide (P (m + d))) =
      (List.range' (m + 1) r).countP (fun x => decide (P x))
  | 0 => by simp
  | r + 1 => by
    rw [List.range'_concat, List.range'_concat, List.countP_append, List.countP_append,
      countP_add_range' P m r]
    simp only [List.countP_cons, List.countP_nil, show m + (1 + 1 * r) = m + 1 + 1 * r by omega]

/-- **`{1, 2, c}` is co-reachable for `N ≡ 1 (mod 4)` and odd `c`, `7 ≤ c ≤ N - 4`**, given
the smaller strips. -/
theorem coReach_one_two_odd {N c : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q) (hN4 : N % 4 = 1)
    (h17 : 17 ≤ N) (hc : c % 2 = 1) (hc7 : 7 ≤ c) (hcN : c + 4 ≤ N) : CoReach N {1, 2, c} := by
  obtain ⟨p, hp⟩ : ∃ p, p = (N + 1) / 2 := ⟨_, rfl⟩
  have hNp : N = 2 * p - 1 := by omega
  have hφ := nearEmb_phi12 (p := p) (by omega) (by omega)
  have hmem := fun x => mem_image_phi12 (p := p) (x := x) (by omega)
  -- the image `B` and `B ∪ {4}`
  set B := (Finset.Icc 1 p).image phi12 with hB
  have hBs : B ⊆ Finset.Icc 1 N := by
    intro x hx; rw [hmem] at hx; rw [Finset.mem_Icc]; omega
  have h4 : (4 : Nat) ∉ B := by rw [hmem]; omega
  have hmem4 : ∀ x, 1 ≤ x → x ≤ N →
      (x ∈ insert 4 B ↔ (x = 1 ∨ x = 2 ∨ x = 4 ∨ (x % 2 = 1 ∧ 5 ≤ x))) := by
    intro x hx1 hxN; rw [Finset.mem_insert, hmem]; omega
  have hinw : Inward N 1 (insert 4 B) := by
    intro m hm1 hmN hmB
    refine ⟨by omega, fun h => by omega, fun _ => ?_⟩
    rw [leftCount_finset, rightCount_finset]
    obtain ⟨r, hr⟩ : ∃ r, r = reach N m := ⟨_, rfl⟩
    rw [← hr]
    have hr1 : r ≤ m - 1 := by rw [hr]; unfold reach; omega
    have hr2 : r ≤ N - m := by rw [hr]; unfold reach; omega
    have L : (List.range' 1 r).countP (fun d => decide (m - d ∈ insert 4 B)) =
        F12 m - F12 (m - r) := by
      have e1 := countP_sub_range' (fun x => x ∈ insert 4 B) m r (by omega)
      have e2 : (List.range' (m - r) r).countP (fun x => decide (x ∈ insert 4 B)) =
          (List.range' (m - r) r).countP
            (fun x => decide (x = 1 ∨ x = 2 ∨ x = 4 ∨ (x % 2 = 1 ∧ 5 ≤ x))) := by
        apply List.countP_congr; intro x hx; rw [List.mem_range'_1] at hx
        simp only [decide_eq_true_eq]; exact hmem4 x (by omega) (by omega)
      rw [countP_F12, show m - r + r = m by omega] at e2
      exact e1.trans e2
    have R : (List.range' 1 r).countP (fun d => decide (m + d ∈ insert 4 B)) =
        F12 (m + 1 + r) - F12 (m + 1) := by
      have e1 := countP_add_range' (fun x => x ∈ insert 4 B) m r
      have e2 : (List.range' (m + 1) r).countP (fun x => decide (x ∈ insert 4 B)) =
          (List.range' (m + 1) r).countP
            (fun x => decide (x = 1 ∨ x = 2 ∨ x = 4 ∨ (x % 2 = 1 ∧ 5 ≤ x))) := by
        apply List.countP_congr; intro x hx; rw [List.mem_range'_1] at hx
        simp only [decide_eq_true_eq]; exact hmem4 x (by omega) (by omega)
      rw [countP_F12] at e2
      exact e1.trans e2
    rw [L, R]
    have hm' := (hmem4 m hm1 hmN).not.1 hmB
    unfold reach at hr
    unfold F12
    split_ifs <;> omega
  have hY4 : CoReach N (insert 4 B) := coReach_of_inward (fun x hx => by
    rw [Finset.mem_insert] at hx; rcases hx with rfl | hx
    · rw [Finset.mem_Icc]; omega
    · exact hBs hx) hinw
  have hstep : SemiStep N B.toList 4 := by
    unfold SemiStep
    rw [leftCount_finset, rightCount_finset, show reach N 4 = 3 by unfold reach; omega]
    simp only [List.range', List.countP_cons, List.countP_nil, hmem]
    norm_num
    split_ifs <;> omega
  have hY : CoReach N B := coReach_of_step hBs (by omega) (by omega) h4 hstep hY4
  -- the preimage `{1, 2, (c + 1)/2}`
  have hv : valid3B p 1 2 ((c + 1) / 2) = true := by
    unfold valid3B
    have h1 : step2B p ((c + 1) / 2) ((c + 1) / 2) 2 = true := by
      unfold step2B reach; simp only [beq_iff_eq]; split_ifs <;> omega
    have h2 : step2B p ((c + 1) / 2) 2 1 = true := by
      unfold step2B reach; simp only [beq_iff_eq]; split_ifs <;> omega
    simp [h1, h2]
  have hd : dead3B p 1 2 ((c + 1) / 2) = false := by
    simp only [dead3B, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      decide_eq_false_iff_not, ne_eq]
    omega
  have hD := IH p (by omega) (by omega) 1 2 ((c + 1) / 2) le_rfl (by omega) (by omega)
    (by omega) hv hd
  rw [hNp] at hY ⊢
  have := coReach_nearEmb hφ hY (D := {1, 2, (c + 1) / 2}) (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]; omega)
    (fun j _ _ hj => by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
                        exact hj.2.1) hD
  have e1 : phi12 1 = 1 := by simp [phi12]
  have e2 : phi12 2 = 2 := by simp [phi12]
  have e3 : phi12 ((c + 1) / 2) = c := by unfold phi12; split_ifs <;> omega
  simpa [Finset.image_insert, e1, e2, e3] using this

/-! ## The enlarged rules and the reduction -/

/-- The new rules for a sorted triple: a near copy (`nearTrB`, `nearTrP`) or the copy `X_N`
(`chiXB`). -/
def NearCov (N a b c : Nat) : Prop :=
  (∃ k p u v y₁ e₁ y₂ e₂ i j l c2 ms, nearTrB N a b c k p u v y₁ e₁ y₂ e₂ i j l c2 ms = true) ∨
    (∃ k p u v y₁ e₁ y₂ e₂ i j l i₁ i₂, nearTrP N a b c k p u v y₁ e₁ y₂ e₂ i j l i₁ i₂ = true) ∨
    ∃ i j l, chiXB N a b c i j l = true

/-- `Covered3S` (Live3q) or a new rule, for the triple or its mirror image. -/
def Covered3R (N a b c : Nat) : Prop :=
  Covered3S N a b c ∨ NearCov N a b c ∨ NearCov N (N + 1 - c) (N + 1 - b) (N + 1 - a)

theorem coReach_of_nearCov {N a b c : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (h : NearCov N a b c) : CoReach N {a, b, c} := by
  rcases h with ⟨k, p, u, v, y₁, e₁, y₂, e₂, i, j, l, c2, ms, h⟩ |
    ⟨k, p, u, v, y₁, e₁, y₂, e₂, i, j, l, i₁, i₂, h⟩ | ⟨i, j, l, h⟩
  · exact coReach_of_nearTrB IH h
  · exact coReach_of_nearTrP IH h
  · exact coReach_of_chiXB IH h

theorem coReach_of_covered3R {N a b c : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcN : c ≤ N) (h : Covered3R N a b c) :
    CoReach N {a, b, c} := by
  rcases h with h | h | h
  · exact coReach_of_covered3S IH ha hab hbc hcN h
  · exact coReach_of_nearCov IH h
  · exact coReach3_of_mirror (by omega) (by omega) hcN (coReach_of_nearCov IH h)

/-- **The smaller residual statement**: every valid, non-dead sorted triple of `[N]` not
settled by `Covered3R` is co-reachable. -/
def Residual3R (N : Nat) : Prop :=
  ∀ a b c, 1 ≤ a → a < b → b < c → c ≤ N → valid3B N a b c = true → dead3B N a b c = false →
    ¬ Covered3R N a b c → CoReach N {a, b, c}

/-- Given the smaller strips, `Residual3R N` implies `Residual3 N` (Live3q's statement). -/
theorem residual3_of_residual3R {N : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (h : Residual3R N) : Residual3 N := by
  intro a b c ha hab hbc hcN hv hd _
  by_cases hc : Covered3R N a b c
  · exact coReach_of_covered3R IH ha hab hbc hcN hc
  · exact h a b c ha hab hbc hcN hv hd hc

/-- **Reduction** with the enlarged rules: the 3-prefix property for all `N ≠ 7` follows from
the base strips and `Residual3R` above them. -/
theorem good3_of_residual3R {M : Nat} (hbase : ∀ N, N ≤ M → N ≠ 7 → Good3 N)
    (hres : ∀ N, M < N → Residual3R N) : ∀ N, N ≠ 7 → Good3 N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro h7
    by_cases hN : N ≤ M
    · exact hbase N hN h7
    intro a b c ha hab hbc hcN hv hd
    by_cases hc : Covered3R N a b c
    · exact coReach_of_covered3R ih ha hab hbc hcN hc
    · exact hres N (by omega) a b c ha hab hbc hcN hv hd hc

/-- The form in which `Residual3` is needed by `Live3q.good3_of_residual`, from `Residual3R`:
`Residual3 N` for all `N > M` given the base strips and `Residual3R N` for all `N > M`. -/
theorem residual3_all_of_residual3R {M : Nat} (hbase : ∀ N, N ≤ M → N ≠ 7 → Good3 N)
    (hres : ∀ N, M < N → Residual3R N) : ∀ N, M < N → Residual3 N := fun N hN =>
  residual3_of_residual3R (fun q _ hq7 => good3_of_residual3R hbase hres q hq7) (hres N hN)

end Live3r
end Folds
