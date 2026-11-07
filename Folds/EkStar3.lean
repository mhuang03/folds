import Folds.EkStar
import Folds.Live3q

/-!
# Conjecture E*_3: the 3-subsets of `[2, N - 1]`

`experiments/ekstar3/PROOFS.txt`.  For `k = 3` (`c_3 = 1`) Conjecture E*_k says that every
3-subset of `[2, N - 1]` is co-reachable (`E3 N`).

* `ekStarConj_three_of`, `e3_of_ekStarConj_three`: `(∀ N, E3 N) ↔ EkStarConj 3`.
* `dead3B_inner`, `coReach_of_good3_inner`: an interior triple is never one of the dead 3-sets
  of `Live3p`, so `Good3 N` (the 3-prefix property of `Live3q`) settles every VALID interior
  triple; `e3_valid_le_50`: the valid interior triples for `N ≤ 50`.  The invalid triples
  (no ordering is a valid 3-prefix) are outside the scope of `Good3` and are the bulk of the
  work here.
* `preOK`, `trEB`, `coReach_of_trEB`: **transfers inside the E*_3 induction**: the triple is
  the image under one of the copies of `Live3q` of a triple of a smaller strip `[p]` that is
  interior (induction hypothesis `E3 p`), or valid and non-dead with `p ≤ 50`
  (`Live3q.good3_le_50`), or satisfies Theorem G in closed form (`F3S`).
* `CoveredE`, `ResidualE`, `e3_of_residualE`: **the reduction for all `N`**: E*_3 holds for
  every `N` iff (given the base) the interior triples not settled by Theorem G, Theorem G
  after at most two valid steps, or such a transfer (for the triple or its mirror image)
  are co-reachable for every `N` above the base.
* `HintE` checks (`chkE`, `CovQE`, `e3_of_covE`), and **`e3_le_50`: E*_3 for every
  `N ≤ 50`**, by kernel-checked certificates (`decide +kernel`).
-/

namespace Folds
namespace EkStar3

open Live2 Live3p Live3q

/-! ## The statement -/

/-- **E*_3 for the strip `[N]`**: every 3-subset `{a, b, c}` of `[2, N - 1]` is co-reachable. -/
def E3 (N : Nat) : Prop :=
  ∀ a b c, 2 ≤ a → a < b → b < c → c + 1 ≤ N → CoReach N {a, b, c}

theorem sort3 {x y z : Nat} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ a b c, a < b ∧ b < c ∧ ({x, y, z} : Finset Nat) = {a, b, c} ∧
      a = min x (min y z) ∧ c = max x (max y z) := by
  refine ⟨min x (min y z), x + y + z - min x (min y z) - max x (max y z), max x (max y z),
    by omega, by omega, ?_, rfl, rfl⟩
  ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; omega

/-- `E3 N` in set form: every 3-subset of `[2, N - 1]` is co-reachable. -/
theorem coReach_of_e3 {N : Nat} (h : E3 N) {D : Finset Nat} (hD : D ⊆ Finset.Icc 2 (N - 1))
    (hc : D.card = 3) : CoReach N D := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hc
  have hx := Finset.mem_Icc.1 (hD (show x ∈ ({x, y, z} : Finset Nat) by simp))
  have hy := Finset.mem_Icc.1 (hD (show y ∈ ({x, y, z} : Finset Nat) by simp))
  have hz := Finset.mem_Icc.1 (hD (show z ∈ ({x, y, z} : Finset Nat) by simp))
  obtain ⟨a, b, c, hab, hbc, e, ea, ec⟩ := sort3 hxy hxz hyz
  rw [e]
  exact h a b c (by omega) hab hbc (by omega)

/-- `E3` for all `N` is Conjecture E*_3 in the form of `EkStar.EkStarConj`. -/
theorem ekStarConj_three_of (h : ∀ N, E3 N) : EkStar.EkStarConj 3 :=
  fun N D hD hc hd => absurd (coReach_of_e3 (h N) (by simpa [EkStar.cK] using hD) hc) hd

theorem e3_of_ekStarConj_three (h : EkStar.EkStarConj 3) (N : Nat) : E3 N := by
  intro a b c ha hab hbc hc
  by_contra hd
  have hD : ({a, b, c} : Finset Nat) ⊆ Finset.Icc (EkStar.cK 3 + 1) (N - EkStar.cK 3) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [EkStar.cK, Finset.mem_Icc]; omega
  have hcard : ({a, b, c} : Finset Nat).card = 3 := by
    rw [Finset.card_eq_three]; exact ⟨a, b, c, by omega, by omega, by omega, rfl⟩
  obtain ⟨h1, -⟩ := h N _ hD hcard hd
  omega

/-! ## Valid interior triples: the 3-prefix property -/

/-- An interior triple is never one of the dead 3-sets of `Live3p`. -/
theorem dead3B_inner {N a b c : Nat} (ha : 2 ≤ a) (hc : c + 1 ≤ N) : dead3B N a b c = false := by
  have h1 : (a == 1) = false := by simp; omega
  have h2 : (c == N) = false := by simp; omega
  simp [dead3B, h1, h2]

/-- `Good3 N` settles every valid interior triple. -/
theorem coReach_of_good3_inner {N a b c : Nat} (hG : Good3 N) (ha : 2 ≤ a) (hab : a < b)
    (hbc : b < c) (hc : c + 1 ≤ N) (hv : valid3B N a b c = true) : CoReach N {a, b, c} :=
  hG a b c (by omega) hab hbc (by omega) hv (dead3B_inner ha hc)

/-- **The valid interior triples, `N ≤ 50`, `N ≠ 7`.** -/
theorem e3_valid_le_50 {N a b c : Nat} (hN : N ≤ 50) (h7 : N ≠ 7) (ha : 2 ≤ a) (hab : a < b)
    (hbc : b < c) (hc : c + 1 ≤ N) (hv : valid3B N a b c = true) : CoReach N {a, b, c} :=
  coReach_of_good3_inner (good3_le_50 N hN h7) ha hab hbc hc hv

/-! ## Transfers inside the E*_3 induction -/

/-- The preimage triple `(i, j, l)` of `[p]` is known to be co-reachable: interior (induction
hypothesis), or valid and non-dead with `p ≤ 50`, `p ≠ 7` (`good3_le_50`), or `F3S`. -/
def preOK (p i j l : Nat) : Bool :=
  (decide (2 ≤ i) && decide (l + 1 ≤ p)) ||
    (decide (p ≤ 50) && p != 7 && valid3B p i j l && !dead3B p i j l) || f3SB p i j l

/-- A transfer hint for E*_3. -/
def trEB (N a b c k p u v i j l : Nat) : Bool :=
  copyOK k N p u v && decide (p < N) && decide (1 ≤ i) && decide (i < j) &&
    decide (j < l) && decide (l ≤ p) && copyF k N p u v i == a && copyF k N p u v j == b &&
    copyF k N p u v l == c && preOK p i j l

theorem coReach_of_preOK {p i j l : Nat} (IH : E3 p) (hi : 1 ≤ i) (hij : i < j) (hjl : j < l)
    (hl : l ≤ p) (h : preOK p i j l = true) : CoReach p {i, j, l} := by
  unfold preOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    Bool.not_eq_true'] at h
  rcases h with (⟨h1, h2⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | h
  · exact IH i j l h1 hij hjl h2
  · exact good3_le_50 p h1 h2 i j l hi hij hjl hl h3 h4
  · exact coReach3_of_F hi hij hjl hl (f3S_of_f3SB h)

theorem coReach_of_trEB {N a b c k p u v i j l : Nat} (IH : ∀ q, q < N → E3 q)
    (h : trEB N a b c k p u v i j l = true) : CoReach N {a, b, c} := by
  unfold trEB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, hp⟩, hi⟩, hij⟩, hjl⟩, hl⟩, ea⟩, eb⟩, ec⟩, hpre⟩ := h
  have hD := coReach_of_preOK (IH p hp) hi hij hjl hl hpre
  have := transfers_of_copyOK hc {i, j, l} (fun x hx => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Icc]; omega) hD
  simpa [Finset.image_insert, ea, eb, ec] using this

/-! ## The covering rules and the reduction for all `N` -/

/-- The rules: Theorem G in closed form, Theorem G after at most two valid steps, or a
transfer from a smaller strip (`trEB`). -/
def CoveredE (N a b c : Nat) : Prop :=
  f3SB N a b c = true ∨ (∃ ms c2, ms.length ≤ 2 ∧ stepsB N [a, b, c] ms c2 = true) ∨
    ∃ k p u v i j l, trEB N a b c k p u v i j l = true

/-- `CoveredE` for the triple or its mirror image. -/
def CoveredES (N a b c : Nat) : Prop :=
  CoveredE N a b c ∨ CoveredE N (N + 1 - c) (N + 1 - b) (N + 1 - a)

theorem coReach_of_coveredE {N a b c : Nat} (IH : ∀ q, q < N → E3 q) (ha : 1 ≤ a)
    (hab : a < b) (hbc : b < c) (hcN : c ≤ N) (h : CoveredE N a b c) : CoReach N {a, b, c} := by
  rcases h with h | ⟨ms, c2, -, h⟩ | ⟨k, p, u, v, i, j, l, h⟩
  · exact coReach3_of_F ha hab hbc hcN (f3S_of_f3SB h)
  · exact coReach3_of_stepsB ha hab hbc hcN h
  · exact coReach_of_trEB IH h

theorem coReach_of_coveredES {N a b c : Nat} (IH : ∀ q, q < N → E3 q) (ha : 1 ≤ a)
    (hab : a < b) (hbc : b < c) (hcN : c ≤ N) (h : CoveredES N a b c) :
    CoReach N {a, b, c} := by
  rcases h with h | h
  · exact coReach_of_coveredE IH ha hab hbc hcN h
  · exact coReach3_of_mirror (by omega) (by omega) hcN
      (coReach_of_coveredE IH (by omega) (by omega) (by omega) (by omega) h)

/-- **The residual statement for `N`**: every interior triple not settled by `CoveredES` is
co-reachable. -/
def ResidualE (N : Nat) : Prop :=
  ∀ a b c, 2 ≤ a → a < b → b < c → c + 1 ≤ N → ¬ CoveredES N a b c → CoReach N {a, b, c}

/-- **Reduction**: E*_3 for every `N` follows from a base and the residual statements above
it. -/
theorem e3_of_residualE {M : Nat} (hbase : ∀ N, N ≤ M → E3 N)
    (hres : ∀ N, M < N → ResidualE N) : ∀ N, E3 N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hN : N ≤ M
    · exact hbase N hN
    intro a b c ha hab hbc hcN
    by_cases hc : CoveredES N a b c
    · exact coReach_of_coveredES ih (by omega) hab hbc (by omega) hc
    · exact hres N (by omega) a b c ha hab hbc hcN hc

/-! ## Certificates -/

/-- A hint (the `Live3q.Hint` format, with `.tr` read as an E*_3 transfer `trEB`). -/
def hintBE (N a b c : Nat) : Hint → Bool
  | .wit w => witB3 N a b c w
  | .st c2 ms => stepsB N [a, b, c] ms c2
  | .tr k p u v i j l => trEB N a b c k p u v i j l

def hintOKE (N a b c : Nat) (h : Bool × Hint) : Bool :=
  if h.1 then hintBE N (N + 1 - c) (N + 1 - b) (N + 1 - a) h.2 else hintBE N a b c h.2

theorem coReach_of_hintBE {N a b c : Nat} (IH : ∀ q, q < N → E3 q) (ha : 1 ≤ a)
    (hab : a < b) (hbc : b < c) (hcN : c ≤ N) {h : Hint} (hh : hintBE N a b c h = true) :
    CoReach N {a, b, c} := by
  cases h with
  | wit w => exact coReach_of_witB3 hh
  | st c2 ms => exact coReach3_of_stepsB ha hab hbc hcN hh
  | tr k p u v i j l => exact coReach_of_trEB IH hh

theorem coReach_of_hintOKE {N a b c : Nat} (IH : ∀ q, q < N → E3 q) (ha : 1 ≤ a)
    (hab : a < b) (hbc : b < c) (hcN : c ≤ N) {h : Bool × Hint}
    (hh : hintOKE N a b c h = true) : CoReach N {a, b, c} := by
  unfold hintOKE at hh
  split_ifs at hh
  · exact coReach3_of_mirror (by omega) (by omega) hcN
      (coReach_of_hintBE IH (by omega) (by omega) (by omega) (by omega) hh)
  · exact coReach_of_hintBE IH ha hab hbc hcN hh

/-- The interior triples that need a hint: canonical orientation (`a + c ≤ N + 1`), invalid
(the valid ones are settled by `Good3 N`, except for `N = 7`), not `F3S`. -/
def needE (N a b c : Nat) : Bool :=
  decide (a + c ≤ N + 1) && !(N != 7 && valid3B N a b c) && !f3SB N a b c

/-- The pairs `(b, c)`, `b₀ ≤ b < b₁`, `b < c ≤ N - 1`, whose triple needs a hint. -/
def neededE (N a b₀ b₁ : Nat) : List (Nat × Nat) :=
  ((List.range' b₀ (b₁ - b₀)).flatMap fun b =>
    (List.range' (b + 1) (N - 1 - b)).map fun c => (b, c)).filter fun t => needE N a t.1 t.2

def all2E (N a : Nat) : List (Nat × Nat) → List (Bool × Hint) → Bool
  | [], [] => true
  | t :: ts, h :: hs => hintOKE N a t.1 t.2 h && all2E N a ts hs
  | _, _ => false

theorem all2E_sound {N a : Nat} : ∀ (ts : List (Nat × Nat)) (hs : List (Bool × Hint)),
    all2E N a ts hs = true → ∀ t ∈ ts, ∃ h, hintOKE N a t.1 t.2 h = true
  | [], [], _ => fun t ht => absurd ht (List.not_mem_nil)
  | t :: ts, h :: hs, e => by
      simp only [all2E, Bool.and_eq_true] at e
      intro t' ht'
      rw [List.mem_cons] at ht'
      rcases ht' with rfl | ht'
      · exact ⟨h, e.1⟩
      · exact all2E_sound ts hs e.2 t' ht'
  | [], _ :: _, e => by simp [all2E] at e
  | _ :: _, [], e => by simp [all2E] at e

/-- The certificate check for the triples `(a, b, c)`, `b₀ ≤ b < b₁`. -/
def chkE (N a b₀ b₁ : Nat) (hs : List (Bool × Hint)) : Bool := all2E N a (neededE N a b₀ b₁) hs

/-- Hints for the needed triples `(a, b, c)` with `b₀ ≤ b < b₁`. -/
def CovBE (N a b₀ b₁ : Nat) : Prop :=
  ∀ b c, b₀ ≤ b → b < b₁ → b < c → c + 1 ≤ N → needE N a b c = true →
    ∃ h, hintOKE N a b c h = true

theorem CovBE.of_chk {N a b₀ b₁ : Nat} {hs : List (Bool × Hint)}
    (hc : chkE N a b₀ b₁ hs = true) : CovBE N a b₀ b₁ := by
  intro b c h0 h1 hbc hcN hn
  have hmem : (b, c) ∈ neededE N a b₀ b₁ := by
    unfold neededE
    rw [List.mem_filter, List.mem_flatMap]
    exact ⟨⟨b, List.mem_range'_1.2 ⟨h0, by omega⟩, List.mem_map.2
      ⟨c, List.mem_range'_1.2 ⟨by omega, by omega⟩, rfl⟩⟩, hn⟩
  exact all2E_sound _ _ hc _ hmem

theorem CovBE.trans {N a b₀ b₁ b₂ : Nat} (h₁ : CovBE N a b₀ b₁) (h₂ : CovBE N a b₁ b₂) :
    CovBE N a b₀ b₂ := fun b c h0 h1 h2 h3 hn => by
  by_cases hb : b < b₁
  · exact h₁ b c h0 hb h2 h3 hn
  · exact h₂ b c (by omega) h1 h2 h3 hn

/-- Hints for the needed triples with smallest element `a₀ ≤ a < a₁`. -/
def CovAE (N a₀ a₁ : Nat) : Prop := ∀ a, a₀ ≤ a → a < a₁ → CovBE N a (a + 1) N

theorem CovAE.one {N a : Nat} (h : CovBE N a (a + 1) N) : CovAE N a (a + 1) :=
  fun a' h0 h1 => by rw [show a' = a by omega]; exact h

theorem CovAE.trans {N a₀ a₁ a₂ : Nat} (h₁ : CovAE N a₀ a₁) (h₂ : CovAE N a₁ a₂) :
    CovAE N a₀ a₂ := fun a h0 h1 => by
  by_cases ha : a < a₁
  · exact h₁ a h0 ha
  · exact h₂ a (by omega) h1

/-- A hint for every needed interior triple of `[N]`. -/
def CovQE (N : Nat) : Prop :=
  ∀ a b c, 2 ≤ a → a < b → b < c → c + 1 ≤ N → needE N a b c = true →
    ∃ h, hintOKE N a b c h = true

theorem CovQE.of_covAE {N : Nat} (h : CovAE N 2 (N - 2)) : CovQE N :=
  fun a b c h0 h1 h2 h3 hn => h a h0 (by omega) b c (by omega) (by omega) h2 h3 hn

/-- Below `N = 5` there are no interior triples. -/
theorem CovQE.of_small {N : Nat} (hN : N ≤ 4) : CovQE N :=
  fun a b c h0 h1 h2 h3 _ => by omega

/-- **Soundness of the certificates**: given `E3` below `N` and `Good3 N`, hints for all needed
triples give `E3 N`. -/
theorem e3_of_covE {N : Nat} (IH : ∀ q, q < N → E3 q) (hG : N ≠ 7 → Good3 N) (h : CovQE N) :
    E3 N := by
  have canon : ∀ a b c, 2 ≤ a → a < b → b < c → c + 1 ≤ N → a + c ≤ N + 1 →
      CoReach N {a, b, c} := by
    intro a b c ha hab hbc hcN hcan
    by_cases hv : (N != 7 && valid3B N a b c) = true
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hv
      exact coReach_of_good3_inner (hG hv.1) ha hab hbc hcN hv.2
    by_cases hf : f3SB N a b c = true
    · exact coReach3_of_F (by omega) hab hbc (by omega) (f3S_of_f3SB hf)
    obtain ⟨h', hh⟩ := h a b c ha hab hbc hcN (by
      simp only [needE, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      simp only [Bool.not_eq_true] at hv hf
      exact ⟨⟨hcan, hv⟩, hf⟩)
    exact coReach_of_hintOKE IH (by omega) hab hbc (by omega) hh
  intro a b c ha hab hbc hcN
  by_cases hcan : a + c ≤ N + 1
  · exact canon a b c ha hab hbc hcN hcan
  · exact coReach3_of_mirror (by omega) (by omega) (by omega)
      (canon _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega))

/-! ## Certificates for `N ≤ 40` (generated by `experiments/ekstar3/mkE.py`)

Checked sequentially (`Elab.async false`) to keep the memory low. -/

set_option Elab.async false

/-! ### `N = 0` -/

theorem cove_0 : CovQE 0 := CovQE.of_small (by decide)

/-! ### `N = 1` -/

theorem cove_1 : CovQE 1 := CovQE.of_small (by decide)

/-! ### `N = 2` -/

theorem cove_2 : CovQE 2 := CovQE.of_small (by decide)

/-! ### `N = 3` -/

theorem cove_3 : CovQE 3 := CovQE.of_small (by decide)

/-! ### `N = 4` -/

theorem cove_4 : CovQE 4 := CovQE.of_small (by decide)

/-! ### `N = 5` -/

theorem che_5_2_0 : chkE 5 2 3 5 (decH 1 0) = true := by decide +kernel
theorem cove_5_2 : CovBE 5 2 3 5 :=
  CovBE.of_chk che_5_2_0

theorem cove_5 : CovQE 5 :=
  CovQE.of_covAE (CovAE.one cove_5_2)

/-! ### `N = 6` -/

theorem che_6_2_0 : chkE 6 2 3 6 (decH 1 0) = true := by decide +kernel
theorem cove_6_2 : CovBE 6 2 3 6 :=
  CovBE.of_chk che_6_2_0

theorem che_6_3_0 : chkE 6 3 4 6 (decH 1 0) = true := by decide +kernel
theorem cove_6_3 : CovBE 6 3 4 6 :=
  CovBE.of_chk che_6_3_0

theorem cove_6 : CovQE 6 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_6_2) (CovAE.one cove_6_3))

/-! ### `N = 7` -/

theorem che_7_2_0 : chkE 7 2 3 7 (decH 1 0) = true := by decide +kernel
theorem cove_7_2 : CovBE 7 2 3 7 :=
  CovBE.of_chk che_7_2_0

theorem che_7_3_0 : chkE 7 3 4 7 (decH 1 0) = true := by decide +kernel
theorem cove_7_3 : CovBE 7 3 4 7 :=
  CovBE.of_chk che_7_3_0

theorem che_7_4_0 : chkE 7 4 5 7 (decH 1 0) = true := by decide +kernel
theorem cove_7_4 : CovBE 7 4 5 7 :=
  CovBE.of_chk che_7_4_0

theorem cove_7 : CovQE 7 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_7_2) (CovAE.trans (CovAE.one cove_7_3) (CovAE.one cove_7_4)))

/-! ### `N = 8` -/

theorem che_8_2_0 : chkE 8 2 3 8 (decH 3 36966676143848588931) = true := by decide +kernel
theorem cove_8_2 : CovBE 8 2 3 8 :=
  CovBE.of_chk che_8_2_0

theorem che_8_3_0 : chkE 8 3 4 8 (decH 1 0) = true := by decide +kernel
theorem cove_8_3 : CovBE 8 3 4 8 :=
  CovBE.of_chk che_8_3_0

theorem che_8_4_0 : chkE 8 4 5 8 (decH 1 0) = true := by decide +kernel
theorem cove_8_4 : CovBE 8 4 5 8 :=
  CovBE.of_chk che_8_4_0

theorem che_8_5_0 : chkE 8 5 6 8 (decH 1 0) = true := by decide +kernel
theorem cove_8_5 : CovBE 8 5 6 8 :=
  CovBE.of_chk che_8_5_0

theorem cove_8 : CovQE 8 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_8_2) (CovAE.trans (CovAE.one cove_8_3) (CovAE.trans (CovAE.one cove_8_4) (CovAE.one cove_8_5))))

/-! ### `N = 9` -/

theorem che_9_2_0 : chkE 9 2 3 9 (decH 4 605763622004676402102403) = true := by decide +kernel
theorem cove_9_2 : CovBE 9 2 3 9 :=
  CovBE.of_chk che_9_2_0

theorem che_9_3_0 : chkE 9 3 4 9 (decH 1 0) = true := by decide +kernel
theorem cove_9_3 : CovBE 9 3 4 9 :=
  CovBE.of_chk che_9_3_0

theorem che_9_4_0 : chkE 9 4 5 9 (decH 1 0) = true := by decide +kernel
theorem cove_9_4 : CovBE 9 4 5 9 :=
  CovBE.of_chk che_9_4_0

theorem che_9_5_0 : chkE 9 5 6 9 (decH 1 0) = true := by decide +kernel
theorem cove_9_5 : CovBE 9 5 6 9 :=
  CovBE.of_chk che_9_5_0

theorem che_9_6_0 : chkE 9 6 7 9 (decH 1 0) = true := by decide +kernel
theorem cove_9_6 : CovBE 9 6 7 9 :=
  CovBE.of_chk che_9_6_0

theorem cove_9 : CovQE 9 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_9_2) (CovAE.trans (CovAE.one cove_9_3) (CovAE.trans (CovAE.one cove_9_4) (CovAE.trans (CovAE.one cove_9_5) (CovAE.one cove_9_6)))))

/-! ### `N = 10` -/

theorem che_10_2_0 : chkE 10 2 3 10 (decH 5 1077415897331880858452335776882677192306245763) = true := by decide +kernel
theorem cove_10_2 : CovBE 10 2 3 10 :=
  CovBE.of_chk che_10_2_0

theorem che_10_3_0 : chkE 10 3 4 10 (decH 1 0) = true := by decide +kernel
theorem cove_10_3 : CovBE 10 3 4 10 :=
  CovBE.of_chk che_10_3_0

theorem che_10_4_0 : chkE 10 4 5 10 (decH 1 0) = true := by decide +kernel
theorem cove_10_4 : CovBE 10 4 5 10 :=
  CovBE.of_chk che_10_4_0

theorem che_10_5_0 : chkE 10 5 6 10 (decH 1 0) = true := by decide +kernel
theorem cove_10_5 : CovBE 10 5 6 10 :=
  CovBE.of_chk che_10_5_0

theorem che_10_6_0 : chkE 10 6 7 10 (decH 1 0) = true := by decide +kernel
theorem cove_10_6 : CovBE 10 6 7 10 :=
  CovBE.of_chk che_10_6_0

theorem che_10_7_0 : chkE 10 7 8 10 (decH 1 0) = true := by decide +kernel
theorem cove_10_7 : CovBE 10 7 8 10 :=
  CovBE.of_chk che_10_7_0

theorem cove_10 : CovQE 10 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_10_2) (CovAE.trans (CovAE.one cove_10_3) (CovAE.trans (CovAE.one cove_10_4) (CovAE.trans (CovAE.one cove_10_5) (CovAE.trans (CovAE.one cove_10_6) (CovAE.one cove_10_7))))))

/-! ### `N = 11` -/

theorem che_11_2_0 : chkE 11 2 3 11 (decH 7 64391312679053483524245615385078557560819515184468264482783363) = true := by decide +kernel
theorem cove_11_2 : CovBE 11 2 3 11 :=
  CovBE.of_chk che_11_2_0

theorem che_11_3_0 : chkE 11 3 4 11 (decH 3 46190048181246527619) = true := by decide +kernel
theorem cove_11_3 : CovBE 11 3 4 11 :=
  CovBE.of_chk che_11_3_0

theorem che_11_4_0 : chkE 11 4 5 11 (decH 1 0) = true := by decide +kernel
theorem cove_11_4 : CovBE 11 4 5 11 :=
  CovBE.of_chk che_11_4_0

theorem che_11_5_0 : chkE 11 5 6 11 (decH 1 0) = true := by decide +kernel
theorem cove_11_5 : CovBE 11 5 6 11 :=
  CovBE.of_chk che_11_5_0

theorem che_11_6_0 : chkE 11 6 7 11 (decH 1 0) = true := by decide +kernel
theorem cove_11_6 : CovBE 11 6 7 11 :=
  CovBE.of_chk che_11_6_0

theorem che_11_7_0 : chkE 11 7 8 11 (decH 1 0) = true := by decide +kernel
theorem cove_11_7 : CovBE 11 7 8 11 :=
  CovBE.of_chk che_11_7_0

theorem che_11_8_0 : chkE 11 8 9 11 (decH 1 0) = true := by decide +kernel
theorem cove_11_8 : CovBE 11 8 9 11 :=
  CovBE.of_chk che_11_8_0

theorem cove_11 : CovQE 11 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_11_2) (CovAE.trans (CovAE.one cove_11_3) (CovAE.trans (CovAE.one cove_11_4) (CovAE.trans (CovAE.one cove_11_5) (CovAE.trans (CovAE.one cove_11_6) (CovAE.trans (CovAE.one cove_11_7) (CovAE.one cove_11_8)))))))

/-! ### `N = 12` -/

theorem che_12_2_0 : chkE 12 2 3 12 (decH 8 50998725769749062576229602415218014507525995737177370395891515429554478956675) = true := by decide +kernel
theorem cove_12_2 : CovBE 12 2 3 12 :=
  CovBE.of_chk che_12_2_0

theorem che_12_3_0 : chkE 12 3 4 12 (decH 6 6981320130187338570015343710380887734502019) = true := by decide +kernel
theorem cove_12_3 : CovBE 12 3 4 12 :=
  CovBE.of_chk che_12_3_0

theorem che_12_4_0 : chkE 12 4 5 12 (decH 1 0) = true := by decide +kernel
theorem cove_12_4 : CovBE 12 4 5 12 :=
  CovBE.of_chk che_12_4_0

theorem che_12_5_0 : chkE 12 5 6 12 (decH 1 0) = true := by decide +kernel
theorem cove_12_5 : CovBE 12 5 6 12 :=
  CovBE.of_chk che_12_5_0

theorem che_12_6_0 : chkE 12 6 7 12 (decH 1 0) = true := by decide +kernel
theorem cove_12_6 : CovBE 12 6 7 12 :=
  CovBE.of_chk che_12_6_0

theorem che_12_7_0 : chkE 12 7 8 12 (decH 1 0) = true := by decide +kernel
theorem cove_12_7 : CovBE 12 7 8 12 :=
  CovBE.of_chk che_12_7_0

theorem che_12_8_0 : chkE 12 8 9 12 (decH 1 0) = true := by decide +kernel
theorem cove_12_8 : CovBE 12 8 9 12 :=
  CovBE.of_chk che_12_8_0

theorem che_12_9_0 : chkE 12 9 10 12 (decH 1 0) = true := by decide +kernel
theorem cove_12_9 : CovBE 12 9 10 12 :=
  CovBE.of_chk che_12_9_0

theorem cove_12 : CovQE 12 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_12_2) (CovAE.trans (CovAE.one cove_12_3) (CovAE.trans (CovAE.one cove_12_4) (CovAE.trans (CovAE.one cove_12_5) (CovAE.trans (CovAE.one cove_12_6) (CovAE.trans (CovAE.one cove_12_7) (CovAE.trans (CovAE.one cove_12_8) (CovAE.one cove_12_9))))))))

/-! ### `N = 13` -/

theorem che_13_2_0 : chkE 13 2 3 13 (decH 10 8783580839370904837540816072060674216490854157201280932334532202435751878169469549244002171478884483) = true := by decide +kernel
theorem cove_13_2 : CovBE 13 2 3 13 :=
  CovBE.of_chk che_13_2_0

theorem che_13_3_0 : chkE 13 3 4 13 (decH 7 103447439675863470371906873311984268281246702871181214454170243) = true := by decide +kernel
theorem cove_13_3 : CovBE 13 3 4 13 :=
  CovBE.of_chk che_13_3_0

theorem che_13_4_0 : chkE 13 4 5 13 (decH 1 0) = true := by decide +kernel
theorem cove_13_4 : CovBE 13 4 5 13 :=
  CovBE.of_chk che_13_4_0

theorem che_13_5_0 : chkE 13 5 6 13 (decH 1 0) = true := by decide +kernel
theorem cove_13_5 : CovBE 13 5 6 13 :=
  CovBE.of_chk che_13_5_0

theorem che_13_6_0 : chkE 13 6 7 13 (decH 1 0) = true := by decide +kernel
theorem cove_13_6 : CovBE 13 6 7 13 :=
  CovBE.of_chk che_13_6_0

theorem che_13_7_0 : chkE 13 7 8 13 (decH 1 0) = true := by decide +kernel
theorem cove_13_7 : CovBE 13 7 8 13 :=
  CovBE.of_chk che_13_7_0

theorem che_13_8_0 : chkE 13 8 9 13 (decH 1 0) = true := by decide +kernel
theorem cove_13_8 : CovBE 13 8 9 13 :=
  CovBE.of_chk che_13_8_0

theorem che_13_9_0 : chkE 13 9 10 13 (decH 1 0) = true := by decide +kernel
theorem cove_13_9 : CovBE 13 9 10 13 :=
  CovBE.of_chk che_13_9_0

theorem che_13_10_0 : chkE 13 10 11 13 (decH 1 0) = true := by decide +kernel
theorem cove_13_10 : CovBE 13 10 11 13 :=
  CovBE.of_chk che_13_10_0

theorem cove_13 : CovQE 13 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_13_2) (CovAE.trans (CovAE.one cove_13_3) (CovAE.trans (CovAE.one cove_13_4) (CovAE.trans (CovAE.one cove_13_5) (CovAE.trans (CovAE.one cove_13_6) (CovAE.trans (CovAE.one cove_13_7) (CovAE.trans (CovAE.one cove_13_8) (CovAE.trans (CovAE.one cove_13_9) (CovAE.one cove_13_10)))))))))

/-! ### `N = 14` -/

theorem che_14_2_0 : chkE 14 2 3 14 (decH 11 115897357738281806879898077631836999433851014899367551054826969495765041606512054226698196358868662075555051168434474331887542873875457083109446510818904555651) = true := by decide +kernel
theorem cove_14_2 : CovBE 14 2 3 14 :=
  CovBE.of_chk che_14_2_0

theorem che_14_3_0 : chkE 14 3 4 14 (decH 10 5566445956067545194686466445048739693413808026274837986258736565339327251366531) = true := by decide +kernel
theorem cove_14_3 : CovBE 14 3 4 14 :=
  CovBE.of_chk che_14_3_0

theorem che_14_4_0 : chkE 14 4 5 14 (decH 3 55413420218642369155) = true := by decide +kernel
theorem cove_14_4 : CovBE 14 4 5 14 :=
  CovBE.of_chk che_14_4_0

theorem che_14_5_0 : chkE 14 5 6 14 (decH 1 0) = true := by decide +kernel
theorem cove_14_5 : CovBE 14 5 6 14 :=
  CovBE.of_chk che_14_5_0

theorem che_14_6_0 : chkE 14 6 7 14 (decH 1 0) = true := by decide +kernel
theorem cove_14_6 : CovBE 14 6 7 14 :=
  CovBE.of_chk che_14_6_0

theorem che_14_7_0 : chkE 14 7 8 14 (decH 1 0) = true := by decide +kernel
theorem cove_14_7 : CovBE 14 7 8 14 :=
  CovBE.of_chk che_14_7_0

theorem che_14_8_0 : chkE 14 8 9 14 (decH 1 0) = true := by decide +kernel
theorem cove_14_8 : CovBE 14 8 9 14 :=
  CovBE.of_chk che_14_8_0

theorem che_14_9_0 : chkE 14 9 10 14 (decH 1 0) = true := by decide +kernel
theorem cove_14_9 : CovBE 14 9 10 14 :=
  CovBE.of_chk che_14_9_0

theorem che_14_10_0 : chkE 14 10 11 14 (decH 1 0) = true := by decide +kernel
theorem cove_14_10 : CovBE 14 10 11 14 :=
  CovBE.of_chk che_14_10_0

theorem che_14_11_0 : chkE 14 11 12 14 (decH 1 0) = true := by decide +kernel
theorem cove_14_11 : CovBE 14 11 12 14 :=
  CovBE.of_chk che_14_11_0

theorem cove_14 : CovQE 14 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_14_2) (CovAE.trans (CovAE.one cove_14_3) (CovAE.trans (CovAE.one cove_14_4) (CovAE.trans (CovAE.one cove_14_5) (CovAE.trans (CovAE.one cove_14_6) (CovAE.trans (CovAE.one cove_14_7) (CovAE.trans (CovAE.one cove_14_8) (CovAE.trans (CovAE.one cove_14_9) (CovAE.trans (CovAE.one cove_14_10) (CovAE.one cove_14_11))))))))))

/-! ### `N = 15` -/

theorem che_15_2_0 : chkE 15 2 3 15 (decH 14 2080396503318977012522346478039634630959441287202195185172703131124192692811978585516799059410909259917125668119796949535419679408508242196650884887701822693865177219) = true := by decide +kernel
theorem cove_15_2 : CovBE 15 2 3 15 :=
  CovBE.of_chk che_15_2_0

theorem che_15_3_0 : chkE 15 3 4 15 (decH 11 91334480487508397111181560418004213372613385843181653296991181253811044313485127978112881469864749798999740317930930819) = true := by decide +kernel
theorem cove_15_3 : CovBE 15 3 4 15 :=
  CovBE.of_chk che_15_3_0

theorem che_15_4_0 : chkE 15 4 5 15 (decH 6 8375456992655354158002544335220122203472771) = true := by decide +kernel
theorem cove_15_4 : CovBE 15 4 5 15 :=
  CovBE.of_chk che_15_4_0

theorem che_15_5_0 : chkE 15 5 6 15 (decH 1 0) = true := by decide +kernel
theorem cove_15_5 : CovBE 15 5 6 15 :=
  CovBE.of_chk che_15_5_0

theorem che_15_6_0 : chkE 15 6 7 15 (decH 1 0) = true := by decide +kernel
theorem cove_15_6 : CovBE 15 6 7 15 :=
  CovBE.of_chk che_15_6_0

theorem che_15_7_0 : chkE 15 7 8 15 (decH 1 0) = true := by decide +kernel
theorem cove_15_7 : CovBE 15 7 8 15 :=
  CovBE.of_chk che_15_7_0

theorem che_15_8_0 : chkE 15 8 9 15 (decH 1 0) = true := by decide +kernel
theorem cove_15_8 : CovBE 15 8 9 15 :=
  CovBE.of_chk che_15_8_0

theorem che_15_9_0 : chkE 15 9 10 15 (decH 1 0) = true := by decide +kernel
theorem cove_15_9 : CovBE 15 9 10 15 :=
  CovBE.of_chk che_15_9_0

theorem che_15_10_0 : chkE 15 10 11 15 (decH 1 0) = true := by decide +kernel
theorem cove_15_10 : CovBE 15 10 11 15 :=
  CovBE.of_chk che_15_10_0

theorem che_15_11_0 : chkE 15 11 12 15 (decH 1 0) = true := by decide +kernel
theorem cove_15_11 : CovBE 15 11 12 15 :=
  CovBE.of_chk che_15_11_0

theorem che_15_12_0 : chkE 15 12 13 15 (decH 1 0) = true := by decide +kernel
theorem cove_15_12 : CovBE 15 12 13 15 :=
  CovBE.of_chk che_15_12_0

theorem cove_15 : CovQE 15 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_15_2) (CovAE.trans (CovAE.one cove_15_3) (CovAE.trans (CovAE.one cove_15_4) (CovAE.trans (CovAE.one cove_15_5) (CovAE.trans (CovAE.one cove_15_6) (CovAE.trans (CovAE.one cove_15_7) (CovAE.trans (CovAE.one cove_15_8) (CovAE.trans (CovAE.one cove_15_9) (CovAE.trans (CovAE.one cove_15_10) (CovAE.trans (CovAE.one cove_15_11) (CovAE.one cove_15_12)))))))))))

/-! ### `N = 16` -/

theorem che_16_2_0 : chkE 16 2 3 14 (decH 14 25181335669372230804564931725547929565827042230407822411697536033176639254781618263281441576581531688356081330659341506057764989349082053211603216568417519662943846553759622840972659492491255601828613636227) = true := by decide +kernel
theorem che_16_2_1 : chkE 16 2 14 16 (decH 2 336895293128734157515266410113) = true := by decide +kernel
theorem cove_16_2 : CovBE 16 2 3 16 :=
  CovBE.trans (CovBE.of_chk che_16_2_0) (CovBE.of_chk che_16_2_1)

theorem che_16_3_0 : chkE 16 3 4 16 (decH 15 83470903283062322767662682712885906192803454039079314081596904675848849672973712638607287121662191809187791731319114827651053179416621367939) = true := by decide +kernel
theorem cove_16_3 : CovBE 16 3 4 16 :=
  CovBE.of_chk che_16_3_0

theorem che_16_4_0 : chkE 16 4 5 16 (decH 7 116403377657704502828561418028861869804393849511119014741459843) = true := by decide +kernel
theorem cove_16_4 : CovBE 16 4 5 16 :=
  CovBE.of_chk che_16_4_0

theorem che_16_5_0 : chkE 16 5 6 16 (decH 1 0) = true := by decide +kernel
theorem cove_16_5 : CovBE 16 5 6 16 :=
  CovBE.of_chk che_16_5_0

theorem che_16_6_0 : chkE 16 6 7 16 (decH 1 0) = true := by decide +kernel
theorem cove_16_6 : CovBE 16 6 7 16 :=
  CovBE.of_chk che_16_6_0

theorem che_16_7_0 : chkE 16 7 8 16 (decH 1 0) = true := by decide +kernel
theorem cove_16_7 : CovBE 16 7 8 16 :=
  CovBE.of_chk che_16_7_0

theorem che_16_8_0 : chkE 16 8 9 16 (decH 1 0) = true := by decide +kernel
theorem cove_16_8 : CovBE 16 8 9 16 :=
  CovBE.of_chk che_16_8_0

theorem che_16_9_0 : chkE 16 9 10 16 (decH 1 0) = true := by decide +kernel
theorem cove_16_9 : CovBE 16 9 10 16 :=
  CovBE.of_chk che_16_9_0

theorem che_16_10_0 : chkE 16 10 11 16 (decH 1 0) = true := by decide +kernel
theorem cove_16_10 : CovBE 16 10 11 16 :=
  CovBE.of_chk che_16_10_0

theorem che_16_11_0 : chkE 16 11 12 16 (decH 1 0) = true := by decide +kernel
theorem cove_16_11 : CovBE 16 11 12 16 :=
  CovBE.of_chk che_16_11_0

theorem che_16_12_0 : chkE 16 12 13 16 (decH 1 0) = true := by decide +kernel
theorem cove_16_12 : CovBE 16 12 13 16 :=
  CovBE.of_chk che_16_12_0

theorem che_16_13_0 : chkE 16 13 14 16 (decH 1 0) = true := by decide +kernel
theorem cove_16_13 : CovBE 16 13 14 16 :=
  CovBE.of_chk che_16_13_0

theorem cove_16 : CovQE 16 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_16_2) (CovAE.trans (CovAE.one cove_16_3) (CovAE.trans (CovAE.one cove_16_4) (CovAE.trans (CovAE.one cove_16_5) (CovAE.trans (CovAE.one cove_16_6) (CovAE.trans (CovAE.one cove_16_7) (CovAE.trans (CovAE.one cove_16_8) (CovAE.trans (CovAE.one cove_16_9) (CovAE.trans (CovAE.one cove_16_10) (CovAE.trans (CovAE.one cove_16_11) (CovAE.trans (CovAE.one cove_16_12) (CovAE.one cove_16_13))))))))))))

/-! ### `N = 17` -/

theorem che_17_2_0 : chkE 17 2 3 17 (decH 18 1995254390351213706603668900090800807091812109818343206540472133653624762582315389436610417213094350075666961130056499446794586661377947287831292731114730937089147642276949871212525879332204122521067063784307881011081920643) = true := by decide +kernel
theorem cove_17_2 : CovBE 17 2 3 17 :=
  CovBE.of_chk che_17_2_0

theorem che_17_3_0 : chkE 17 3 4 17 (decH 16 3743915134624828823007282081815491973440186560004797609499582081617732675249874644517095802690712591440815921034766373511772912460694414829638056483390665540604123407765606205450415597405580005072107537653879146690484722431198274860271743642157699) = true := by decide +kernel
theorem cove_17_3 : CovBE 17 3 4 17 :=
  CovBE.of_chk che_17_3_0

theorem che_17_4_0 : chkE 17 4 5 17 (decH 12 33713629350304867780892021689747475363962993666301349394849375987535299792066376590417386300047000458674195940227) = true := by decide +kernel
theorem cove_17_4 : CovBE 17 4 5 17 :=
  CovBE.of_chk che_17_4_0

theorem che_17_5_0 : chkE 17 5 6 17 (decH 3 64708885034450324611) = true := by decide +kernel
theorem cove_17_5 : CovBE 17 5 6 17 :=
  CovBE.of_chk che_17_5_0

theorem che_17_6_0 : chkE 17 6 7 17 (decH 1 0) = true := by decide +kernel
theorem cove_17_6 : CovBE 17 6 7 17 :=
  CovBE.of_chk che_17_6_0

theorem che_17_7_0 : chkE 17 7 8 17 (decH 1 0) = true := by decide +kernel
theorem cove_17_7 : CovBE 17 7 8 17 :=
  CovBE.of_chk che_17_7_0

theorem che_17_8_0 : chkE 17 8 9 17 (decH 1 0) = true := by decide +kernel
theorem cove_17_8 : CovBE 17 8 9 17 :=
  CovBE.of_chk che_17_8_0

theorem che_17_9_0 : chkE 17 9 10 17 (decH 1 0) = true := by decide +kernel
theorem cove_17_9 : CovBE 17 9 10 17 :=
  CovBE.of_chk che_17_9_0

theorem che_17_10_0 : chkE 17 10 11 17 (decH 1 0) = true := by decide +kernel
theorem cove_17_10 : CovBE 17 10 11 17 :=
  CovBE.of_chk che_17_10_0

theorem che_17_11_0 : chkE 17 11 12 17 (decH 1 0) = true := by decide +kernel
theorem cove_17_11 : CovBE 17 11 12 17 :=
  CovBE.of_chk che_17_11_0

theorem che_17_12_0 : chkE 17 12 13 17 (decH 1 0) = true := by decide +kernel
theorem cove_17_12 : CovBE 17 12 13 17 :=
  CovBE.of_chk che_17_12_0

theorem che_17_13_0 : chkE 17 13 14 17 (decH 1 0) = true := by decide +kernel
theorem cove_17_13 : CovBE 17 13 14 17 :=
  CovBE.of_chk che_17_13_0

theorem che_17_14_0 : chkE 17 14 15 17 (decH 1 0) = true := by decide +kernel
theorem cove_17_14 : CovBE 17 14 15 17 :=
  CovBE.of_chk che_17_14_0

theorem cove_17 : CovQE 17 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_17_2) (CovAE.trans (CovAE.one cove_17_3) (CovAE.trans (CovAE.one cove_17_4) (CovAE.trans (CovAE.one cove_17_5) (CovAE.trans (CovAE.one cove_17_6) (CovAE.trans (CovAE.one cove_17_7) (CovAE.trans (CovAE.one cove_17_8) (CovAE.trans (CovAE.one cove_17_9) (CovAE.trans (CovAE.one cove_17_10) (CovAE.trans (CovAE.one cove_17_11) (CovAE.trans (CovAE.one cove_17_12) (CovAE.trans (CovAE.one cove_17_13) (CovAE.one cove_17_14)))))))))))))

/-! ### `N = 18` -/

theorem che_18_2_0 : chkE 18 2 3 16 (decH 18 355965278123827169043094431093217040198103215199591183826314966278452459194855419611150574347057055410660133566718021601335703565454792151184146778882372208897659100580164412726754417709528944935357210745924791405545939276616610294635932105972375122500702787248111747) = true := by decide +kernel
theorem che_18_2_1 : chkE 18 2 16 18 (decH 2 5560569262718383838090104347543425) = true := by decide +kernel
theorem cove_18_2 : CovBE 18 2 3 18 :=
  CovBE.trans (CovBE.of_chk che_18_2_0) (CovBE.of_chk che_18_2_1)

theorem che_18_3_0 : chkE 18 3 4 18 (decH 20 121780663473602395696359587978479854887153693088895098397913569599617346870310465261997299149990151740432031344982820176623484518895997651614914088231421565236896608690846574565284951955984023713402259186929329030316675) = true := by decide +kernel
theorem cove_18_3 : CovBE 18 3 4 18 :=
  CovBE.of_chk che_18_3_0

theorem che_18_4_0 : chkE 18 4 5 18 (decH 14 141470628445015314378514750188570163433728799974150584805717569057003012502449312313977807118600981504762261953595163975013739057462055289273855851803958847783811) = true := by decide +kernel
theorem cove_18_4 : CovBE 18 4 5 18 :=
  CovBE.of_chk che_18_4_0

theorem che_18_5_0 : chkE 18 5 6 18 (decH 6 9769593855123369746140916027743406447936643) = true := by decide +kernel
theorem cove_18_5 : CovBE 18 5 6 18 :=
  CovBE.of_chk che_18_5_0

theorem che_18_6_0 : chkE 18 6 7 18 (decH 1 0) = true := by decide +kernel
theorem cove_18_6 : CovBE 18 6 7 18 :=
  CovBE.of_chk che_18_6_0

theorem che_18_7_0 : chkE 18 7 8 18 (decH 1 0) = true := by decide +kernel
theorem cove_18_7 : CovBE 18 7 8 18 :=
  CovBE.of_chk che_18_7_0

theorem che_18_8_0 : chkE 18 8 9 18 (decH 1 0) = true := by decide +kernel
theorem cove_18_8 : CovBE 18 8 9 18 :=
  CovBE.of_chk che_18_8_0

theorem che_18_9_0 : chkE 18 9 10 18 (decH 1 0) = true := by decide +kernel
theorem cove_18_9 : CovBE 18 9 10 18 :=
  CovBE.of_chk che_18_9_0

theorem che_18_10_0 : chkE 18 10 11 18 (decH 1 0) = true := by decide +kernel
theorem cove_18_10 : CovBE 18 10 11 18 :=
  CovBE.of_chk che_18_10_0

theorem che_18_11_0 : chkE 18 11 12 18 (decH 1 0) = true := by decide +kernel
theorem cove_18_11 : CovBE 18 11 12 18 :=
  CovBE.of_chk che_18_11_0

theorem che_18_12_0 : chkE 18 12 13 18 (decH 1 0) = true := by decide +kernel
theorem cove_18_12 : CovBE 18 12 13 18 :=
  CovBE.of_chk che_18_12_0

theorem che_18_13_0 : chkE 18 13 14 18 (decH 1 0) = true := by decide +kernel
theorem cove_18_13 : CovBE 18 13 14 18 :=
  CovBE.of_chk che_18_13_0

theorem che_18_14_0 : chkE 18 14 15 18 (decH 1 0) = true := by decide +kernel
theorem cove_18_14 : CovBE 18 14 15 18 :=
  CovBE.of_chk che_18_14_0

theorem che_18_15_0 : chkE 18 15 16 18 (decH 1 0) = true := by decide +kernel
theorem cove_18_15 : CovBE 18 15 16 18 :=
  CovBE.of_chk che_18_15_0

theorem cove_18 : CovQE 18 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_18_2) (CovAE.trans (CovAE.one cove_18_3) (CovAE.trans (CovAE.one cove_18_4) (CovAE.trans (CovAE.one cove_18_5) (CovAE.trans (CovAE.one cove_18_6) (CovAE.trans (CovAE.one cove_18_7) (CovAE.trans (CovAE.one cove_18_8) (CovAE.trans (CovAE.one cove_18_9) (CovAE.trans (CovAE.one cove_18_10) (CovAE.trans (CovAE.one cove_18_11) (CovAE.trans (CovAE.one cove_18_12) (CovAE.trans (CovAE.one cove_18_13) (CovAE.trans (CovAE.one cove_18_14) (CovAE.one cove_18_15))))))))))))))

/-! ### `N = 19` -/

theorem che_19_2_0 : chkE 19 2 3 15 (decH 19 969415614370699559754063582317776167178704836547268527444483786191254281828805349546029310180077611917609291730492582383743162938287939054926668342129961095224559711872169580446045297406631289693763302785773408264079137346204567488350607326556073805482049667) = true := by decide +kernel
theorem che_19_2_1 : chkE 19 2 15 19 (decH 5 3714806834649775902157033455331269083280535852743463060921943189468230724021741657026194538150745523026246473263932069280787181010177907773566215211009) = true := by decide +kernel
theorem cove_19_2 : CovBE 19 2 3 19 :=
  CovBE.trans (CovBE.of_chk che_19_2_0) (CovBE.of_chk che_19_2_1)

theorem che_19_3_0 : chkE 19 3 4 16 (decH 20 24859334533960132200351564403672538484362090075931058460690388836199813224387305701881952508557979930474242822873828954252545981669436691943581926527889213649844908914011454833088787249818164916380696368175347517303665577117391474486114429897659299338049275688359486695497634906328155412823499340685296259) = true := by decide +kernel
theorem che_19_3_1 : chkE 19 3 16 19 (decH 2 716985749685031243232850896623011841) = true := by decide +kernel
theorem cove_19_3 : CovBE 19 3 4 19 :=
  CovBE.trans (CovBE.of_chk che_19_3_0) (CovBE.of_chk che_19_3_1)

theorem che_19_4_0 : chkE 19 4 5 19 (decH 18 9579594059272275262728430466279204060812202789245574161957878709117214227560673997662549054335092038558431814710645737277055923279258861015807522846174096719423420631008119984347855456240789524333443) = true := by decide +kernel
theorem cove_19_4 : CovBE 19 4 5 19 :=
  CovBE.of_chk che_19_4_0

theorem che_19_5_0 : chkE 19 5 6 19 (decH 7 10247657765277304354234732414611964390434796865978118484061205750747036167226499) = true := by decide +kernel
theorem cove_19_5 : CovBE 19 5 6 19 :=
  CovBE.of_chk che_19_5_0

theorem che_19_6_0 : chkE 19 6 7 19 (decH 1 0) = true := by decide +kernel
theorem cove_19_6 : CovBE 19 6 7 19 :=
  CovBE.of_chk che_19_6_0

theorem che_19_7_0 : chkE 19 7 8 19 (decH 1 0) = true := by decide +kernel
theorem cove_19_7 : CovBE 19 7 8 19 :=
  CovBE.of_chk che_19_7_0

theorem che_19_8_0 : chkE 19 8 9 19 (decH 1 0) = true := by decide +kernel
theorem cove_19_8 : CovBE 19 8 9 19 :=
  CovBE.of_chk che_19_8_0

theorem che_19_9_0 : chkE 19 9 10 19 (decH 1 0) = true := by decide +kernel
theorem cove_19_9 : CovBE 19 9 10 19 :=
  CovBE.of_chk che_19_9_0

theorem che_19_10_0 : chkE 19 10 11 19 (decH 1 0) = true := by decide +kernel
theorem cove_19_10 : CovBE 19 10 11 19 :=
  CovBE.of_chk che_19_10_0

theorem che_19_11_0 : chkE 19 11 12 19 (decH 1 0) = true := by decide +kernel
theorem cove_19_11 : CovBE 19 11 12 19 :=
  CovBE.of_chk che_19_11_0

theorem che_19_12_0 : chkE 19 12 13 19 (decH 1 0) = true := by decide +kernel
theorem cove_19_12 : CovBE 19 12 13 19 :=
  CovBE.of_chk che_19_12_0

theorem che_19_13_0 : chkE 19 13 14 19 (decH 1 0) = true := by decide +kernel
theorem cove_19_13 : CovBE 19 13 14 19 :=
  CovBE.of_chk che_19_13_0

theorem che_19_14_0 : chkE 19 14 15 19 (decH 1 0) = true := by decide +kernel
theorem cove_19_14 : CovBE 19 14 15 19 :=
  CovBE.of_chk che_19_14_0

theorem che_19_15_0 : chkE 19 15 16 19 (decH 1 0) = true := by decide +kernel
theorem cove_19_15 : CovBE 19 15 16 19 :=
  CovBE.of_chk che_19_15_0

theorem che_19_16_0 : chkE 19 16 17 19 (decH 1 0) = true := by decide +kernel
theorem cove_19_16 : CovBE 19 16 17 19 :=
  CovBE.of_chk che_19_16_0

theorem cove_19 : CovQE 19 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_19_2) (CovAE.trans (CovAE.one cove_19_3) (CovAE.trans (CovAE.one cove_19_4) (CovAE.trans (CovAE.one cove_19_5) (CovAE.trans (CovAE.one cove_19_6) (CovAE.trans (CovAE.one cove_19_7) (CovAE.trans (CovAE.one cove_19_8) (CovAE.trans (CovAE.one cove_19_9) (CovAE.trans (CovAE.one cove_19_10) (CovAE.trans (CovAE.one cove_19_11) (CovAE.trans (CovAE.one cove_19_12) (CovAE.trans (CovAE.one cove_19_13) (CovAE.trans (CovAE.one cove_19_14) (CovAE.trans (CovAE.one cove_19_15) (CovAE.one cove_19_16)))))))))))))))

/-! ### `N = 20` -/

theorem che_20_2_0 : chkE 20 2 3 13 (decH 12 43519410853243846786813244012972803717411559091059507683376140766350803077612207164121693828261322769813348843000942864042396998293626286959869934464967804393684646188963527935864501273348140031850964954534993779061569173504066109571) = true := by decide +kernel
theorem che_20_2_1 : chkE 20 2 13 20 (decH 13 7909301910431387297190694740299927269972731633883491071822547173303920988409250376563417849996470267899630790991383788143360810988339565918740823898200878013928353913046273468460524823384289604800673924623006421268149660233214474998279195550035556204675) = true := by decide +kernel
theorem cove_20_2 : CovBE 20 2 3 20 :=
  CovBE.trans (CovBE.of_chk che_20_2_0) (CovBE.of_chk che_20_2_1)

theorem che_20_3_0 : chkE 20 3 4 20 (decH 26 586381697850519014523246064574025427542122856425885052569935915842727514298914281285203079096169266569891592170015072277418981202420568828679094323233001120878352600357518817793042760259295699249152601506722084822046182811432908069302741361755326113947311162569343497994790372350023380249200328269060095623811) = true := by decide +kernel
theorem cove_20_3 : CovBE 20 3 4 20 :=
  CovBE.of_chk che_20_3_0

theorem che_20_4_0 : chkE 20 4 5 20 (decH 20 1807178325423158577803457890346546096767906193537124011422024589927994579342552733695442297558559405659067081049859918505661093245960626871187127817180806489475902896862588568197392331196876583086465098058578368065731701054391463836686374803522119571897633788596105436323912530121475631801614124219526208944599326917189752159029216131) = true := by decide +kernel
theorem cove_20_4 : CovBE 20 4 5 20 :=
  CovBE.of_chk che_20_4_0

theorem che_20_5_0 : chkE 20 5 6 20 (decH 12 38524618848362469853869263027663257617273434385026803026283947374135720022695613597891314871756020504144778380419) = true := by decide +kernel
theorem cove_20_5 : CovBE 20 5 6 20 :=
  CovBE.of_chk che_20_5_0

theorem che_20_6_0 : chkE 20 6 7 20 (decH 3 74004323461977116291) = true := by decide +kernel
theorem cove_20_6 : CovBE 20 6 7 20 :=
  CovBE.of_chk che_20_6_0

theorem che_20_7_0 : chkE 20 7 8 20 (decH 1 0) = true := by decide +kernel
theorem cove_20_7 : CovBE 20 7 8 20 :=
  CovBE.of_chk che_20_7_0

theorem che_20_8_0 : chkE 20 8 9 20 (decH 1 0) = true := by decide +kernel
theorem cove_20_8 : CovBE 20 8 9 20 :=
  CovBE.of_chk che_20_8_0

theorem che_20_9_0 : chkE 20 9 10 20 (decH 1 0) = true := by decide +kernel
theorem cove_20_9 : CovBE 20 9 10 20 :=
  CovBE.of_chk che_20_9_0

theorem che_20_10_0 : chkE 20 10 11 20 (decH 1 0) = true := by decide +kernel
theorem cove_20_10 : CovBE 20 10 11 20 :=
  CovBE.of_chk che_20_10_0

theorem che_20_11_0 : chkE 20 11 12 20 (decH 1 0) = true := by decide +kernel
theorem cove_20_11 : CovBE 20 11 12 20 :=
  CovBE.of_chk che_20_11_0

theorem che_20_12_0 : chkE 20 12 13 20 (decH 1 0) = true := by decide +kernel
theorem cove_20_12 : CovBE 20 12 13 20 :=
  CovBE.of_chk che_20_12_0

theorem che_20_13_0 : chkE 20 13 14 20 (decH 1 0) = true := by decide +kernel
theorem cove_20_13 : CovBE 20 13 14 20 :=
  CovBE.of_chk che_20_13_0

theorem che_20_14_0 : chkE 20 14 15 20 (decH 1 0) = true := by decide +kernel
theorem cove_20_14 : CovBE 20 14 15 20 :=
  CovBE.of_chk che_20_14_0

theorem che_20_15_0 : chkE 20 15 16 20 (decH 1 0) = true := by decide +kernel
theorem cove_20_15 : CovBE 20 15 16 20 :=
  CovBE.of_chk che_20_15_0

theorem che_20_16_0 : chkE 20 16 17 20 (decH 1 0) = true := by decide +kernel
theorem cove_20_16 : CovBE 20 16 17 20 :=
  CovBE.of_chk che_20_16_0

theorem che_20_17_0 : chkE 20 17 18 20 (decH 1 0) = true := by decide +kernel
theorem cove_20_17 : CovBE 20 17 18 20 :=
  CovBE.of_chk che_20_17_0

theorem cove_20 : CovQE 20 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_20_2) (CovAE.trans (CovAE.one cove_20_3) (CovAE.trans (CovAE.one cove_20_4) (CovAE.trans (CovAE.one cove_20_5) (CovAE.trans (CovAE.one cove_20_6) (CovAE.trans (CovAE.one cove_20_7) (CovAE.trans (CovAE.one cove_20_8) (CovAE.trans (CovAE.one cove_20_9) (CovAE.trans (CovAE.one cove_20_10) (CovAE.trans (CovAE.one cove_20_11) (CovAE.trans (CovAE.one cove_20_12) (CovAE.trans (CovAE.one cove_20_13) (CovAE.trans (CovAE.one cove_20_14) (CovAE.trans (CovAE.one cove_20_15) (CovAE.trans (CovAE.one cove_20_16) (CovAE.one cove_20_17))))))))))))))))

/-! ### `N = 21` -/

theorem che_21_2_0 : chkE 21 2 3 16 (decH 22 8949936447272694962009606540679628908302379953722921771212368476119590843412798237232261366807280731253782106122476601090335496542212099684963271843486829502638838354912092239865691281863299751153443820543679306083406598739786208557769442053156943250580432327192732846140702851) = true := by decide +kernel
theorem che_21_2_1 : chkE 21 2 16 19 (decH 6 139969904387287766428837947094329837428224951098876894681549523176864797166482502135048222485574898946093433731591473366714258634900085304803356070719587736785492285860750316259585) = true := by decide +kernel
theorem che_21_2_2 : chkE 21 2 19 21 (decH 2 109834192941789477547488039293442582677761) = true := by decide +kernel
theorem cove_21_2 : CovBE 21 2 3 21 :=
  CovBE.trans (CovBE.of_chk che_21_2_0) (CovBE.trans (CovBE.of_chk che_21_2_1) (CovBE.of_chk che_21_2_2))

theorem che_21_3_0 : chkE 21 3 4 15 (decH 19 477156881024591668869086929647252739509425909262410425776950809719460457961387171647444394427015530614220270425654360741688805888479074840834231106143798539158378188406005617548468837804062990456553075370991717369839959315021653955682991433242113033780939347823540964584468396798737213450448806601250366523967586947) = true := by decide +kernel
theorem che_21_3_1 : chkE 21 3 15 21 (decH 9 6170600902029201949917229386260446790884869382255431088870208321289739403297403658786995549408156430361333771308373089992345747752579) = true := by decide +kernel
theorem cove_21_3 : CovBE 21 3 4 21 :=
  CovBE.trans (CovBE.of_chk che_21_3_0) (CovBE.of_chk che_21_3_1)

theorem che_21_4_0 : chkE 21 4 5 21 (decH 25 51830099708241607183666042926248422985090750311355340508903387455050517756086305072266554620334469777747520434387927611370613466737994532522752703206209044746156394891173899248120200219126899662462045630540813846719701601947625131864015265379916403660780669316693638969008618730276172764356901124140330741941123) = true := by decide +kernel
theorem cove_21_4 : CovBE 21 4 5 21 :=
  CovBE.of_chk che_21_4_0

theorem che_21_5_0 : chkE 21 5 6 21 (decH 14 2355042222671915618327780437757896029998163186960118997892920575150077833219094555537424249792825974140977600158977811065375266445249744061121667) = true := by decide +kernel
theorem cove_21_5 : CovBE 21 5 6 21 :=
  CovBE.of_chk che_21_5_0

theorem che_21_6_0 : chkE 21 6 7 21 (decH 6 804431576014300756325575969136914282707052599163575022404995) = true := by decide +kernel
theorem cove_21_6 : CovBE 21 6 7 21 :=
  CovBE.of_chk che_21_6_0

theorem che_21_7_0 : chkE 21 7 8 21 (decH 1 0) = true := by decide +kernel
theorem cove_21_7 : CovBE 21 7 8 21 :=
  CovBE.of_chk che_21_7_0

theorem che_21_8_0 : chkE 21 8 9 21 (decH 1 0) = true := by decide +kernel
theorem cove_21_8 : CovBE 21 8 9 21 :=
  CovBE.of_chk che_21_8_0

theorem che_21_9_0 : chkE 21 9 10 21 (decH 1 0) = true := by decide +kernel
theorem cove_21_9 : CovBE 21 9 10 21 :=
  CovBE.of_chk che_21_9_0

theorem che_21_10_0 : chkE 21 10 11 21 (decH 1 0) = true := by decide +kernel
theorem cove_21_10 : CovBE 21 10 11 21 :=
  CovBE.of_chk che_21_10_0

theorem che_21_11_0 : chkE 21 11 12 21 (decH 1 0) = true := by decide +kernel
theorem cove_21_11 : CovBE 21 11 12 21 :=
  CovBE.of_chk che_21_11_0

theorem che_21_12_0 : chkE 21 12 13 21 (decH 1 0) = true := by decide +kernel
theorem cove_21_12 : CovBE 21 12 13 21 :=
  CovBE.of_chk che_21_12_0

theorem che_21_13_0 : chkE 21 13 14 21 (decH 1 0) = true := by decide +kernel
theorem cove_21_13 : CovBE 21 13 14 21 :=
  CovBE.of_chk che_21_13_0

theorem che_21_14_0 : chkE 21 14 15 21 (decH 1 0) = true := by decide +kernel
theorem cove_21_14 : CovBE 21 14 15 21 :=
  CovBE.of_chk che_21_14_0

theorem che_21_15_0 : chkE 21 15 16 21 (decH 1 0) = true := by decide +kernel
theorem cove_21_15 : CovBE 21 15 16 21 :=
  CovBE.of_chk che_21_15_0

theorem che_21_16_0 : chkE 21 16 17 21 (decH 1 0) = true := by decide +kernel
theorem cove_21_16 : CovBE 21 16 17 21 :=
  CovBE.of_chk che_21_16_0

theorem che_21_17_0 : chkE 21 17 18 21 (decH 1 0) = true := by decide +kernel
theorem cove_21_17 : CovBE 21 17 18 21 :=
  CovBE.of_chk che_21_17_0

theorem che_21_18_0 : chkE 21 18 19 21 (decH 1 0) = true := by decide +kernel
theorem cove_21_18 : CovBE 21 18 19 21 :=
  CovBE.of_chk che_21_18_0

theorem cove_21 : CovQE 21 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_21_2) (CovAE.trans (CovAE.one cove_21_3) (CovAE.trans (CovAE.one cove_21_4) (CovAE.trans (CovAE.one cove_21_5) (CovAE.trans (CovAE.one cove_21_6) (CovAE.trans (CovAE.one cove_21_7) (CovAE.trans (CovAE.one cove_21_8) (CovAE.trans (CovAE.one cove_21_9) (CovAE.trans (CovAE.one cove_21_10) (CovAE.trans (CovAE.one cove_21_11) (CovAE.trans (CovAE.one cove_21_12) (CovAE.trans (CovAE.one cove_21_13) (CovAE.trans (CovAE.one cove_21_14) (CovAE.trans (CovAE.one cove_21_15) (CovAE.trans (CovAE.one cove_21_16) (CovAE.trans (CovAE.one cove_21_17) (CovAE.one cove_21_18)))))))))))))))))

/-! ### `N = 22` -/

theorem che_22_2_0 : chkE 22 2 3 4 (decH 9 2653988598404045836667955579447384547295285617299067272646935702866683646497699807033665553043956384661011396953506324450436972338539133615814754263974418718040099981362256311688382028840011940935781456367045827137459668277079816264521928509857052030425677955) = true := by decide +kernel
theorem che_22_2_1 : chkE 22 2 4 18 (decH 17 15147622862314624888030115950681541347944010970983629138552898197916795361573517530493630223425819580495934651316104368357443122878790542071373817235512733553144587989875908807131287844376590750799945703846595733397895970376547722661812256899) = true := by decide +kernel
theorem che_22_2_2 : chkE 22 2 18 22 (decH 5 8600566176085799214076337094330996432961513899694072776998578184595310658366011890071347235652421989068036676702618920125275170844649363951161395231274438087605837476565158273) = true := by decide +kernel
theorem cove_22_2 : CovBE 22 2 3 22 :=
  CovBE.trans (CovBE.of_chk che_22_2_0) (CovBE.trans (CovBE.of_chk che_22_2_1) (CovBE.of_chk che_22_2_2))

theorem che_22_3_0 : chkE 22 3 4 22 (decH 32 690818952501262279631874920955395685395833180023658740452773295685930064995378328845918310483617041078320855529756210877812812134648598045730019476735150890896063123674120409289470699909161541529662649294498649516916114112059053057382218112663564584044945716488143009553223250684088689238366834435882594845960460461897000491344318544782322421638738936852321933655152771791672754967963983838289625875130368643) = true := by decide +kernel
theorem cove_22_3 : CovBE 22 3 4 22 :=
  CovBE.of_chk che_22_3_0

theorem che_22_4_0 : chkE 22 4 5 18 (decH 26 1102827575653128315713859780967556176298107719488261729499816325729299005205176216797765738744620807954811658825688037570736902532093273297814163939895133717817207432007231887473681302626750919764360928769330963297916034970012823127260520681457436845359530266659835750372543096519379510741798053586952962699578382970969863546965102936054380103226369475589123193246949851852217853526229460586413665370897021434300541562971369150154326915) = true := by decide +kernel
theorem che_22_4_1 : chkE 22 4 18 22 (decH 2 2908486524870888280546146823839995343915393) = true := by decide +kernel
theorem cove_22_4 : CovBE 22 4 5 22 :=
  CovBE.trans (CovBE.of_chk che_22_4_0) (CovBE.of_chk che_22_4_1)

theorem che_22_5_0 : chkE 22 5 6 22 (decH 20 776485606925762521760652984226481296677598464055206656803418022525332362356500165528325499729232970566027456488910667450305696850943176742182946877637442186475107569707715177327245641382321930882544527655373276988547) = true := by decide +kernel
theorem cove_22_5 : CovBE 22 5 6 22 :=
  CovBE.of_chk che_22_5_0

theorem che_22_6_0 : chkE 22 6 7 22 (decH 7 12107681311372573293775753581640278476525644374522945504472244888993147830453635) = true := by decide +kernel
theorem cove_22_6 : CovBE 22 6 7 22 :=
  CovBE.of_chk che_22_6_0

theorem che_22_7_0 : chkE 22 7 8 22 (decH 1 0) = true := by decide +kernel
theorem cove_22_7 : CovBE 22 7 8 22 :=
  CovBE.of_chk che_22_7_0

theorem che_22_8_0 : chkE 22 8 9 22 (decH 1 0) = true := by decide +kernel
theorem cove_22_8 : CovBE 22 8 9 22 :=
  CovBE.of_chk che_22_8_0

theorem che_22_9_0 : chkE 22 9 10 22 (decH 1 0) = true := by decide +kernel
theorem cove_22_9 : CovBE 22 9 10 22 :=
  CovBE.of_chk che_22_9_0

theorem che_22_10_0 : chkE 22 10 11 22 (decH 1 0) = true := by decide +kernel
theorem cove_22_10 : CovBE 22 10 11 22 :=
  CovBE.of_chk che_22_10_0

theorem che_22_11_0 : chkE 22 11 12 22 (decH 1 0) = true := by decide +kernel
theorem cove_22_11 : CovBE 22 11 12 22 :=
  CovBE.of_chk che_22_11_0

theorem che_22_12_0 : chkE 22 12 13 22 (decH 1 0) = true := by decide +kernel
theorem cove_22_12 : CovBE 22 12 13 22 :=
  CovBE.of_chk che_22_12_0

theorem che_22_13_0 : chkE 22 13 14 22 (decH 1 0) = true := by decide +kernel
theorem cove_22_13 : CovBE 22 13 14 22 :=
  CovBE.of_chk che_22_13_0

theorem che_22_14_0 : chkE 22 14 15 22 (decH 1 0) = true := by decide +kernel
theorem cove_22_14 : CovBE 22 14 15 22 :=
  CovBE.of_chk che_22_14_0

theorem che_22_15_0 : chkE 22 15 16 22 (decH 1 0) = true := by decide +kernel
theorem cove_22_15 : CovBE 22 15 16 22 :=
  CovBE.of_chk che_22_15_0

theorem che_22_16_0 : chkE 22 16 17 22 (decH 1 0) = true := by decide +kernel
theorem cove_22_16 : CovBE 22 16 17 22 :=
  CovBE.of_chk che_22_16_0

theorem che_22_17_0 : chkE 22 17 18 22 (decH 1 0) = true := by decide +kernel
theorem cove_22_17 : CovBE 22 17 18 22 :=
  CovBE.of_chk che_22_17_0

theorem che_22_18_0 : chkE 22 18 19 22 (decH 1 0) = true := by decide +kernel
theorem cove_22_18 : CovBE 22 18 19 22 :=
  CovBE.of_chk che_22_18_0

theorem che_22_19_0 : chkE 22 19 20 22 (decH 1 0) = true := by decide +kernel
theorem cove_22_19 : CovBE 22 19 20 22 :=
  CovBE.of_chk che_22_19_0

theorem cove_22 : CovQE 22 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_22_2) (CovAE.trans (CovAE.one cove_22_3) (CovAE.trans (CovAE.one cove_22_4) (CovAE.trans (CovAE.one cove_22_5) (CovAE.trans (CovAE.one cove_22_6) (CovAE.trans (CovAE.one cove_22_7) (CovAE.trans (CovAE.one cove_22_8) (CovAE.trans (CovAE.one cove_22_9) (CovAE.trans (CovAE.one cove_22_10) (CovAE.trans (CovAE.one cove_22_11) (CovAE.trans (CovAE.one cove_22_12) (CovAE.trans (CovAE.one cove_22_13) (CovAE.trans (CovAE.one cove_22_14) (CovAE.trans (CovAE.one cove_22_15) (CovAE.trans (CovAE.one cove_22_16) (CovAE.trans (CovAE.one cove_22_17) (CovAE.trans (CovAE.one cove_22_18) (CovAE.one cove_22_19))))))))))))))))))

/-! ### `N = 23` -/

theorem che_23_2_0 : chkE 23 2 3 16 (decH 22 43819922404888859375282479687952978405120167526824510823402533151682756649593586905626736837399719402301873281210417383166269575295354510652720837806935961844146471607577364571755471892239446064441485338151073860329058934210664545946575654137093314714904195157461243579613315) = true := by decide +kernel
theorem che_23_2_1 : chkE 23 2 16 19 (decH 9 1545375951193642606437716380265566124894935856215162071445348043392782279923087311845716890974228233897698522307425784727934479557339538069178858401823698289361596241754233573295027565802905010868374017) = true := by decide +kernel
theorem che_23_2_2 : chkE 23 2 19 23 (decH 5 23570940290528514262997285495717119307720997135126383472242671532604238716921163049189937849216788376641642251671662278240039093680664199767410035145962154090296435364560500050364713473) = true := by decide +kernel
theorem cove_23_2 : CovBE 23 2 3 23 :=
  CovBE.trans (CovBE.of_chk che_23_2_0) (CovBE.trans (CovBE.of_chk che_23_2_1) (CovBE.of_chk che_23_2_2))

theorem che_23_3_0 : chkE 23 3 4 5 (decH 8 213357502485067605220228166902322653784829709813594598386959016105446369284338908039268013490500491150358229316573667128454503959607413890962843899215023749201155712191266077838617402343151394122082952930920781365865661059) = true := by decide +kernel
theorem che_23_3_1 : chkE 23 3 5 23 (decH 26 21728485826801689858926681968939262746855383071555964695956078394096212348246106187457834084894690328090311104731107622887436064761556200540771960883591131057502499983183685004645294752444921572315001301056191867493675303069962339805144973673942704014463389793478406593005297752572481594571127573880461340873627411823670251340884324169117532036565323506457125230433423680488882819) = true := by decide +kernel
theorem cove_23_3 : CovBE 23 3 4 23 :=
  CovBE.trans (CovBE.of_chk che_23_3_0) (CovBE.of_chk che_23_3_1)

theorem che_23_4_0 : chkE 23 4 5 23 (decH 32 6825009591678924512388962250911596922312826473437527135560650672006774848467637007969336358972604519346759435800085741868208157665930356123664442104771429186867349456071692361570961449543177541452608351030265437377020024877229203585883025041701760815278009301969902602031171708026823263687644546264606739461990249176426937847852074373856574031471043193522414761888847188982059417901294243750171469429198652966512247396355818371) = true := by decide +kernel
theorem cove_23_4 : CovBE 23 4 5 23 :=
  CovBE.of_chk che_23_4_0

theorem che_23_5_0 : chkE 23 5 6 18 (decH 22 18359293199014373394506366454563313678456458328994234664404446977469019570591255911113433177961240192093124483118347970068078614023945319937281806534347408418250262988225158757456355909033722166906828557751533641211063344943708816497909376784271714661801875383403853102061879414159739829367684052290474773674528683556444945343511128000480387) = true := by decide +kernel
theorem che_23_5_1 : chkE 23 5 18 23 (decH 2 373679816552244230062271414651667066688702977) = true := by decide +kernel
theorem cove_23_5 : CovBE 23 5 6 23 :=
  CovBE.trans (CovBE.of_chk che_23_5_0) (CovBE.of_chk che_23_5_1)

theorem che_23_6_0 : chkE 23 6 7 23 (decH 12 3122659673730156843025803566693941833350317948141321588302416338479643001610632603931321588156300674961090464049820837036913870211) = true := by decide +kernel
theorem cove_23_6 : CovBE 23 6 7 23 :=
  CovBE.of_chk che_23_6_0

theorem che_23_7_0 : chkE 23 7 8 23 (decH 3 83227704295468077187) = true := by decide +kernel
theorem cove_23_7 : CovBE 23 7 8 23 :=
  CovBE.of_chk che_23_7_0

theorem che_23_8_0 : chkE 23 8 9 23 (decH 1 0) = true := by decide +kernel
theorem cove_23_8 : CovBE 23 8 9 23 :=
  CovBE.of_chk che_23_8_0

theorem che_23_9_0 : chkE 23 9 10 23 (decH 1 0) = true := by decide +kernel
theorem cove_23_9 : CovBE 23 9 10 23 :=
  CovBE.of_chk che_23_9_0

theorem che_23_10_0 : chkE 23 10 11 23 (decH 1 0) = true := by decide +kernel
theorem cove_23_10 : CovBE 23 10 11 23 :=
  CovBE.of_chk che_23_10_0

theorem che_23_11_0 : chkE 23 11 12 23 (decH 1 0) = true := by decide +kernel
theorem cove_23_11 : CovBE 23 11 12 23 :=
  CovBE.of_chk che_23_11_0

theorem che_23_12_0 : chkE 23 12 13 23 (decH 1 0) = true := by decide +kernel
theorem cove_23_12 : CovBE 23 12 13 23 :=
  CovBE.of_chk che_23_12_0

theorem che_23_13_0 : chkE 23 13 14 23 (decH 1 0) = true := by decide +kernel
theorem cove_23_13 : CovBE 23 13 14 23 :=
  CovBE.of_chk che_23_13_0

theorem che_23_14_0 : chkE 23 14 15 23 (decH 1 0) = true := by decide +kernel
theorem cove_23_14 : CovBE 23 14 15 23 :=
  CovBE.of_chk che_23_14_0

theorem che_23_15_0 : chkE 23 15 16 23 (decH 1 0) = true := by decide +kernel
theorem cove_23_15 : CovBE 23 15 16 23 :=
  CovBE.of_chk che_23_15_0

theorem che_23_16_0 : chkE 23 16 17 23 (decH 1 0) = true := by decide +kernel
theorem cove_23_16 : CovBE 23 16 17 23 :=
  CovBE.of_chk che_23_16_0

theorem che_23_17_0 : chkE 23 17 18 23 (decH 1 0) = true := by decide +kernel
theorem cove_23_17 : CovBE 23 17 18 23 :=
  CovBE.of_chk che_23_17_0

theorem che_23_18_0 : chkE 23 18 19 23 (decH 1 0) = true := by decide +kernel
theorem cove_23_18 : CovBE 23 18 19 23 :=
  CovBE.of_chk che_23_18_0

theorem che_23_19_0 : chkE 23 19 20 23 (decH 1 0) = true := by decide +kernel
theorem cove_23_19 : CovBE 23 19 20 23 :=
  CovBE.of_chk che_23_19_0

theorem che_23_20_0 : chkE 23 20 21 23 (decH 1 0) = true := by decide +kernel
theorem cove_23_20 : CovBE 23 20 21 23 :=
  CovBE.of_chk che_23_20_0

theorem cove_23 : CovQE 23 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_23_2) (CovAE.trans (CovAE.one cove_23_3) (CovAE.trans (CovAE.one cove_23_4) (CovAE.trans (CovAE.one cove_23_5) (CovAE.trans (CovAE.one cove_23_6) (CovAE.trans (CovAE.one cove_23_7) (CovAE.trans (CovAE.one cove_23_8) (CovAE.trans (CovAE.one cove_23_9) (CovAE.trans (CovAE.one cove_23_10) (CovAE.trans (CovAE.one cove_23_11) (CovAE.trans (CovAE.one cove_23_12) (CovAE.trans (CovAE.one cove_23_13) (CovAE.trans (CovAE.one cove_23_14) (CovAE.trans (CovAE.one cove_23_15) (CovAE.trans (CovAE.one cove_23_16) (CovAE.trans (CovAE.one cove_23_17) (CovAE.trans (CovAE.one cove_23_18) (CovAE.trans (CovAE.one cove_23_19) (CovAE.one cove_23_20)))))))))))))))))))

/-! ### `N = 24` -/

theorem che_24_2_0 : chkE 24 2 3 4 (decH 10 15032606987695173381095402144055129002965610486151589922753655742268322068349933214247509414576228625038818859114628112620123068810755604989660623048040804764421072261270500949686816075186659453366807700168834395395541146597025321182656437613000361133768224574568204890712033147717120918864003) = true := by decide +kernel
theorem che_24_2_1 : chkE 24 2 4 20 (decH 22 3544338355252216128929833529369691864996364126654514575608050382889136397473723779562801471297008637966426086772178860161805337018197463599811354063585651636116595062574673557952442420560691272255761223807504653911934218069618597505879709020392014594719156939940870954822851099654394244440866181178804174979) = true := by decide +kernel
theorem che_24_2_2 : chkE 24 2 20 24 (decH 5 624227513016360796193019704435026878041788700548985989011118993623216295877352096720917072135772020221297206886124855634423945917736661008807013103561283631248862668572688959986090019073084033) = true := by decide +kernel
theorem cove_24_2 : CovBE 24 2 3 24 :=
  CovBE.trans (CovBE.of_chk che_24_2_0) (CovBE.trans (CovBE.of_chk che_24_2_1) (CovBE.of_chk che_24_2_2))

theorem che_24_3_0 : chkE 24 3 4 20 (decH 36 544496620868021876422255604874340213343915268769963126903581350632024379153667686629475444298011545787538784880109963930884979998962986842186697037818767501396702788415951536753826402023843771202675984391030053693533011496987051139299636213522280878714081299854735816991887742533325284975356503474547581769552782119743128377352226233684991843109917281369616484387570391518800758301643039632498364968391950979) = true := by decide +kernel
theorem che_24_3_1 : chkE 24 3 20 24 (decH 4 6650129863925562305274499741507012854083513775870575765829108572730264193) = true := by decide +kernel
theorem cove_24_3 : CovBE 24 3 4 24 :=
  CovBE.trans (CovBE.of_chk che_24_3_0) (CovBE.of_chk che_24_3_1)

theorem che_24_4_0 : chkE 24 4 5 15 (decH 17 565239952593074865417950912041730927245053553864896097440015441718266843001256182261585362442886494625264304514036789171198939975398533966006512605178480986439434443437891036853054275492287446605259400595537214085795848190011006582283127257204935404316398054540183895808089175739305273339202616193782975245286142405653298828221744520241672289932854147) = true := by decide +kernel
theorem che_24_4_1 : chkE 24 4 15 24 (decH 18 79736871769909150420630814837455558272227357038180561038392903570264283717551429715569210269619882442746068616322652058628821495465835500638197921803866735509205696432480918958035657936445334307037482501391033161477313715070020048297899470818537817905952228485576243108253828257612317571) = true := by decide +kernel
theorem cove_24_4 : CovBE 24 4 5 24 :=
  CovBE.trans (CovBE.of_chk che_24_4_0) (CovBE.of_chk che_24_4_1)

theorem che_24_5_0 : chkE 24 5 6 24 (decH 29 21544777948514702795812145623912827381655349565434406025720847490473435364232327055580845453618133497201685588587137158502966253684182518885201293415272169113302404152834442093087321553028875635206117565463645873373152723750625649477839129959223593551887136866212922709049109884285387773954832003049124995099171834686769522212676737264523372597090761909957837955) = true := by decide +kernel
theorem cove_24_5 : CovBE 24 5 6 24 :=
  CovBE.of_chk che_24_5_0

theorem che_24_6_0 : chkE 24 6 7 24 (decH 14 49356588094598447142130688846240811602864462691168398614728049956991149818668032455844749293356262769985527750885507967355690708800250961654126707523926017194558291494275) = true := by decide +kernel
theorem cove_24_6 : CovBE 24 6 7 24 :=
  CovBE.of_chk che_24_6_0

theorem che_24_7_0 : chkE 24 7 8 24 (decH 6 904889723709141502768682338693537979813916297000444944729731) = true := by decide +kernel
theorem cove_24_7 : CovBE 24 7 8 24 :=
  CovBE.of_chk che_24_7_0

theorem che_24_8_0 : chkE 24 8 9 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_8 : CovBE 24 8 9 24 :=
  CovBE.of_chk che_24_8_0

theorem che_24_9_0 : chkE 24 9 10 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_9 : CovBE 24 9 10 24 :=
  CovBE.of_chk che_24_9_0

theorem che_24_10_0 : chkE 24 10 11 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_10 : CovBE 24 10 11 24 :=
  CovBE.of_chk che_24_10_0

theorem che_24_11_0 : chkE 24 11 12 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_11 : CovBE 24 11 12 24 :=
  CovBE.of_chk che_24_11_0

theorem che_24_12_0 : chkE 24 12 13 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_12 : CovBE 24 12 13 24 :=
  CovBE.of_chk che_24_12_0

theorem che_24_13_0 : chkE 24 13 14 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_13 : CovBE 24 13 14 24 :=
  CovBE.of_chk che_24_13_0

theorem che_24_14_0 : chkE 24 14 15 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_14 : CovBE 24 14 15 24 :=
  CovBE.of_chk che_24_14_0

theorem che_24_15_0 : chkE 24 15 16 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_15 : CovBE 24 15 16 24 :=
  CovBE.of_chk che_24_15_0

theorem che_24_16_0 : chkE 24 16 17 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_16 : CovBE 24 16 17 24 :=
  CovBE.of_chk che_24_16_0

theorem che_24_17_0 : chkE 24 17 18 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_17 : CovBE 24 17 18 24 :=
  CovBE.of_chk che_24_17_0

theorem che_24_18_0 : chkE 24 18 19 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_18 : CovBE 24 18 19 24 :=
  CovBE.of_chk che_24_18_0

theorem che_24_19_0 : chkE 24 19 20 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_19 : CovBE 24 19 20 24 :=
  CovBE.of_chk che_24_19_0

theorem che_24_20_0 : chkE 24 20 21 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_20 : CovBE 24 20 21 24 :=
  CovBE.of_chk che_24_20_0

theorem che_24_21_0 : chkE 24 21 22 24 (decH 1 0) = true := by decide +kernel
theorem cove_24_21 : CovBE 24 21 22 24 :=
  CovBE.of_chk che_24_21_0

theorem cove_24 : CovQE 24 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_24_2) (CovAE.trans (CovAE.one cove_24_3) (CovAE.trans (CovAE.one cove_24_4) (CovAE.trans (CovAE.one cove_24_5) (CovAE.trans (CovAE.one cove_24_6) (CovAE.trans (CovAE.one cove_24_7) (CovAE.trans (CovAE.one cove_24_8) (CovAE.trans (CovAE.one cove_24_9) (CovAE.trans (CovAE.one cove_24_10) (CovAE.trans (CovAE.one cove_24_11) (CovAE.trans (CovAE.one cove_24_12) (CovAE.trans (CovAE.one cove_24_13) (CovAE.trans (CovAE.one cove_24_14) (CovAE.trans (CovAE.one cove_24_15) (CovAE.trans (CovAE.one cove_24_16) (CovAE.trans (CovAE.one cove_24_17) (CovAE.trans (CovAE.one cove_24_18) (CovAE.trans (CovAE.one cove_24_19) (CovAE.trans (CovAE.one cove_24_20) (CovAE.one cove_24_21))))))))))))))))))))

/-! ### `N = 25` -/

theorem che_25_2_0 : chkE 25 2 3 16 (decH 20 9963496814836812376434518157100905774568711314446889011960604547899642302629677586967461477516289641278414961661794852348350092567741534384024139936614799686148023343343899285275606192615990355319754916588662851275441985641661836875640811138762971665278219337859) = true := by decide +kernel
theorem che_25_2_1 : chkE 25 2 16 19 (decH 12 3238142733306355432414140175433188255540729342127980498526901884173390693022331326636549069176097460036474966580730516604948559579954310096719075283481077966658469352059286933162978718934662241047468480776961) = true := by decide +kernel
theorem che_25_2_2 : chkE 25 2 19 21 (decH 6 635922629146500966621060480095759684022186441101368834593894993966370641214724051282457385836886550481588721957094544049679005710005725690604251500452842693469428982405032752405195787670044563820475843032350863192368229328060032492548034411281019915009) = true := by decide +kernel
theorem che_25_2_3 : chkE 25 2 21 25 (decH 5 1852761665622886192014817877486470326549671332718261579635904112195889201770633174377368435404389124072375695420282216638191913765914686592727367435350466641223799566609003292764336229418113291511958273) = true := by decide +kernel
theorem cove_25_2 : CovBE 25 2 3 25 :=
  CovBE.trans (CovBE.of_chk che_25_2_0) (CovBE.trans (CovBE.of_chk che_25_2_1) (CovBE.trans (CovBE.of_chk che_25_2_2) (CovBE.of_chk che_25_2_3)))

theorem che_25_3_0 : chkE 25 3 4 5 (decH 9 5828541898893000459075945590770215699142557240561746935182596796929334364784118843228941149734731438768020279318067375767367289980682887236278403186865885561537555877978852380567492049839585638655285667988084058094312352519415771181119417737454973182816208065922091618273639454632694563459) = true := by decide +kernel
theorem che_25_3_1 : chkE 25 3 5 20 (decH 27 1113386148881063557096591291011416340663933460153632173654544868158684054240150628752467175176884315189651472153940483812276762518296415027028089782692965323277567952138905904012646652265192112565478330931751823763065075831428424126325438450040256025173237293515144486702660653518502988356641843453598359816644593274239182148038067764175709597911984942327455127936098844805) = true := by decide +kernel
theorem che_25_3_2 : chkE 25 3 20 25 (decH 6 12161155708741153500493203761272628673198890948674912976410138572172833537796436606865987774219229567544729604109463054422583386572457746343673660713350777959707339055970889883237059366051485446991223116597232197077761) = true := by decide +kernel
theorem cove_25_3 : CovBE 25 3 4 25 :=
  CovBE.trans (CovBE.of_chk che_25_3_0) (CovBE.trans (CovBE.of_chk che_25_3_1) (CovBE.of_chk che_25_3_2))

theorem che_25_4_0 : chkE 25 4 5 20 (decH 37 487131916249847837549001003371308839966841766051560170834737912847375403574500328649143599849093912749066603121372955595717215048653550235605689290221239616200470397506978375336000847134338648733605814614190041940311460412817148853350015497712283763884120412624872343609053086862436230400594441889733463938485081628562503944211888798434762930261021724564888079000242437576697941471925262211353652393287743931267320973946963070283561543034548124035373686631427219852095458994472355386038157332942080983450499) = true := by decide +kernel
theorem che_25_4_1 : chkE 25 4 20 25 (decH 4 14879906863866032717294604818019127197126116414953228459360489187659364895705857) = true := by decide +kernel
theorem cove_25_4 : CovBE 25 4 5 25 :=
  CovBE.trans (CovBE.of_chk che_25_4_0) (CovBE.of_chk che_25_4_1)

theorem che_25_5_0 : chkE 25 5 6 18 (decH 25 18695670882717480159121871651462174617109009527523609355275362761468845163391402352970909763776292005934955030780323758355365598984160513833132259524782517396777500793936002272554781443367830584298226657290176762978638830828569449445075795978575600987089447145028335563499108068218206252090672678512532865123067767944592928707677731829423158769518554352999059425652378553427266053324092047721405157670512154630514852995) = true := by decide +kernel
theorem che_25_5_1 : chkE 25 5 18 25 (decH 7 10112260485544044530261204367823334354376411278465706761074896826125183628539737773489100571913759185745542692995) = true := by decide +kernel
theorem cove_25_5 : CovBE 25 5 6 25 :=
  CovBE.trans (CovBE.of_chk che_25_5_0) (CovBE.of_chk che_25_5_1)

theorem che_25_6_0 : chkE 25 6 7 25 (decH 20 4479335903372941202873243551715192009838277592578657462233108779150722109751971269171219592394892434629734652646955309883903338258952124230340244419126186738823963485028228305729546790627141900614861608016431690239540769467984746955064240460187846019) = true := by decide +kernel
theorem cove_25_6 : CovBE 25 6 7 25 :=
  CovBE.of_chk che_25_6_0

theorem che_25_7_0 : chkE 25 7 8 25 (decH 7 13967591751648711029557426315780007218782403937992283670915667806010463821547139) = true := by decide +kernel
theorem cove_25_7 : CovBE 25 7 8 25 :=
  CovBE.of_chk che_25_7_0

theorem che_25_8_0 : chkE 25 8 9 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_8 : CovBE 25 8 9 25 :=
  CovBE.of_chk che_25_8_0

theorem che_25_9_0 : chkE 25 9 10 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_9 : CovBE 25 9 10 25 :=
  CovBE.of_chk che_25_9_0

theorem che_25_10_0 : chkE 25 10 11 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_10 : CovBE 25 10 11 25 :=
  CovBE.of_chk che_25_10_0

theorem che_25_11_0 : chkE 25 11 12 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_11 : CovBE 25 11 12 25 :=
  CovBE.of_chk che_25_11_0

theorem che_25_12_0 : chkE 25 12 13 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_12 : CovBE 25 12 13 25 :=
  CovBE.of_chk che_25_12_0

theorem che_25_13_0 : chkE 25 13 14 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_13 : CovBE 25 13 14 25 :=
  CovBE.of_chk che_25_13_0

theorem che_25_14_0 : chkE 25 14 15 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_14 : CovBE 25 14 15 25 :=
  CovBE.of_chk che_25_14_0

theorem che_25_15_0 : chkE 25 15 16 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_15 : CovBE 25 15 16 25 :=
  CovBE.of_chk che_25_15_0

theorem che_25_16_0 : chkE 25 16 17 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_16 : CovBE 25 16 17 25 :=
  CovBE.of_chk che_25_16_0

theorem che_25_17_0 : chkE 25 17 18 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_17 : CovBE 25 17 18 25 :=
  CovBE.of_chk che_25_17_0

theorem che_25_18_0 : chkE 25 18 19 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_18 : CovBE 25 18 19 25 :=
  CovBE.of_chk che_25_18_0

theorem che_25_19_0 : chkE 25 19 20 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_19 : CovBE 25 19 20 25 :=
  CovBE.of_chk che_25_19_0

theorem che_25_20_0 : chkE 25 20 21 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_20 : CovBE 25 20 21 25 :=
  CovBE.of_chk che_25_20_0

theorem che_25_21_0 : chkE 25 21 22 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_21 : CovBE 25 21 22 25 :=
  CovBE.of_chk che_25_21_0

theorem che_25_22_0 : chkE 25 22 23 25 (decH 1 0) = true := by decide +kernel
theorem cove_25_22 : CovBE 25 22 23 25 :=
  CovBE.of_chk che_25_22_0

theorem cove_25 : CovQE 25 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_25_2) (CovAE.trans (CovAE.one cove_25_3) (CovAE.trans (CovAE.one cove_25_4) (CovAE.trans (CovAE.one cove_25_5) (CovAE.trans (CovAE.one cove_25_6) (CovAE.trans (CovAE.one cove_25_7) (CovAE.trans (CovAE.one cove_25_8) (CovAE.trans (CovAE.one cove_25_9) (CovAE.trans (CovAE.one cove_25_10) (CovAE.trans (CovAE.one cove_25_11) (CovAE.trans (CovAE.one cove_25_12) (CovAE.trans (CovAE.one cove_25_13) (CovAE.trans (CovAE.one cove_25_14) (CovAE.trans (CovAE.one cove_25_15) (CovAE.trans (CovAE.one cove_25_16) (CovAE.trans (CovAE.one cove_25_17) (CovAE.trans (CovAE.one cove_25_18) (CovAE.trans (CovAE.one cove_25_19) (CovAE.trans (CovAE.one cove_25_20) (CovAE.trans (CovAE.one cove_25_21) (CovAE.one cove_25_22)))))))))))))))))))))

/-! ### `N = 26` -/

theorem che_26_2_0 : chkE 26 2 3 4 (decH 11 920734768388717443873988771845851828703182673854808940189029253623814734985482214255407786521137907038572197235362717389640566863477312695168994812403591986770458708410484574725191551488235367730368534079992537028502694973963275963955863503328363246762746399426954218916875211040590347523586528918335037541381304666039868111286010448869658391425592286067149785579651) = true := by decide +kernel
theorem che_26_2_1 : chkE 26 2 4 20 (decH 22 489713327473820767116026544742105260573427354925739583238903546069102481540542375257572166096418354675711687271296760703445527415979447344007769959484771068798322637774957201927685812916149906808448322481064784906541028729566544003) = true := by decide +kernel
theorem che_26_2_2 : chkE 26 2 20 22 (decH 6 21850250625242079892926047791697885020348782702952986675025203329292358630333582529220817736186221336094301030574244315003694480224096051817894993841551501413002068160894412833726865041754838456460266744844705719907645885751280555973143079921660702425623608675201) = true := by decide +kernel
theorem che_26_2_3 : chkE 26 2 22 26 (decH 5 45303854974074113667253640794190965031717415194865461973505165376659298081892188482424156765625779024428471179601691790133067392361222800781028956887410886820293789371449952552005370131073728919642024488291201) = true := by decide +kernel
theorem cove_26_2 : CovBE 26 2 3 26 :=
  CovBE.trans (CovBE.of_chk che_26_2_0) (CovBE.trans (CovBE.of_chk che_26_2_1) (CovBE.trans (CovBE.of_chk che_26_2_2) (CovBE.of_chk che_26_2_3)))

theorem che_26_3_0 : chkE 26 3 4 17 (decH 27 12883975619529410623223796123513863818297670765456291216327210039002664449777142793389827437425338570998992639035704110588214955620204200140321544792378883199930491433792712457480592670537350342229524414303407357332072917772181026209660869767641910948739406975452880704135556167321807463766571860172275698256885481163702669139427751965428374644367919642409218063091080847801444221571) = true := by decide +kernel
theorem che_26_3_1 : chkE 26 3 17 21 (decH 15 30454804338330724201536574303210784107030679908304131395261663818791793454315459935200817467462856687558055152140425430399402069192085897507583267137506366404608483886419487010713977213857303970615809114468229223187756621807240570822416429560003996861288396763144264727071367930249355713497545484022089091) = true := by decide +kernel
theorem che_26_3_2 : chkE 26 3 21 26 (decH 6 35837796361958792183975637601179253246902995890317013162992165064250640249016203512948819492720311562976504347415852672931472365215667124370750074095170759671386276783232733476455254937883758828653526741861509707027731464964993) = true := by decide +kernel
theorem cove_26_3 : CovBE 26 3 4 26 :=
  CovBE.trans (CovBE.of_chk che_26_3_0) (CovBE.trans (CovBE.of_chk che_26_3_1) (CovBE.of_chk che_26_3_2))

theorem che_26_4_0 : chkE 26 4 5 6 (decH 8 7677947055279431315976520087925902000850131562088261046529225594182257080649100551603753478664046797321069406317467438350637251687017556954475907117835616965291157723247467120687855747200407327616579822717762917534999510341505346941246802935989123) = true := by decide +kernel
theorem che_26_4_1 : chkE 26 4 6 22 (decH 34 424727232780060629988756509155850849229917461017645758520607575831189052674863482503468231564226347152142193326660597225011779823092137569404336697399910083125966720961165724423832676303878898171100744665985862717895158917816223596208304717138709062643197696804709680127504083798183131730987477880103895404924754911680688218876069684556028107939772857441998249974435420366285254681616780984938306682782959859932035478055506568684280823617028703763158516003623253125866541507317705441651609508425946734265468143878353493752788396493657062228898458703112379039956997) = true := by decide +kernel
theorem che_26_4_2 : chkE 26 4 22 26 (decH 2 786632946065691302595303331635948614638501483432833) = true := by decide +kernel
theorem cove_26_4 : CovBE 26 4 5 26 :=
  CovBE.trans (CovBE.of_chk che_26_4_0) (CovBE.trans (CovBE.of_chk che_26_4_1) (CovBE.of_chk che_26_4_2))

theorem che_26_5_0 : chkE 26 5 6 20 (decH 35 70629931012947226040049623654934993014454005880754548200184027855249022604635586914966581940469348138810404564874823599807157035475857343782562662626363976334595197337182684856246064268621888702147977029845637870580931080742203479113161704760225125635825752741219615796383309503367690492083886298103377252263644703302647171867925949928201972396434947236052406300389466269383122563638194060116352863030879824455534578474572495230726499286273955505128579) = true := by decide +kernel
theorem che_26_5_1 : chkE 26 5 20 26 (decH 4 79681721236089098965489568823517301991248373954599247559725638694251658480513) = true := by decide +kernel
theorem cove_26_5 : CovBE 26 5 6 26 :=
  CovBE.trans (CovBE.of_chk che_26_5_0) (CovBE.of_chk che_26_5_1)

theorem che_26_6_0 : chkE 26 6 7 26 (decH 23 568059614790090374148280360332902640710482830404228008911830921229217851063541854593693733666655780311712635698296761220658869316221220632179534652955982316757253567870572030404209876639714287700612371541825793873560366428071678316113960545754645271036025744495010872647866057875293865449232308243632581093244572251501613000118121147345883650429137687349548674918810918624629693440795451092335904131) = true := by decide +kernel
theorem cove_26_6 : CovBE 26 6 7 26 :=
  CovBE.of_chk che_26_6_0

theorem che_26_7_0 : chkE 26 7 8 26 (decH 12 249991428562159221942653230928448997862910660097640096755067894540043073136614301002892227371732075259437666335376707566908051034862924290058110595) = true := by decide +kernel
theorem cove_26_7 : CovBE 26 7 8 26 :=
  CovBE.of_chk che_26_7_0

theorem che_26_8_0 : chkE 26 8 9 26 (decH 3 92523142722994868867) = true := by decide +kernel
theorem cove_26_8 : CovBE 26 8 9 26 :=
  CovBE.of_chk che_26_8_0

theorem che_26_9_0 : chkE 26 9 10 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_9 : CovBE 26 9 10 26 :=
  CovBE.of_chk che_26_9_0

theorem che_26_10_0 : chkE 26 10 11 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_10 : CovBE 26 10 11 26 :=
  CovBE.of_chk che_26_10_0

theorem che_26_11_0 : chkE 26 11 12 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_11 : CovBE 26 11 12 26 :=
  CovBE.of_chk che_26_11_0

theorem che_26_12_0 : chkE 26 12 13 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_12 : CovBE 26 12 13 26 :=
  CovBE.of_chk che_26_12_0

theorem che_26_13_0 : chkE 26 13 14 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_13 : CovBE 26 13 14 26 :=
  CovBE.of_chk che_26_13_0

theorem che_26_14_0 : chkE 26 14 15 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_14 : CovBE 26 14 15 26 :=
  CovBE.of_chk che_26_14_0

theorem che_26_15_0 : chkE 26 15 16 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_15 : CovBE 26 15 16 26 :=
  CovBE.of_chk che_26_15_0

theorem che_26_16_0 : chkE 26 16 17 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_16 : CovBE 26 16 17 26 :=
  CovBE.of_chk che_26_16_0

theorem che_26_17_0 : chkE 26 17 18 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_17 : CovBE 26 17 18 26 :=
  CovBE.of_chk che_26_17_0

theorem che_26_18_0 : chkE 26 18 19 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_18 : CovBE 26 18 19 26 :=
  CovBE.of_chk che_26_18_0

theorem che_26_19_0 : chkE 26 19 20 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_19 : CovBE 26 19 20 26 :=
  CovBE.of_chk che_26_19_0

theorem che_26_20_0 : chkE 26 20 21 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_20 : CovBE 26 20 21 26 :=
  CovBE.of_chk che_26_20_0

theorem che_26_21_0 : chkE 26 21 22 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_21 : CovBE 26 21 22 26 :=
  CovBE.of_chk che_26_21_0

theorem che_26_22_0 : chkE 26 22 23 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_22 : CovBE 26 22 23 26 :=
  CovBE.of_chk che_26_22_0

theorem che_26_23_0 : chkE 26 23 24 26 (decH 1 0) = true := by decide +kernel
theorem cove_26_23 : CovBE 26 23 24 26 :=
  CovBE.of_chk che_26_23_0

theorem cove_26 : CovQE 26 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_26_2) (CovAE.trans (CovAE.one cove_26_3) (CovAE.trans (CovAE.one cove_26_4) (CovAE.trans (CovAE.one cove_26_5) (CovAE.trans (CovAE.one cove_26_6) (CovAE.trans (CovAE.one cove_26_7) (CovAE.trans (CovAE.one cove_26_8) (CovAE.trans (CovAE.one cove_26_9) (CovAE.trans (CovAE.one cove_26_10) (CovAE.trans (CovAE.one cove_26_11) (CovAE.trans (CovAE.one cove_26_12) (CovAE.trans (CovAE.one cove_26_13) (CovAE.trans (CovAE.one cove_26_14) (CovAE.trans (CovAE.one cove_26_15) (CovAE.trans (CovAE.one cove_26_16) (CovAE.trans (CovAE.one cove_26_17) (CovAE.trans (CovAE.one cove_26_18) (CovAE.trans (CovAE.one cove_26_19) (CovAE.trans (CovAE.one cove_26_20) (CovAE.trans (CovAE.one cove_26_21) (CovAE.trans (CovAE.one cove_26_22) (CovAE.one cove_26_23))))))))))))))))))))))

/-! ### `N = 27` -/

theorem che_27_2_0 : chkE 27 2 3 16 (decH 17 801148991900274909148035620823071170126375028204230351485039256996974611187620629307432812363293522581750086230663850043979922883644865683658742172862941937207035293681791466950761421013159692825907348410296727461939659189709476741251) = true := by decide +kernel
theorem che_27_2_1 : chkE 27 2 16 20 (decH 19 6295511813586753062594117938151543798846462667629880471151188639692763993944338881012866091104123094078741805566586286801455851072974707312204125730111517815336285370513595034263586766263134683116630110697362267891097914009728970773798207541749539042768497828764025191831226383192397216877569) = true := by decide +kernel
theorem che_27_2_2 : chkE 27 2 20 22 (decH 7 2584052992404788626605286067959594984612434482338743638177101406640803882346971034457842139636586672812867483941019584149405620008458969491971011339229556539404490151461017713701487475560788936424375821377060353491617523913939093649242552830977) = true := by decide +kernel
theorem che_27_2_3 : chkE 27 2 22 25 (decH 6 74601420496063703004782196413117948794187976689076460286893854393438356061944666828190570469547075490817750136371788068154842958242902366236379277785036449891769486679325981251129215369665106004539826810389530373136552943748579958353540377902587082197366794403329763232769) = true := by decide +kernel
theorem che_27_2_4 : chkE 27 2 25 27 (decH 2 627858341332995885797392015752530793487947977807940609) = true := by decide +kernel
theorem cove_27_2 : CovBE 27 2 3 27 :=
  CovBE.trans (CovBE.of_chk che_27_2_0) (CovBE.trans (CovBE.of_chk che_27_2_1) (CovBE.trans (CovBE.of_chk che_27_2_2) (CovBE.trans (CovBE.of_chk che_27_2_3) (CovBE.of_chk che_27_2_4))))

theorem che_27_3_0 : chkE 27 3 4 5 (decH 10 30660393058168870307334111731449276520235625082638317548356374134951254626963215013268640695731373686181188622164196239834406448128328673424324902568482287307679806230983805068894214788990882744666468735786164533262264035061702501858296589029723777288988783418407804647655458910623267119528831075049196794491657944203051651) = true := by decide +kernel
theorem che_27_3_1 : chkE 27 3 5 21 (decH 30 11385594731496960205724092977467227188036167998476156773992414123976069665035815791597767671356760818604092598137491350660504733611567832935159716112512531349710389597798400227949304414174538233003645837903609097516659095695759193407614808054845829339655115311360196029040426111946702424785299042742510223883924508842319832066698595384255163751453786391171) = true := by decide +kernel
theorem che_27_3_2 : chkE 27 3 21 23 (decH 6 9626394138019420360689813450214626100083682539304375606263442896091064829246625787387487833776827579728061914909548470989168604271735733640128521847710145806887922957926568277786629196455461856847394506434621301934148225141363376933889) = true := by decide +kernel
theorem che_27_3_3 : chkE 27 3 23 27 (decH 4 23486976395043185010818184299197982907254718370076611198728601777287091087732064019636368625406373801451066053969265157262337) = true := by decide +kernel
theorem cove_27_3 : CovBE 27 3 4 27 :=
  CovBE.trans (CovBE.of_chk che_27_3_0) (CovBE.trans (CovBE.of_chk che_27_3_1) (CovBE.trans (CovBE.of_chk che_27_3_2) (CovBE.of_chk che_27_3_3)))

theorem che_27_4_0 : chkE 27 4 5 20 (decH 39 2533696645076473467030325767172484958120316734800612228405813075928926902868286619048506007296363782625648526652987589702759547410714596435821486917856476820970949636778886202829832558981184900869215596087503500765336424862245053517930416016693303302210528346617065859377457923553631025137404075096318789144213048546315194271231617940121970829105698199088106084120366269499320441740015779561699143551747359241871766446234071958090651003731221095904748213867802414185265167671284576340142856980860279758245974613136557113385324016217121375107) = true := by decide +kernel
theorem che_27_4_1 : chkE 27 4 20 27 (decH 10 8242688516844574592026774048537130680905651531698090393086890167351262372177890594626462493734221416288446735005373916476337895923483102602167903654182338020030344528445571) = true := by decide +kernel
theorem cove_27_4 : CovBE 27 4 5 27 :=
  CovBE.trans (CovBE.of_chk che_27_4_0) (CovBE.of_chk che_27_4_1)

theorem che_27_5_0 : chkE 27 5 6 9 (decH 17 239658112162864870060605852091911574859368146161138134803917740336005145578943831563657275240800497676093939551355324363012828348954619687309530384712808475977584930546053829346689607761402551154880613463880127998075827557360585242688538966371073563279976019006302312495875487752369696402086633530487536978927204008027092630968016669702751306883) = true := by decide +kernel
theorem che_27_5_1 : chkE 27 5 9 27 (decH 24 3847232720063153697242186617489920420065502144662913985866767683668528964017212857269314693953940629944229741937074606901209676387810987363800506131579043555612568631710574289111805247143692105982602524011798098047612786221490364966181223640254940109940373481081914965754640586576344677370892531535839297612114884022167491958714063917171843) = true := by decide +kernel
theorem cove_27_5 : CovBE 27 5 6 27 :=
  CovBE.trans (CovBE.of_chk che_27_5_0) (CovBE.of_chk che_27_5_1)

theorem che_27_6_0 : chkE 27 6 7 27 (decH 31 8866329787106182460572112820177550849695975433506826245066746721025003717209567028905183005156398316095183281357502388174079536500699169673475756624954475472783945368936653509553703177669105613195820475436313779754467686026803585190616405018185246074359263409846754060440855026921284182054868742625778849107649046404287167225877351388675038837764924505404966005499046206523906246616368123655475214700107171644803) = true := by decide +kernel
theorem cove_27_6 : CovBE 27 6 7 27 :=
  CovBE.of_chk che_27_6_0

theorem che_27_7_0 : chkE 27 7 8 27 (decH 14 16296292488414638805240665809159181776053380435684047527314334122549323484999721645453355602972491662519765221799778538827976332597604287561486533033047486890310090420166917670531) = true := by decide +kernel
theorem cove_27_7 : CovBE 27 7 8 27 :=
  CovBE.of_chk che_27_7_0

theorem che_27_8_0 : chkE 27 8 9 27 (decH 6 1005347872158139930070285016585205256766495116277119128192899) = true := by decide +kernel
theorem cove_27_8 : CovBE 27 8 9 27 :=
  CovBE.of_chk che_27_8_0

theorem che_27_9_0 : chkE 27 9 10 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_9 : CovBE 27 9 10 27 :=
  CovBE.of_chk che_27_9_0

theorem che_27_10_0 : chkE 27 10 11 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_10 : CovBE 27 10 11 27 :=
  CovBE.of_chk che_27_10_0

theorem che_27_11_0 : chkE 27 11 12 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_11 : CovBE 27 11 12 27 :=
  CovBE.of_chk che_27_11_0

theorem che_27_12_0 : chkE 27 12 13 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_12 : CovBE 27 12 13 27 :=
  CovBE.of_chk che_27_12_0

theorem che_27_13_0 : chkE 27 13 14 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_13 : CovBE 27 13 14 27 :=
  CovBE.of_chk che_27_13_0

theorem che_27_14_0 : chkE 27 14 15 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_14 : CovBE 27 14 15 27 :=
  CovBE.of_chk che_27_14_0

theorem che_27_15_0 : chkE 27 15 16 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_15 : CovBE 27 15 16 27 :=
  CovBE.of_chk che_27_15_0

theorem che_27_16_0 : chkE 27 16 17 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_16 : CovBE 27 16 17 27 :=
  CovBE.of_chk che_27_16_0

theorem che_27_17_0 : chkE 27 17 18 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_17 : CovBE 27 17 18 27 :=
  CovBE.of_chk che_27_17_0

theorem che_27_18_0 : chkE 27 18 19 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_18 : CovBE 27 18 19 27 :=
  CovBE.of_chk che_27_18_0

theorem che_27_19_0 : chkE 27 19 20 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_19 : CovBE 27 19 20 27 :=
  CovBE.of_chk che_27_19_0

theorem che_27_20_0 : chkE 27 20 21 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_20 : CovBE 27 20 21 27 :=
  CovBE.of_chk che_27_20_0

theorem che_27_21_0 : chkE 27 21 22 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_21 : CovBE 27 21 22 27 :=
  CovBE.of_chk che_27_21_0

theorem che_27_22_0 : chkE 27 22 23 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_22 : CovBE 27 22 23 27 :=
  CovBE.of_chk che_27_22_0

theorem che_27_23_0 : chkE 27 23 24 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_23 : CovBE 27 23 24 27 :=
  CovBE.of_chk che_27_23_0

theorem che_27_24_0 : chkE 27 24 25 27 (decH 1 0) = true := by decide +kernel
theorem cove_27_24 : CovBE 27 24 25 27 :=
  CovBE.of_chk che_27_24_0

theorem cove_27 : CovQE 27 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_27_2) (CovAE.trans (CovAE.one cove_27_3) (CovAE.trans (CovAE.one cove_27_4) (CovAE.trans (CovAE.one cove_27_5) (CovAE.trans (CovAE.one cove_27_6) (CovAE.trans (CovAE.one cove_27_7) (CovAE.trans (CovAE.one cove_27_8) (CovAE.trans (CovAE.one cove_27_9) (CovAE.trans (CovAE.one cove_27_10) (CovAE.trans (CovAE.one cove_27_11) (CovAE.trans (CovAE.one cove_27_12) (CovAE.trans (CovAE.one cove_27_13) (CovAE.trans (CovAE.one cove_27_14) (CovAE.trans (CovAE.one cove_27_15) (CovAE.trans (CovAE.one cove_27_16) (CovAE.trans (CovAE.one cove_27_17) (CovAE.trans (CovAE.one cove_27_18) (CovAE.trans (CovAE.one cove_27_19) (CovAE.trans (CovAE.one cove_27_20) (CovAE.trans (CovAE.one cove_27_21) (CovAE.trans (CovAE.one cove_27_22) (CovAE.trans (CovAE.one cove_27_23) (CovAE.one cove_27_24)))))))))))))))))))))))

/-! ### `N = 28` -/

theorem che_28_2_0 : chkE 28 2 3 4 (decH 12 15048691440843804636299555414536114307625239150380362289122153207300050962582840592223107777475165618832537557888673203894788752730949124191907025957846401294750724620783129777302598625420785305839311110503939299845182454565948083984440944558819757099331325206991039677381024886970986381223012555963998903134065089136059724063276817189824426318344230771867578098510101864177890440440946413198895216794033128975424416101493424821212146863307816484995) = true := by decide +kernel
theorem che_28_2_1 : chkE 28 2 4 21 (decH 25 170691863112644514387148686921076535795198521684285389210033101117083168754950308118404608824269747964586968823013805150196818093811841220152117632635494056698252553757580632492177929566421021343822532627095131414328128208800724233884228695525336889306720010371) = true := by decide +kernel
theorem che_28_2_2 : chkE 28 2 21 22 (decH 4 45704038840816322351068160942740898834519448197405938468415116308989171973005666862791804762693701849008040914849258652582856277479934117122502502377289206025557534592129) = true := by decide +kernel
theorem che_28_2_3 : chkE 28 2 22 24 (decH 6 28137981587595291972846016920603240235873659110424956080355856882899888242773079865793277567704331313388362609888218699939932813230759093404991061427046162986677078675786021752283246816856033582952314497707762123609519759946736610198029036961593794666676219266715702021454592754355329) = true := by decide +kernel
theorem che_28_2_4 : chkE 28 2 24 28 (decH 5 3287807508550359700439947796544180653036902635961331229601463089333263442105226117013436025599754269378337611942702913543806126908350219791755612506472086663935476089026212568533063894567133924659651418575076032121094497520769) = true := by decide +kernel
theorem cove_28_2 : CovBE 28 2 3 28 :=
  CovBE.trans (CovBE.of_chk che_28_2_0) (CovBE.trans (CovBE.of_chk che_28_2_1) (CovBE.trans (CovBE.of_chk che_28_2_2) (CovBE.trans (CovBE.of_chk che_28_2_3) (CovBE.of_chk che_28_2_4))))

theorem che_28_3_0 : chkE 28 3 4 17 (decH 25 34440475882345233836226452352802187666706653836427337559022226151635041817794673861548607037617300804155170036084029893716942196799162326076660611442324531816794466489887782993639040109864707530442899276426963345961574577223336606857046857671362398434078794699688855708893416380881237868690274666243524588365539890277953112584848323415351712825987) = true := by decide +kernel
theorem che_28_3_1 : chkE 28 3 17 22 (decH 22 670134122643466831492660145936144082050683402030946193042744722484720764479347690464219577780296024087206551313183608567331228930384909178555932405024870083131180711861353650448024699187684289145379393040999093565720246128221428231995632262849749615058361440217133933256045042851060837546740374111383879057500308099) = true := by decide +kernel
theorem che_28_3_2 : chkE 28 3 22 24 (decH 6 2793924095189918101412202677799495104754511775073172221705331598135159305412630088847225592985001234782991560724565863785876530573756647469416474289431389091064879309734181258326067899502425155254671845047666577451777864324331306894506989063297) = true := by decide +kernel
theorem che_28_3_3 : chkE 28 3 24 28 (decH 4 49478001265637855842597568206740514078451580488446682122784372641775838947658727992701685019961405398910190231360071040867205042357756494470228258191736245739640720788609) = true := by decide +kernel
theorem cove_28_3 : CovBE 28 3 4 28 :=
  CovBE.trans (CovBE.of_chk che_28_3_0) (CovBE.trans (CovBE.of_chk che_28_3_1) (CovBE.trans (CovBE.of_chk che_28_3_2) (CovBE.of_chk che_28_3_3)))

theorem che_28_4_0 : chkE 28 4 5 6 (decH 9 437204835377045639526542442084129477447628569159125269481977035840864661608004899104232440506419339052434986798876822986770033909331338262957240056732613319605897541711900090271413121693644096040017355505290689016025879596245786809558474882371080453132382713916132957555890522484046606111151337236603582017576996066870147) = true := by decide +kernel
theorem che_28_4_1 : chkE 28 4 6 22 (decH 36 41261979494616869381601132808506657592904008685809627167216881718171421443388563403220632638452566055721779514683169853988926070151765984604061430914660433294721075515473253981589956878659441130267977444205076997051978099275575195031643353614706925690906713729583797112024568584136932081626474706043122997206810260721520758364165164163475085805688193601315354135250034599256838159863979818385721272429171859278875435256692195545265699513319417654386895038208957721052148906531800244086818279877279720901094874734428088565034091174965941807300613) = true := by decide +kernel
theorem che_28_4_2 : chkE 28 4 22 28 (decH 7 16702588022566527471085202878161865398363959908142754273189151791966334617840624011080030603911016900253836943587271898044177189472017414525135962195653465708218899235596536961) = true := by decide +kernel
theorem cove_28_4 : CovBE 28 4 5 28 :=
  CovBE.trans (CovBE.of_chk che_28_4_0) (CovBE.trans (CovBE.of_chk che_28_4_1) (CovBE.of_chk che_28_4_2))

theorem che_28_5_0 : chkE 28 5 6 21 (decH 41 1342283465109621070047516442076115308164214542561253265160942444847349072365421932889495034150296567772229993887871114187966404356526583975403793285482192857079399003522917224353732949503409840866625196601197571097470950967823563067141487854021845893677892800900017729323382827582743208512265060464261236673382302365653206247159201516141605131662825038004166256282938663579652798336029744621510076354624005582783739603426148272224563973443453213516403794798115231267317397266135775493621512954007463670919556315612417206959319583573123) = true := by decide +kernel
theorem che_28_5_1 : chkE 28 5 21 28 (decH 7 2986493291102226388568521112171581254986541568930725802831574605942172985629650481520821297234732897286341600790585102324867) = true := by decide +kernel
theorem cove_28_5 : CovBE 28 5 6 28 :=
  CovBE.trans (CovBE.of_chk che_28_5_0) (CovBE.of_chk che_28_5_1)

theorem che_28_6_0 : chkE 28 6 7 19 (decH 24 20062612399041171041394867884606407114779401342942493836900292496327810371268806348239058228808057569386963964749718213645974460085560454442665932771893584920477063091301865322995614303035880289657700111782496951809436211721937606880817305425224165525215859087131938951074917259447088503731276505226333340764652017127630672880090032559070566593842817581477972151000357262112434920944036860544498369048311808591709858739021280490349249217923) = true := by decide +kernel
theorem che_28_6_1 : chkE 28 6 19 28 (decH 11 3150996591292867888661934487609378586539155268613360882532705019840627114223517120246492831480871786034395710453542614405397796587195944899503079281652808711375214306908857979523) = true := by decide +kernel
theorem cove_28_6 : CovBE 28 6 7 28 :=
  CovBE.trans (CovBE.of_chk che_28_6_0) (CovBE.of_chk che_28_6_1)

theorem che_28_7_0 : chkE 28 7 8 28 (decH 20 68374861687086907136366909240915534497482238332525897165586829941912423006802037169737948822024925160223577669329313821774803196227856180461574406118352448042963065222199212985199709536900314022749733522213613561124380988467891422851) = true := by decide +kernel
theorem cove_28_7 : CovBE 28 7 8 28 :=
  CovBE.of_chk che_28_7_0

theorem che_28_8_0 : chkE 28 8 9 28 (decH 7 15827558731030921673637645715439759734431669980946321857165741391054184323794819) = true := by decide +kernel
theorem cove_28_8 : CovBE 28 8 9 28 :=
  CovBE.of_chk che_28_8_0

theorem che_28_9_0 : chkE 28 9 10 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_9 : CovBE 28 9 10 28 :=
  CovBE.of_chk che_28_9_0

theorem che_28_10_0 : chkE 28 10 11 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_10 : CovBE 28 10 11 28 :=
  CovBE.of_chk che_28_10_0

theorem che_28_11_0 : chkE 28 11 12 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_11 : CovBE 28 11 12 28 :=
  CovBE.of_chk che_28_11_0

theorem che_28_12_0 : chkE 28 12 13 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_12 : CovBE 28 12 13 28 :=
  CovBE.of_chk che_28_12_0

theorem che_28_13_0 : chkE 28 13 14 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_13 : CovBE 28 13 14 28 :=
  CovBE.of_chk che_28_13_0

theorem che_28_14_0 : chkE 28 14 15 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_14 : CovBE 28 14 15 28 :=
  CovBE.of_chk che_28_14_0

theorem che_28_15_0 : chkE 28 15 16 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_15 : CovBE 28 15 16 28 :=
  CovBE.of_chk che_28_15_0

theorem che_28_16_0 : chkE 28 16 17 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_16 : CovBE 28 16 17 28 :=
  CovBE.of_chk che_28_16_0

theorem che_28_17_0 : chkE 28 17 18 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_17 : CovBE 28 17 18 28 :=
  CovBE.of_chk che_28_17_0

theorem che_28_18_0 : chkE 28 18 19 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_18 : CovBE 28 18 19 28 :=
  CovBE.of_chk che_28_18_0

theorem che_28_19_0 : chkE 28 19 20 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_19 : CovBE 28 19 20 28 :=
  CovBE.of_chk che_28_19_0

theorem che_28_20_0 : chkE 28 20 21 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_20 : CovBE 28 20 21 28 :=
  CovBE.of_chk che_28_20_0

theorem che_28_21_0 : chkE 28 21 22 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_21 : CovBE 28 21 22 28 :=
  CovBE.of_chk che_28_21_0

theorem che_28_22_0 : chkE 28 22 23 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_22 : CovBE 28 22 23 28 :=
  CovBE.of_chk che_28_22_0

theorem che_28_23_0 : chkE 28 23 24 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_23 : CovBE 28 23 24 28 :=
  CovBE.of_chk che_28_23_0

theorem che_28_24_0 : chkE 28 24 25 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_24 : CovBE 28 24 25 28 :=
  CovBE.of_chk che_28_24_0

theorem che_28_25_0 : chkE 28 25 26 28 (decH 1 0) = true := by decide +kernel
theorem cove_28_25 : CovBE 28 25 26 28 :=
  CovBE.of_chk che_28_25_0

theorem cove_28 : CovQE 28 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_28_2) (CovAE.trans (CovAE.one cove_28_3) (CovAE.trans (CovAE.one cove_28_4) (CovAE.trans (CovAE.one cove_28_5) (CovAE.trans (CovAE.one cove_28_6) (CovAE.trans (CovAE.one cove_28_7) (CovAE.trans (CovAE.one cove_28_8) (CovAE.trans (CovAE.one cove_28_9) (CovAE.trans (CovAE.one cove_28_10) (CovAE.trans (CovAE.one cove_28_11) (CovAE.trans (CovAE.one cove_28_12) (CovAE.trans (CovAE.one cove_28_13) (CovAE.trans (CovAE.one cove_28_14) (CovAE.trans (CovAE.one cove_28_15) (CovAE.trans (CovAE.one cove_28_16) (CovAE.trans (CovAE.one cove_28_17) (CovAE.trans (CovAE.one cove_28_18) (CovAE.trans (CovAE.one cove_28_19) (CovAE.trans (CovAE.one cove_28_20) (CovAE.trans (CovAE.one cove_28_21) (CovAE.trans (CovAE.one cove_28_22) (CovAE.trans (CovAE.one cove_28_23) (CovAE.trans (CovAE.one cove_28_24) (CovAE.one cove_28_25))))))))))))))))))))))))

/-! ### `N = 29` -/

theorem che_29_2_0 : chkE 29 2 3 18 (decH 24 7829799507776949652240989841869244196291214883901467261709358682432507329699129404985360755314495400707938522442768713450470601843420196105362756126224519120251483998422006679084208615287361073619443586002972936869230593538294534816794349379486831221681859375137028170264065748959678122846205797267883065350191363145859) = true := by decide +kernel
theorem che_29_2_1 : chkE 29 2 18 22 (decH 19 498932874836384697420584048966960480650228387665764219165731837661285931623933463208935489046050235471745280500038001640251897358666971308961681028259650212326473624691537235169309248070858802507043972701298182987834808676907547878347368340574957661378553100840105643861091461869376760002132580538439331908865) = true := by decide +kernel
theorem che_29_2_2 : chkE 29 2 22 23 (decH 4 95910172002309487972573077150464547869719149578987779184611995542155966487241737957605819246553539128133462879174874598771747245138568142502691581220566837804777492523084188929) = true := by decide +kernel
theorem che_29_2_3 : chkE 29 2 23 25 (decH 6 1047271267481282591398642457770928866280645507486775598389579725368287075530588684965707155176092463521704749892173567822979930905500687467297326292634624856612800144700235484559015917901874898821528579572411314431624807092273980360281417199511072583086703949724149813375580583054885970065526017) = true := by decide +kernel
theorem che_29_2_4 : chkE 29 2 25 29 (decH 5 11222385422752934487854191687811420755118556312431962741043646204526586167937310618426440341624625874945180839748065097684215817260129241224416593672215365739810907592519431585515965077647833529092589151790145209830858410286247567461633) = true := by decide +kernel
theorem cove_29_2 : CovBE 29 2 3 29 :=
  CovBE.trans (CovBE.of_chk che_29_2_0) (CovBE.trans (CovBE.of_chk che_29_2_1) (CovBE.trans (CovBE.of_chk che_29_2_2) (CovBE.trans (CovBE.of_chk che_29_2_3) (CovBE.of_chk che_29_2_4))))

theorem che_29_3_0 : chkE 29 3 4 5 (decH 11 3682494211854960848293996227385774993579000938204276541261170199165834315596597732719137042268337580784096882286862003314438869975977805454040438260093597400283124667942289105242074638135916506461445729296276126986546145987559937692380952872738593857242739625163388791592576546848341712685389598003408282398138954274424738719858594431536708553911931507568326043483711420657845182580761519684683483366019) = true := by decide +kernel
theorem che_29_3_1 : chkE 29 3 5 22 (decH 34 5932295306528757969437990056230648384077508368346560142617133017072398263396487007606083270135298900483664779676539502874028592775616885293462679244031265726694656970779002654799447578122066827298597414715744364426361718293049293129289793845732804761816140998037601048960163769112415437741345834449117242048914101482020782795101219470924627821324691700218317401738697043081950402646752238897064943473583971875139169977316393093) = true := by decide +kernel
theorem che_29_3_2 : chkE 29 3 22 23 (decH 4 95910635905106304002314034468979251332415945246994940023645491677912727024774219851369872368346652161658153323653484380748496268420639288443831042707217310991581819333626858753) = true := by decide +kernel
theorem che_29_3_3 : chkE 29 3 23 25 (decH 6 751383614807701292810789133325081034536952301256583449149334187869768161624433986827844229553992976206614177139133369363684077400953793068802837573874595243030874055788690920740362934867624651040069175607794180159246821086416229175901944003456372346113) = true := by decide +kernel
theorem che_29_3_4 : chkE 29 3 25 29 (decH 4 6349448971017392303971826793668007897057136533876675770040290487335622367037167212306638539055213643834555555915254799150911685168385) = true := by decide +kernel
theorem cove_29_3 : CovBE 29 3 4 29 :=
  CovBE.trans (CovBE.of_chk che_29_3_0) (CovBE.trans (CovBE.of_chk che_29_3_1) (CovBE.trans (CovBE.of_chk che_29_3_2) (CovBE.trans (CovBE.of_chk che_29_3_3) (CovBE.of_chk che_29_3_4))))

theorem che_29_4_0 : chkE 29 4 5 20 (decH 40 59763570381364198962016878565806507420855245678213465427053374192731426817334483421407131425939080048804125086379851936045303093668005180867053378450494666838042089833523173796575409911661005744357037191425897589973802168285510484646616735891743036964194333369952138395274612421309418060696247401964159689777005111796874100931077045932215608616972753936526562086082474007721379600011379664509832741888580000908072994384655726534736272642671023843930766303038696704998115188307208272389220837667827519263556615766253274077465293860793696476889425040140859654302352259) = true := by decide +kernel
theorem che_29_4_1 : chkE 29 4 20 29 (decH 18 9332992303471016357670295210588899372833220023699328926128684633644408891613814799806325972015543246687201970201114286004847010798948847825832188120808066619672874845820304446189038450588138234016562152912512929889629162403890136361947412312129947526923111746687221935007970773091344878428062948133654066168153108474512601465632401875536400982524035) = true := by decide +kernel
theorem cove_29_4 : CovBE 29 4 5 29 :=
  CovBE.trans (CovBE.of_chk che_29_4_0) (CovBE.of_chk che_29_4_1)

theorem che_29_5_0 : chkE 29 5 6 7 (decH 8 136845699949229400934297752107853871945653838008489279084274767488045486046388498674693563472795709055761112949810899142650439523758781415231458339268834806085294736739435333556678231089702810277010454224449006499475505528562456595602744115768146371812829922633273783141507) = true := by decide +kernel
theorem che_29_5_1 : chkE 29 5 7 22 (decH 36 2620376859170709326208126510221752426328989601156963258262313102518530086112610487226979971276690786820710687671317080424443853753942296180177969975934602202888174337057961260554402092727341906887112678656986386445712846940864461797938599572937985643813963945706262528892580720543591844337656824609534507646287261581169478635395407774362341539515845380263143743234406523102556243371651639383291277744833884071308914706318815781117717951676581261696364841628517260268529410595480691691944669371088901) = true := by decide +kernel
theorem che_29_5_2 : chkE 29 5 22 29 (decH 7 16764409685740579696415567455960241119964087736454620880777767101980631769652923751771719896779431929065200617574608100999737649203359333187796480873221239862977654822701157633) = true := by decide +kernel
theorem cove_29_5 : CovBE 29 5 6 29 :=
  CovBE.trans (CovBE.of_chk che_29_5_0) (CovBE.trans (CovBE.of_chk che_29_5_1) (CovBE.of_chk che_29_5_2))

theorem che_29_6_0 : chkE 29 6 7 22 (decH 39 7093620200505801198616381584038392010107317609101691544775317912689547166920540051924059084251420638833246279646406163574984263737972494598320235190082743740664185291790079453398118931572160235721648295002562733608686060864952703280540723047035743226751004995338747550378745529159000752702613908007594228040757265500087536863256036986829602774420904258426169977499966396540719018858600358920968694616676652813554077214490458308224433603717030135647773643607180811384286717428627855411311651172707637874500060547) = true := by decide +kernel
theorem che_29_6_1 : chkE 29 6 22 29 (decH 4 182285487235040915114801912470474258980619549861082035456746465920760171825472015617) = true := by decide +kernel
theorem cove_29_6 : CovBE 29 6 7 29 :=
  CovBE.trans (CovBE.of_chk che_29_6_0) (CovBE.of_chk che_29_6_1)

theorem che_29_7_0 : chkE 29 7 8 29 (decH 23 34847598362747041670034241853804837047981795904703818950660957781531094479491701064342180296030410556839740182333320402442460613574060392679028285393011867352604295819082974029913874342364265248684761828712371724603827396437804722634835665323382165142199145740710986888615103501163845795963397159306185914735588667799926499943864997136046587059426705267260997582068068368536775852460319558387331) = true := by decide +kernel
theorem cove_29_7 : CovBE 29 7 8 29 :=
  CovBE.of_chk che_29_7_0

theorem che_29_8_0 : chkE 29 8 9 29 (decH 12 3815996330190873370946324253027679539549101624829761113533530926111672007340958269338590236093813682233986034313685492977666901891) = true := by decide +kernel
theorem cove_29_8 : CovBE 29 8 9 29 :=
  CovBE.of_chk che_29_8_0

theorem che_29_9_0 : chkE 29 9 10 29 (decH 3 101746523556485829763) = true := by decide +kernel
theorem cove_29_9 : CovBE 29 9 10 29 :=
  CovBE.of_chk che_29_9_0

theorem che_29_10_0 : chkE 29 10 11 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_10 : CovBE 29 10 11 29 :=
  CovBE.of_chk che_29_10_0

theorem che_29_11_0 : chkE 29 11 12 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_11 : CovBE 29 11 12 29 :=
  CovBE.of_chk che_29_11_0

theorem che_29_12_0 : chkE 29 12 13 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_12 : CovBE 29 12 13 29 :=
  CovBE.of_chk che_29_12_0

theorem che_29_13_0 : chkE 29 13 14 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_13 : CovBE 29 13 14 29 :=
  CovBE.of_chk che_29_13_0

theorem che_29_14_0 : chkE 29 14 15 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_14 : CovBE 29 14 15 29 :=
  CovBE.of_chk che_29_14_0

theorem che_29_15_0 : chkE 29 15 16 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_15 : CovBE 29 15 16 29 :=
  CovBE.of_chk che_29_15_0

theorem che_29_16_0 : chkE 29 16 17 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_16 : CovBE 29 16 17 29 :=
  CovBE.of_chk che_29_16_0

theorem che_29_17_0 : chkE 29 17 18 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_17 : CovBE 29 17 18 29 :=
  CovBE.of_chk che_29_17_0

theorem che_29_18_0 : chkE 29 18 19 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_18 : CovBE 29 18 19 29 :=
  CovBE.of_chk che_29_18_0

theorem che_29_19_0 : chkE 29 19 20 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_19 : CovBE 29 19 20 29 :=
  CovBE.of_chk che_29_19_0

theorem che_29_20_0 : chkE 29 20 21 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_20 : CovBE 29 20 21 29 :=
  CovBE.of_chk che_29_20_0

theorem che_29_21_0 : chkE 29 21 22 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_21 : CovBE 29 21 22 29 :=
  CovBE.of_chk che_29_21_0

theorem che_29_22_0 : chkE 29 22 23 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_22 : CovBE 29 22 23 29 :=
  CovBE.of_chk che_29_22_0

theorem che_29_23_0 : chkE 29 23 24 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_23 : CovBE 29 23 24 29 :=
  CovBE.of_chk che_29_23_0

theorem che_29_24_0 : chkE 29 24 25 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_24 : CovBE 29 24 25 29 :=
  CovBE.of_chk che_29_24_0

theorem che_29_25_0 : chkE 29 25 26 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_25 : CovBE 29 25 26 29 :=
  CovBE.of_chk che_29_25_0

theorem che_29_26_0 : chkE 29 26 27 29 (decH 1 0) = true := by decide +kernel
theorem cove_29_26 : CovBE 29 26 27 29 :=
  CovBE.of_chk che_29_26_0

theorem cove_29 : CovQE 29 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_29_2) (CovAE.trans (CovAE.one cove_29_3) (CovAE.trans (CovAE.one cove_29_4) (CovAE.trans (CovAE.one cove_29_5) (CovAE.trans (CovAE.one cove_29_6) (CovAE.trans (CovAE.one cove_29_7) (CovAE.trans (CovAE.one cove_29_8) (CovAE.trans (CovAE.one cove_29_9) (CovAE.trans (CovAE.one cove_29_10) (CovAE.trans (CovAE.one cove_29_11) (CovAE.trans (CovAE.one cove_29_12) (CovAE.trans (CovAE.one cove_29_13) (CovAE.trans (CovAE.one cove_29_14) (CovAE.trans (CovAE.one cove_29_15) (CovAE.trans (CovAE.one cove_29_16) (CovAE.trans (CovAE.one cove_29_17) (CovAE.trans (CovAE.one cove_29_18) (CovAE.trans (CovAE.one cove_29_19) (CovAE.trans (CovAE.one cove_29_20) (CovAE.trans (CovAE.one cove_29_21) (CovAE.trans (CovAE.one cove_29_22) (CovAE.trans (CovAE.one cove_29_23) (CovAE.trans (CovAE.one cove_29_24) (CovAE.trans (CovAE.one cove_29_25) (CovAE.one cove_29_26)))))))))))))))))))))))))

/-! ### `N = 30` -/

theorem che_30_2_0 : chkE 30 2 3 4 (decH 13 22472600453100079017773004706826055433164242344440914217744302614268766943135561296910079668559009366276971083706461050578571247519150739657297347984695145637219101221375138138139095528921643233265115264935219846591256369623208456547270475661908206696974182817938683173336285889256487818377182555697277745215825373013327858356697294229172405207179393778551583184501269541350697079440092876797753699811523984641545851957446555041794703830869317696044694252690224395820992365523006477616332931) = true := by decide +kernel
theorem che_30_2_1 : chkE 30 2 4 23 (decH 31 82241155512071910390607861058432812236847784846786232063930368799642458016576330600646516514409101970821210682779544852496406446555166712059143873043075353240861054848491906202329104413412495033868583839153908717396862589505766771025747726269949300349646751398848254530403157008124649487504008421183538171430638044267417113670467715) = true := by decide +kernel
theorem che_30_2_2 : chkE 30 2 23 24 (decH 4 217737244185189497226655697574620522229929037807065026425800202864528879840859770461344270556576471967218815606852269498322361397600057312357124647724455305543071658017418031810252161) = true := by decide +kernel
theorem che_30_2_3 : chkE 30 2 24 26 (decH 6 35984126388752934606094113501229658878169625588718358878183667284564182171029103651542944915315065185173899009064548107964517334260740366667486116220419458188426802464778720835756152575709628608991147602007231297329197096300634229526069128126711092338493020302453138421406409563728317299588575100882292097) = true := by decide +kernel
theorem che_30_2_4 : chkE 30 2 26 30 (decH 5 238591322308230888608258352684052973036895917914425840448437096332404153075228529616929051766066963098585263103803566624345764179644778018116903429530176960887691073023070102235722541830239906254677344673304945741607635658601133375404072373633) = true := by decide +kernel
theorem cove_30_2 : CovBE 30 2 3 30 :=
  CovBE.trans (CovBE.of_chk che_30_2_0) (CovBE.trans (CovBE.of_chk che_30_2_1) (CovBE.trans (CovBE.of_chk che_30_2_2) (CovBE.trans (CovBE.of_chk che_30_2_3) (CovBE.of_chk che_30_2_4))))

theorem che_30_3_0 : chkE 30 3 4 18 (decH 27 593262706101313311401959999622962527680029168447765056773697286351365657989083184656390727978958978826895313795135072349396955985336099281803809038511747534260194861815908390255889456733999516056518878157392512021428719929345053942456188740394815347834720944805898124157285159385903689515433858220371514895277198721068628054381830161277119236968265505377685598808744831580873903107243378697690013589554872963) = true := by decide +kernel
theorem che_30_3_1 : chkE 30 3 18 23 (decH 25 259507329534700207658734263784319754782913931816781853391265518797853461904253402193148385676941073349119404944600723695207117663136673204862499463136933247360275095069869452295712428870101337625626562938685890444690132953012674455736540320677673643257280201929151376886133271947897685212548402019090563) = true := by decide +kernel
theorem che_30_3_2 : chkE 30 3 23 24 (decH 4 1220459463612094991599532051342232921220073245002977869595100317599140771159175709687487139914161373560170982079477450586835001654276033921) = true := by decide +kernel
theorem che_30_3_3 : chkE 30 3 24 26 (decH 6 216818962959080630079475693040504931013455682884551801173735303182725947827542433998307434184757128689115526566299308234910411488327827726863224309618883250459905845849996812152200138334094461035376404238076429240904431692759169240114922152520798380982733671809) = true := by decide +kernel
theorem che_30_3_4 : chkE 30 3 26 30 (decH 4 234335307446592629456006697531372702247345719389920399370648490827825612407834042643632697394671725689625182790550147249056291190395977742661762416611838233086900190422981957791403393) = true := by decide +kernel
theorem cove_30_3 : CovBE 30 3 4 30 :=
  CovBE.trans (CovBE.of_chk che_30_3_0) (CovBE.trans (CovBE.of_chk che_30_3_1) (CovBE.trans (CovBE.of_chk che_30_3_2) (CovBE.trans (CovBE.of_chk che_30_3_3) (CovBE.of_chk che_30_3_4))))

theorem che_30_4_0 : chkE 30 4 5 6 (decH 10 2286196385577869456357072585567967852504102307786915028937612714915547764584496759581494749241777784626154601473540072603640957936469224394897792976482658139450740327467329090674474782864325412558377944996098531349150500765975377591869601553619068993446954875714166415631151694776271309889512621573110785318041470120891974760709945514936429374838281388931) = true := by decide +kernel
theorem che_30_4_1 : chkE 30 4 6 23 (decH 41 3994198978618661232261901179025587825055603196751939039229643223780354563737765546441672859003137569081217554184135981674256118846795675155654399256234940777385294967698140517320378686564458052641884733952360645154993733452169414098093921891245070259771486834540752517532526011533809940704498145780416485565990548958358421082312338623375794172981868258916850878852006053264961293142635143767640137427083258220087073440609553346679138920855284881361847361891838906987824372894364822337849098809570518968004655467100864585985597463333138521266394410860736758689507326370863523468645085556505218928888228629190184737007012397813315613004873733) = true := by decide +kernel
theorem che_30_4_2 : chkE 30 4 23 30 (decH 10 102768586446687553587170165241928135055891339140739335108931121995911165858902267569295711431984011988883524113642989192452391645560172911119585212093101258160780949585210333814437091881246048371669903450624654683587494249431619203) = true := by decide +kernel
theorem cove_30_4 : CovBE 30 4 5 30 :=
  CovBE.trans (CovBE.of_chk che_30_4_0) (CovBE.trans (CovBE.of_chk che_30_4_1) (CovBE.of_chk che_30_4_2))

theorem che_30_5_0 : chkE 30 5 6 20 (decH 38 130650752453235359647432607128418697597988607726343786359376047899790467142590752262384828453295408410002047695605866759694606571947645929999002147485349510918463189375231697575754826861849338915723357395264007960864589639488858116612269692194599324425955757555443762749903045239996328939192056303796798202464401186477041561147579310339564162352532920186012712142920846196379355901815409806437732351656109525874538474572855719687117113137541955441240591546588366618494918271362870136245929057255783615043596537840771) = true := by decide +kernel
theorem che_30_5_1 : chkE 30 5 20 30 (decH 20 1011885053121352505262018587127844120986963829468700867028337399434470958572103096570283547225003078173022296208019886314455279725517292803215010027768929541787973765391568129001278009962859384633113407268375729528802114780947954562937560767460631151635349120793681419406381969995311107185143483113370819441139697641452949028782211) = true := by decide +kernel
theorem cove_30_5 : CovBE 30 5 6 30 :=
  CovBE.trans (CovBE.of_chk che_30_5_0) (CovBE.of_chk che_30_5_1)

theorem che_30_6_0 : chkE 30 6 7 10 (decH 17 42756435952839378354598167788489614643100226796652693485505643880958152102522846550421116937547718190350248018436553572885413093238180866268739256973523733276652084037193858210234527864732756594686034509141972969910949279363640589681710045163591027222159925150435218783239887659445659446781423388979666561510896857148297299167541874172996765354132808478453140759001054005572178065116677507) = true := by decide +kernel
theorem che_30_6_1 : chkE 30 6 10 30 (decH 29 8665260376063739572710778517885943789877695372117715196257873904697893881965780226272318532210148871085647351728575790310174006174092303414279225300114372990942726195948000961088787809387226717475291352007351064245520939320220330683285102586197688587361175040228593324643883821628069132116208307014150895377709273253020300599280880386643948082351327304908535196400142945395984111189429306811153835425702299611936022093662440512209336918643500979833499881380314624223899955620986885) = true := by decide +kernel
theorem cove_30_6 : CovBE 30 6 7 30 :=
  CovBE.trans (CovBE.of_chk che_30_6_0) (CovBE.of_chk che_30_6_1)

theorem che_30_7_0 : chkE 30 7 8 30 (decH 31 9671801136758191984225314965038207326852388524612428635944428048947481197184484593495144825632561097745171087863900184204102011797455093142322395343219397040587950124056907192877658339109672059696091174367151423991809975646354001266799363429987492762260382135938995958839702403080347435467147956741835229142587704583794706745176421219235486087405848898748136985381828364136313615804554028702699106307600245868163) = true := by decide +kernel
theorem cove_30_7 : CovBE 30 7 8 30 :=
  CovBE.of_chk che_30_7_0

theorem che_30_8_0 : chkE 30 8 9 30 (decH 14 4920529161941125670161561515316852640754366354964223941634782707778502566500053806972876819125393675534177256552404033006231376620085390703265630717904606821095640964685446904128202655619) = true := by decide +kernel
theorem cove_30_8 : CovBE 30 8 9 30 :=
  CovBE.of_chk che_30_8_0

theorem che_30_9_0 : chkE 30 9 10 30 (decH 6 1105806019852980676513391386141828953873358814113989050517635) = true := by decide +kernel
theorem cove_30_9 : CovBE 30 9 10 30 :=
  CovBE.of_chk che_30_9_0

theorem che_30_10_0 : chkE 30 10 11 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_10 : CovBE 30 10 11 30 :=
  CovBE.of_chk che_30_10_0

theorem che_30_11_0 : chkE 30 11 12 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_11 : CovBE 30 11 12 30 :=
  CovBE.of_chk che_30_11_0

theorem che_30_12_0 : chkE 30 12 13 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_12 : CovBE 30 12 13 30 :=
  CovBE.of_chk che_30_12_0

theorem che_30_13_0 : chkE 30 13 14 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_13 : CovBE 30 13 14 30 :=
  CovBE.of_chk che_30_13_0

theorem che_30_14_0 : chkE 30 14 15 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_14 : CovBE 30 14 15 30 :=
  CovBE.of_chk che_30_14_0

theorem che_30_15_0 : chkE 30 15 16 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_15 : CovBE 30 15 16 30 :=
  CovBE.of_chk che_30_15_0

theorem che_30_16_0 : chkE 30 16 17 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_16 : CovBE 30 16 17 30 :=
  CovBE.of_chk che_30_16_0

theorem che_30_17_0 : chkE 30 17 18 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_17 : CovBE 30 17 18 30 :=
  CovBE.of_chk che_30_17_0

theorem che_30_18_0 : chkE 30 18 19 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_18 : CovBE 30 18 19 30 :=
  CovBE.of_chk che_30_18_0

theorem che_30_19_0 : chkE 30 19 20 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_19 : CovBE 30 19 20 30 :=
  CovBE.of_chk che_30_19_0

theorem che_30_20_0 : chkE 30 20 21 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_20 : CovBE 30 20 21 30 :=
  CovBE.of_chk che_30_20_0

theorem che_30_21_0 : chkE 30 21 22 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_21 : CovBE 30 21 22 30 :=
  CovBE.of_chk che_30_21_0

theorem che_30_22_0 : chkE 30 22 23 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_22 : CovBE 30 22 23 30 :=
  CovBE.of_chk che_30_22_0

theorem che_30_23_0 : chkE 30 23 24 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_23 : CovBE 30 23 24 30 :=
  CovBE.of_chk che_30_23_0

theorem che_30_24_0 : chkE 30 24 25 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_24 : CovBE 30 24 25 30 :=
  CovBE.of_chk che_30_24_0

theorem che_30_25_0 : chkE 30 25 26 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_25 : CovBE 30 25 26 30 :=
  CovBE.of_chk che_30_25_0

theorem che_30_26_0 : chkE 30 26 27 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_26 : CovBE 30 26 27 30 :=
  CovBE.of_chk che_30_26_0

theorem che_30_27_0 : chkE 30 27 28 30 (decH 1 0) = true := by decide +kernel
theorem cove_30_27 : CovBE 30 27 28 30 :=
  CovBE.of_chk che_30_27_0

theorem cove_30 : CovQE 30 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_30_2) (CovAE.trans (CovAE.one cove_30_3) (CovAE.trans (CovAE.one cove_30_4) (CovAE.trans (CovAE.one cove_30_5) (CovAE.trans (CovAE.one cove_30_6) (CovAE.trans (CovAE.one cove_30_7) (CovAE.trans (CovAE.one cove_30_8) (CovAE.trans (CovAE.one cove_30_9) (CovAE.trans (CovAE.one cove_30_10) (CovAE.trans (CovAE.one cove_30_11) (CovAE.trans (CovAE.one cove_30_12) (CovAE.trans (CovAE.one cove_30_13) (CovAE.trans (CovAE.one cove_30_14) (CovAE.trans (CovAE.one cove_30_15) (CovAE.trans (CovAE.one cove_30_16) (CovAE.trans (CovAE.one cove_30_17) (CovAE.trans (CovAE.one cove_30_18) (CovAE.trans (CovAE.one cove_30_19) (CovAE.trans (CovAE.one cove_30_20) (CovAE.trans (CovAE.one cove_30_21) (CovAE.trans (CovAE.one cove_30_22) (CovAE.trans (CovAE.one cove_30_23) (CovAE.trans (CovAE.one cove_30_24) (CovAE.trans (CovAE.one cove_30_25) (CovAE.trans (CovAE.one cove_30_26) (CovAE.one cove_30_27))))))))))))))))))))))))))

/-! ### `N = 31` -/

theorem che_31_2_0 : chkE 31 2 3 18 (decH 20 6844975442160373612070310903515117456609921586312489952676360668231107780443141324029690469348373825884617156146949935219460897068652336660817764878725450364057565140212693550250043076896401175626188599485583584078600626629126226053778885136218146572096601885657607687602604188810116981357616097757183491955703140443521051869069443) = true := by decide +kernel
theorem che_31_2_1 : chkE 31 2 18 22 (decH 23 695900310675979426939770164391292356763834034919233170564942860198277039124233196055835658004776367190369447451658609909327621342383106720232508969544019058351629803462825677369130342468176927613563239814653916150628880268850212292574382323188570653329068261927142837918658006817113719662679922229169458660700905576588865327410744394237667169255476737) = true := by decide +kernel
theorem che_31_2_2 : chkE 31 2 22 23 (decH 5 13243187940920712087881995289603640672015439535626084095940696011136528252193982263826555006825582081) = true := by decide +kernel
theorem che_31_2_3 : chkE 31 2 23 24 (decH 5 751830883044618083886984234417119495228511135431246744057570418087938038841951252939668945638500519030197302995924230751370913849738472522110076932644554365459982839387415502810933045199646275043586419250060158009360814657313139886974430579858411408897) = true := by decide +kernel
theorem che_31_2_4 : chkE 31 2 24 25 (decH 4 456900157382469344214884343215003690335780382885673451931599310609455375611733120885530182979889636021550831828266459543983397119384071012552252409886961525290639878326030923591925283212801) = true := by decide +kernel
theorem che_31_2_5 : chkE 31 2 25 27 (decH 6 1331392709857805121115166939046935800102411426994783689266319385530055439403678378864924826293097973607339958391213984557535812793894003632649549103752850856512937320992567415543001363319629041490422243245150049860822198299017817682645263743398422915129814702308283572496796687593118531607646948697595385499156270593) = true := by decide +kernel
theorem che_31_2_6 : chkE 31 2 27 31 (decH 5 866386494867557873293000911230112057370671004816241329648656080022363964339037139107729991815345774436384824217034229771176109119255438517887557998925639296222843501362301717367002212684171457033698370771096223406408786368602085684859430246835642863105) = true := by decide +kernel
theorem cove_31_2 : CovBE 31 2 3 31 :=
  CovBE.trans (CovBE.of_chk che_31_2_0) (CovBE.trans (CovBE.of_chk che_31_2_1) (CovBE.trans (CovBE.of_chk che_31_2_2) (CovBE.trans (CovBE.of_chk che_31_2_3) (CovBE.trans (CovBE.of_chk che_31_2_4) (CovBE.trans (CovBE.of_chk che_31_2_5) (CovBE.of_chk che_31_2_6))))))

theorem che_31_3_0 : chkE 31 3 4 5 (decH 12 118706740923951933590491051194730471271874630654324696140472058568517903434821224760491268792073770919144212684968089563020276315163449484285734980586543487200549622002757001398241336685125569283665703331215450880708508115782051133521097867119921944314829609523113383475688310030763692958991396539109381309079267531084881323919795445800451378223620846397349895069718290351930380839809606916773846416072808706763167905948556597358471694222329614671543570554165245262732381119895685548212273795) = true := by decide +kernel
theorem che_31_3_1 : chkE 31 3 5 22 (decH 33 46451063809290191425503001127609837765876337720352701232722483097466607016516208232202745406576229325991451712383104950765077536772309240671371373579420993437124755100407861347001763142322774114580877838478582520799661685762341380616365254365392887701041130524205628458536388323245228993037569085104300641876773007603186772529528818641016529376544236661904251243386342772408959368502984449421602713494645096578838161654924072710008157995802837635) = true := by decide +kernel
theorem che_31_3_2 : chkE 31 3 22 25 (decH 12 6423636016118290494849591687178247077055311136538560591970114150662844566294485923120074095874584871741201493666223228672604724770203755863158972613035271737859919555068947028959153226767879226954518530391040033539602210809185588979534267260574423586963639772128862449715971548433127952180252985199562643463558585891762358028344097477179012531929219) = true := by decide +kernel
theorem che_31_3_3 : chkE 31 3 25 27 (decH 6 58302694942124267817079889999086164107540425653134954982695636780502584016710592519430255169416439159042610186845582636053989878109920598786684427775187856179390398482823869514776101917550495830340880044825964186408719523279016133273253672098470883885231777534030728705) = true := by decide +kernel
theorem che_31_3_4 : chkE 31 3 27 31 (decH 4 1716419603085015448749474300596574041421225138461612922213214309466436942734631536350241117507400219812142239242972886377021955752154139807233) = true := by decide +kernel
theorem cove_31_3 : CovBE 31 3 4 31 :=
  CovBE.trans (CovBE.of_chk che_31_3_0) (CovBE.trans (CovBE.of_chk che_31_3_1) (CovBE.trans (CovBE.of_chk che_31_3_2) (CovBE.trans (CovBE.of_chk che_31_3_3) (CovBE.of_chk che_31_3_4))))

theorem che_31_4_0 : chkE 31 4 5 19 (decH 33 174162840952566445282235709333090992982720306441637741204869744132232541971634936595835825593547453324340582858340201636085605177497765847623751383509640687426686660439539618142755989306566487748752909069107294074360387968370015542452532075295011102148151343231068632710787416223834819772264151547805908082584180934796891931844965066439946549215552455737078205856372541391733739615456921086270527656064710198853383274136184029681379238382061240313815625352745635777557403249177338012431166303629884725691368547042179) = true := by decide +kernel
theorem che_31_4_1 : chkE 31 4 19 24 (decH 25 14552206547436538978793101189812468435418666803233743249393825932558081790507583802063533253236298115589971431066542672447542741246468674170923666321379081804880887017421818392001273378665887541950473390051411612265417475288654770289209713800106521610134033345369351463141557075394302659598891342044233808590332798041461262396858130045962107905408089375125199342683925532251025074712351513564313207731189358560131) = true := by decide +kernel
theorem che_31_4_2 : chkE 31 4 24 31 (decH 10 1571837546190823618029529718126385989669258033725766562981434501575459266068201411582918348986048823629979653699719015592108644851002318787039649623946605837582483445531292748837068872657487596068822717347412877503893011954356574962601546374646877889088772518935129830346781708949813763668485061850824340034304870559944975887652924771841) = true := by decide +kernel
theorem cove_31_4 : CovBE 31 4 5 31 :=
  CovBE.trans (CovBE.of_chk che_31_4_0) (CovBE.trans (CovBE.of_chk che_31_4_1) (CovBE.of_chk che_31_4_2))

theorem che_31_5_0 : chkE 31 5 6 7 (decH 9 16225952765149289550644775618655422496320354353230145982364195414679077605259150148702434413530163199731791090602414253586516095522672163728406663560458046770663570197198035077659662321044254290826962316148350846838299144276241489111733732114674277944626546913864873983010439739958053700411592724536248732377735468175133562238020257659133800298957554819) = true := by decide +kernel
theorem che_31_5_1 : chkE 31 5 7 23 (decH 41 107242900742430914737826883039228718918677811244632859858968546631612299243948996386730489833068271048104943812830530041708854895965167914247032998988164332920041838132368769103552773530985728700894276959671546610982794336767016628840067848334874351784276890218168385845087914095590277731824209195622555507489249866131886009900934112273482750760753804957989449782895404906518937250298811898868331034837989997157969112047484344703773808692468772479738214800636119631872418021323629512665349975263932270770282793412529598893878374051924945789408823629404474811189332349655819643763730599762985093) = true := by decide +kernel
theorem che_31_5_2 : chkE 31 5 23 31 (decH 11 7432564268230378701636466563013594984166440641462402664803800091097605273455284777106524784477275177359006398022578908767328876520959906127557920223925789509403375143022462339091635923470300533665784225605212155785962699982434917593687020271621763) = true := by decide +kernel
theorem cove_31_5 : CovBE 31 5 6 31 :=
  CovBE.trans (CovBE.of_chk che_31_5_0) (CovBE.trans (CovBE.of_chk che_31_5_1) (CovBE.of_chk che_31_5_2))

theorem che_31_6_0 : chkE 31 6 7 21 (decH 38 1146761127807657375929256310838812733450272255268276926434685394359430591867335939968649892178856064884670110836820660708875668973045035472750052753630502555916534173184171793714397760010230687776425315077469661780690994142119036753154478383754804760225003275648444565557308827518628991920806604388391793379624551206138751673203134103931706202923316197311357538296913792079633303605461167316000176347544292309081148057278932555732781405447785560446081956919731582560400030442781576736117114243) = true := by decide +kernel
theorem che_31_6_1 : chkE 31 6 21 31 (decH 16 200046254546878345861688891074167581924690777946662360979979749159600578202690464962860541721499638755261129590187302940622932676999376459836484786848998789763496249727525426962115396603775222026329043223463953734964532463779330030184119519657081226478886081667) = true := by decide +kernel
theorem cove_31_6 : CovBE 31 6 7 31 :=
  CovBE.trans (CovBE.of_chk che_31_6_0) (CovBE.of_chk che_31_6_1)

theorem che_31_7_0 : chkE 31 7 8 21 (decH 24 4561709920162950547747296210996849145937115487084941276523878774563030839349171357912428699796585544102086030079853013007809567982470452586025721688230046966905357420874469378176367128479324942078261919451380197786741428945280066794886229175168146684815296532504502699098350362509914818626682340075458593411177020520803532359449223153812340306453807009688203462869810046187549632500240843098832537926649480614544011103542756995) = true := by decide +kernel
theorem che_31_7_1 : chkE 31 7 21 31 (decH 11 6641576306804667764220471289152956787188773292314245755352539377315814595661441200305884389830037342077739481598958085235948510165768541045999481274615386073526021391413261233236759683) = true := by decide +kernel
theorem cove_31_7 : CovBE 31 7 8 31 :=
  CovBE.trans (CovBE.of_chk che_31_7_0) (CovBE.of_chk che_31_7_1)

theorem che_31_8_0 : chkE 31 8 9 31 (decH 20 5374520148322220347576183691129009480001346440592725734938828201412730359884731016578182687307648636407682050279648878822936145429815571571818186332425628104736484198757567403419996963914801844645402896372438338644769986733616260566468244179997706115) = true := by decide +kernel
theorem cove_31_8 : CovBE 31 8 9 31 :=
  CovBE.of_chk che_31_8_0

theorem che_31_9_0 : chkE 31 9 10 31 (decH 7 16761132457408954399062062184687273790935230309104066607721474508847609290999939) = true := by decide +kernel
theorem cove_31_9 : CovBE 31 9 10 31 :=
  CovBE.of_chk che_31_9_0

theorem che_31_10_0 : chkE 31 10 11 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_10 : CovBE 31 10 11 31 :=
  CovBE.of_chk che_31_10_0

theorem che_31_11_0 : chkE 31 11 12 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_11 : CovBE 31 11 12 31 :=
  CovBE.of_chk che_31_11_0

theorem che_31_12_0 : chkE 31 12 13 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_12 : CovBE 31 12 13 31 :=
  CovBE.of_chk che_31_12_0

theorem che_31_13_0 : chkE 31 13 14 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_13 : CovBE 31 13 14 31 :=
  CovBE.of_chk che_31_13_0

theorem che_31_14_0 : chkE 31 14 15 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_14 : CovBE 31 14 15 31 :=
  CovBE.of_chk che_31_14_0

theorem che_31_15_0 : chkE 31 15 16 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_15 : CovBE 31 15 16 31 :=
  CovBE.of_chk che_31_15_0

theorem che_31_16_0 : chkE 31 16 17 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_16 : CovBE 31 16 17 31 :=
  CovBE.of_chk che_31_16_0

theorem che_31_17_0 : chkE 31 17 18 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_17 : CovBE 31 17 18 31 :=
  CovBE.of_chk che_31_17_0

theorem che_31_18_0 : chkE 31 18 19 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_18 : CovBE 31 18 19 31 :=
  CovBE.of_chk che_31_18_0

theorem che_31_19_0 : chkE 31 19 20 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_19 : CovBE 31 19 20 31 :=
  CovBE.of_chk che_31_19_0

theorem che_31_20_0 : chkE 31 20 21 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_20 : CovBE 31 20 21 31 :=
  CovBE.of_chk che_31_20_0

theorem che_31_21_0 : chkE 31 21 22 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_21 : CovBE 31 21 22 31 :=
  CovBE.of_chk che_31_21_0

theorem che_31_22_0 : chkE 31 22 23 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_22 : CovBE 31 22 23 31 :=
  CovBE.of_chk che_31_22_0

theorem che_31_23_0 : chkE 31 23 24 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_23 : CovBE 31 23 24 31 :=
  CovBE.of_chk che_31_23_0

theorem che_31_24_0 : chkE 31 24 25 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_24 : CovBE 31 24 25 31 :=
  CovBE.of_chk che_31_24_0

theorem che_31_25_0 : chkE 31 25 26 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_25 : CovBE 31 25 26 31 :=
  CovBE.of_chk che_31_25_0

theorem che_31_26_0 : chkE 31 26 27 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_26 : CovBE 31 26 27 31 :=
  CovBE.of_chk che_31_26_0

theorem che_31_27_0 : chkE 31 27 28 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_27 : CovBE 31 27 28 31 :=
  CovBE.of_chk che_31_27_0

theorem che_31_28_0 : chkE 31 28 29 31 (decH 1 0) = true := by decide +kernel
theorem cove_31_28 : CovBE 31 28 29 31 :=
  CovBE.of_chk che_31_28_0

theorem cove_31 : CovQE 31 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_31_2) (CovAE.trans (CovAE.one cove_31_3) (CovAE.trans (CovAE.one cove_31_4) (CovAE.trans (CovAE.one cove_31_5) (CovAE.trans (CovAE.one cove_31_6) (CovAE.trans (CovAE.one cove_31_7) (CovAE.trans (CovAE.one cove_31_8) (CovAE.trans (CovAE.one cove_31_9) (CovAE.trans (CovAE.one cove_31_10) (CovAE.trans (CovAE.one cove_31_11) (CovAE.trans (CovAE.one cove_31_12) (CovAE.trans (CovAE.one cove_31_13) (CovAE.trans (CovAE.one cove_31_14) (CovAE.trans (CovAE.one cove_31_15) (CovAE.trans (CovAE.one cove_31_16) (CovAE.trans (CovAE.one cove_31_17) (CovAE.trans (CovAE.one cove_31_18) (CovAE.trans (CovAE.one cove_31_19) (CovAE.trans (CovAE.one cove_31_20) (CovAE.trans (CovAE.one cove_31_21) (CovAE.trans (CovAE.one cove_31_22) (CovAE.trans (CovAE.one cove_31_23) (CovAE.trans (CovAE.one cove_31_24) (CovAE.trans (CovAE.one cove_31_25) (CovAE.trans (CovAE.one cove_31_26) (CovAE.trans (CovAE.one cove_31_27) (CovAE.one cove_31_28)))))))))))))))))))))))))))

/-! ### `N = 32` -/

theorem che_32_2_0 : chkE 32 2 3 4 (decH 14 1600013433092956036253838424736893728268433781870226942094230383135855962098688913735650194907081186786207494785933599572461625291807730094233622357759611267983771641150395401199843636367346857983148775330808173697897824262489682270692458638392637316947095629108427236775172537937357980552191782998564725965422320247331959548828441668952154335741630244847945205841293102165897662436258534891781733745954018784613292249808764934899960251268667820840708875417550795906550132088590775102363238142736093597222430611546205618713308163164805254654171991641142838872362005513393072158604836995) = true := by decide +kernel
theorem che_32_2_1 : chkE 32 2 4 24 (decH 34 427020493407605266201803278668810953558859628653226504208828598061252177221812034708779195565221410682379651624686273388037785743702326563448324296315696732753314019042085493141710404641442115628894979637060291918359605733925465215126667578915851085401491887246482052887161053725003777578590199620198216022679543083580849674551586861458226966119926977240419258105987) = true := by decide +kernel
theorem che_32_2_2 : chkE 32 2 24 25 (decH 5 217194463834423753754718867898970816309078184325566535566306016745358737224276458039321887684769647442750063998166131573875219713423403817705046257056610958487361714680113979628469960328592214484406821602851432535332774832326377078648972778394839713518295895681) = true := by decide +kernel
theorem che_32_2_3 : chkE 32 2 25 26 (decH 4 1031192372671873649189409781220635786685574413695695398659522917320104870237499363537371011829546483054013584277174698403707907655973056958079357111156269371396611773382348250677853820574343941761) = true := by decide +kernel
theorem che_32_2_4 : chkE 32 2 26 28 (decH 6 45746493448253459850002231672489394266942230317261059117563383595336204768574770779841978699205265542813100754022630749164834768448446545932835321978671125405478845999037431013818922819493905024806862434535642315722913893937541342224815557592264765515133399951745057689003648613483410242114559210208981967539279560825760976513) = true := by decide +kernel
theorem che_32_2_5 : chkE 32 2 28 32 (decH 5 17313404737137333112244254831691863997325135353746631251766883640583573462129252122513291239087065542155011591532440476016496915323141242618119839779021191696617687432699939429393034031351470041852735348862348733800299556480592201508210644933360000539260505729) = true := by decide +kernel
theorem cove_32_2 : CovBE 32 2 3 32 :=
  CovBE.trans (CovBE.of_chk che_32_2_0) (CovBE.trans (CovBE.of_chk che_32_2_1) (CovBE.trans (CovBE.of_chk che_32_2_2) (CovBE.trans (CovBE.of_chk che_32_2_3) (CovBE.trans (CovBE.of_chk che_32_2_4) (CovBE.of_chk che_32_2_5)))))

theorem che_32_3_0 : chkE 32 3 4 5 (decH 12 12204134638855898434611198118745158925612359520834726927094088237673210986609792363220220788764696318359074636861538484881149097787335041267174439456117775083211535485654097240010746013232134131965257292814112277123) = true := by decide +kernel
theorem che_32_3_1 : chkE 32 3 5 21 (decH 31 18257469029015730981795024901330116822843230304281270949784718385971455556157564526769333448190681564420844784026357361648966319962233636565862274710878867866780428131739626364917729106874303272744801451903244336687433219974218575428294168653037907217150675706942772169661529620251539909473393607195738428216068864796142762387436273221667005439999456796401823844177668152474729200949980741093687694475907) = true := by decide +kernel
theorem che_32_3_2 : chkE 32 3 21 24 (decH 15 8037806801535852013342287615853513807820128158031733418522823866643489161950970209483944960395798748596263977435361740656215384965393473261512328139670401649065434516118955581267245586939166851) = true := by decide +kernel
theorem che_32_3_3 : chkE 32 3 24 25 (decH 5 217194463834423753754718890218705823036009151213936297286685924024150150863677369989636562047211879200527296043578425619129078412484049915888590966203193513041792373471327740421743851382829871003360602058970158144469402746868590452222381208192102260217345298049) = true := by decide +kernel
theorem che_32_3_4 : chkE 32 3 25 26 (decH 4 352785226623183839516934543658564717231253412053308400653778599535312091668357189164604594666168639646422094547292579876239617244582392816067726977) = true := by decide +kernel
theorem che_32_3_5 : chkE 32 3 26 28 (decH 6 16740022322820560343094312256292781868323373099756780383148334227050649678854692461023317728192311562188320042301860338835662867482436391931994021550046007073521418890116911529069140924418663414312270991030323386400457518857104234924019006877721279424149101947952882817379438209) = true := by decide +kernel
theorem che_32_3_6 : chkE 32 3 28 32 (decH 4 1104191422553828620640623587108175640665009702560429629251622678794168024671996267503420485120645991809123407946444953833915008538721291188082510614921131534486493369974002818426752305257299496577) = true := by decide +kernel
theorem cove_32_3 : CovBE 32 3 4 32 :=
  CovBE.trans (CovBE.of_chk che_32_3_0) (CovBE.trans (CovBE.of_chk che_32_3_1) (CovBE.trans (CovBE.of_chk che_32_3_2) (CovBE.trans (CovBE.of_chk che_32_3_3) (CovBE.trans (CovBE.of_chk che_32_3_4) (CovBE.trans (CovBE.of_chk che_32_3_5) (CovBE.of_chk che_32_3_6))))))

theorem che_32_4_0 : chkE 32 4 5 6 (decH 11 572492519118309123674332804899986351749146711878781189563692133023267511307012640554365796210343383331119237763155056578236503308307411902392947712522593845163058830082239789692151167466581214597343044786189581464116795517802757454861823685114544739311102899436767273624620229556661256933036570823411453073899598497474723656564707098635571557698599264979390883864169255729547992784802587897790087402373174691130815153379238553405249151878019) = true := by decide +kernel
theorem che_32_4_1 : chkE 32 4 6 23 (decH 41 126670230481644603889114997038234136404438161213234530572257278475623488103663815446626154196266380740090862643696242726644878946495793960157248912598094935836338427232933958196053454991172736269361148390112455496279267600026391427287303199084737726253470317090845161450188247961218363556228968581977387446249201782195746225327077616690948133065098776472013531468612768394732045407308251102986625084913250461874368369462029921620253822195310848069765292000373449820225199562130128597665936542311297803035915837610989576751875723841490059762323043989811394790181427777140415141149267690508676976546334539340746887551912877508495694410185291385104744453) = true := by decide +kernel
theorem che_32_4_2 : chkE 32 4 23 27 (decH 15 14643986769070054378018173981947570277434869123725305714348373473160988582986157888963122906750000744771600312460914745247785639690840538652909140741233967840049139909935179578767174812056827885639494534882255156904694464546379632980549197978641315883460363578340133790157751828273481470061628682378866098537998923184921490173213435111210054841157640061213988774260273976492163) = true := by decide +kernel
theorem che_32_4_3 : chkE 32 4 27 32 (decH 4 53097365890966128041778332937614844176216755811292952180819467744114842140279624695005061349371127689086483620137639928743452376374359686157602433) = true := by decide +kernel
theorem cove_32_4 : CovBE 32 4 5 32 :=
  CovBE.trans (CovBE.of_chk che_32_4_0) (CovBE.trans (CovBE.of_chk che_32_4_1) (CovBE.trans (CovBE.of_chk che_32_4_2) (CovBE.of_chk che_32_4_3)))

theorem che_32_5_0 : chkE 32 5 6 20 (decH 37 864574155558227951273784529985374516658481708813916248003876638301361783496374798122848680553227463067216234412247008453231709065403058596667774372564277059577225138665545856940918469219756663472715320401331153596355888259240984523401991164121628104342394381751038995987811297476726835010520255405274606838851161785616622325015710047318017760042822422316175471567081441545024707340314119514198887733531730567217961143638276160512145712512249988747684872867305628872394091323160164032690799747) = true := by decide +kernel
theorem che_32_5_1 : chkE 32 5 20 26 (decH 28 9573968404906261300058319003652065213693996800784519923343939674011637902585940916357395019203780211873631702659738195557664421765175342779158756694227467857785161620203938963220020212754621007438426441957581300802414417104656930427274185606773412896449140075708445184308593983264759369294512832204191950215214197704550305104259817905266798755590951719802653008910190233587610012389115484697882240103451155800501569533019943856029827) = true := by decide +kernel
theorem che_32_5_2 : chkE 32 5 26 32 (decH 4 10992292578913860855075409355221877722992127186727582869041342076045847301688444559615001448065) = true := by decide +kernel
theorem cove_32_5 : CovBE 32 5 6 32 :=
  CovBE.trans (CovBE.of_chk che_32_5_0) (CovBE.trans (CovBE.of_chk che_32_5_1) (CovBE.of_chk che_32_5_2))

theorem che_32_6_0 : chkE 32 6 7 10 (decH 20 17990845604588951472143890695267186070923041856924688559943821691050684061641260657030567499659976037810332396289995024983647490917663302498814664208175050548574420436127119383674562445979947284022633551088157572397375591774307188451683285540461260514526127718047135972444351537990789039885698570793127832398634675987236580152608498455098848507751701610510798866264723946579113444126858506549910565852024570221971894572586850805554299848067) = true := by decide +kernel
theorem che_32_6_1 : chkE 32 6 10 25 (decH 34 23328984045823357506472709528316266602197923825069061214942498524167100874753149677783576353130584398921273920191617931436331596304177578159084052647894782411240912566152686585879676196919324778429427646907303941785377593961399507353096613428437767982590214165832161427379337720906196162081337623246265474662522525642725803685507589128644888503960379432565741575202182884185969681487614155369726973331562350236897011489106167254561496009033686811012778012640365124149171589361372118983363125000490589397622361389236656695488858376040364987320232756330591567877) = true := by decide +kernel
theorem che_32_6_2 : chkE 32 6 25 32 (decH 4 99499874411970657922342510505959334349692807596198593483857593914017044285645833575094403) = true := by decide +kernel
theorem cove_32_6 : CovBE 32 6 7 32 :=
  CovBE.trans (CovBE.of_chk che_32_6_0) (CovBE.trans (CovBE.of_chk che_32_6_1) (CovBE.of_chk che_32_6_2))

theorem che_32_7_0 : chkE 32 7 8 24 (decH 41 239101625055660213330361745105290559992813342925734915075068340748838734879124365465111486467071966632405617176487934987615004673381590627835829581844384323057607600235536165480199918367841551173260748279810981833142007561842101316891423678431593410661383819665297849770844613977836042037393297841763789584950727099011952889197998357318793135400701220907847695883633565884585855812040081250507246706989384897946908659286495213968050258862160445923835106036035225388948047102592058608430808641166287373482396049741159958390286588821707161829511881737325986583412098805258472408707) = true := by decide +kernel
theorem che_32_7_1 : chkE 32 7 24 32 (decH 4 414116831931735773229065244698855078200194273544903472737374178435019356283585689561861761) = true := by decide +kernel
theorem cove_32_7 : CovBE 32 7 8 32 :=
  CovBE.trans (CovBE.of_chk che_32_7_0) (CovBE.of_chk che_32_7_1)

theorem che_32_8_0 : chkE 32 8 9 32 (decH 23 3922750299489326274568862936456386407202188970810627366867273448606238568319433002452709881692645097224581694574410599674845641329291744706938180074695219972208562951255013971716365829090253895302709580522874301608305184831550505115219161680901563808406775164687619714883320294994800978943028874540568405985586089814246469794824834529814931166257450471248758312620239700663537257554368034868559294016412937541980652723844517854234499) = true := by decide +kernel
theorem cove_32_8 : CovBE 32 8 9 32 :=
  CovBE.of_chk che_32_8_0

theorem che_32_9_0 : chkE 32 9 10 32 (decH 12 299951599978782034230155639427149820243763439499201710161103646848080955533793902247897469847487697726093317439700239392169493572680321669374429315) = true := by decide +kernel
theorem cove_32_9 : CovBE 32 9 10 32 :=
  CovBE.of_chk che_32_9_0

theorem che_32_10_0 : chkE 32 10 11 32 (decH 3 111041961984012621443) = true := by decide +kernel
theorem cove_32_10 : CovBE 32 10 11 32 :=
  CovBE.of_chk che_32_10_0

theorem che_32_11_0 : chkE 32 11 12 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_11 : CovBE 32 11 12 32 :=
  CovBE.of_chk che_32_11_0

theorem che_32_12_0 : chkE 32 12 13 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_12 : CovBE 32 12 13 32 :=
  CovBE.of_chk che_32_12_0

theorem che_32_13_0 : chkE 32 13 14 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_13 : CovBE 32 13 14 32 :=
  CovBE.of_chk che_32_13_0

theorem che_32_14_0 : chkE 32 14 15 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_14 : CovBE 32 14 15 32 :=
  CovBE.of_chk che_32_14_0

theorem che_32_15_0 : chkE 32 15 16 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_15 : CovBE 32 15 16 32 :=
  CovBE.of_chk che_32_15_0

theorem che_32_16_0 : chkE 32 16 17 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_16 : CovBE 32 16 17 32 :=
  CovBE.of_chk che_32_16_0

theorem che_32_17_0 : chkE 32 17 18 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_17 : CovBE 32 17 18 32 :=
  CovBE.of_chk che_32_17_0

theorem che_32_18_0 : chkE 32 18 19 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_18 : CovBE 32 18 19 32 :=
  CovBE.of_chk che_32_18_0

theorem che_32_19_0 : chkE 32 19 20 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_19 : CovBE 32 19 20 32 :=
  CovBE.of_chk che_32_19_0

theorem che_32_20_0 : chkE 32 20 21 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_20 : CovBE 32 20 21 32 :=
  CovBE.of_chk che_32_20_0

theorem che_32_21_0 : chkE 32 21 22 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_21 : CovBE 32 21 22 32 :=
  CovBE.of_chk che_32_21_0

theorem che_32_22_0 : chkE 32 22 23 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_22 : CovBE 32 22 23 32 :=
  CovBE.of_chk che_32_22_0

theorem che_32_23_0 : chkE 32 23 24 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_23 : CovBE 32 23 24 32 :=
  CovBE.of_chk che_32_23_0

theorem che_32_24_0 : chkE 32 24 25 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_24 : CovBE 32 24 25 32 :=
  CovBE.of_chk che_32_24_0

theorem che_32_25_0 : chkE 32 25 26 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_25 : CovBE 32 25 26 32 :=
  CovBE.of_chk che_32_25_0

theorem che_32_26_0 : chkE 32 26 27 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_26 : CovBE 32 26 27 32 :=
  CovBE.of_chk che_32_26_0

theorem che_32_27_0 : chkE 32 27 28 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_27 : CovBE 32 27 28 32 :=
  CovBE.of_chk che_32_27_0

theorem che_32_28_0 : chkE 32 28 29 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_28 : CovBE 32 28 29 32 :=
  CovBE.of_chk che_32_28_0

theorem che_32_29_0 : chkE 32 29 30 32 (decH 1 0) = true := by decide +kernel
theorem cove_32_29 : CovBE 32 29 30 32 :=
  CovBE.of_chk che_32_29_0

theorem cove_32 : CovQE 32 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_32_2) (CovAE.trans (CovAE.one cove_32_3) (CovAE.trans (CovAE.one cove_32_4) (CovAE.trans (CovAE.one cove_32_5) (CovAE.trans (CovAE.one cove_32_6) (CovAE.trans (CovAE.one cove_32_7) (CovAE.trans (CovAE.one cove_32_8) (CovAE.trans (CovAE.one cove_32_9) (CovAE.trans (CovAE.one cove_32_10) (CovAE.trans (CovAE.one cove_32_11) (CovAE.trans (CovAE.one cove_32_12) (CovAE.trans (CovAE.one cove_32_13) (CovAE.trans (CovAE.one cove_32_14) (CovAE.trans (CovAE.one cove_32_15) (CovAE.trans (CovAE.one cove_32_16) (CovAE.trans (CovAE.one cove_32_17) (CovAE.trans (CovAE.one cove_32_18) (CovAE.trans (CovAE.one cove_32_19) (CovAE.trans (CovAE.one cove_32_20) (CovAE.trans (CovAE.one cove_32_21) (CovAE.trans (CovAE.one cove_32_22) (CovAE.trans (CovAE.one cove_32_23) (CovAE.trans (CovAE.one cove_32_24) (CovAE.trans (CovAE.one cove_32_25) (CovAE.trans (CovAE.one cove_32_26) (CovAE.trans (CovAE.one cove_32_27) (CovAE.trans (CovAE.one cove_32_28) (CovAE.one cove_32_29))))))))))))))))))))))))))))

/-! ### `N = 33` -/

theorem che_33_2_0 : chkE 33 2 3 18 (decH 14 23718891254786625908674257616742545525955973700439655886535776535551875221458497015885373470305327896826959424297903280236097196939824986743462121398047896745901569898294066535494245222293774976105561388523303122567368992223817635757065317878665204680490706018345568938222158808237913249575646281859) = true := by decide +kernel
theorem che_33_2_1 : chkE 33 2 18 22 (decH 27 10954405140089196004508181182756346505026631836441657945761669118807085320636403581908414208161954069309080639647214268515761335786496002420078979175952563978539906942453668447382011212547620444057828827672089786589927504765329863328140761719177188486612250555960270161137395426246446064613452489580742861010269420667011) = true := by decide +kernel
theorem che_33_2_2 : chkE 33 2 22 25 (decH 15 3901114499470272321424706351106086326681972475002763390219144386905390797436839914541666750088094129376544050109509628819437050975148065564865495361212161731627622854164065455706816394937379356855643696904069780800986727537926159345288724549544927577124770665025378161218558358156791553) = true := by decide +kernel
theorem che_33_2_3 : chkE 33 2 25 26 (decH 5 58334953424925959440132071553609162170478768668364277539043846191151911581359393349920843488006921489040012986849065427772243239474385816052374869487572548496282586589207763594713398976069038951865949721123059376292060034030626499263108145881495005591368405330937958145) = true := by decide +kernel
theorem che_33_2_4 : chkE 33 2 26 27 (decH 4 2163763680437996265699472755814341385719347737874547332912583911238751173025936074589089036207310009495054351962844442706853215896678124707167139232305110970870362175705215669275904613950580287001153281) = true := by decide +kernel
theorem che_33_2_5 : chkE 33 2 27 29 (decH 6 1683979101724981214149341902776866839360149218105734824646039002162823814165405448362636917356645685003432129344145553946687128680141006987632328947623580218542587692785794226789401483917685162991362187774830843097726003104589313986510212312725208459247445060488846352400037374542959804284532885058586000203946244896652144588942519684865) = true := by decide +kernel
theorem che_33_2_6 : chkE 33 2 29 33 (decH 5 66589557459520011736671482449859697473973926290091013747516481553615426152165423131307881935341621102070510358100944283397554263300754756916213731645291053161190225389579491131673931783264622844324110712041712349226331598661108778960729453952975823265609667751144984321) = true := by decide +kernel
theorem cove_33_2 : CovBE 33 2 3 33 :=
  CovBE.trans (CovBE.of_chk che_33_2_0) (CovBE.trans (CovBE.of_chk che_33_2_1) (CovBE.trans (CovBE.of_chk che_33_2_2) (CovBE.trans (CovBE.of_chk che_33_2_3) (CovBE.trans (CovBE.of_chk che_33_2_4) (CovBE.trans (CovBE.of_chk che_33_2_5) (CovBE.of_chk che_33_2_6))))))

theorem che_33_3_0 : chkE 33 3 4 5 (decH 13 167540656237255684072929467793371390418810905675368277135702863844951332113278202912640898223063405102898591387379135136976668573750478294668924203297964039482560885924591937587897057299717644123333157787896188968377944256611025199281588743705532760171023144657391051913529858266869560520259973496881276551395784147223220164707598726522727476961178466853136667958069310646044870006634267746019247808398055880983640247879564759999278032567672834500028339127992047528201116645322465503544147411903104211568763984101723044200367416984195) = true := by decide +kernel
theorem che_33_3_1 : chkE 33 3 5 22 (decH 31 219408393637329725944128158229972833708192512657856713375509305877718681653441901821262421040228927527789865252128972751267770751130086565176248026620849176162569194731436644754367042482987594388022877352141901779341518153957173312674095239414314495287595217798800301493190602267581093552453662630764759429622778203046805744604631019488974740801034271579983391842486773533241082136070266906178274028460042642070957990167480074092981534853) = true := by decide +kernel
theorem che_33_3_2 : chkE 33 3 22 26 (decH 19 121084994421930344430718437839434814653378913761888115115593998233713944065374200499124459713231436311020127071107944888515972212160046016120357218527365628661552797586096489277563605991618022502618387489694420895511466453410237689711720793080373833857776597527975644370358664431302679099515309790559942614295420579771939618218278638261432504440946999427) = true := by decide +kernel
theorem che_33_3_3 : chkE 33 3 26 27 (decH 4 2163772580053805903739403581287438102511826534690134584779804779384567965848955991544764263924192983439864154921351151296255293116629952254398041144568070189836920025756307288307422713063827711877140225) = true := by decide +kernel
theorem che_33_3_4 : chkE 33 3 27 29 (decH 6 4500897062817227173831142971481810732363495604248581015733183807297440574864347423859105034752559919647047824126468594312123497697856411666344326807018923933542412233600779047518484215215364050221656588861749153453960295155201376087954422396533367132022188068738550117808976361236696833) = true := by decide +kernel
theorem che_33_3_5 : chkE 33 3 29 33 (decH 4 463969697092919687579011701634795781274555406371948226206525667853955434965672681134490841871570889578914669971743288249558376585537411230470672682753) = true := by decide +kernel
theorem cove_33_3 : CovBE 33 3 4 33 :=
  CovBE.trans (CovBE.of_chk che_33_3_0) (CovBE.trans (CovBE.of_chk che_33_3_1) (CovBE.trans (CovBE.of_chk che_33_3_2) (CovBE.trans (CovBE.of_chk che_33_3_3) (CovBE.trans (CovBE.of_chk che_33_3_4) (CovBE.of_chk che_33_3_5)))))

theorem che_33_4_0 : chkE 33 4 5 19 (decH 30 64288455630955877556102303972348696927916654273044757440499397319719004546929267409683378296709606187547941396667152711257225845521997130659288087854626125721531041680085076271807492608705820889269634022921880112693206177907908651386004619033749468156877613612011474382663835803291340940233361316424226993900224885381154432872348702844196419190357907675655937826994115326825813148350671658669357227450267832460388632721157354996854951591857239635596832601991383368579) = true := by decide +kernel
theorem che_33_4_1 : chkE 33 4 19 25 (decH 34 24168597923278175892203859807729011080835226589338171448417852269178607643300615472453857902413191875456892048094005528525097459293410498186984243858575987067801417350291898925982927635039181984447667179752543619894331523587615475673524539681607133113769940815972153987540197870779357624526053626515178901977863221920208312031090554527804975400117192061444962812052730500421200613719123344628208481635229177202198686556725806440238314807689125297792546371388340195165025387433255609023170426850814356234906959284814723) = true := by decide +kernel
theorem che_33_4_2 : chkE 33 4 25 28 (decH 11 7524443565178117121172832135796837451333609707838215788383086186965100467178771692442586360287232585689236587485588188711416797945194437127808085637262129998627696774437630520111831587863949352907115941248990743557129417725198858040364924709443688048831836959144898440651054703240994941473585087672773767101793703123543119364911657897431656151136005935909670154613935873) = true := by decide +kernel
theorem che_33_4_3 : chkE 33 4 28 33 (decH 4 6192428818617638681454783728155302588717662635316331506884899899822922935947223767792484675915922704173495680586494221824252989990659305021034889367297) = true := by decide +kernel
theorem cove_33_4 : CovBE 33 4 5 33 :=
  CovBE.trans (CovBE.of_chk che_33_4_0) (CovBE.trans (CovBE.of_chk che_33_4_1) (CovBE.trans (CovBE.of_chk che_33_4_2) (CovBE.of_chk che_33_4_3)))

theorem che_33_5_0 : chkE 33 5 6 7 (decH 10 84250003429852741043089772708372808136147815773292027283065197113493720838328078695536951206537178652615635508139435621945152937333559229262075858501183426626109811631727695685985339293015041058879155692552607882418544039059935396682884281251357338201274038746259464202167712008214367492515950352992621190241789662389767651069777350410189510812867639589463425282337301285179947843896451) = true := by decide +kernel
theorem che_33_5_1 : chkE 33 5 7 23 (decH 41 1364758686954756731430849957160835008070372770867475172626900512881774218826852386470416756898301216401688415444094381828199162685393433673150940532911730829516565600889899222640945686072358979221816357329353384487092127543227871444640827864344176973532648840298018281149900208252678660721845988149205038076855977106767033548469590892564944316166412289143178164732065633554038116263828026712954301678735132896493264197341427149507033507865419088808485935639356153257566151911744561718662801716836245772560328997629897010199670746907242990691575824190991455368589056974455672525928565361011879542493024466510233605) = true := by decide +kernel
theorem che_33_5_2 : chkE 33 5 23 33 (decH 20 88838691187361361872788686895412814786152005783178533949270179559302304066448809512259760495988594876708531208211424221307729404511720377834861036742834845250269902634680913286351938320281355255370099280461442541814456174472146390050641722803092205693548710061220435078819350765808703362612519772258088136990733812824945383870715074054481440384388698796745097379265187710852737676642947) = true := by decide +kernel
theorem cove_33_5 : CovBE 33 5 6 33 :=
  CovBE.trans (CovBE.of_chk che_33_5_0) (CovBE.trans (CovBE.of_chk che_33_5_1) (CovBE.of_chk che_33_5_2))

theorem che_33_6_0 : chkE 33 6 7 21 (decH 38 222783927046460792613473173932468114281908912666862205418772267967540633454944971519279994355717090756411156856858018835499775968855956415435439844943961929381434155384447885602926143320035948659437425447195699610079458433134509090320748662508133549345780486325603215125920425218363588058026598631926299188752506644085508605904380461801545202846281197826269802106312808798283968562189096270452657516048071442878177227222880438453598457430364695529089821023753200984389994361844484290999457708542636330146984587523123994594152841004205443) = true := by decide +kernel
theorem che_33_6_1 : chkE 33 6 21 33 (decH 27 20039800451234752108792478615123722330445233824905878112645872939512826765278353523451030700207836272786490845703698011255102393454427735652465166297995121541354424743935774228663046149928250601616999912549816367929357707862213465677523968598094977149144026918416367150898127726162995654525458003613239373105156334127372181154914713858707539146215390906229560752415105292546576793321073939648428048989331286287997126012320073054704771) = true := by decide +kernel
theorem cove_33_6 : CovBE 33 6 7 33 :=
  CovBE.trans (CovBE.of_chk che_33_6_0) (CovBE.of_chk che_33_6_1)

theorem che_33_7_0 : chkE 33 7 8 21 (decH 27 21987284956057668418413261824112192552164519698349308347632012780072089812834013683607142207255034137831108705834368288179062220666957993456378899375117857450553993690807612506040449476726727694739345120961774241321399922202742987151139718517266909360597890633212973172399019952535880937247643285159216412274897668482112744158926775491805900523185638609199531089542158895896722260939698667572083541854272158617410603817986852109809952967045124754416404835327869114500270507355965360131992893572739) = true := by decide +kernel
theorem che_33_7_1 : chkE 33 7 21 33 (decH 22 6745297946243622623558748427165330933655461550999256549039705726216566412089854722784060026075918841999216794266404325414289657744131041939279915379882468225949197635909247660090546589659071510718035579021448993220452720877793480596364829280684680750039324811340677805452722448988123618757760623439667992238714572664896560035208002210216994858504475709842409091) = true := by decide +kernel
theorem cove_33_7 : CovBE 33 7 8 33 :=
  CovBE.trans (CovBE.of_chk che_33_7_0) (CovBE.of_chk che_33_7_1)

theorem che_33_8_0 : chkE 33 8 9 33 (decH 31 39030881547965860023642022882289985305889763756346065463844178770991813126279481286928029557185224584688053021202634672746243366872504029030453969030339489395558599599810861631346083335569691365686345016571428119900126687457243651596414780519000257240162117066278345988608623141981266315319176903957921015765017549833176956114245502215840228043891938251476788181065699589489840653914329776135903857624963) = true := by decide +kernel
theorem cove_33_8 : CovBE 33 8 9 33 :=
  CovBE.of_chk che_33_8_0

theorem che_33_9_0 : chkE 33 9 10 33 (decH 14 19351379455107108287338396060922821662775804907257187531295245189655866707414268607547684501793768595703434984701632689176762883614161792610698202718129156735112434535426426980483) = true := by decide +kernel
theorem cove_33_9 : CovBE 33 9 10 33 :=
  CovBE.of_chk che_33_9_0

theorem che_33_10_0 : chkE 33 10 11 33 (decH 6 1206264168301979103814994064033496230825937633390663233980803) = true := by decide +kernel
theorem cove_33_10 : CovBE 33 10 11 33 :=
  CovBE.of_chk che_33_10_0

theorem che_33_11_0 : chkE 33 11 12 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_11 : CovBE 33 11 12 33 :=
  CovBE.of_chk che_33_11_0

theorem che_33_12_0 : chkE 33 12 13 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_12 : CovBE 33 12 13 33 :=
  CovBE.of_chk che_33_12_0

theorem che_33_13_0 : chkE 33 13 14 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_13 : CovBE 33 13 14 33 :=
  CovBE.of_chk che_33_13_0

theorem che_33_14_0 : chkE 33 14 15 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_14 : CovBE 33 14 15 33 :=
  CovBE.of_chk che_33_14_0

theorem che_33_15_0 : chkE 33 15 16 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_15 : CovBE 33 15 16 33 :=
  CovBE.of_chk che_33_15_0

theorem che_33_16_0 : chkE 33 16 17 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_16 : CovBE 33 16 17 33 :=
  CovBE.of_chk che_33_16_0

theorem che_33_17_0 : chkE 33 17 18 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_17 : CovBE 33 17 18 33 :=
  CovBE.of_chk che_33_17_0

theorem che_33_18_0 : chkE 33 18 19 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_18 : CovBE 33 18 19 33 :=
  CovBE.of_chk che_33_18_0

theorem che_33_19_0 : chkE 33 19 20 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_19 : CovBE 33 19 20 33 :=
  CovBE.of_chk che_33_19_0

theorem che_33_20_0 : chkE 33 20 21 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_20 : CovBE 33 20 21 33 :=
  CovBE.of_chk che_33_20_0

theorem che_33_21_0 : chkE 33 21 22 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_21 : CovBE 33 21 22 33 :=
  CovBE.of_chk che_33_21_0

theorem che_33_22_0 : chkE 33 22 23 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_22 : CovBE 33 22 23 33 :=
  CovBE.of_chk che_33_22_0

theorem che_33_23_0 : chkE 33 23 24 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_23 : CovBE 33 23 24 33 :=
  CovBE.of_chk che_33_23_0

theorem che_33_24_0 : chkE 33 24 25 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_24 : CovBE 33 24 25 33 :=
  CovBE.of_chk che_33_24_0

theorem che_33_25_0 : chkE 33 25 26 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_25 : CovBE 33 25 26 33 :=
  CovBE.of_chk che_33_25_0

theorem che_33_26_0 : chkE 33 26 27 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_26 : CovBE 33 26 27 33 :=
  CovBE.of_chk che_33_26_0

theorem che_33_27_0 : chkE 33 27 28 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_27 : CovBE 33 27 28 33 :=
  CovBE.of_chk che_33_27_0

theorem che_33_28_0 : chkE 33 28 29 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_28 : CovBE 33 28 29 33 :=
  CovBE.of_chk che_33_28_0

theorem che_33_29_0 : chkE 33 29 30 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_29 : CovBE 33 29 30 33 :=
  CovBE.of_chk che_33_29_0

theorem che_33_30_0 : chkE 33 30 31 33 (decH 1 0) = true := by decide +kernel
theorem cove_33_30 : CovBE 33 30 31 33 :=
  CovBE.of_chk che_33_30_0

theorem cove_33 : CovQE 33 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_33_2) (CovAE.trans (CovAE.one cove_33_3) (CovAE.trans (CovAE.one cove_33_4) (CovAE.trans (CovAE.one cove_33_5) (CovAE.trans (CovAE.one cove_33_6) (CovAE.trans (CovAE.one cove_33_7) (CovAE.trans (CovAE.one cove_33_8) (CovAE.trans (CovAE.one cove_33_9) (CovAE.trans (CovAE.one cove_33_10) (CovAE.trans (CovAE.one cove_33_11) (CovAE.trans (CovAE.one cove_33_12) (CovAE.trans (CovAE.one cove_33_13) (CovAE.trans (CovAE.one cove_33_14) (CovAE.trans (CovAE.one cove_33_15) (CovAE.trans (CovAE.one cove_33_16) (CovAE.trans (CovAE.one cove_33_17) (CovAE.trans (CovAE.one cove_33_18) (CovAE.trans (CovAE.one cove_33_19) (CovAE.trans (CovAE.one cove_33_20) (CovAE.trans (CovAE.one cove_33_21) (CovAE.trans (CovAE.one cove_33_22) (CovAE.trans (CovAE.one cove_33_23) (CovAE.trans (CovAE.one cove_33_24) (CovAE.trans (CovAE.one cove_33_25) (CovAE.trans (CovAE.one cove_33_26) (CovAE.trans (CovAE.one cove_33_27) (CovAE.trans (CovAE.one cove_33_28) (CovAE.trans (CovAE.one cove_33_29) (CovAE.one cove_33_30)))))))))))))))))))))))))))))

/-! ### `N = 34` -/

theorem che_34_2_0 : chkE 34 2 3 4 (decH 15 30460349902722534914857713282366440024497829356111066879005664707278899173988083483211078146102982228968574754608751850456482528507318258564536496384704751374203136454326051768103809215885331737593746270972124281351352897908321298224862836064580615183494258657797547540070352111023756242699583605689291148640458023576642297729661527287525472055386299728196454065036822296184936891533202360883614695694135222850137209038872099705350488149968980815022798007093066268077406607972455532869656921331296817791796752568263136112094001575604941658766725822953785318100363170192834841529020971791477232172625803426503623148275148008822611250706984819600702865338115380969460689308253426756916134019) = true := by decide +kernel
theorem che_34_2_1 : chkE 34 2 4 25 (decH 37 18763639853634281996729656658440630646605288263657991327707772312037085897715733958067704960912616999253049286364725775691167621759444706042893168321003704334125659069070807429038039544819671143579168326269555845467674015906001433848091160065151845114452114367422861832618721272766514235045271882280063071161687750603306878171056373496431396290690241618452924019773940187569839514151206660840898691) = true := by decide +kernel
theorem che_34_2_2 : chkE 34 2 25 26 (decH 5 15659234229928027899025845824369498462830397827658940119758678402342742068924878884560553331078208389481284207005104880889813208546082758162228609747644772033011333573613223891325239842492647000168084392144246931210858920695345256538949445656716161249218125602652399181830213505) = true := by decide +kernel
theorem che_34_2_3 : chkE 34 2 26 27 (decH 5 16767148162488236765630969463506200617767991724161062730134406395266247796880521634928716791793062887702479752118612491716157546498976998803923277358125222491838982657689979421560082929875038088316049840750842288046379821910525442348014482500697284925993476233574274043736444801) = true := by decide +kernel
theorem che_34_2_4 : chkE 34 2 27 28 (decH 4 4858813232129516429798332672460186526592527911726103932220454218711514167121697467409561296848406504861376787512808561023599486466919445243063884753401805373068422847297997545175424512458332282038537156939649) = true := by decide +kernel
theorem che_34_2_5 : chkE 34 2 28 30 (decH 6 57861302046419061895247848945487203827025965670764794925976851050519842012034549467247479729558708478272176571764348807816294873458845237316742864881827883675534194597021938538070034894597868155601895742103536907400908290357311131691349877722211923164687100761303909916016119486587023162425482375228840332346821447169682233521677436417546943516545) = true := by decide +kernel
theorem che_34_2_6 : chkE 34 2 30 34 (decH 5 1256284432672030211674371666835498111251023285303479346491782441894887619408076662913121677077275419377067438795518784990753060622694698008928140646200285594193131857345248714933518585321515911374477096046772646437107029557068845165586360677724290078493431678897623182707052417) = true := by decide +kernel
theorem cove_34_2 : CovBE 34 2 3 34 :=
  CovBE.trans (CovBE.of_chk che_34_2_0) (CovBE.trans (CovBE.of_chk che_34_2_1) (CovBE.trans (CovBE.of_chk che_34_2_2) (CovBE.trans (CovBE.of_chk che_34_2_3) (CovBE.trans (CovBE.of_chk che_34_2_4) (CovBE.trans (CovBE.of_chk che_34_2_5) (CovBE.of_chk che_34_2_6))))))

theorem che_34_3_0 : chkE 34 3 4 5 (decH 13 15209246947539387186721116267596978269415874926305999532071129109147254839958838834233300081604320123224547517730406011740613573220436238656739977718041153782366222974726704564939069232439521619344425148276151402377031890638543786099331) = true := by decide +kernel
theorem che_34_3_1 : chkE 34 3 5 22 (decH 33 4243975554855797628392174918188694415327209459134495618724045756054615591310253889872455812995251665029414974140722438426107173682372607525932400563697045630921239535772248884418208080409881254086584577705139567107786831811725619366205747098181835096405449913763093069896527830268527497678816106331039053884819220225857901172437382583510987986339093024848967293313854566740669454336291192659091272711297322393969334087273798178528489039461960158502741544192458885) = true := by decide +kernel
theorem che_34_3_2 : chkE 34 3 22 26 (decH 21 299791925577061810220297498639383612288184862313292996189348634564301955300836775542181514722794551245200185423199368476264767699761844666454055321501719399045874154599608429145879465323245280637520344582185344376794800585906496426732155014533586303273148763296217547401071799568603009459189357867228931749445640969688992412704310678539430383538747849277502720193486038635863130243) = true := by decide +kernel
theorem che_34_3_3 : chkE 34 3 26 27 (decH 5 16767148162488236765630969463506200617819882051601971438153418299939223263739418483758777272464790403906795760798609963117557380485430451211367226264533757066918723531936642995768497057591853409763883248947364263978265313248612584395766909565713069144776413714199278207587700609) = true := by decide +kernel
theorem che_34_3_4 : chkE 34 3 27 28 (decH 4 101456754216912274127676134007006262823999829241356002979966723091769902043528749345554573694738848068190249849899141390458483737092412753874977503306076033) = true := by decide +kernel
theorem che_34_3_5 : chkE 34 3 28 30 (decH 6 1286703045204097224797232004507551213430122627760109886990720400697989524433685986058698167023707785416866509303876311461997334392041539036344887749362836620464533211884415934915316488653254571085820695240744797019952618371027693607435938425947352113982973989428028409145242207811356308019679105) = true := by decide +kernel
theorem che_34_3_6 : chkE 34 3 30 34 (decH 4 5179866448551696548321250375598137212119925109049219605770667888178508208920618804909396257019776912153578534289353271998264987481504122873144392196216140493325305355364562794277868709509864222946718212640641) = true := by decide +kernel
theorem cove_34_3 : CovBE 34 3 4 34 :=
  CovBE.trans (CovBE.of_chk che_34_3_0) (CovBE.trans (CovBE.of_chk che_34_3_1) (CovBE.trans (CovBE.of_chk che_34_3_2) (CovBE.trans (CovBE.of_chk che_34_3_3) (CovBE.trans (CovBE.of_chk che_34_3_4) (CovBE.trans (CovBE.of_chk che_34_3_5) (CovBE.of_chk che_34_3_6))))))

theorem che_34_4_0 : chkE 34 4 5 6 (decH 12 38480857455497580581037460045760560047295952158911450866933805888336811764642385000899030208851388999036312419786751104009694696677231957336213593314641573834971009028342180519299832410597480992400230823791620322254204182715788009968337958144865122544248698519015328124859283234934163379727759536891798338680426899386097392378519021504269210385351304310643549714980349944821312814577488275931378084620313295701523777261057825169821055670702923988429554873122348209343244113026460484122122777823353397252692264622484522038991307839423363) = true := by decide +kernel
theorem che_34_4_1 : chkE 34 4 6 23 (decH 40 16016604271650819343044682057877227024627468014016823391807446962732571026846736074913913315311643522933237399385276252245354323641494141837853193445203878632544195458892908786103812852503015054311646531910499180929357207858505266022372973214964774978757841357967265633286665799283967213781140507722017493796610245588358421488416562559638825509321423280897242011985128596126674095901074815014652885519082588867226461333907202411495245380873668802771806960273700846353695924265336285383291428619200240701560646292308630026493181788212807850625926654543306534847799534954848250429393622177145138036648306324930869571140822992242851845) = true := by decide +kernel
theorem che_34_4_2 : chkE 34 4 23 27 (decH 19 2765092462560184067604369214817903988751777466963421525425742167511267596639420883122824925202643033785658374241346911086454128583985742768021776328492633985135587784287188796330764733774048780921248948586769434773489512115621813832855745007170226122832594640456262212129818547962880624191463983665337561489374121154846743908861947650306768377791071497965109975352961406650121635725677997657033851011) = true := by decide +kernel
theorem che_34_4_3 : chkE 34 4 27 34 (decH 10 4592988174991504447829218863834707163063061601148758585670096135867224501476805820755072831721128589178269110431653862574714487671806415247134022084000178105492723313725534299013042216125200626289949080670194249478892851124462904443023627837999551461171755204935618731895926500797597760940933016124943812173143710494529754755283408079997418231985616398051561345) = true := by decide +kernel
theorem cove_34_4 : CovBE 34 4 5 34 :=
  CovBE.trans (CovBE.of_chk che_34_4_0) (CovBE.trans (CovBE.of_chk che_34_4_1) (CovBE.trans (CovBE.of_chk che_34_4_2) (CovBE.of_chk che_34_4_3)))

theorem che_34_5_0 : chkE 34 5 6 20 (decH 35 17476155135817807378699794406423459038001386725811275715805067096826228498063990479712387446933779086582656827554152724419854702286693270950586892486826009299582820219135685363296520829135159292915918651496380717256284823744936482804412814207534866242841056597199954539282885483214273450928714617870912250494648658022754186745309240676113333943377797327351693839748151993641430094350833252916358939041587390170024851880822736516381980853734620823702833929908414994294847325315) = true := by decide +kernel
theorem che_34_5_1 : chkE 34 5 20 26 (decH 34 2561417018238528068667173782043493114202440532946473906896138296789424742736052752944942682908310110197137419021649219029878681799126158571753926706565993232572292300010470766777175432448972205446167960243436310469361326007321676726841648138880170463368743994098526339298628252527411866481731956319420510282098793058659873273274079464215118490139613108689319272929205372351193431995889741161418794777571322286910105186639115220980726594854784475499869168486303405906668921323651) = true := by decide +kernel
theorem che_34_5_2 : chkE 34 5 26 34 (decH 11 339594103055446166711305259731592725046522541493468649989831643943352448199114748934821548570632423116920551314906321850120213521390550483426579186356015256295583666505014075229301673529939285764481687297515284377542804043769537166834178306341487128842988769153) = true := by decide +kernel
theorem cove_34_5 : CovBE 34 5 6 34 :=
  CovBE.trans (CovBE.of_chk che_34_5_0) (CovBE.trans (CovBE.of_chk che_34_5_1) (CovBE.of_chk che_34_5_2))

theorem che_34_6_0 : chkE 34 6 7 8 (decH 9 1057435449124814247124396247984089894359621823067264442676502157346464219273117672458288761470149421059509253803747608720106749870641911876449200556848362359715462568545116433683358659122955656214319353989811104129157179171255610441651975597558608629789215119417329028223980793569401095574483277040287660602574755960605233528511285318700194222615555474515522869262438365831395924821379) = true := by decide +kernel
theorem che_34_6_1 : chkE 34 6 8 23 (decH 39 50539710765755951411799130655625243657388931969153041088782807804804071999255048569335389848031958806309027463407859224430265384225411058974019340051540956267886066525856489089271906562456910368110819854630479310234955073130272254278477997555479102346233962914609753026672296019788289921932651593718513798587726863812410043103793448092466867479605113556048442166012480333954663246953106094922897393265012497931205223719473732449430855594894213447185141742160528040934394172385696083393830775314228181167386963327962463766317320067343208805232071000749016728165528498369109856680444614251928778927505413) = true := by decide +kernel
theorem che_34_6_2 : chkE 34 6 23 34 (decH 21 19716528455620095957518009961105965615969781841807193434562448141536791210362167546879764087362559430842933443850535390671917423121475781974590198164911354202682821362378729330023621031663993092579182155819647245581620871420024844823960887025494581677685100021556437659870850464830591709621652171302054264221999661513583496369119382445624046778036536265245903131651648528953716448158375687904235002411620521603) = true := by decide +kernel
theorem cove_34_6 : CovBE 34 6 7 34 :=
  CovBE.trans (CovBE.of_chk che_34_6_0) (CovBE.trans (CovBE.of_chk che_34_6_1) (CovBE.of_chk che_34_6_2))

theorem che_34_7_0 : chkE 34 7 8 22 (decH 36 1587873529338203411735797833316938133190955658911288769528372731754678557962446928378462944798724907579060847643591717623779562869825537552783225539975559456149991640832828296092668701437961493553490639556981402774877977944410261613727482043199978631094380774676938898853946858346119796415979206696650914902506565253528619341225320078027781762736562928739054069939397045370314371338270149717634131320442005869677449221037766336254955415455045615397316165753133674777245289907332368899639814048997580280214209971843) = true := by decide +kernel
theorem che_34_7_1 : chkE 34 7 22 34 (decH 22 14379558360194474417358183530018060126740627391897752808506911094682472974853726808565314036898533939914396653756825993327460232200679520203101383176162759475413380047067691045177085955214033518795508152091394375711098066211342220420100924593470452053129640039325668817823730449033097391788418813901098658351776417698237116321368954878854740417130579148931) = true := by decide +kernel
theorem cove_34_7 : CovBE 34 7 8 34 :=
  CovBE.trans (CovBE.of_chk che_34_7_0) (CovBE.of_chk che_34_7_1)

theorem che_34_8_0 : chkE 34 8 9 23 (decH 24 104171039333543354311966060731050099409893386269019158176793744747986552544220605025767774212179229939903969427060264874827443416134024301754292006516591858197342215417843861058975536839412496060997126756211685413722835660507863198354758261369994289781225161072590083512595038094149685903250133237951160892427789946320118454795472035891749889468393765580847304706104997864837092130406693030606651316736979854703016194206834259609164544682321200805531002478845821087343757187) = true := by decide +kernel
theorem che_34_8_1 : chkE 34 8 23 34 (decH 11 4944381957104964612287983371409516356135609684525997211095879867528330906690204614188413923489211380093010931167952380385331416075718956073068434046219497616062163699776517017583226225008939997615747) = true := by decide +kernel
theorem cove_34_8 : CovBE 34 8 9 34 :=
  CovBE.trans (CovBE.of_chk che_34_8_0) (CovBE.of_chk che_34_8_1)

theorem che_34_9_0 : chkE 34 9 10 34 (decH 20 419527402694443639475459947974311528044451479694547908872623801432620270684496046762000244080831356631683755542314523262436863863969888269975048778841744663872402172773130986665979117896873684861919322068855161705072251330837740302150968233925198263900267343937292419) = true := by decide +kernel
theorem cove_34_9 : CovBE 34 9 10 34 :=
  CovBE.of_chk che_34_9_0

theorem che_34_10_0 : chkE 34 10 11 34 (decH 7 18621099436791165043142281584347026306584496352058104793971548093891330061683075) = true := by decide +kernel
theorem cove_34_10 : CovBE 34 10 11 34 :=
  CovBE.of_chk che_34_10_0

theorem che_34_11_0 : chkE 34 11 12 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_11 : CovBE 34 11 12 34 :=
  CovBE.of_chk che_34_11_0

theorem che_34_12_0 : chkE 34 12 13 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_12 : CovBE 34 12 13 34 :=
  CovBE.of_chk che_34_12_0

theorem che_34_13_0 : chkE 34 13 14 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_13 : CovBE 34 13 14 34 :=
  CovBE.of_chk che_34_13_0

theorem che_34_14_0 : chkE 34 14 15 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_14 : CovBE 34 14 15 34 :=
  CovBE.of_chk che_34_14_0

theorem che_34_15_0 : chkE 34 15 16 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_15 : CovBE 34 15 16 34 :=
  CovBE.of_chk che_34_15_0

theorem che_34_16_0 : chkE 34 16 17 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_16 : CovBE 34 16 17 34 :=
  CovBE.of_chk che_34_16_0

theorem che_34_17_0 : chkE 34 17 18 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_17 : CovBE 34 17 18 34 :=
  CovBE.of_chk che_34_17_0

theorem che_34_18_0 : chkE 34 18 19 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_18 : CovBE 34 18 19 34 :=
  CovBE.of_chk che_34_18_0

theorem che_34_19_0 : chkE 34 19 20 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_19 : CovBE 34 19 20 34 :=
  CovBE.of_chk che_34_19_0

theorem che_34_20_0 : chkE 34 20 21 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_20 : CovBE 34 20 21 34 :=
  CovBE.of_chk che_34_20_0

theorem che_34_21_0 : chkE 34 21 22 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_21 : CovBE 34 21 22 34 :=
  CovBE.of_chk che_34_21_0

theorem che_34_22_0 : chkE 34 22 23 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_22 : CovBE 34 22 23 34 :=
  CovBE.of_chk che_34_22_0

theorem che_34_23_0 : chkE 34 23 24 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_23 : CovBE 34 23 24 34 :=
  CovBE.of_chk che_34_23_0

theorem che_34_24_0 : chkE 34 24 25 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_24 : CovBE 34 24 25 34 :=
  CovBE.of_chk che_34_24_0

theorem che_34_25_0 : chkE 34 25 26 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_25 : CovBE 34 25 26 34 :=
  CovBE.of_chk che_34_25_0

theorem che_34_26_0 : chkE 34 26 27 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_26 : CovBE 34 26 27 34 :=
  CovBE.of_chk che_34_26_0

theorem che_34_27_0 : chkE 34 27 28 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_27 : CovBE 34 27 28 34 :=
  CovBE.of_chk che_34_27_0

theorem che_34_28_0 : chkE 34 28 29 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_28 : CovBE 34 28 29 34 :=
  CovBE.of_chk che_34_28_0

theorem che_34_29_0 : chkE 34 29 30 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_29 : CovBE 34 29 30 34 :=
  CovBE.of_chk che_34_29_0

theorem che_34_30_0 : chkE 34 30 31 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_30 : CovBE 34 30 31 34 :=
  CovBE.of_chk che_34_30_0

theorem che_34_31_0 : chkE 34 31 32 34 (decH 1 0) = true := by decide +kernel
theorem cove_34_31 : CovBE 34 31 32 34 :=
  CovBE.of_chk che_34_31_0

theorem cove_34 : CovQE 34 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_34_2) (CovAE.trans (CovAE.one cove_34_3) (CovAE.trans (CovAE.one cove_34_4) (CovAE.trans (CovAE.one cove_34_5) (CovAE.trans (CovAE.one cove_34_6) (CovAE.trans (CovAE.one cove_34_7) (CovAE.trans (CovAE.one cove_34_8) (CovAE.trans (CovAE.one cove_34_9) (CovAE.trans (CovAE.one cove_34_10) (CovAE.trans (CovAE.one cove_34_11) (CovAE.trans (CovAE.one cove_34_12) (CovAE.trans (CovAE.one cove_34_13) (CovAE.trans (CovAE.one cove_34_14) (CovAE.trans (CovAE.one cove_34_15) (CovAE.trans (CovAE.one cove_34_16) (CovAE.trans (CovAE.one cove_34_17) (CovAE.trans (CovAE.one cove_34_18) (CovAE.trans (CovAE.one cove_34_19) (CovAE.trans (CovAE.one cove_34_20) (CovAE.trans (CovAE.one cove_34_21) (CovAE.trans (CovAE.one cove_34_22) (CovAE.trans (CovAE.one cove_34_23) (CovAE.trans (CovAE.one cove_34_24) (CovAE.trans (CovAE.one cove_34_25) (CovAE.trans (CovAE.one cove_34_26) (CovAE.trans (CovAE.one cove_34_27) (CovAE.trans (CovAE.one cove_34_28) (CovAE.trans (CovAE.one cove_34_29) (CovAE.trans (CovAE.one cove_34_30) (CovAE.one cove_34_31))))))))))))))))))))))))))))))

/-! ### `N = 35` -/

theorem che_35_2_0 : chkE 35 2 3 19 (decH 15 29558702613011701682863554562318354219628127008765958989055820748987216587857383222710242067914596050484990921834050727775783895167488322056275255793209048317752885768429658580160130187288093723776974920660697311211090139650301236398176536064700196675534382386590208621145437695751536249342349049561485323902792291598467) = true := by decide +kernel
theorem che_35_2_1 : chkE 35 2 19 22 (decH 23 52678365103229508840521710087418195930880477182652609968077789882625011882370797564790899559505634414091982316838411721273194438245829575243492494756518109910585388761073407461943083708874045874743568219671426902687046393979500446538369805980770037208255570735552800076349571) = true := by decide +kernel
theorem che_35_2_2 : chkE 35 2 22 26 (decH 23 4268898757284898527283927931421005545186359466392898531962004896323758904490152928787466257070565358475742063488749000539769518543316536464991816149914409088773324312631917990926061659634576537223410551997542919038640921134712464887343033226748560411214544858345595453150553882390923020037260957801993184215192197136971030651806071840018178482614137686261858786872293329799110742822913) = true := by decide +kernel
theorem che_35_2_3 : chkE 35 2 26 27 (decH 5 4503219272698711983615237838244411610976817489057295747908429197425295645678813267623040172725689244582536414641722246731777728812088651683452198642986358135732558595319986897070803131129263932603682609026890220766696758508271509860374384018540059235116786437743882332425309777169846273) = true := by decide +kernel
theorem che_35_2_4 : chkE 35 2 27 28 (decH 5 4503221674534062203161037721223538850960716962524694355657077065492102656827267885296600891016656246344575294151595804785602119933333047924938303577797064925925665510837204103243360141700792937921012831783985006100175911438973544270239157588506120003895677021897539258119843595812163585) = true := by decide +kernel
theorem che_35_2_5 : chkE 35 2 28 29 (decH 4 10194932576349275385872107493764878308176424546499777546989563167653658077980358031344147308065236768965342777242453199080248060849202573626624361834135436503524577802570258385370969719518361165730193962974862413825) = true := by decide +kernel
theorem che_35_2_6 : chkE 35 2 29 31 (decH 6 2120492572425246926895862553804523511326265570538550550937758511702366497005176870389498408796662712766201311985941148597051291436427001148417028762649944728209876126511062366051865567576291490713957624476381889356184257128448485309261320039402357213343700983980320943848047912048617651076821823402515801256698349098656408470912313415317954293025892687400961) = true := by decide +kernel
theorem che_35_2_7 : chkE 35 2 31 35 (decH 5 5098026013869676379531581471533440654631373040001068510613205640772496718428679397982343887522829560191347344486270162099079941608032851624661970885281313714078960380409520219126963513252972162211769280746091652459223010642393875827005483285864157614211013183431500981225071762594992129) = true := by decide +kernel
theorem cove_35_2 : CovBE 35 2 3 35 :=
  CovBE.trans (CovBE.of_chk che_35_2_0) (CovBE.trans (CovBE.of_chk che_35_2_1) (CovBE.trans (CovBE.of_chk che_35_2_2) (CovBE.trans (CovBE.of_chk che_35_2_3) (CovBE.trans (CovBE.of_chk che_35_2_4) (CovBE.trans (CovBE.of_chk che_35_2_5) (CovBE.trans (CovBE.of_chk che_35_2_6) (CovBE.of_chk che_35_2_7)))))))

theorem che_35_3_0 : chkE 35 3 4 5 (decH 14 23745250713986859238368652998344958522549360679446925811106314708589022157850728443928166326121983287932006619458156970466490746649438360373633438415259947973392209764176687759894371747816044446692189258233002535005863393892775108265774095576755191304265303202534160125682368233435619560842221069842999193127687587774108752755743419080857048346249069062747622527029550599515191411402234488142517249274839542924763237165397951359594651779838899435533553288932515229328508451669231560509364067451582630024200658108334735256764121614502542633875580287507106855322352669341133838462030607550089312486959770935757811792519626640800941654659) = true := by decide +kernel
theorem che_35_3_1 : chkE 35 3 5 23 (decH 33 110496167746542590937010974272009568475227675121264846570455549716906075580911258452249941197896169597479056005612888468399659657366248251095112946269452903849580892411747029004992252355222874857860648176620295291737791148504304244568652633957541115112375636958034850994964702512718839947126758958226098132198761664620008355399011961537367459754687567976617202696651728766492123432717100258792013616006294816861734597425611223613556408963) = true := by decide +kernel
theorem che_35_3_2 : chkE 35 3 23 26 (decH 17 2372183015855327138304597604526379701252766074034527244291007897794812141019534490982457230637456582652571598543064091211136591569700235725521160027567305081106171908019781334302618405540935272010521051935189231609206325379) = true := by decide +kernel
theorem che_35_3_3 : chkE 35 3 26 27 (decH 5 4503238821882452412091287121626422999912705433607517462439274836889958004921232835350900365849045405654215155581926108604318349080684628366471394675022928406417673563580515927329445032572191686843357257626371183670688677955609403366751894530415711077001829926271020868768137139877957633) = true := by decide +kernel
theorem che_35_3_4 : chkE 35 3 27 28 (decH 5 127499788097914212100004400355405138855423149132740641304859353037296689941181934105650747318357402155843071373193826243068955141982203493098344198572483006969407635925605109761) = true := by decide +kernel
theorem che_35_3_5 : chkE 35 3 28 29 (decH 4 10194971396553622828811891637568390786928313960731345692187291011727807950132909469823413218904164113614009088960007895005046344500944629051844689337356661432402603352055048993661341884025440484397388615751920111617) = true := by decide +kernel
theorem che_35_3_6 : chkE 35 3 29 31 (decH 6 345922727026237349506869425348877862405504294152362545643083140768783335880346375134373090668584888627075579051359315389855119957933160119870665099777213735221890035467187685582768127905824321909903308658210874007358621687075793647493276468270750335299723661421796421502158394918095432931510775930261505) = true := by decide +kernel
theorem che_35_3_7 : chkE 35 3 31 35 (decH 4 125410780163218508420935047982573707949288522300198879999740933020956613102283874037614422712423227801782243496245995598776635972599509047331597502963194941441) = true := by decide +kernel
theorem cove_35_3 : CovBE 35 3 4 35 :=
  CovBE.trans (CovBE.of_chk che_35_3_0) (CovBE.trans (CovBE.of_chk che_35_3_1) (CovBE.trans (CovBE.of_chk che_35_3_2) (CovBE.trans (CovBE.of_chk che_35_3_3) (CovBE.trans (CovBE.of_chk che_35_3_4) (CovBE.trans (CovBE.of_chk che_35_3_5) (CovBE.trans (CovBE.of_chk che_35_3_6) (CovBE.of_chk che_35_3_7)))))))

theorem che_35_4_0 : chkE 35 4 5 20 (decH 33 394087086334377702527508623488454995372396555302368209502037365225992779053314641193111644287122733093866214171563486917798549752164953346089380803785961100670423021489101375204906692552190450934621707455656090553496739809443712957335287470966549325481930443917776615463293803861274593512266862832623117938394523941578574005333749070340838205376808930466561565469613824016878852630428526090950353309969800301274610878729607269214728927417810526996186621786799017014193042673018293970962576314449560215803448235631436645251) = true := by decide +kernel
theorem che_35_4_1 : chkE 35 4 20 26 (decH 37 4311821952742103775603737548254965309705296982803346565213338480987435277616873377894592141007576987134925301222500187618794040786094439992120061253396942515601207403762832695536017911361073619183735089286048947971292393526157120734161387852309529204718836868015529174316591837629245747945881566130293889326137965658432083965023490088035703914280678756033779221421687369283933007302070113962771789275458618751812129435512292486870330743249863147618260504506420181673297187343916270426464215989826874851902637504511738495471855138897261711880004475325453852246147) = true := by decide +kernel
theorem che_35_4_2 : chkE 35 4 26 29 (decH 12 33233437785083580750139978536669770274922223870093131465900211721170474854859636710808427242300268810481251389336335411683648640171506708134339912204582890913198301285172254285367820615968531583574639430570630710387149959378632090812973896060458243216697897506772575802268430323122276493826698855989904237442892410614900335724864861348510941721866157150737112514093042082773786933264618341899284378914817) = true := by decide +kernel
theorem che_35_4_3 : chkE 35 4 29 35 (decH 7 4066302114403822432604538473236017099018330991402022907984743184082785903548449105140065783995154400699450778388584370273633778749171079335331097843766566197496896436249127513684951319443092603884211887957736064549960552821630206247298401196687858383677223436914689) = true := by decide +kernel
theorem cove_35_4 : CovBE 35 4 5 35 :=
  CovBE.trans (CovBE.of_chk che_35_4_0) (CovBE.trans (CovBE.of_chk che_35_4_1) (CovBE.trans (CovBE.of_chk che_35_4_2) (CovBE.of_chk che_35_4_3)))

theorem che_35_5_0 : chkE 35 5 6 7 (decH 11 43934814512757384263919596410100244308884709623640030969312095989114566249470700395600647482567925685093562381024203095086997364380434553044143824457105140521498164085684305957001523759488848489202151814709590431181308216422104158367054336506554378389045088399007089605841656218617284745456471432333757830650160553324959228802560324445323403314272799581828924398636279465730094266757212482308049001591641100183278410300491661153025662198407512679752625724209095586496318544069763) = true := by decide +kernel
theorem che_35_5_1 : chkE 35 5 7 23 (decH 40 17215617409752219181694175971783258124116098647294063296304986066104636631201025259442972642623673179861038362034803415343423099321114654435502396354012831130185690634085690361679499474049914864669018752442442014870592897442567987350506210551818729519262269390745138143118020225611741916969318464595755329755660114361141608292913374334056392955772927372039456308786866408264647362201228565931170386693716087686106569262069297275908755998295174531993867413567414036202604807577254498723652731075721514488024688685928645333177425714521752513264442782205456320309047101851585071958936640787690242053) = true := by decide +kernel
theorem che_35_5_2 : chkE 35 5 23 28 (decH 25 445735841733024160022531025062944971860681431493319196870286783820605832238859245325145881050944158491852721654725912696256338823910071013872091135719781350558034220768982977267077178267825743043667343593299731080216938739009666486236808301261277327687969986312406631148199157348981470908354884838472984598066045511192521941192420938186845809200055375500301228450531232897363613746840520064938007702088015434644664073881731) = true := by decide +kernel
theorem che_35_5_3 : chkE 35 5 28 35 (decH 7 327887146312133729440177449997935730153513786514301813210668509484688808103256256619112285248079362700613755805560842803754710320237643531350804398578681561569188109464579059484463730481420221894987777) = true := by decide +kernel
theorem cove_35_5 : CovBE 35 5 6 35 :=
  CovBE.trans (CovBE.of_chk che_35_5_0) (CovBE.trans (CovBE.of_chk che_35_5_1) (CovBE.trans (CovBE.of_chk che_35_5_2) (CovBE.of_chk che_35_5_3)))

theorem che_35_6_0 : chkE 35 6 7 21 (decH 37 24082137374372214502865219935283293055853005854678712314325108779063587777513533545125810920497822896991683561442281660685785243206870906157891340715845294861137516387121981594014452675590843451399982358383343198695710832295465867519802561809757066465396329605960304548338743779878640995483135165492217484431890995003017414641831714658409762024558643252893759964088708260791939640975084357700083644866034534835233103569754260435986443655700195468638256400851737053261214127034175165437405895350587144097159762789025155) = true := by decide +kernel
theorem che_35_6_1 : chkE 35 6 21 27 (decH 34 2986109957865389755970019116141708938905201963213363746396095911557026728542944155347697353054505950078098457999920169075125594066102260856475158022114560283376815760152023815210738096456421369372212446460574870058592967059330672462583517767452657821036433600944713229100130088125752909886158361198791243199363659747447845311384356800441720668991412757401322489656658462285150100790084833164886323939419465246619301652364726935768826600751302584618999334416803059931536272114988887901891450245783588413025910685834345058227358741601054725868395212585428104267139) = true := by decide +kernel
theorem che_35_6_2 : chkE 35 6 27 35 (decH 7 576570840786602725893839244913146596979940922032145358943795856621779641792982679199652390030921650058698616938741942149232991632271391236210875011) = true := by decide +kernel
theorem cove_35_6 : CovBE 35 6 7 35 :=
  CovBE.trans (CovBE.of_chk che_35_6_0) (CovBE.trans (CovBE.of_chk che_35_6_1) (CovBE.of_chk che_35_6_2))

theorem che_35_7_0 : chkE 35 7 8 11 (decH 20 202859499372645332028948851686843814204137842177253331262747385614291394489759378819031751880913196565961083568998890395682002264085084996330306369727268759805790910433741342829577632945867574062906763296302810456824485223699268449305602002946437107961536534432038566240450643602836022783268325905869581325922243037234059531508569159319335103354176875891195414737105169411633497267768636025005964894779619380996948928145959680321339078432052722106678793782915) = true := by decide +kernel
theorem che_35_7_1 : chkE 35 7 11 26 (decH 36 137210569838901854210604666974502161221640616131023646374174682359460689578944149395485524014277057979566430914559395220316679825285901840842411343111709882819604738924821769578613485239459312563701499976818961649117260998940931477367826272001297500993603969127195433131654585074228836207232084887245467274185850389726423401346146993261820276793298695137442574273745280953774678802476554856054390028505218078171317936663968120648055939863817196367164914237123515892500214187575601391834398622376178863025881925025676573469283774227431429) = true := by decide +kernel
theorem che_35_7_2 : chkE 35 7 26 35 (decH 7 480986876488304413346841038741468223910616547950592069279563287328335292827109479196657594783383827316296532835731959739775086544219919220736501824624891892987064293771628295700918493149549512525991937) = true := by decide +kernel
theorem cove_35_7 : CovBE 35 7 8 35 :=
  CovBE.trans (CovBE.of_chk che_35_7_0) (CovBE.trans (CovBE.of_chk che_35_7_1) (CovBE.of_chk che_35_7_2))

theorem che_35_8_0 : chkE 35 8 9 26 (decH 41 12361264292247835300106700073172371795728659569516589613945841344820433038485926566608698584662902647012255986617061530898183756028206404219195212283183992426102384074312408280040448639888474082125777733008983358599357545226344611748261622284106741958819710252787225232117241650154598544783930426134980444493410961299663456375130594909190232096421335406937156997803140592352997305043763293849895538986221741961618826889295927392848774376887507619234822758427829858693293511859442649149030152548783957377818301503419128661625374864488370544257625785124739) = true := by decide +kernel
theorem che_35_8_1 : chkE 35 8 26 35 (decH 4 935231833980866407579084756605422066358392722558788624050564108617236868564223657554906379014145) = true := by decide +kernel
theorem cove_35_8 : CovBE 35 8 9 35 :=
  CovBE.trans (CovBE.of_chk che_35_8_0) (CovBE.of_chk che_35_8_1)

theorem che_35_9_0 : chkE 35 9 10 35 (decH 23 64514685879645833982807537437805977416525493385191218902674829312058873503046810427451931181141080703567778552966623521672212984313952729244769915155777699336450205867281728453467151492654205453510400069516031773071906027982601693899629242279359368039981796605088124933892953117049162295479638662523023254337487029364834738592445945179097003963017771898836143220144313486544247861092356747491897228338721270843329100968730296171752376451) = true := by decide +kernel
theorem cove_35_9 : CovBE 35 9 10 35 :=
  CovBE.of_chk che_35_9_0

theorem che_35_10_0 : chkE 35 10 11 35 (decH 12 1210464856527661447627315409388589596689408102666391942990841127225542508735691158737510783344564381617467744764243125466768829690041878915) = true := by decide +kernel
theorem cove_35_10 : CovBE 35 10 11 35 :=
  CovBE.of_chk che_35_10_0

theorem che_35_11_0 : chkE 35 11 12 35 (decH 3 120265342817503582339) = true := by decide +kernel
theorem cove_35_11 : CovBE 35 11 12 35 :=
  CovBE.of_chk che_35_11_0

theorem che_35_12_0 : chkE 35 12 13 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_12 : CovBE 35 12 13 35 :=
  CovBE.of_chk che_35_12_0

theorem che_35_13_0 : chkE 35 13 14 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_13 : CovBE 35 13 14 35 :=
  CovBE.of_chk che_35_13_0

theorem che_35_14_0 : chkE 35 14 15 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_14 : CovBE 35 14 15 35 :=
  CovBE.of_chk che_35_14_0

theorem che_35_15_0 : chkE 35 15 16 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_15 : CovBE 35 15 16 35 :=
  CovBE.of_chk che_35_15_0

theorem che_35_16_0 : chkE 35 16 17 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_16 : CovBE 35 16 17 35 :=
  CovBE.of_chk che_35_16_0

theorem che_35_17_0 : chkE 35 17 18 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_17 : CovBE 35 17 18 35 :=
  CovBE.of_chk che_35_17_0

theorem che_35_18_0 : chkE 35 18 19 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_18 : CovBE 35 18 19 35 :=
  CovBE.of_chk che_35_18_0

theorem che_35_19_0 : chkE 35 19 20 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_19 : CovBE 35 19 20 35 :=
  CovBE.of_chk che_35_19_0

theorem che_35_20_0 : chkE 35 20 21 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_20 : CovBE 35 20 21 35 :=
  CovBE.of_chk che_35_20_0

theorem che_35_21_0 : chkE 35 21 22 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_21 : CovBE 35 21 22 35 :=
  CovBE.of_chk che_35_21_0

theorem che_35_22_0 : chkE 35 22 23 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_22 : CovBE 35 22 23 35 :=
  CovBE.of_chk che_35_22_0

theorem che_35_23_0 : chkE 35 23 24 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_23 : CovBE 35 23 24 35 :=
  CovBE.of_chk che_35_23_0

theorem che_35_24_0 : chkE 35 24 25 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_24 : CovBE 35 24 25 35 :=
  CovBE.of_chk che_35_24_0

theorem che_35_25_0 : chkE 35 25 26 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_25 : CovBE 35 25 26 35 :=
  CovBE.of_chk che_35_25_0

theorem che_35_26_0 : chkE 35 26 27 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_26 : CovBE 35 26 27 35 :=
  CovBE.of_chk che_35_26_0

theorem che_35_27_0 : chkE 35 27 28 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_27 : CovBE 35 27 28 35 :=
  CovBE.of_chk che_35_27_0

theorem che_35_28_0 : chkE 35 28 29 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_28 : CovBE 35 28 29 35 :=
  CovBE.of_chk che_35_28_0

theorem che_35_29_0 : chkE 35 29 30 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_29 : CovBE 35 29 30 35 :=
  CovBE.of_chk che_35_29_0

theorem che_35_30_0 : chkE 35 30 31 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_30 : CovBE 35 30 31 35 :=
  CovBE.of_chk che_35_30_0

theorem che_35_31_0 : chkE 35 31 32 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_31 : CovBE 35 31 32 35 :=
  CovBE.of_chk che_35_31_0

theorem che_35_32_0 : chkE 35 32 33 35 (decH 1 0) = true := by decide +kernel
theorem cove_35_32 : CovBE 35 32 33 35 :=
  CovBE.of_chk che_35_32_0

theorem cove_35 : CovQE 35 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_35_2) (CovAE.trans (CovAE.one cove_35_3) (CovAE.trans (CovAE.one cove_35_4) (CovAE.trans (CovAE.one cove_35_5) (CovAE.trans (CovAE.one cove_35_6) (CovAE.trans (CovAE.one cove_35_7) (CovAE.trans (CovAE.one cove_35_8) (CovAE.trans (CovAE.one cove_35_9) (CovAE.trans (CovAE.one cove_35_10) (CovAE.trans (CovAE.one cove_35_11) (CovAE.trans (CovAE.one cove_35_12) (CovAE.trans (CovAE.one cove_35_13) (CovAE.trans (CovAE.one cove_35_14) (CovAE.trans (CovAE.one cove_35_15) (CovAE.trans (CovAE.one cove_35_16) (CovAE.trans (CovAE.one cove_35_17) (CovAE.trans (CovAE.one cove_35_18) (CovAE.trans (CovAE.one cove_35_19) (CovAE.trans (CovAE.one cove_35_20) (CovAE.trans (CovAE.one cove_35_21) (CovAE.trans (CovAE.one cove_35_22) (CovAE.trans (CovAE.one cove_35_23) (CovAE.trans (CovAE.one cove_35_24) (CovAE.trans (CovAE.one cove_35_25) (CovAE.trans (CovAE.one cove_35_26) (CovAE.trans (CovAE.one cove_35_27) (CovAE.trans (CovAE.one cove_35_28) (CovAE.trans (CovAE.one cove_35_29) (CovAE.trans (CovAE.one cove_35_30) (CovAE.trans (CovAE.one cove_35_31) (CovAE.one cove_35_32)))))))))))))))))))))))))))))))

/-! ### `N = 36` -/

theorem che_36_2_0 : chkE 36 2 3 4 (decH 16 12066802488930231286730796898484322686312742572060714505258261373491217486997821723741698982945292268445603067929990945778222076715400537382736640704702723699171817575755771807604261539966963820065649678354895663550037594741600142629496848114122287480620141280514922438243214824903508007856257691305786577153345715817501176302779077845594874007644203532637231124793787962757636346125145692752923771456473717574448123465292843999416388632206237946643587016699900348217262444364918701242311012507477527833436184055318617111501395104728613593942307066634611934350643519492592045207722185110514644302649999506628764196334206127791526902802053233512479678139435204423091143532942764658670738196934967518792027176302645460455452833144067074343043) = true := by decide +kernel
theorem che_36_2_1 : chkE 36 2 4 26 (decH 40 761596987716276358557862114847937101150539026662129564431906622490497879268647446542547857441099464015411382720308654342755736976488469656445608125602692422581023834921408438882814355140389689052960770564604662823577908160293173975714676038281514731541811764336492034917207729110509970587458098037193900603197003712923637177566633866500543077104045718755314346016347843164774500013182135895982570912885386896495873810108726149251) = true := by decide +kernel
theorem che_36_2_2 : chkE 36 2 26 28 (decH 10 1989133573614163967409040807052159087163504472428965873178705598987020417234129666864213068592895615583032206599229261077623101875124068711709040948195417060856953795372660046464300810308556232562760850183677122473391673223842370380283694871031061774624472487963924082823799741306079737622491879148989753359127267588345118324035400934314370434204336874635395) = true := by decide +kernel
theorem che_36_2_3 : chkE 36 2 28 29 (decH 5 1288662578963893872406124804861087019514259340511187041751821122144543375613419887627492478565079068111507749811022387776784220596948985601975814114650629165739094560395496937205414372731075943915136138285156997254865966654987160518481154788469747328846028507429032558421175486184909547214721153) = true := by decide +kernel
theorem che_36_2_4 : chkE 36 2 29 30 (decH 4 22792411632793378826892787153111488777655272001999813816989868874393006141975983630961318777445829503732517291479268689736560792488672407099137689437939206218985057456500005936443312169981085939893566302420400146953523329) = true := by decide +kernel
theorem che_36_2_5 : chkE 36 2 30 32 (decH 6 72859830244227162045657259994414612600088373472309157192572964570764557473270321471716149116183767032832634170661392733794660452335888428655717069020810642103158655396238970710992804196682900168705478233043961058940543666383335331176383042377923361790585798614294726133778384686983808484047546693627043366363656166496570746842783050499125895062515873009903894710816897) = true := by decide +kernel
theorem che_36_2_6 : chkE 36 2 32 36 (decH 5 91153558971985239238531476313241888706182636298888550051260424821569442908428409407165035081494220496292348418016557901758460815818353420102418505797384486304033434243976106342146108749116143525971960664391464939179527330008767763906669466770730332976906483349900003665333764889082448968880257) = true := by decide +kernel
theorem cove_36_2 : CovBE 36 2 3 36 :=
  CovBE.trans (CovBE.of_chk che_36_2_0) (CovBE.trans (CovBE.of_chk che_36_2_1) (CovBE.trans (CovBE.of_chk che_36_2_2) (CovBE.trans (CovBE.of_chk che_36_2_3) (CovBE.trans (CovBE.of_chk che_36_2_4) (CovBE.trans (CovBE.of_chk che_36_2_5) (CovBE.of_chk che_36_2_6))))))

theorem che_36_3_0 : chkE 36 3 4 5 (decH 14 1153670556368161858197486548461917220870647162947255064671026984866562542695070545823570944546316062307630312879418836352152847556946019067920209008419538166007815752868422360895587298759939037092494745449177513370277535213270326964226589771986129404547) = true := by decide +kernel
theorem che_36_3_1 : chkE 36 3 5 22 (decH 29 68014372250863147076923898865890838521645847290539365657828443436494414445834254998345650977967391198331014096538115803017184220129399822479236051267743530621392962203694955646062582533176223655379868356230642276230357529298532728213109039190505102318066136591564209038003124274789541435264180228005722415833716273567053476935501817422982001036967232107446997186819515118590497338303422402675331) = true := by decide +kernel
theorem che_36_3_2 : chkE 36 3 22 27 (decH 30 1044588006690954791601266560022839816263598205695818865561388631999472811011877483725744778487541219630299964104079543390538713952629425064018542412105048227358377111172677230828429983221536065084668936790246750937440014092231383122150118380222010548278300930293432991973556051200726811209630095694576372388170706752161159170941829754061967452560646504290633668857958547587) = true := by decide +kernel
theorem che_36_3_3 : chkE 36 3 27 28 (decH 5 2088956528679293641423629388562251031100089563348399968450034250280204387986219283457808671859470823181202297698602112269170867768336969929488008112356385572683519244903856036204673) = true := by decide +kernel
theorem che_36_3_4 : chkE 36 3 28 29 (decH 5 1288662578963893872406124804861087019514259568727261458457364190927072384961124159598178357640993663098954475747821001679202310072844105863462424781616409969198191453722451492798026013636708596526058413673752199519293140520146534946064068155665378901036281432864617321696388770132096794170495105) = true := by decide +kernel
theorem che_36_3_5 : chkE 36 3 29 30 (decH 4 29048325285923472770579674630442131387228331245899161310995697767924594783451438801094332113316138663707791394993707115740779931824955418099967310828840541430894721) = true := by decide +kernel
theorem che_36_3_6 : chkE 36 3 30 32 (decH 6 98514286038780867813233864200911478373836447198528674385114195645194818995279475268996259019462587197052760535545227143015966141026980783761243960948416763134333390226751641402491901065656819467635862950321382082886209796024295972961240616004377494367745532946019119818191718194229969636904087608770915769651329) = true := by decide +kernel
theorem che_36_3_7 : chkE 36 3 32 36 (decH 4 24204418612147484496995556714060757613849322826120911151947158887217451020306241641858879944600854334011136190646062816459665448796483779475816339117246836426359752478596426820177311181296180151448424768535595991339241601) = true := by decide +kernel
theorem cove_36_3 : CovBE 36 3 4 36 :=
  CovBE.trans (CovBE.of_chk che_36_3_0) (CovBE.trans (CovBE.of_chk che_36_3_1) (CovBE.trans (CovBE.of_chk che_36_3_2) (CovBE.trans (CovBE.of_chk che_36_3_3) (CovBE.trans (CovBE.of_chk che_36_3_4) (CovBE.trans (CovBE.of_chk che_36_3_5) (CovBE.trans (CovBE.of_chk che_36_3_6) (CovBE.of_chk che_36_3_7)))))))

theorem che_36_4_0 : chkE 36 4 5 6 (decH 13 54006928912123577209779623007014245364341858888294265068937929393087883680400988797758765998540537541417861030595540969032235267553719976550316994909637542663610109219985224795792901411661983500153755721963594956130809291000539125735523520286738924677825408371004926755049105671477047106392828081533371283536754062589072277782741874247897563561133079117573473001500498188842760040018138323939949127559420314001420399147500848700732251021949421850145500139705266835501018832844138001772307524940476848474340672684412398457317793552214038317536818319743852256907801259776120243075) = true := by decide +kernel
theorem che_36_4_1 : chkE 36 4 6 23 (decH 37 174803856089024610813985735791534395843113181346415080191317967471791202723305354286247394896312234291932107005667776990238902793457405911243708633614994674081160027704261233532246876903443787132804561694137739217405614578455144587054259835971616370825247317219392272682856214181451922063948625647712159671379811978049949031145684324643766397534951291121676704264439921899079420395349417976475426208147492861024625073140763304779266478115541548199671775813939346467237315557655588072696488224191832693976715824555310922262280002715506419779430182937169677850613866524876183276531784438465708037) = true := by decide +kernel
theorem che_36_4_2 : chkE 36 4 23 28 (decH 27 20010989573387451556234868397041329911881459478835863875203402837514067054531440086972499846031511073087982619417709896593344302967576034945156906435064660306444583142967231256578551126565529646496201824923211722196557464047499478202494624582452136255868762321242225840381354206340130748777687300179934990008480099481057789955264153257033375228293837581452369692620879746360970322228723895569152679088772079307976140346548723733448879519323881592878027536079639217216967182211) = true := by decide +kernel
theorem che_36_4_3 : chkE 36 4 28 32 (decH 13 876746109343703775560933831134757267667951678146284685472003467215310701438242095996533857595963122474652272054395124701563601219670490817624584787403500712437929994536697658443261203352658430605232119625938095265448503504652706818341748358634622586985917259181242159046526691478699460897884501556319099683396203612145672688563073426524497702749624927472627760317468964113666485929122127702312791901301901407545034871320160407681) = true := by decide +kernel
theorem che_36_4_4 : chkE 36 4 32 36 (decH 2 946082466972384590975970368715477088237821500559526909547657802486894721) = true := by decide +kernel
theorem cove_36_4 : CovBE 36 4 5 36 :=
  CovBE.trans (CovBE.of_chk che_36_4_0) (CovBE.trans (CovBE.of_chk che_36_4_1) (CovBE.trans (CovBE.of_chk che_36_4_2) (CovBE.trans (CovBE.of_chk che_36_4_3) (CovBE.of_chk che_36_4_4))))

theorem che_36_5_0 : chkE 36 5 6 21 (decH 39 1601200694447908873324823318549922228084809158577841340145741107842097795383326478723710299140488552069411543683754799438287985834194963855606704972627932681197886021482262288914987106364780640460220667334134231586269578840257094663930201565054471356063308080389184926800088928312224614859400018318518286270801462961418657882634436128715905708896949133219865388009943189604177530969109066237404670216927598152153386463474905895531917124431189239166473710740619920842821029727912784716669645495135244808211834881155) = true := by decide +kernel
theorem che_36_5_1 : chkE 36 5 21 28 (decH 41 1682190318485636456629583631113080019704409170867126903581157135736642841260548344086673920676415461618812360252211989849993841428565726289664207859746309590995057128376911959299056790992815138169460280193247775455827305768359948382906279525368398572326118035014351282204326353865701992799839686376486343903323157655876147813653609497830144945793066662740615643221677411977318694318161679967275205397983534717463726454383866030859189668531155320004231239290603243161803225025653858524525295820860399042694030849007736370083108772379246292506831892446419154037362815738824043267026523764311171) = true := by decide +kernel
theorem che_36_5_2 : chkE 36 5 28 36 (decH 11 95286650905062514397415184585737375360581403788776655324619736351784136282511161408698810182490788581884921336912831691799777407749300692271187524217194892853466880449343047233959126951872559910747951439250647540157948469850477995402096484598716149010349377364834160769) = true := by decide +kernel
theorem cove_36_5 : CovBE 36 5 6 36 :=
  CovBE.trans (CovBE.of_chk che_36_5_0) (CovBE.trans (CovBE.of_chk che_36_5_1) (CovBE.of_chk che_36_5_2))

theorem che_36_6_0 : chkE 36 6 7 8 (decH 10 5517009890364942207942966941262801607881951965061733976909087012807914650598632032069018264344914688228029756499250639617541618213790495556070189589074019606981460653994239981195766947256175109546076421252072269896725352773326239356237523608487460836061105697041856929153447379671491116199231618380877397133083187388442808540465595889720993646587195592702185362615222834426261446835623791626161148509308487869321495939) = true := by decide +kernel
theorem che_36_6_1 : chkE 36 6 8 23 (decH 38 26415735153872413818458221675989163901082676156502516842382836214075034830452238437208540542846376229228375296415611782160972465325283832453807787650721845728449882313299586873374191923765736520450856639338052019095020816048511913770855370681845191119425528940364748826962114072552193465705895253148787989310773975406055317542904191548716738487839238653750683624046691531423795491806846092678350133657178983565264463717133066938460247951979318793588679181878875076336290802133950001465120724779452508512083946098581170859087028233369197826386204956511057881807708473259916132730214838931555684166066200632837080875013) = true := by decide +kernel
theorem che_36_6_2 : chkE 36 6 23 30 (decH 32 64482971877963265399494740639762039981743623326254776891368236371468437560638962459334893542693601835187733719622240850319693813459548839427872529081132290481264502314806034240821699298970214625748532925637596026633321386182600869410512710796122127466691572363006822933492148045988565414513429701111929684465936680469032491254842627013714179077959666284527498472588543394634063305302370528454214883290836221629562096725391198767830256854706915911288618473280123915858993330443143298837213372231855518150697481385773144260055744883737795485521539) = true := by decide +kernel
theorem che_36_6_3 : chkE 36 6 30 36 (decH 2 1387794233154125162936754196163990184320236626128498138744539328998232193) = true := by decide +kernel
theorem cove_36_6 : CovBE 36 6 7 36 :=
  CovBE.trans (CovBE.of_chk che_36_6_0) (CovBE.trans (CovBE.of_chk che_36_6_1) (CovBE.trans (CovBE.of_chk che_36_6_2) (CovBE.of_chk che_36_6_3)))

theorem che_36_7_0 : chkE 36 7 8 22 (decH 37 178776075091956377459463246382647989121415260476467558664940625943412902589766727518683548350140685469743965530154652936565882343414409499656095649936682028220555704729351886066873506031067035593692987272700989793396376921828737545147704190312936450447943230827913160316076076826653343917459511317035764394028439766669366996815591010356802072326034541135608273494471069134161586384445011345954700689931915642788589000782963134399609176392432628115900513257122348133400340220241161621322993809176289380919363515465210081406749787779) = true := by decide +kernel
theorem che_36_7_1 : chkE 36 7 22 29 (decH 34 28550411889377157531251294698315890279602388753520364480284973214590262365119533125247751776610886749208129264329281933909506244241144223966748753989874294035704446854273134812413609121298795248597304419105226867179716793441501271422617723011467597427230782405354449823268547161326055767632673627840350760980536501347932791236120361990978888207142268207773912634764708450808156723100394754312642583149743308865722331233254353780909915656100994737870859007807501098898767613388712905480318755951427256287705914905834676907610639954545246339) = true := by decide +kernel
theorem che_36_7_2 : chkE 36 7 29 36 (decH 2 31480963) = true := by decide +kernel
theorem cove_36_7 : CovBE 36 7 8 36 :=
  CovBE.trans (CovBE.of_chk che_36_7_0) (CovBE.trans (CovBE.of_chk che_36_7_1) (CovBE.of_chk che_36_7_2))

theorem che_36_8_0 : chkE 36 8 9 23 (decH 27 4977181996351025670645764945896162809972124897049132745440111265698324906609179329603146588093882091555138500221335689548188416312337037636794635135109807209853971847259770316631640535026311165483329318153347411342217322864583952279404689304377470098140820455272681682011043604930032016533829031075264401036945503494774203226437520887273686361274826074875333972706858242129734699184950797275292564902841860001877775933243510855117517035165600372031728364081141353876025085382877100749938219277834453611609444849653691178862467) = true := by decide +kernel
theorem che_36_8_1 : chkE 36 8 23 36 (decH 22 69645988993805364671284056965874977847130671532539720535415314770555974484408391051911759802916689982841623544653129508734860177151797483006971924458610599775780644733213894201786394954803908993863438742575502596643325761541957744190908335527904075927055950010700668751223474169108583955058737373131688495387293706291375210773023791649944253854916827450197891) = true := by decide +kernel
theorem cove_36_8 : CovBE 36 8 9 36 :=
  CovBE.trans (CovBE.of_chk che_36_8_0) (CovBE.of_chk che_36_8_1)

theorem che_36_9_0 : chkE 36 9 10 36 (decH 31 218240005549177142182572352387000790320161396569785499479707369850549925679261709296571510391833376803222852947635960580296913241489851610465604971666904294757403289657624865259749351989065797761730862410803119408687187997028806260544212201193036571091575400265706414242298142212839949479712994078666315324240028175383651861742440392983336731611086993688307555891009601021660790905438017126150825446633939169094456840179580246514500388995) = true := by decide +kernel
theorem cove_36_9 : CovBE 36 9 10 36 :=
  CovBE.of_chk che_36_9_0

theorem che_36_10_0 : chkE 36 10 11 36 (decH 14 5740622824964750892245464441914308888790792203190187061454052072502780199250620387891128806070719252880457890235343918958685704794626128744678614120788546208769983385082366720076574411139) = true := by decide +kernel
theorem cove_36_10 : CovBE 36 10 11 36 :=
  CovBE.of_chk che_36_10_0

theorem che_36_11_0 : chkE 36 11 12 36 (decH 6 1306722315996819850258100433590119927932801331227533156305539) = true := by decide +kernel
theorem cove_36_11 : CovBE 36 11 12 36 :=
  CovBE.of_chk che_36_11_0

theorem che_36_12_0 : chkE 36 12 13 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_12 : CovBE 36 12 13 36 :=
  CovBE.of_chk che_36_12_0

theorem che_36_13_0 : chkE 36 13 14 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_13 : CovBE 36 13 14 36 :=
  CovBE.of_chk che_36_13_0

theorem che_36_14_0 : chkE 36 14 15 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_14 : CovBE 36 14 15 36 :=
  CovBE.of_chk che_36_14_0

theorem che_36_15_0 : chkE 36 15 16 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_15 : CovBE 36 15 16 36 :=
  CovBE.of_chk che_36_15_0

theorem che_36_16_0 : chkE 36 16 17 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_16 : CovBE 36 16 17 36 :=
  CovBE.of_chk che_36_16_0

theorem che_36_17_0 : chkE 36 17 18 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_17 : CovBE 36 17 18 36 :=
  CovBE.of_chk che_36_17_0

theorem che_36_18_0 : chkE 36 18 19 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_18 : CovBE 36 18 19 36 :=
  CovBE.of_chk che_36_18_0

theorem che_36_19_0 : chkE 36 19 20 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_19 : CovBE 36 19 20 36 :=
  CovBE.of_chk che_36_19_0

theorem che_36_20_0 : chkE 36 20 21 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_20 : CovBE 36 20 21 36 :=
  CovBE.of_chk che_36_20_0

theorem che_36_21_0 : chkE 36 21 22 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_21 : CovBE 36 21 22 36 :=
  CovBE.of_chk che_36_21_0

theorem che_36_22_0 : chkE 36 22 23 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_22 : CovBE 36 22 23 36 :=
  CovBE.of_chk che_36_22_0

theorem che_36_23_0 : chkE 36 23 24 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_23 : CovBE 36 23 24 36 :=
  CovBE.of_chk che_36_23_0

theorem che_36_24_0 : chkE 36 24 25 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_24 : CovBE 36 24 25 36 :=
  CovBE.of_chk che_36_24_0

theorem che_36_25_0 : chkE 36 25 26 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_25 : CovBE 36 25 26 36 :=
  CovBE.of_chk che_36_25_0

theorem che_36_26_0 : chkE 36 26 27 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_26 : CovBE 36 26 27 36 :=
  CovBE.of_chk che_36_26_0

theorem che_36_27_0 : chkE 36 27 28 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_27 : CovBE 36 27 28 36 :=
  CovBE.of_chk che_36_27_0

theorem che_36_28_0 : chkE 36 28 29 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_28 : CovBE 36 28 29 36 :=
  CovBE.of_chk che_36_28_0

theorem che_36_29_0 : chkE 36 29 30 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_29 : CovBE 36 29 30 36 :=
  CovBE.of_chk che_36_29_0

theorem che_36_30_0 : chkE 36 30 31 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_30 : CovBE 36 30 31 36 :=
  CovBE.of_chk che_36_30_0

theorem che_36_31_0 : chkE 36 31 32 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_31 : CovBE 36 31 32 36 :=
  CovBE.of_chk che_36_31_0

theorem che_36_32_0 : chkE 36 32 33 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_32 : CovBE 36 32 33 36 :=
  CovBE.of_chk che_36_32_0

theorem che_36_33_0 : chkE 36 33 34 36 (decH 1 0) = true := by decide +kernel
theorem cove_36_33 : CovBE 36 33 34 36 :=
  CovBE.of_chk che_36_33_0

theorem cove_36 : CovQE 36 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_36_2) (CovAE.trans (CovAE.one cove_36_3) (CovAE.trans (CovAE.one cove_36_4) (CovAE.trans (CovAE.one cove_36_5) (CovAE.trans (CovAE.one cove_36_6) (CovAE.trans (CovAE.one cove_36_7) (CovAE.trans (CovAE.one cove_36_8) (CovAE.trans (CovAE.one cove_36_9) (CovAE.trans (CovAE.one cove_36_10) (CovAE.trans (CovAE.one cove_36_11) (CovAE.trans (CovAE.one cove_36_12) (CovAE.trans (CovAE.one cove_36_13) (CovAE.trans (CovAE.one cove_36_14) (CovAE.trans (CovAE.one cove_36_15) (CovAE.trans (CovAE.one cove_36_16) (CovAE.trans (CovAE.one cove_36_17) (CovAE.trans (CovAE.one cove_36_18) (CovAE.trans (CovAE.one cove_36_19) (CovAE.trans (CovAE.one cove_36_20) (CovAE.trans (CovAE.one cove_36_21) (CovAE.trans (CovAE.one cove_36_22) (CovAE.trans (CovAE.one cove_36_23) (CovAE.trans (CovAE.one cove_36_24) (CovAE.trans (CovAE.one cove_36_25) (CovAE.trans (CovAE.one cove_36_26) (CovAE.trans (CovAE.one cove_36_27) (CovAE.trans (CovAE.one cove_36_28) (CovAE.trans (CovAE.one cove_36_29) (CovAE.trans (CovAE.one cove_36_30) (CovAE.trans (CovAE.one cove_36_31) (CovAE.trans (CovAE.one cove_36_32) (CovAE.one cove_36_33))))))))))))))))))))))))))))))))

/-! ### `N = 37` -/

theorem che_37_2_0 : chkE 37 2 3 4 (decH 16 990351351767676502336110937934610749446043829235639776984543754804638852103013174560655359102918338995513159278496748673300135016728950066749503408716086917707067372454121859221333589804986275734692982095429043902172305695142958183592157250071037037327211929004931734618541670440398450619679464170675600373010914949163282449560685418221530450923730590174841373244218041086272078084615312697987764982797844611) = true := by decide +kernel
theorem che_37_2_1 : chkE 37 2 4 24 (decH 31 1954331182644826527666446056533466020868321437117751726565942756583262002564965636410853190180401829573267791566768276917688583893939975776749350761590814089000760382406231879388922649986654523051861303917968025271368966669068218904704309284667658509987413863092165988585001820581540744380766905666913513667509520686099872963578611709854821348714779686201634865283) = true := by decide +kernel
theorem che_37_2_2 : chkE 37 2 24 27 (decH 18 25751082516913716671464632958047541238886663847781856797480732820277888271218547758879107362773989757756371866337035825859832329194760384289869953862537934153716403582067857835404626971393351767626392384452074944845072644269173831999710909380476706093303905066200236404657976477204273779995668876344167345422929622412819363618943969318490369) = true := by decide +kernel
theorem che_37_2_3 : chkE 37 2 27 28 (decH 6 2504655608600032249293514288760668183447246225113948808290108379672957339458806759838195245416281088932653384878670449899908618815343213157965365045266993428203962241109588480507443592578812458410516647605017733417777892785293809604290065741581061339198477432138889775469752896280728458594611014450323111799134489414800941448513600842144699125685874726216468004656919220274483457) = true := by decide +kernel
theorem che_37_2_4 : chkE 37 2 28 29 (decH 5 346090232942427379067873729532878809041578559947977989260180999784010256392372349273286048878797981932779641669927243722118616115757839284623658068043480924655856652476618714453636543330921063273429027106544101803004006581099325794402379501784011303557731780342276941377093824496060866405881382730879233) = true := by decide +kernel
theorem che_37_2_5 : chkE 37 2 29 30 (decH 5 346090232942427379067873729532878809073821131151372237339653502160832991253787037936829780503678893052414992680549795068598244861210168413554740508592384098273809004873394679713732679776333721678204193022048986326010472548805004533797471439978427160412313023103735320678085370271045549332239099351109889) = true := by decide +kernel
theorem che_37_2_6 : chkE 37 2 30 31 (decH 4 47822297391403371793180392219343219753602531691036927352214891216650921827961083032397172075390654382942215126030782389619072791799987566381953632913851620378510899808677315866677661564688710913678666199782106696084171516154113) = true := by decide +kernel
theorem che_37_2_7 : chkE 37 2 31 33 (decH 6 2659747295344712371113161816382733595897969452709704956817819178001187470267840407716205127433963507542883063684921591156578686987466924875737740038697706446021027307049627086678913399976836089488760927430483386918693917903072296125623695839801120452785891538631156140432671706964242980579305044760469255777124971427943002135866086494261062818999991069720452582631243518589636865) = true := by decide +kernel
theorem che_37_2_8 : chkE 37 2 33 37 (decH 5 388950587540952408645721534914909261369586588052782809872008476423689660993094446990329871493118685147386372555759837140555565348906737641759880456784852989405530195408160033939616434127209941296439775635060890663879725240546797785565292841681168923140987630775978609827413380099076933763532784224588033) = true := by decide +kernel
theorem cove_37_2 : CovBE 37 2 3 37 :=
  CovBE.trans (CovBE.of_chk che_37_2_0) (CovBE.trans (CovBE.of_chk che_37_2_1) (CovBE.trans (CovBE.of_chk che_37_2_2) (CovBE.trans (CovBE.of_chk che_37_2_3) (CovBE.trans (CovBE.of_chk che_37_2_4) (CovBE.trans (CovBE.of_chk che_37_2_5) (CovBE.trans (CovBE.of_chk che_37_2_6) (CovBE.trans (CovBE.of_chk che_37_2_7) (CovBE.of_chk che_37_2_8))))))))

theorem che_37_3_0 : chkE 37 3 4 5 (decH 15 903248817253876787632730567096272379775100051184141596198717889922270085954559357226217434927553583530579934006183663567257229087894032476875092236375252170830411786436131237051963431897331979834725372304518260835224208053097057596177592755303080227692300764533790840905984462267709176045754704201931948248271795639150508047578110147289706828799126353491056920272430700545496795057540841324910463470142895140387011195683376788942608937567644465506992467797512365248906839716496964665993720035615506305327513657082442862685575536309146403931451709669506678808418787487961893150761731202000182602785220649759723913707895979725334056466458425991589826206509043784925277765236728431973581172018780121344023857674206920993488498890876417579665113731) = true := by decide +kernel
theorem che_37_3_1 : chkE 37 3 5 23 (decH 29 93593894626659532786087918358142651217576538166124063969944487377797873948225620116843459574121438691356006121084308594271939368652720612635914643413247207935965470192615712430824875428543824609772350009125744601716478341144912877463284392107621441313084315999614449678039196646453664977869314207912316339704031435353072488029739212830612703412585545195657649601804501647114323806633666306245294832803439214355333253) = true := by decide +kernel
theorem che_37_3_2 : chkE 37 3 23 27 (decH 25 21812015319290111792381228596795097663448932734245155021072107770719520437516001597942069625000940957124353357234787916677626558933829554320853466633064891613277435845657794618647364624378889478610100886237888982073877384446619008394868007128845526114779814124669484275056688168758724210515941208333861674336964703191683) = true := by decide +kernel
theorem che_37_3_3 : chkE 37 3 27 28 (decH 6 248308450945173496186805867195835913108972776774395233868087335638326739303777190089783528860177725182328574323474075159888484814400006069883056223848286374146128945804041543247544419214633938094858831905640546710433680933647983977177585888348427939753429930241) = true := by decide +kernel
theorem che_37_3_4 : chkE 37 3 28 29 (decH 5 346091468448134587406932911411675726626291029174766915718064868497435163887664343967183929074620679701010559133636379501852649198603085444659660473591875541134662563457145125886335294736505548493642327493845786087321221581384243141556442875015161960386382767725244046579795031949340131673872150630355201) = true := by decide +kernel
theorem che_37_3_5 : chkE 37 3 29 30 (decH 5 36366613791571399170622316841993065591549794609099140739500491290670474531915351722836956485016743222061025415862914359705951082544584515150851049349798744809649952185867806342467916033) = true := by decide +kernel
theorem che_37_3_6 : chkE 37 3 30 31 (decH 4 47822468111972530125263992205158942680120407285754262176165551955706967723537407053608171589431642794788418346803957130917733615082716498662648539599596241221469114698475547920051396767945877377597099707073641136253631023386881) = true := by decide +kernel
theorem che_37_3_7 : chkE 37 3 31 33 (decH 6 26482725177912697252394878346607715963719988406306665663474546970021196774858021743204402400341608496035406770149740483992875147125461203493878667467805114048573155434201621113625822894646927232266758502440528171049628639426165362673596699216841962701629424368059632911885940549518783404476345729654726294696513319047425) = true := by decide +kernel
theorem che_37_3_8 : chkE 37 3 33 37 (decH 4 33896856212403200749171762144357332615014213838368096362852801593063350069631535537787339724173148096682150030749371913292038205918776307934784373020289722740383977729) = true := by decide +kernel
theorem cove_37_3 : CovBE 37 3 4 37 :=
  CovBE.trans (CovBE.of_chk che_37_3_0) (CovBE.trans (CovBE.of_chk che_37_3_1) (CovBE.trans (CovBE.of_chk che_37_3_2) (CovBE.trans (CovBE.of_chk che_37_3_3) (CovBE.trans (CovBE.of_chk che_37_3_4) (CovBE.trans (CovBE.of_chk che_37_3_5) (CovBE.trans (CovBE.of_chk che_37_3_6) (CovBE.trans (CovBE.of_chk che_37_3_7) (CovBE.of_chk che_37_3_8))))))))

theorem che_37_4_0 : chkE 37 4 5 6 (decH 13 4512802021020300005342844933300964127889758290186433075401839266632524222852910847989901612131436712389959113887352030286856829352699179317569558655386972002299562763056264068579544271620902197954977284393753677338954989136999817699915586356099) = true := by decide +kernel
theorem che_37_4_1 : chkE 37 4 6 22 (decH 32 136654733897903663818211416353707483885285994874448895306880604347809461432638886779389941763189889413109289289259065329309731109145983664313184353358078469521778062243575884263874141848398002358525035076911502202618056675341102731745911559942117647139860350758024742534274319436962175658868107890988858423155150699944152759671726057614936879493610389652040977294573920994650284392243433578219873505149947481282462297695918310302103670752724993534043978118772507914178911933679049035155722773411544324813901076915345337234486337850122230765475109301271880249167812204183557) = true := by decide +kernel
theorem che_37_4_2 : chkE 37 4 22 27 (decH 32 1249487227170317133680985940251423444756530296910267943264587908395777367010550714120686226886020387513443511395437402945249270880058092887992258915704515555052842872408873731288805507506052813618476369327286980576595744901076151223632290396948705495954381088428140949654673965121363249273551728124899129563062767900171035377530899509481791353132999447348610792661955368309854655478574448516324309881362589657032544422113405380353299048389832301582606010306895490640363583258174343272124694659) = true := by decide +kernel
theorem che_37_4_3 : chkE 37 4 27 29 (decH 10 3804272351118726235463467727920040823349404428281353381767804109337549822724127687621116795862949719932575122125133420747985045085665778893288805183279057539542617304720514290380377811957181905752570302155182662388870947972316725644949166167576090348339998165930241) = true := by decide +kernel
theorem che_37_4_4 : chkE 37 4 29 32 (decH 11 42303392694981809190232841971783059805346546970302120735047528815185676382696489587343897021708917434264116022321715156197482519671257239195953919622845904700511802173592677764408921377390304047820252385867015973794394896201821572462293653775696814522100616145418624197520241317091016585665433224056260331024533245126689366786862653760175682266372292141951264489598298502461428561972375211332744945963265) = true := by decide +kernel
theorem che_37_4_5 : chkE 37 4 32 37 (decH 4 505644000941075229800050307113349311727575923784067440913051055123386203694742122337962322077044447654632876837852083081512552788739157955216548468748743171635438768385) = true := by decide +kernel
theorem cove_37_4 : CovBE 37 4 5 37 :=
  CovBE.trans (CovBE.of_chk che_37_4_0) (CovBE.trans (CovBE.of_chk che_37_4_1) (CovBE.trans (CovBE.of_chk che_37_4_2) (CovBE.trans (CovBE.of_chk che_37_4_3) (CovBE.trans (CovBE.of_chk che_37_4_4) (CovBE.of_chk che_37_4_5)))))

theorem che_37_5_0 : chkE 37 5 6 7 (decH 12 6150176022507469306259333667720854571549667949181029179801518092708375962277664009669701166198773570472081073670721275098705386611305989945954821262544770452308792637685435070921156587523019860140973708578563065807340279491647562050518994223402610991552829380274788850681163136722109353672770518993415940739645414242195319957704148733348968617661840317302842031174559530337794825844066775282465399572887391357819674019132680858839903266198228879657440298639395152325768557541213346799834405324083536592802338825338876280519368586422823949497806225602407725469700936771056965829763) = true := by decide +kernel
theorem che_37_5_1 : chkE 37 5 7 23 (decH 37 173267221867098729704024708726994168876845995361764438347672331263928385191773996867287575923786188089409029826966271349798164960409521759728324106721627876295502889754232221774245590401556438156781383569427851193187062788105170250059822708132435277150907240735317348508387232090960737257208347653273417001167679579634065780433292671793584065705673859045737804032432287849502303800217963672098683721368450445502340940586288219767447207486398876835770809193274741781347132420550016566014867289912715324727456599917699) = true := by decide +kernel
theorem che_37_5_2 : chkE 37 5 23 28 (decH 30 1005603764614750192738190112521566383555440149800917211880631347102035781081634628147342576885331887103592279602505333318672524759746471688189587014890002676682596542243464660083441855509495019881699001364662481818769240222020355266341132489869692060395766928749370899089100797715180270763431871376079833246408797666676763353871972924452630630082371654067213341461140199601667252637433319613208498894158725468880934899300943260093598963866422228457821328182267375673306967915984999974019) = true := by decide +kernel
theorem che_37_5_3 : chkE 37 5 28 30 (decH 9 98469694801086963383517848369076209417468450531353144658863165217948417346833145681758701563677701823608126361441057408683444044536335387994189345734869002499575416145938650763306559312594463130682329202032592612119006556508153245629118544598858207406332244261213724610610821306870432064649675770710631976915201) = true := by decide +kernel
theorem che_37_5_4 : chkE 37 5 30 37 (decH 7 239197231165991392500358917935751015207134534635964477500242147643689496918829257777559634754558990489534842058545380326439620395212694704910322516428275397520553865121676156082678031399549231404924926719238600303280176156619473576307804633582262557528313911883990137530919095711100202635395089894542553182937902786744122403439929348353) = true := by decide +kernel
theorem cove_37_5 : CovBE 37 5 6 37 :=
  CovBE.trans (CovBE.of_chk che_37_5_0) (CovBE.trans (CovBE.of_chk che_37_5_1) (CovBE.trans (CovBE.of_chk che_37_5_2) (CovBE.trans (CovBE.of_chk che_37_5_3) (CovBE.of_chk che_37_5_4))))

theorem che_37_6_0 : chkE 37 6 7 11 (decH 35 9502531407202593716513840344706245377742421075505247774597681959417383431817760086936236024808567040782399710344597738541034334185714125851224287594685992903967476513085947931201057740358192511288272498798822571621561428546890911040211044869327814217877159484384027428535423490129665333351384079677583962039106897905281325684169723680070841483435614399019915048557415548311523471009226670470718575024728154547937470301681726324805483902145864816260331427375214296581507) = true := by decide +kernel
theorem che_37_6_1 : chkE 37 6 11 27 (decH 39 44913374214518889359492910766382728085353793334671888342138854252108750068821302475099322553228892213845084531918032855007343871637332606502757727644395033093247388249462933183704115811884047437015307837598405521291454900267183487115697065591667396727401053736428532125270390028302023109119747974168299062766405063715154195435438213726492792071215791250652867826920511593036916462707607983371284058747010983141350836418555355650931292120329582637982933465257564001074555546086389013898987910888964952159414603894122701523062880870873805405900332782499142001729543760471209494326032859397) = true := by decide +kernel
theorem che_37_6_2 : chkE 37 6 27 37 (decH 16 11791444844368674344218267724753885570616873368879329708838793220475927625153866539386196378355579784408169581826374629889462296761351038365147358893398818226083814959288846691280247662082140061930642954465848226308566135031389392264415805911699573003435197136746285912702403040715463539632418196480231286251894554901807334080434735693999116516383363) = true := by decide +kernel
theorem cove_37_6 : CovBE 37 6 7 37 :=
  CovBE.trans (CovBE.of_chk che_37_6_0) (CovBE.trans (CovBE.of_chk che_37_6_1) (CovBE.of_chk che_37_6_2))

theorem che_37_7_0 : chkE 37 7 8 9 (decH 9 24307570529091349288056915061529683202806810055844274451049768804469821363813429003173700821463855360732810495009407714212841786545115608818070259484968981530323907079569269613629385291026777364341668151274815431448830283439953635830962568028768612613640663592047696195292151423017297526042370564133520336322403532854071557832257134526526847904320112259) = true := by decide +kernel
theorem che_37_7_1 : chkE 37 7 9 24 (decH 39 36495078385219329731297771543542544551522021627533507447855962412207523736180481158214950732626675672885961109971816706961792496651607579398132012744696129306421203041697054359584857819308450567887392710833190875154327847577237676141022666206704301687954561509134586776010338927123532740969056402005278868491349832069642766184143517346555232987478826541558908267742397339862181730316020048583341369103301125774357356750155547135051488414039439586311255582776347889423652276815321980700429121000551024599054323033279838039990446933983550868381442816916081236455079489961613492273285) = true := by decide +kernel
theorem che_37_7_2 : chkE 37 7 24 30 (decH 27 203954755034210276793505455678850358198468511500892474054792396034336710797093524553572123397867138352083044996017546268825255336092828393355855963715980906350193550605326720196655665784998634435875857854666149217457663341216551187833487915645730520661685295301011186450067251707889254701120753038908064996879926680148442171883578031323600977455772317859192571319833355886040114235800749296395916409250909350122320974799812526032103194755) = true := by decide +kernel
theorem che_37_7_3 : chkE 37 7 30 37 (decH 2 178082850600879606064094010517402374428195079549283419997404397787245072641) = true := by decide +kernel
theorem cove_37_7 : CovBE 37 7 8 37 :=
  CovBE.trans (CovBE.of_chk che_37_7_0) (CovBE.trans (CovBE.of_chk che_37_7_1) (CovBE.trans (CovBE.of_chk che_37_7_2) (CovBE.of_chk che_37_7_3)))

theorem che_37_8_0 : chkE 37 8 9 24 (decH 38 426241554805497512531567037818820598262171129224314647358752312292053653150052512999366012571013870234712669371973152662409839372710066711723466877176890958728229885276165180856265065688051843400527738838609199550395411114396461936036561520039289972884631895601597239486589309178281060012898908116638053819383978946787144469747836479386467154096601125638115559641252666428773868256312168651214824918603785876961171842220242049979557651168884022988039711079568054971048603493922459615757604426256283127733125256471962994563) = true := by decide +kernel
theorem che_37_8_1 : chkE 37 8 24 37 (decH 22 32308954988700514124554849651964829628156898323981958235791766027966639392370161271911280960268209707617107557701672371916473600648517347720201468703828640547373322667006479804237378166209352486930950432719370193922581252146966943118503597072214927714151591154377037948309558828777904274649228552564018256958744111749109912746357263502601711268440048195560589187) = true := by decide +kernel
theorem cove_37_8 : CovBE 37 8 9 37 :=
  CovBE.trans (CovBE.of_chk che_37_8_0) (CovBE.of_chk che_37_8_1)

theorem che_37_9_0 : chkE 37 9 10 25 (decH 24 105911179116956963145630386817692272061102830751306602891252711083742652670569069974685407818817726991939574752653728257786473649851731039166418836224813646157243491090778440456944647719527942831472589658455551937140650686895576736389985450573133090408604579310602684398544708972943060456474197600350831767123706223897640970299218174962284901907536649047464455749065023029345757860367858338297491875053906049390589683814782816941937682090821213067724931) = true := by decide +kernel
theorem che_37_9_1 : chkE 37 9 25 37 (decH 11 38774561286456884336208066049793500746566872994007291452726577730061683871995914577024011753378260993253501163123362821827986132366194692349196399524904768660679687400388185551801097156886551091331) = true := by decide +kernel
theorem cove_37_9 : CovBE 37 9 10 37 :=
  CovBE.trans (CovBE.of_chk che_37_9_0) (CovBE.of_chk che_37_9_1)

theorem che_37_10_0 : chkE 37 10 11 37 (decH 20 6269704396631655386068733488752017777003709166546129786862887378781589415957034326162814970473159849972489341028135548724424502894509055429973472838041683746875226046151549423532058226549865743851402497329086875490064380501152858841953220070370986371) = true := by decide +kernel
theorem cove_37_10 : CovBE 37 10 11 37 :=
  CovBE.of_chk che_37_10_0

theorem che_37_11_0 : chkE 37 11 12 37 (decH 7 20481009877067302778923954318486755048841255915527442960414971010908646052776579) = true := by decide +kernel
theorem cove_37_11 : CovBE 37 11 12 37 :=
  CovBE.of_chk che_37_11_0

theorem che_37_12_0 : chkE 37 12 13 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_12 : CovBE 37 12 13 37 :=
  CovBE.of_chk che_37_12_0

theorem che_37_13_0 : chkE 37 13 14 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_13 : CovBE 37 13 14 37 :=
  CovBE.of_chk che_37_13_0

theorem che_37_14_0 : chkE 37 14 15 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_14 : CovBE 37 14 15 37 :=
  CovBE.of_chk che_37_14_0

theorem che_37_15_0 : chkE 37 15 16 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_15 : CovBE 37 15 16 37 :=
  CovBE.of_chk che_37_15_0

theorem che_37_16_0 : chkE 37 16 17 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_16 : CovBE 37 16 17 37 :=
  CovBE.of_chk che_37_16_0

theorem che_37_17_0 : chkE 37 17 18 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_17 : CovBE 37 17 18 37 :=
  CovBE.of_chk che_37_17_0

theorem che_37_18_0 : chkE 37 18 19 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_18 : CovBE 37 18 19 37 :=
  CovBE.of_chk che_37_18_0

theorem che_37_19_0 : chkE 37 19 20 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_19 : CovBE 37 19 20 37 :=
  CovBE.of_chk che_37_19_0

theorem che_37_20_0 : chkE 37 20 21 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_20 : CovBE 37 20 21 37 :=
  CovBE.of_chk che_37_20_0

theorem che_37_21_0 : chkE 37 21 22 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_21 : CovBE 37 21 22 37 :=
  CovBE.of_chk che_37_21_0

theorem che_37_22_0 : chkE 37 22 23 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_22 : CovBE 37 22 23 37 :=
  CovBE.of_chk che_37_22_0

theorem che_37_23_0 : chkE 37 23 24 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_23 : CovBE 37 23 24 37 :=
  CovBE.of_chk che_37_23_0

theorem che_37_24_0 : chkE 37 24 25 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_24 : CovBE 37 24 25 37 :=
  CovBE.of_chk che_37_24_0

theorem che_37_25_0 : chkE 37 25 26 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_25 : CovBE 37 25 26 37 :=
  CovBE.of_chk che_37_25_0

theorem che_37_26_0 : chkE 37 26 27 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_26 : CovBE 37 26 27 37 :=
  CovBE.of_chk che_37_26_0

theorem che_37_27_0 : chkE 37 27 28 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_27 : CovBE 37 27 28 37 :=
  CovBE.of_chk che_37_27_0

theorem che_37_28_0 : chkE 37 28 29 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_28 : CovBE 37 28 29 37 :=
  CovBE.of_chk che_37_28_0

theorem che_37_29_0 : chkE 37 29 30 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_29 : CovBE 37 29 30 37 :=
  CovBE.of_chk che_37_29_0

theorem che_37_30_0 : chkE 37 30 31 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_30 : CovBE 37 30 31 37 :=
  CovBE.of_chk che_37_30_0

theorem che_37_31_0 : chkE 37 31 32 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_31 : CovBE 37 31 32 37 :=
  CovBE.of_chk che_37_31_0

theorem che_37_32_0 : chkE 37 32 33 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_32 : CovBE 37 32 33 37 :=
  CovBE.of_chk che_37_32_0

theorem che_37_33_0 : chkE 37 33 34 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_33 : CovBE 37 33 34 37 :=
  CovBE.of_chk che_37_33_0

theorem che_37_34_0 : chkE 37 34 35 37 (decH 1 0) = true := by decide +kernel
theorem cove_37_34 : CovBE 37 34 35 37 :=
  CovBE.of_chk che_37_34_0

theorem cove_37 : CovQE 37 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_37_2) (CovAE.trans (CovAE.one cove_37_3) (CovAE.trans (CovAE.one cove_37_4) (CovAE.trans (CovAE.one cove_37_5) (CovAE.trans (CovAE.one cove_37_6) (CovAE.trans (CovAE.one cove_37_7) (CovAE.trans (CovAE.one cove_37_8) (CovAE.trans (CovAE.one cove_37_9) (CovAE.trans (CovAE.one cove_37_10) (CovAE.trans (CovAE.one cove_37_11) (CovAE.trans (CovAE.one cove_37_12) (CovAE.trans (CovAE.one cove_37_13) (CovAE.trans (CovAE.one cove_37_14) (CovAE.trans (CovAE.one cove_37_15) (CovAE.trans (CovAE.one cove_37_16) (CovAE.trans (CovAE.one cove_37_17) (CovAE.trans (CovAE.one cove_37_18) (CovAE.trans (CovAE.one cove_37_19) (CovAE.trans (CovAE.one cove_37_20) (CovAE.trans (CovAE.one cove_37_21) (CovAE.trans (CovAE.one cove_37_22) (CovAE.trans (CovAE.one cove_37_23) (CovAE.trans (CovAE.one cove_37_24) (CovAE.trans (CovAE.one cove_37_25) (CovAE.trans (CovAE.one cove_37_26) (CovAE.trans (CovAE.one cove_37_27) (CovAE.trans (CovAE.one cove_37_28) (CovAE.trans (CovAE.one cove_37_29) (CovAE.trans (CovAE.one cove_37_30) (CovAE.trans (CovAE.one cove_37_31) (CovAE.trans (CovAE.one cove_37_32) (CovAE.trans (CovAE.one cove_37_33) (CovAE.one cove_37_34)))))))))))))))))))))))))))))))))

/-! ### `N = 38` -/

theorem che_38_2_0 : chkE 38 2 3 4 (decH 17 1003729543774505126320244628734127802665213763423056217792112385081887944206813844623851206367448272982580474589377278203348444235218519464803926132005757518255260059179681157901471170563201977588038465485829114440210329705913275826010350731778355076291551015080841658108832924435198996285357127434608625320722509963673628479068029011134552503366722090885167435979738665663917977253382639480728257011386987890426531144079732753082217554889547477630268906884735595308772081886837751117475497481201941956830270829338040691718562212005155239429550665237241870083220575028567463754005724341984055408235739324571726748101768884438253753412080756624321223287011000639640576209921078013845782103325015896430141796170074070477956111688387718828661442563156744905709140765825263093337433908222289229498851502465478663598218133803026922009644309785441391638692806787) = true := by decide +kernel
theorem che_38_2_1 : chkE 38 2 4 26 (decH 37 33350771541288274258126765579012815844423325439127014869256616979803405247265178242489064492493361006748236106148617603253974918389126359354505133410651690221024573817355532584228884242771583197690248381402543530064387004837578017770998775312512902747970739444289240447360996338236884397682650632403903100257102383011773637527606550684555530598800595554347610198963299128987642511491) = true := by decide +kernel
theorem che_38_2_2 : chkE 38 2 26 28 (decH 12 1314857064121437308360628468146138141557521487640593687129803796462240215721327656299866592235818506704662652901935476942651807992482152579) = true := by decide +kernel
theorem che_38_2_3 : chkE 38 2 28 29 (decH 6 86059664591220716970221826295843117961122900033466944394700708666471952577125348356260105900798921051350710839944232043502163275509589116498500303985779878610651655135649454661498713252935178504045300258673445534783606155882181769875394998475846904407405929705021237112905316760576437274411824036856747086316110024278581054725339150108299765384765699633874611175059712970185928948540920193) = true := by decide +kernel
theorem che_38_2_4 : chkE 38 2 29 30 (decH 5 92903221150584630630386613796023857739256213023314190385687194846723305026959358497002527561812451237582083676057093407933667024985266640747326493000609741854080958445214583025635351129568774039608979687953431215998370350249161803279122758421131792741740591670023833964949641678726560693195345089109294775112065) = true := by decide +kernel
theorem che_38_2_5 : chkE 38 2 30 31 (decH 5 98655839613750443051343584451847235368926529851702144904728064763800138112219527035007490498233874766969374427515696361948056712135136331690356692779906011251929250683661021455126310325938762701098557291977374446372814437218064759727932970076947735050061828794204124574001103729555324082331527583036686794772865) = true := by decide +kernel
theorem che_38_2_6 : chkE 38 2 31 32 (decH 4 106501057481089054463978548424063492815595285100309913187160481619610604673196225604868542983664327719264361163236195681520104638712891768341780536171590352377070717537651422682810848929378417159731462880841680918185266813021016412545) = true := by decide +kernel
theorem che_38_2_7 : chkE 38 2 32 34 (decH 6 91388526274701963527436284781627561762385118831414131238281053031743270973004544567567035108247948372809600695698088215783002910561727539143140353414562503033352367705241353837323261646690219969091644984814180649300411867237452296620355251397863287118962686016749031217644016796333818164902213266122541655704152936159083825224357905664009350893887303471096012077650756039564365152947294593) = true := by decide +kernel
theorem che_38_2_8 : chkE 38 2 34 38 (decH 5 6613594101703527993984929976937464044853525527928865990286832951399044191689918901089090732751282382707376152480962451693786843649520395925452662958290105298757993582261318829769679335514364325912270560340868238255788779394149199317831783132652120459493089287841137076756029270324106730611838248031264144888193) = true := by decide +kernel
theorem cove_38_2 : CovBE 38 2 3 38 :=
  CovBE.trans (CovBE.of_chk che_38_2_0) (CovBE.trans (CovBE.of_chk che_38_2_1) (CovBE.trans (CovBE.of_chk che_38_2_2) (CovBE.trans (CovBE.of_chk che_38_2_3) (CovBE.trans (CovBE.of_chk che_38_2_4) (CovBE.trans (CovBE.of_chk che_38_2_5) (CovBE.trans (CovBE.of_chk che_38_2_6) (CovBE.trans (CovBE.of_chk che_38_2_7) (CovBE.of_chk che_38_2_8))))))))

theorem che_38_3_0 : chkE 38 3 4 5 (decH 15 301228520985784235815152433192718516715064976335048777966870040371135834291698388838966408737698067061777781639800615608879908479166335916523838371740191648866883145324200046383538853378323732403061857943540260594586225872321828517787856859341458291799153484450244312243219242031450081146067388907180733122097170142094083635866994313544323) = true := by decide +kernel
theorem che_38_3_1 : chkE 38 3 5 22 (decH 23 3261067425522944491853003737746600219518028929380492324419819454255841006070871600677094375424327065182566516348213098099740024378519516505887684958328238033926877575642694323239647050189483696920563800418509475223494382700172970062453389889366416172550985186840615175092083447394497711860194900228280641693501856548830914076170745863430045530843478398985106750217247767384325583997421508027781725906256454637051105820805) = true := by decide +kernel
theorem che_38_3_2 : chkE 38 3 22 28 (decH 40 172728266499781591118676032177836104537336301859933872907175565426483935978731967173738328413298790384676897362104534122301845224353696469412650377413087165128234470782143833861017201984812049177034066456203047016993358889765217206511847644190023424189832724976282789543763294168033345671797619329997388877328893587028617494822397040982880034081756250784781833098642521465170250049901669254997855183901914895824474633272331705162491548407163550633861111553115466104209125425394359429060542644355) = true := by decide +kernel
theorem che_38_3_3 : chkE 38 3 28 29 (decH 6 86059664591220716970221826296401317278184094056993242797639223236342063501906008008000494385795605675129825057400227808215277999553191677920633103381926678482272807893355869894842902138879821961416607428333315310590370646887196098133028464684801974715064553889591384350421351544678268550888200508853502479829066448957453646470843226046568330901219705620922049500623763873217345626722193793) = true := by decide +kernel
theorem che_38_3_4 : chkE 38 3 29 30 (decH 5 595830600490778165539007069092727998195088935742597374498968116540555080767220470589084282681053557228215131711344613479465827261420878869525575198398336043354216814539628298919052591927681) = true := by decide +kernel
theorem che_38_3_5 : chkE 38 3 30 31 (decH 5 98655839613750443051343584451847235368926529851702129529333599371774067131288566632049438531750227177586131311177744080078616467932000393118746028427188401958533315802823792440006078138961933294864009247799956181455311352827486737622036303107688213698840669512953582602110733542515875799099621080286396368195969) = true := by decide +kernel
theorem che_38_3_6 : chkE 38 3 31 32 (decH 4 8284471347664810337234208446199419550502766055429633020062065810377657041595363733248837167565152407642152964075793236840006159105058702245320899434363739406067214707970433) = true := by decide +kernel
theorem che_38_3_7 : chkE 38 3 32 34 (decH 6 7516460681157136800305833810311662715048880461154474274691405930795028004072240176644226281973642849450598649672611555328150032250553565657970485281015123850415676155975416241535742949595262062940926244157110967011210444858817744067651920532394167187957875506625412548140793663564165231391276498565195304262996318069032816578945) = true := by decide +kernel
theorem che_38_3_8 : chkE 38 3 34 38 (decH 4 112711129845394973133840132173592831932661187049295173982168877117148519915661231620180946662075654651330703022805943777766389932772598930849473703561515694441612183246704304520622338200688396750429520661740288337867316301648512962945) = true := by decide +kernel
theorem cove_38_3 : CovBE 38 3 4 38 :=
  CovBE.trans (CovBE.of_chk che_38_3_0) (CovBE.trans (CovBE.of_chk che_38_3_1) (CovBE.trans (CovBE.of_chk che_38_3_2) (CovBE.trans (CovBE.of_chk che_38_3_3) (CovBE.trans (CovBE.of_chk che_38_3_4) (CovBE.trans (CovBE.of_chk che_38_3_5) (CovBE.trans (CovBE.of_chk che_38_3_6) (CovBE.trans (CovBE.of_chk che_38_3_7) (CovBE.of_chk che_38_3_8))))))))

theorem che_38_4_0 : chkE 38 4 5 6 (decH 14 15964033406411788848066465456601626015603529064502736766696793728128760365250769772566325144172206408451764097963851021971915991810205557463785102406281876258461246018766219961401564656959833944506642721530054063396105665195415234726838571434283006765345737224606716806858358196987158363842609503787489421128057192172865354852055713641401378935965716067382075790922371795462689310425386008147278815633560327313461006224611385608975453814525818686418830977222234282670617946410274659538754928537373513159158979305855072214982255005376288035696970336147471063860519233016581484408091370240273991245669401731121771318158101988433665271373274494319699365265731401196495192676331749604639619) = true := by decide +kernel
theorem che_38_4_1 : chkE 38 4 6 24 (decH 40 65401887202781438087947074824139119164101470127560404427141445321811182885990565798992162087284738818099209663688409670802668704133961073367168209440190392377689578520817360023673985385674544912138143848721412889191034258631143788055915693659179199704570073394816294711662400863310914919362375054061223615121047311863067342558555851054116375183698176585910896295835958671624578185859548806294148163628707037680708847550828724929197110574298159220935251146217001156039947516138298563441913143658489455733465858726535723022665247511317804436330264321182027875110659950524148316904870097894761068826582942469819797593046271723051637905321263120389) = true := by decide +kernel
theorem che_38_4_2 : chkE 38 4 24 29 (decH 30 958336009047814535879945732696387451931728952268808696091483540784534174243210178069118090767604566024988010416900531175185522779407552020015814240326705405624454002676923979214051771351635866012367694233768963293572417968917676906367622897105401316091520192855440176292307810063214333179730303095401118472153290288306327086846391740887080386452722025819312793184985789797161360906462664599881172958507396525033880500189945837007135069644976477281919523284199872626095385795017076783497176046921970027748798784835841544612266115) = true := by decide +kernel
theorem che_38_4_3 : chkE 38 4 29 32 (decH 12 54553104044378052222892864631683318395133573647902710536209824106721305413859960948177413141375655467030765780712659037604048161453633567187796785742357365659123013052436575439432399611734677588347850476915448828044679461998527206868246905422678697341593709732031346854181915814182709462914150857655965350642960053566534980291171728683905427435720197144732244801573249) = true := by decide +kernel
theorem che_38_4_4 : chkE 38 4 32 38 (decH 7 4994817497988084736791817986800288510435062930706295393919863579517630982574080322098972662762232417272476150320189745580918993931418255691855080899391056612238044326432185836006056947138561396640332210702252808925031663163904863228972309636293199638559776122956959679491598736462209) = true := by decide +kernel
theorem cove_38_4 : CovBE 38 4 5 38 :=
  CovBE.trans (CovBE.of_chk che_38_4_0) (CovBE.trans (CovBE.of_chk che_38_4_1) (CovBE.trans (CovBE.of_chk che_38_4_2) (CovBE.trans (CovBE.of_chk che_38_4_3) (CovBE.of_chk che_38_4_4))))

theorem che_38_5_0 : chkE 38 5 6 9 (decH 33 646287527846206518229383776656367626901139064580888192604783597401125029354706309337325905428515720133864333637499774070915111049664650402793636052416304046268924478235439452988118743062793957914453023146771198751872872099656652858722858814208407029420356930741725888219454911829400979421007768120611303155583852441074668136842160858108728389464241516102557060806970463794273340194504200575165618312959051886850942210211325698224388317985531901657028962933109214430283326107380800781354922515287856543450243) = true := by decide +kernel
theorem che_38_5_1 : chkE 38 5 9 25 (decH 33 17665176242012614683011021040907682587410735944609019536023318490206872821294799386087589177529353400647807972300174987537195425703993374827908256120059522871873721510683858882532587124507811808319727405468838697089249603394183862063850107399092079919692657343065348096269799324268379263621143080589010740563007739268364293141925652276940278024155482928695659347953643596676858759962127884533837606034265795079835679847782275600514170743143983647285095045160603631832676680330140696363886560403091707892840891804756527273659149285348130949) = true := by decide +kernel
theorem che_38_5_2 : chkE 38 5 25 29 (decH 23 851781874619650466062236437645170128209187643411423306577160228078156629152432742791183840284219760709447869728036017168962124924195983350575284758090866167690637911434902193091756305596396571199928001291247276833611126429662491109827172715659217231581906714406283291300813334953799670218728065018847474048300553927313659091704269638158952281932510854471115410482988772035215077092408944029499419889377445316055461239983206084697686562510551350610070642682285296003) = true := by decide +kernel
theorem che_38_5_3 : chkE 38 5 29 32 (decH 12 701307638253091667033344962505106244035400478780729869075268131387461316909531991228602410031000531309381199698944322895796114007764439994588028793904987629048980003322828063054517956488523214369064643566333325142864837786707948306448252231076260442031730267403352984247881885444462516441265440386999993776722233137169363203102059687216902583176203676656351457585377411690065313343013080084239544369945625776488984290710849524097) = true := by decide +kernel
theorem che_38_5_4 : chkE 38 5 32 38 (decH 4 8284500831646413631745238676766822691111699674175102207391496817615730959053538255758265630724694612620265104643809515068471756305652231627287485290520627657283698283762049) = true := by decide +kernel
theorem cove_38_5 : CovBE 38 5 6 38 :=
  CovBE.trans (CovBE.of_chk che_38_5_0) (CovBE.trans (CovBE.of_chk che_38_5_1) (CovBE.trans (CovBE.of_chk che_38_5_2) (CovBE.trans (CovBE.of_chk che_38_5_3) (CovBE.of_chk che_38_5_4))))

theorem che_38_6_0 : chkE 38 6 7 8 (decH 11 6062513312063672847473269971786731769555027372048876071374178397309256138722589701305035101254382253134180737255813984244989127825029621622313374704037441998658656840586287268277698971914619210971908680570052992706083034509321749671451261744674223082302793013650374237362121601884650795888609524126825765887841763796611076307536848152363572053340636232080153543466760363249810201115287935236380537494816070561773946235702622498983358008752420560910977108830231311862359195448418585788341698732438644500680233011168643) = true := by decide +kernel
theorem che_38_6_1 : chkE 38 6 8 23 (decH 35 634290121694250706568097603857286524480240920240210313481474199735185998171872777043646168138116559220693838684044625025861398543361644084101627525993327243190489370247879172967710029264183168189239128601408299286108333152407395536107595151268779495649098862542200433833495473000903029782909535397339118629178331169544320196031444447449466751023157292761433740952068917835135858165339770013771564740038701218686474624522522173306196557335375867430022134543896446062369092813958931773513247399993989598203304948060878758047198061985261153622692480728724967688273925) = true := by decide +kernel
theorem che_38_6_2 : chkE 38 6 23 28 (decH 32 82363255739106555307904311743023382502631150465118517487773594252634989017868979042314483535403972746774839247284157635715171542035627801281283563178109381457704232501073472710625540101148254873994165500426001584077256241200829530912428752578621555955624880709634181655300949967349606812763912565587490632530166180657746079479029957510667715763755598655696553524451806511553732923968820076494473804479474129449441864827941397894868032711632470993632614694787938070797614352907309032686979) = true := by decide +kernel
theorem che_38_6_3 : chkE 38 6 28 38 (decH 16 87149942039622306893410719826407885736623444982360873385232691929836010713406040160163626097529316972862062089144692465663820585343092908825357210398122239238474088596055291213307342583273734527389604240472973704275067530791390377880878274636687608615983068082586266985207671196513267739468013533196539619440933028256832533201816699538767579053378754626101369399903729414080576341301137108736186253583902139600299106931073) = true := by decide +kernel
theorem cove_38_6 : CovBE 38 6 7 38 :=
  CovBE.trans (CovBE.of_chk che_38_6_0) (CovBE.trans (CovBE.of_chk che_38_6_1) (CovBE.trans (CovBE.of_chk che_38_6_2) (CovBE.of_chk che_38_6_3)))

theorem che_38_7_0 : chkE 38 7 8 13 (decH 37 1735300878488124802606771246660293454443892463840972323231378628700788899873176314986849643279915288971313729596595554035843074097806036207617472352858797696065317049122435755376388051648875399450200048425893967263505162332932102944551207195718322661920720870013632562964353645836773280680151427788848594410069537980633890255063082271920837317538868905538129936883007764888067397709327344004098629128635162679951480036352705548765920133009488442985909753699697559940359553284816411322547500558843602371985100483126217011309216251528835) = true := by decide +kernel
theorem che_38_7_1 : chkE 38 7 13 28 (decH 38 1741539140358297110459650897543336215923297023022093387004934277215930263388090834834662814038417696465557138702753668955191778003365082497456151719830186903674476941062868058638325454054664931831610298029092629160323993406129974494733794936832374806562433551036116359400979677889713979636578325011538219274128468328192172586133310732264706690730866739215657080339975366253894182093558904371589106407328450715579232298737074901541633518682915216071134117967658563131188714708806547773108649312214977051918332111996811311853458113740933) = true := by decide +kernel
theorem che_38_7_2 : chkE 38 7 28 38 (decH 11 27802799029131840800984952996822093402419697468013756108021036055763736774241662947685812402117887599506557199047314167456870384679324143414203667066470459580619848572435357446723595152768502815327657212111672089380378370562002223266407829195519595096999151790191533302305165697) = true := by decide +kernel
theorem cove_38_7 : CovBE 38 7 8 38 :=
  CovBE.trans (CovBE.of_chk che_38_7_0) (CovBE.trans (CovBE.of_chk che_38_7_1) (CovBE.of_chk che_38_7_2))

theorem che_38_8_0 : chkE 38 8 9 12 (decH 20 502255793245570276417252632823024816002828390516688591689548375267172679028761905975864927306610567115996816731852392332662726012880472608730700965079679405832033500106021958319457308419038624370283362316187038912382297624512079384419387156541709113596245376228245104981538864216084742323776465768850923762999183404085206017429687064161414589421210375135127524071607575897602540329983780809571001425072899046920589191653599225939359917178859944451891023868072014463923794119351997613955) = true := by decide +kernel
theorem che_38_8_1 : chkE 38 8 12 28 (decH 39 96249940011448129921182735506134391930019538683203596578768828614615725129386831479645934604973836063169816782171084645572412432380414745984889276640427746910832962469366868286010220994542584876366857690400228042012220881936288682898994218078348916584092967553282869999943007666164760772205503674826281508790392389000230977118656797281058723817477457973024077716356340511144466490330999224116678622703951472756127555599458922129382318246637412563134908939279263620527388647041789988654344526178063231106080383795194852374599338612610251638531801501208147630740610502360869437145895698437) = true := by decide +kernel
theorem che_38_8_2 : chkE 38 8 28 38 (decH 7 2794042698533513848674093569472316325347006401232611323691273963129013881862911141352499014507988222855346584041936735942568583105095239564932513957969997057782244856188317778761631712788827323096569205356654580097) = true := by decide +kernel
theorem cove_38_8 : CovBE 38 8 9 38 :=
  CovBE.trans (CovBE.of_chk che_38_8_0) (CovBE.trans (CovBE.of_chk che_38_8_1) (CovBE.of_chk che_38_8_2))

theorem che_38_9_0 : chkE 38 9 10 28 (decH 41 17229087832069622234577674283870206300355847572687770015869505857574402155339279206853016633067591854270147105902401726015115192324765909476171613881826840140254928325722631691512291500013562251023882581735999342756804962567031022371121505736752194781474899567799564391399953213754878491219437222114900037480381782611454032507971410104286349146317521185547483242702108852376230340850544997376991903546853067995788356594213212241695277625780687344877147422846063609010337949669303302101910530971506480771878724560148778810285326543425204280418619019357979355010871160198401628266395768744474331267) = true := by decide +kernel
theorem che_38_9_1 : chkE 38 9 28 38 (decH 4 2101341533275329446108451434684695602167937595613708816562790540827050058132297018085450864377916117377) = true := by decide +kernel
theorem cove_38_9 : CovBE 38 9 10 38 :=
  CovBE.trans (CovBE.of_chk che_38_9_0) (CovBE.of_chk che_38_9_1)

theorem che_38_10_0 : chkE 38 10 11 38 (decH 23 94700641443487922934504547796043257666157341576560663090859412228763245857532003150245138409730431703333213794890467342951515840111229458745686283979389483781626564286342066992082001866047563266129210694255136082855366476020322783445099707077399612134582210492019299238090723108542145694062292225106882363556098551806623960755821786945890727476226440173262232218642780110051155874613927309723868055659989593561421371710686238503436247740230117563768749738371) = true := by decide +kernel
theorem cove_38_10 : CovBE 38 10 11 38 :=
  CovBE.of_chk che_38_10_0

theorem che_38_11_0 : chkE 38 11 12 38 (decH 12 349911771301642651080838226296699362058060495890247828247967122754901790185640239995601670423939319678459997050252817386143511568224774761620720259) = true := by decide +kernel
theorem cove_38_11 : CovBE 38 11 12 38 :=
  CovBE.of_chk che_38_11_0

theorem che_38_12_0 : chkE 38 12 13 38 (decH 3 129560781245030374019) = true := by decide +kernel
theorem cove_38_12 : CovBE 38 12 13 38 :=
  CovBE.of_chk che_38_12_0

theorem che_38_13_0 : chkE 38 13 14 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_13 : CovBE 38 13 14 38 :=
  CovBE.of_chk che_38_13_0

theorem che_38_14_0 : chkE 38 14 15 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_14 : CovBE 38 14 15 38 :=
  CovBE.of_chk che_38_14_0

theorem che_38_15_0 : chkE 38 15 16 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_15 : CovBE 38 15 16 38 :=
  CovBE.of_chk che_38_15_0

theorem che_38_16_0 : chkE 38 16 17 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_16 : CovBE 38 16 17 38 :=
  CovBE.of_chk che_38_16_0

theorem che_38_17_0 : chkE 38 17 18 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_17 : CovBE 38 17 18 38 :=
  CovBE.of_chk che_38_17_0

theorem che_38_18_0 : chkE 38 18 19 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_18 : CovBE 38 18 19 38 :=
  CovBE.of_chk che_38_18_0

theorem che_38_19_0 : chkE 38 19 20 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_19 : CovBE 38 19 20 38 :=
  CovBE.of_chk che_38_19_0

theorem che_38_20_0 : chkE 38 20 21 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_20 : CovBE 38 20 21 38 :=
  CovBE.of_chk che_38_20_0

theorem che_38_21_0 : chkE 38 21 22 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_21 : CovBE 38 21 22 38 :=
  CovBE.of_chk che_38_21_0

theorem che_38_22_0 : chkE 38 22 23 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_22 : CovBE 38 22 23 38 :=
  CovBE.of_chk che_38_22_0

theorem che_38_23_0 : chkE 38 23 24 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_23 : CovBE 38 23 24 38 :=
  CovBE.of_chk che_38_23_0

theorem che_38_24_0 : chkE 38 24 25 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_24 : CovBE 38 24 25 38 :=
  CovBE.of_chk che_38_24_0

theorem che_38_25_0 : chkE 38 25 26 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_25 : CovBE 38 25 26 38 :=
  CovBE.of_chk che_38_25_0

theorem che_38_26_0 : chkE 38 26 27 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_26 : CovBE 38 26 27 38 :=
  CovBE.of_chk che_38_26_0

theorem che_38_27_0 : chkE 38 27 28 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_27 : CovBE 38 27 28 38 :=
  CovBE.of_chk che_38_27_0

theorem che_38_28_0 : chkE 38 28 29 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_28 : CovBE 38 28 29 38 :=
  CovBE.of_chk che_38_28_0

theorem che_38_29_0 : chkE 38 29 30 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_29 : CovBE 38 29 30 38 :=
  CovBE.of_chk che_38_29_0

theorem che_38_30_0 : chkE 38 30 31 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_30 : CovBE 38 30 31 38 :=
  CovBE.of_chk che_38_30_0

theorem che_38_31_0 : chkE 38 31 32 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_31 : CovBE 38 31 32 38 :=
  CovBE.of_chk che_38_31_0

theorem che_38_32_0 : chkE 38 32 33 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_32 : CovBE 38 32 33 38 :=
  CovBE.of_chk che_38_32_0

theorem che_38_33_0 : chkE 38 33 34 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_33 : CovBE 38 33 34 38 :=
  CovBE.of_chk che_38_33_0

theorem che_38_34_0 : chkE 38 34 35 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_34 : CovBE 38 34 35 38 :=
  CovBE.of_chk che_38_34_0

theorem che_38_35_0 : chkE 38 35 36 38 (decH 1 0) = true := by decide +kernel
theorem cove_38_35 : CovBE 38 35 36 38 :=
  CovBE.of_chk che_38_35_0

theorem cove_38 : CovQE 38 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_38_2) (CovAE.trans (CovAE.one cove_38_3) (CovAE.trans (CovAE.one cove_38_4) (CovAE.trans (CovAE.one cove_38_5) (CovAE.trans (CovAE.one cove_38_6) (CovAE.trans (CovAE.one cove_38_7) (CovAE.trans (CovAE.one cove_38_8) (CovAE.trans (CovAE.one cove_38_9) (CovAE.trans (CovAE.one cove_38_10) (CovAE.trans (CovAE.one cove_38_11) (CovAE.trans (CovAE.one cove_38_12) (CovAE.trans (CovAE.one cove_38_13) (CovAE.trans (CovAE.one cove_38_14) (CovAE.trans (CovAE.one cove_38_15) (CovAE.trans (CovAE.one cove_38_16) (CovAE.trans (CovAE.one cove_38_17) (CovAE.trans (CovAE.one cove_38_18) (CovAE.trans (CovAE.one cove_38_19) (CovAE.trans (CovAE.one cove_38_20) (CovAE.trans (CovAE.one cove_38_21) (CovAE.trans (CovAE.one cove_38_22) (CovAE.trans (CovAE.one cove_38_23) (CovAE.trans (CovAE.one cove_38_24) (CovAE.trans (CovAE.one cove_38_25) (CovAE.trans (CovAE.one cove_38_26) (CovAE.trans (CovAE.one cove_38_27) (CovAE.trans (CovAE.one cove_38_28) (CovAE.trans (CovAE.one cove_38_29) (CovAE.trans (CovAE.one cove_38_30) (CovAE.trans (CovAE.one cove_38_31) (CovAE.trans (CovAE.one cove_38_32) (CovAE.trans (CovAE.one cove_38_33) (CovAE.trans (CovAE.one cove_38_34) (CovAE.one cove_38_35))))))))))))))))))))))))))))))))))

/-! ### `N = 39` -/

theorem che_39_2_0 : chkE 39 2 3 4 (decH 17 20114376230600854042364019437777332991738031259907062724497889247235074015298482239202751869057878516835707602656729481754209354574603739443720170323208170195530045019887746091946017721994685066205683324368796419005650281730180903398715129488382969219062845388196393725770428034806120703145459395841279446762840690571453424769293893704936355494631409595440010248632489038551554741974894638542588211163021383116404033644797646207991939) = true := by decide +kernel
theorem che_39_2_1 : chkE 39 2 4 24 (decH 26 5223467416805837633375254241350339176667512609888315772822679539038447471009798424983093121188731832109009593733941637193986842170364910326637024860788427288038752360788819608011127260029476090940263005585198251590771565570395139087009486310967670485834980952671638478999045686018991101769678922098594555430453379) = true := by decide +kernel
theorem che_39_2_2 : chkE 39 2 24 28 (decH 27 7563870455988249764247850429824267517946146098429279728094673961539069967097329278945181527553430648909655313047514991553279441837384368154793365912496217259178964756719509863709109956696662713525467273288018225939022591291250537742364509555908685069972343497848860498354005239411116977249339771637905007800378171486355172013885768766164493747855035471943912823459525242818964580516447137382776288025150170979819075789884772630389792465151425106433) = true := by decide +kernel
theorem che_39_2_3 : chkE 39 2 28 29 (decH 6 5244807976600886543862281016569339225982815990979975372452081483892210699342230531846332851915429811586615238741483327915347513857) = true := by decide +kernel
theorem che_39_2_4 : chkE 39 2 29 30 (decH 6 3141515436212064240659583976109296054531034562565234783630429877786957587328748851558351355476252413240737501482307512902167513949522380861731722679909269321022350060246075998563581342147268028371700075727442773479443055773842979397667703678414924252925733277394875649270565382089707277966468929772042324809270640462089565264780804361765021378886201508798092130958023364435832420077085821166315491841) = true := by decide +kernel
theorem che_39_2_5 : chkE 39 2 30 31 (decH 5 26494795994123859164239810727088755773141407513863571488764061856857641125798455260707408330762528386854595036344731938121969702360465704614557322963513042779516934065761561816630922566717061979789898189852812414730860993140006737455730646557991861106296530853603609333172486915779110704464355863296446179726754052461057) = true := by decide +kernel
theorem che_39_2_6 : chkE 39 2 31 32 (decH 5 26494795994123859164239810727088756068221324182009715452531946115176448462119893420131991888585269964393112031895495695893751788924753619669409754532800895560663844105103058330229282240412793998894016315362420444038215679078044986745666372213099498095871778278112970926534480501522417311667120818985527717425303595110913) = true := by decide +kernel
theorem che_39_2_7 : chkE 39 2 32 33 (decH 4 223450707068451883175594997807237930691490831475784819480613454768188101661487889450640304585890504522539031143969073691625714658469160405492204179129477168849915670941308477159924457163446551757236905830208414232241048967375767994794234369) = true := by decide +kernel
theorem che_39_2_8 : chkE 39 2 33 35 (decH 6 3324615368352148087001953355123038173566105821175952144102603055590169594550099800047928982631244820582534894820458052518698971553773160819699121681319637643178741244769792846465218938949455051151044248227458539870431397965653152886053475205139150541693229481235229204887424501452537786951845422452254150985577511333039488292166621533942500982224483673817923977888570216303415366699171165899338551809) = true := by decide +kernel
theorem che_39_2_9 : chkE 39 2 35 39 (decH 5 29583195218322216593296668824264324378124986421408557715177057599867873092430849821969563488720822729244505040239800492470549232145627866677652106708843885753599687042935623833756556169217862780921834134955869619611081858829517178798290306633986939624703355253212110354134516333870034317712073889266477920022998739882497) = true := by decide +kernel
theorem cove_39_2 : CovBE 39 2 3 39 :=
  CovBE.trans (CovBE.of_chk che_39_2_0) (CovBE.trans (CovBE.of_chk che_39_2_1) (CovBE.trans (CovBE.of_chk che_39_2_2) (CovBE.trans (CovBE.of_chk che_39_2_3) (CovBE.trans (CovBE.of_chk che_39_2_4) (CovBE.trans (CovBE.of_chk che_39_2_5) (CovBE.trans (CovBE.of_chk che_39_2_6) (CovBE.trans (CovBE.of_chk che_39_2_7) (CovBE.trans (CovBE.of_chk che_39_2_8) (CovBE.of_chk che_39_2_9)))))))))

theorem che_39_3_0 : chkE 39 3 4 5 (decH 16 342054020694788796646986791942035985817454408682966227168659980488978948794705242116178293781379477688113816498442413461923269366086073897195638826487670008625897383319708155211863861933904237163575299475684376790132501210839011222530123151298263852804528061263095043333419321875278953082142913573300013634737472055353337364106015693018453088962602181170476565667435742559280009489851373249182454480792404176509043596587649977049188625620366621660737992722018317933152311912946479773911768485371182744922531700183521303879233293840440905661087457184782870731763071282972127685629651428783639168323794437617614581339986530387186697953630946114279041476449738461669620213330776455102922520823934265946227132405378688260246748160193338931976257594568457205779492259018240338411082586536103366410883) = true := by decide +kernel
theorem che_39_3_1 : chkE 39 3 5 24 (decH 31 1958458135023443174126337586108534976635368681345845665876939972466814465917283807112873505052968964859744211854520702917843307114153059992018917585042864526028495461872652652133481107191702187299590674224960308374676457068518158897300678380304063145186006526307897930865656335776039382121579117691509660579182866670806965380709270412288224833884940167741770280574182011275143029407886612800330296220559338038663552711330420928607699587) = true := by decide +kernel
theorem che_39_3_2 : chkE 39 3 24 29 (decH 32 354662831474555199627546970807533499806038199717609990486885855455059722477793780116806258324071001301040045394611648690653665567947803212998030997841640247188970792019328525861233159806551039700329202563425649951088746026684455138306707417328416353321742880179676682904455437205365125011971043857190759975909078076840927744809991113843157077180609726594545088485049240934479117888649301122918981353603) = true := by decide +kernel
theorem che_39_3_3 : chkE 39 3 29 30 (decH 6 1160226270712022687261077065033555436578522510507755993150193803568388398942416457764032356975263963482792844263359263474421218625805873386325505342032353565025950620114836150749103746767129586538893325778460572020705609801705495229396074154881289703690538768315914553577985) = true := by decide +kernel
theorem che_39_3_4 : chkE 39 3 30 31 (decH 5 26494884286256608378535642339329169593671634956277991590928253777917074788209231708976521360204182070841065682770894450072011466709380498996052371424555532028964455163686473396836077917086865844241595302455194540097272720441081320665998655355664715000559149973656589905914088015944583115872123773459410430933026126336513) = true := by decide +kernel
theorem che_39_3_5 : chkE 39 3 31 32 (decH 5 10336849141951376640524790439699230829536513145940504302700724050607587945700130854764240298874507980009006528270654095130313272544297993281241894087545351970684357266794735294410884108985438721) = true := by decide +kernel
theorem che_39_3_6 : chkE 39 3 32 33 (decH 4 223451451702585068200834101576770411946519893374061065340816585900243252892861296775548127305168231306043762791311600524062074687763699263904502290837986806348828564533645823250500734835800006485818566980106054828014131018660331826539237889) = true := by decide +kernel
theorem che_39_3_7 : chkE 39 3 33 35 (decH 6 2020429431477441994626034458880242696233700964860527405432016936297231449370664209472045791537589933964272940155217882826297820800033592795031673730229292979500964062321792425622281331416155801560356279244954001104988921973158165785738802912592230343007874322271336878058409457560834886605357439157411855506689185410804612278250371420673) = true := by decide +kernel
theorem che_39_3_8 : chkE 39 3 35 39 (decH 4 9161438056936128556502547268960972042344064258945573940840305312323810832720328065317232079143249412933363180489485808257505185811406518002168254510957441238997319182065259009) = true := by decide +kernel
theorem cove_39_3 : CovBE 39 3 4 39 :=
  CovBE.trans (CovBE.of_chk che_39_3_0) (CovBE.trans (CovBE.of_chk che_39_3_1) (CovBE.trans (CovBE.of_chk che_39_3_2) (CovBE.trans (CovBE.of_chk che_39_3_3) (CovBE.trans (CovBE.of_chk che_39_3_4) (CovBE.trans (CovBE.of_chk che_39_3_5) (CovBE.trans (CovBE.of_chk che_39_3_6) (CovBE.trans (CovBE.of_chk che_39_3_7) (CovBE.of_chk che_39_3_8))))))))

theorem che_39_4_0 : chkE 39 4 5 6 (decH 14 5581670242944552058901076521730941088844475561900163949753955703273276904177933526852471125440961507984012441236857198567108544295997171185258504476028133314136562054966725955121621780098513566415402324202677257583605667234710707375048884484210301065569737755345795) = true := by decide +kernel
theorem che_39_4_1 : chkE 39 4 6 23 (decH 34 1859803309417035316759097522599708112394455383627275586975556818957187950660655138902033914401658911070236465055830886735516074898915422256125189343604257614649408561499945387977911376873892006336563401880689198831608881827564348072112863808175516637189448770917819675039853785340041752248958588746245892430204740458003366439596787426045542595766205764466930747487948742651164253961265413106764815826044327858230351374420679784749753049096516644963064458881514341357025265125585860348894223542385767552258123867287345643187043287893749792002133804769263386557672175908002987142310277892684200399197728897111474181) = true := by decide +kernel
theorem che_39_4_2 : chkE 39 4 23 29 (decH 40 466403071262329621433447800303995309555783674952732795735789044291407381611777719886861424018466867293002603226860286357246948625787911836853533121701189842862186162777470872964273393546960348545529281989927203877464528774912410774102668898298814241371174430648605578551859606977005385643860801123400560979011544876551292028908510077719315891727515140799041804390696118842208881868567673799516832680066780906598037710529574150919106993008736539268213988632564528986723180647520867266262063282392971892102724557045850731123337066621683525333957004255114884897555019208489062233136378561928407803397288261944597148959015811) = true := by decide +kernel
theorem che_39_4_3 : chkE 39 4 29 31 (decH 10 29368860440321669043732776150838176417296872891012325994939448855789119723564047465578248245029350107172341981966223458253770010416610399548497077571045942197452156915419756583811604577552057339533788312482623147159504077458775300384578130312861670354943164962302982613714070464957426871794475237035251898842267161593076695353796571164955137) = true := by decide +kernel
theorem che_39_4_4 : chkE 39 4 31 34 (decH 11 3266133775352328173276316463265638602566448444111684620833817138065268132680551071260124749973131240472586024474910197382680567308155483225530464133481036602138388486390766395251459758443691534687557347835848291645449088746086666458953355501359899409392932001155670027188521637378284473172834887819941755382021852706178415152512515538318324253672318374912851419666601987731616242657719130293282941517584969502665231176193) = true := by decide +kernel
theorem che_39_4_5 : chkE 39 4 34 39 (decH 4 143709670289076640441270362322730928299223533361141325167687164806364335379480594606476072911808528382633348683743499844973544774276586309832594779961025416631240460176670085633) = true := by decide +kernel
theorem cove_39_4 : CovBE 39 4 5 39 :=
  CovBE.trans (CovBE.of_chk che_39_4_0) (CovBE.trans (CovBE.of_chk che_39_4_1) (CovBE.trans (CovBE.of_chk che_39_4_2) (CovBE.trans (CovBE.of_chk che_39_4_3) (CovBE.trans (CovBE.of_chk che_39_4_4) (CovBE.of_chk che_39_4_5)))))

theorem che_39_5_0 : chkE 39 5 6 7 (decH 13 8572098330906302665286835807820569165171200300022065615435415432846471079613431498145059875690990561218410701232342262900624054719703046096649797797878967058472349542305204534364118392715925519486517881511862745645204461016237334607845941457364826982747880063500940991095928128768042519294486177874679739458766823849634961452746351107619845112089010309852254295822599376300208948970141217427779297975997311876075047971236771505513820993153385992918779256463528967607895355467946051082904354030075459032967910953927179474669779637130581364779678242292256439977713242058329037543329498165757284630419896893423678786382120067) = true := by decide +kernel
theorem che_39_5_1 : chkE 39 5 7 24 (decH 41 13724730676789637046570615415521350680934510748301336211155095719944253869046609357558446502789697640716936197472074008680039418910907272722458447243042289018761647408154252091407148973180132225157742744906824932314114018328882656799674781278280878621883145498058869970296870169954913328787833607257803705627973804995309337582437475506720250567840947227952480321067161777498179288031039491684613118496421147758695793587493003517382496232471335508969122405081517163069074047979318020251302539196964916279294002184601614467596495780887418843636194082198662368849178932203961852164156044462070390553914040681762477893956211714252062725) = true := by decide +kernel
theorem che_39_5_2 : chkE 39 5 24 29 (decH 32 17340118607244119562051810883779746720704391608672205637190484267518529813564973117811280803511584896241891404522026546833882054165313230178597860891498708688409504694119023915473447039015952715427539727757031347851227461910410629165794571255164110331170313407093498580364725541632596781149251826887798605238698400205841745575065629900640274531186975293182762045513931773560876592983530406786258111843937686683668761692202463351141966090334974555650300637030449210276265902211) = true := by decide +kernel
theorem che_39_5_3 : chkE 39 5 29 31 (decH 10 1909164407398659382762624096333271110160485444361379281684106368501936668510183322708656500716653690144081486342188578921901495049841962588188237141167273173955595900871414387791071549602659212145312518260627317607650212666720374895490048044886290521715802631640001458041279117255191123517354956152590872548725978581059995243843101757953) = true := by decide +kernel
theorem che_39_5_4 : chkE 39 5 31 34 (decH 10 42303392694981809362342750498534472876451832862563427027291488596345593881364146857406304711769988712808454431955826197270770964281109231468256176048481890159264887909863956561336813939725179880144093691952603000764463288956681758407452441768774267402821533051087909289859925175210411629068367542475415683674764716990681396617049494623499750552800600976909470289915521490417053505950487972523572568969729) = true := by decide +kernel
theorem che_39_5_5 : chkE 39 5 34 39 (decH 2 1998608470371346720531567510019592732967819178296577527483221343306135846228481) = true := by decide +kernel
theorem cove_39_5 : CovBE 39 5 6 39 :=
  CovBE.trans (CovBE.of_chk che_39_5_0) (CovBE.trans (CovBE.of_chk che_39_5_1) (CovBE.trans (CovBE.of_chk che_39_5_2) (CovBE.trans (CovBE.of_chk che_39_5_3) (CovBE.trans (CovBE.of_chk che_39_5_4) (CovBE.of_chk che_39_5_5)))))

theorem che_39_6_0 : chkE 39 6 7 11 (decH 39 21855675603704280228869369117651423513693786358070432172629721251018140502881241858814209961761495673293901207112744607308521987602317630704606274281105650075144561238342751245105931480207910504709933049798596669385176705184103327010194816064252384055908376644138609927034833785963701943419410780036194948443752886874536072617217301728942223633382095165019152474683351146187084631698219080950918774943867375911342274731314023781612590774645558004566546612793954778648276960826447603706815786352661441646628426772046486679086035262423188867) = true := by decide +kernel
theorem che_39_6_1 : chkE 39 6 11 27 (decH 37 679101761319966145438919726454200107321612654715693148929395024921829541792583846770294229317225835494957922763814801489019798944550034391737736419530819958959449591781496418159492101695244167966791773503818775305574932541563854019083131992229409717005462183287146761169030313609799710012087820180083821037516034577783750189240290908643035656833949962580193424217368172339334224840020415092235544944754880716754913558639683652131709670807034001420603830651419999019668937658070594569178236696400275031097252467090816030153635469760253127940438537332153595615002629) = true := by decide +kernel
theorem che_39_6_2 : chkE 39 6 27 39 (decH 27 427480042279079432018915521832108538057340828942125986808903036303852061854023098846028128488987399273333259500650659852118432803714477030371658117710828657699682333203868468930441658589069653146939755465336322036225382564784438049703648360877826996735628989876898114130312072867946906502074781432284104948548391555257593533534273759714330274275910411251558958232410850860074025766484381217845264383206353362788250007669269502644007263703186715848585882292920006363161289942566244380079721573965246298753441788929379518614506405391010947) = true := by decide +kernel
theorem cove_39_6 : CovBE 39 6 7 39 :=
  CovBE.trans (CovBE.of_chk che_39_6_0) (CovBE.trans (CovBE.of_chk che_39_6_1) (CovBE.of_chk che_39_6_2))

theorem che_39_7_0 : chkE 39 7 8 9 (decH 10 207682687688349655152353471813541547682864329007493852466490164783686295166139885122324157161466939287339334957783662785396152687735052768139426435965041181694532710696714608238575771886269017282264525956041349842917987402491225459366356008024052873448128688077665681024612442117522466886091601403675590762517605422980951852745915471600282961952051471524231689496320045217340618628961834431938533388799188611508230636584436237083716381804822414804611) = true := by decide +kernel
theorem che_39_7_1 : chkE 39 7 9 24 (decH 37 549938800048020884588366108972409076862115745998621105181708380924230434623990159895905789261618195028411916991729803505288409786398839478400391329363758940095705931248567193832375530493054713554025531357414656785732458002484136669937007909037934437350975840777938707803979278448199152051627086605037144531551163358759642262861212113509562786753341837946384243249016081806782645486556372003465005393166689877697134830220324835014789901365202048143101332977397679242092693658122202579576289583053533600963272602232490103995428525665308527700479940539199870824873989) = true := by decide +kernel
theorem che_39_7_2 : chkE 39 7 24 30 (decH 36 1021589672427200896917026386591571400280401920402952152449082887176850722197132077228511073012695223918701321253656097993586778245226851071482939079090128160788397960952103593781815803915839379249281686807164983544721634317575139240874878242131940648825107555445457286428885817114598615983169877808320851468671390394935460028359272693799178198893315783418830343747680878624849416974126179980255854603585278864786951059537133527029550608051551067177941384276140966113022714048339505322653909976490829415749024514179) = true := by decide +kernel
theorem che_39_7_3 : chkE 39 7 30 39 (decH 7 34832478373589227264629206553893211168211670249006224310333591391869738233386679728905377757772230079106520352092407288208649281522664902655749504625518063010496425941951523251530961064971726778921208989315539317182977) = true := by decide +kernel
theorem cove_39_7 : CovBE 39 7 8 39 :=
  CovBE.trans (CovBE.of_chk che_39_7_0) (CovBE.trans (CovBE.of_chk che_39_7_1) (CovBE.trans (CovBE.of_chk che_39_7_2) (CovBE.of_chk che_39_7_3)))

theorem che_39_8_0 : chkE 39 8 9 24 (decH 40 634951690593868457165311268917392665585922390434514480191509825905224661462847223285853693681820587092950880943948352221553164964422835436315238658421199581883075616562901265202585747254578765416316211511908040801946093719943314072615408621296404077027942723454493067261424603305987657372883939154263657208868107955859655877928755221668543959961560572784981242076009466972220587212810465244735878860802403633984083278725348081903420861931666481957424502982059503605557098580486792340037934918689805045874550855470666381600015578844800544867045131702873717905311619) = true := by decide +kernel
theorem che_39_8_1 : chkE 39 8 24 30 (decH 33 114685005709468621959491085580966255419808183306553115593687474558632833842461737966915239713976698791051246528132922900634109027086770894034038932525361214469937146142768420683098662630536729500364033393534770920186719628076491557033450081332758394564100267483853707739200222115426142956931738497744434701462255302851666788463535219353832624576747892381074321052443367677467200472830762108877496664130390448780102914368978193487512791917708779846007147046702797055051466371) = true := by decide +kernel
theorem che_39_8_2 : chkE 39 8 30 39 (decH 4 286894048630839018651881963945063894238887467702490402476640079670796651854755334843134809966527889396225) = true := by decide +kernel
theorem cove_39_8 : CovBE 39 8 9 39 :=
  CovBE.trans (CovBE.of_chk che_39_8_0) (CovBE.trans (CovBE.of_chk che_39_8_1) (CovBE.of_chk che_39_8_2))

theorem che_39_9_0 : chkE 39 9 10 25 (decH 27 303783080831971779969295573882707451805248349227172563823944042617367357613245279711673497817427808314899432623787620672150473796672776777654678943799337982273757507098268659201119646075937443954928057425062943698296131308620842375767164027267491579150377243627606984016440384408789136078281636289178984540054410270173375111168828201436708102697375189832735166923103357275292079358569582841083733982361895885554263284933594125391108761291714375764123564657755352687388935476272786124130263551450552274573223073877214677123) = true := by decide +kernel
theorem che_39_9_1 : chkE 39 9 25 39 (decH 22 10564464924486122939852987532670883489636789572546324711539001593984182748735394818414943248758123825935160675376057312132161190532492484806581656235571401955268900136321148888288790195178877316472111650044285218207515221447773900855766499498840178182536595586246026613987299014708395310809414589754995335144234538643545297981911403516832373499188875535234012388816466885261664471171) = true := by decide +kernel
theorem cove_39_9 : CovBE 39 9 10 39 :=
  CovBE.trans (CovBE.of_chk che_39_9_0) (CovBE.of_chk che_39_9_1)

theorem che_39_10_0 : chkE 39 10 11 39 (decH 31 45032110779587333038967851203359421271809154545397863619423990662500337106522880327393044415893151627922261343191209645454993720722802323173892092385694753836025423195871758205221470221352408303355084893184496607868781304345132824107618552563914716279430242681855346189426670309892447013256388085473108994338899295219575913044668873012503276293845403389089010975842602276885706722906111349141179734182275) = true := by decide +kernel
theorem cove_39_10 : CovBE 39 10 11 39 :=
  CovBE.of_chk che_39_10_0

theorem che_39_11_0 : chkE 39 11 12 39 (decH 14 23419531746233413940947944638782936439882127384748891231564158534518992117227818860234921842740994303727202821293443782464209177661571692089129805969113301155150688204567049456259) = true := by decide +kernel
theorem cove_39_11 : CovBE 39 11 12 39 :=
  CovBE.of_chk che_39_11_0

theorem che_39_12_0 : chkE 39 12 13 39 (decH 6 1407180463691660596701206803106178805832361688216508576058243) = true := by decide +kernel
theorem cove_39_12 : CovBE 39 12 13 39 :=
  CovBE.of_chk che_39_12_0

theorem che_39_13_0 : chkE 39 13 14 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_13 : CovBE 39 13 14 39 :=
  CovBE.of_chk che_39_13_0

theorem che_39_14_0 : chkE 39 14 15 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_14 : CovBE 39 14 15 39 :=
  CovBE.of_chk che_39_14_0

theorem che_39_15_0 : chkE 39 15 16 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_15 : CovBE 39 15 16 39 :=
  CovBE.of_chk che_39_15_0

theorem che_39_16_0 : chkE 39 16 17 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_16 : CovBE 39 16 17 39 :=
  CovBE.of_chk che_39_16_0

theorem che_39_17_0 : chkE 39 17 18 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_17 : CovBE 39 17 18 39 :=
  CovBE.of_chk che_39_17_0

theorem che_39_18_0 : chkE 39 18 19 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_18 : CovBE 39 18 19 39 :=
  CovBE.of_chk che_39_18_0

theorem che_39_19_0 : chkE 39 19 20 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_19 : CovBE 39 19 20 39 :=
  CovBE.of_chk che_39_19_0

theorem che_39_20_0 : chkE 39 20 21 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_20 : CovBE 39 20 21 39 :=
  CovBE.of_chk che_39_20_0

theorem che_39_21_0 : chkE 39 21 22 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_21 : CovBE 39 21 22 39 :=
  CovBE.of_chk che_39_21_0

theorem che_39_22_0 : chkE 39 22 23 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_22 : CovBE 39 22 23 39 :=
  CovBE.of_chk che_39_22_0

theorem che_39_23_0 : chkE 39 23 24 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_23 : CovBE 39 23 24 39 :=
  CovBE.of_chk che_39_23_0

theorem che_39_24_0 : chkE 39 24 25 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_24 : CovBE 39 24 25 39 :=
  CovBE.of_chk che_39_24_0

theorem che_39_25_0 : chkE 39 25 26 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_25 : CovBE 39 25 26 39 :=
  CovBE.of_chk che_39_25_0

theorem che_39_26_0 : chkE 39 26 27 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_26 : CovBE 39 26 27 39 :=
  CovBE.of_chk che_39_26_0

theorem che_39_27_0 : chkE 39 27 28 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_27 : CovBE 39 27 28 39 :=
  CovBE.of_chk che_39_27_0

theorem che_39_28_0 : chkE 39 28 29 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_28 : CovBE 39 28 29 39 :=
  CovBE.of_chk che_39_28_0

theorem che_39_29_0 : chkE 39 29 30 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_29 : CovBE 39 29 30 39 :=
  CovBE.of_chk che_39_29_0

theorem che_39_30_0 : chkE 39 30 31 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_30 : CovBE 39 30 31 39 :=
  CovBE.of_chk che_39_30_0

theorem che_39_31_0 : chkE 39 31 32 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_31 : CovBE 39 31 32 39 :=
  CovBE.of_chk che_39_31_0

theorem che_39_32_0 : chkE 39 32 33 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_32 : CovBE 39 32 33 39 :=
  CovBE.of_chk che_39_32_0

theorem che_39_33_0 : chkE 39 33 34 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_33 : CovBE 39 33 34 39 :=
  CovBE.of_chk che_39_33_0

theorem che_39_34_0 : chkE 39 34 35 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_34 : CovBE 39 34 35 39 :=
  CovBE.of_chk che_39_34_0

theorem che_39_35_0 : chkE 39 35 36 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_35 : CovBE 39 35 36 39 :=
  CovBE.of_chk che_39_35_0

theorem che_39_36_0 : chkE 39 36 37 39 (decH 1 0) = true := by decide +kernel
theorem cove_39_36 : CovBE 39 36 37 39 :=
  CovBE.of_chk che_39_36_0

theorem cove_39 : CovQE 39 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_39_2) (CovAE.trans (CovAE.one cove_39_3) (CovAE.trans (CovAE.one cove_39_4) (CovAE.trans (CovAE.one cove_39_5) (CovAE.trans (CovAE.one cove_39_6) (CovAE.trans (CovAE.one cove_39_7) (CovAE.trans (CovAE.one cove_39_8) (CovAE.trans (CovAE.one cove_39_9) (CovAE.trans (CovAE.one cove_39_10) (CovAE.trans (CovAE.one cove_39_11) (CovAE.trans (CovAE.one cove_39_12) (CovAE.trans (CovAE.one cove_39_13) (CovAE.trans (CovAE.one cove_39_14) (CovAE.trans (CovAE.one cove_39_15) (CovAE.trans (CovAE.one cove_39_16) (CovAE.trans (CovAE.one cove_39_17) (CovAE.trans (CovAE.one cove_39_18) (CovAE.trans (CovAE.one cove_39_19) (CovAE.trans (CovAE.one cove_39_20) (CovAE.trans (CovAE.one cove_39_21) (CovAE.trans (CovAE.one cove_39_22) (CovAE.trans (CovAE.one cove_39_23) (CovAE.trans (CovAE.one cove_39_24) (CovAE.trans (CovAE.one cove_39_25) (CovAE.trans (CovAE.one cove_39_26) (CovAE.trans (CovAE.one cove_39_27) (CovAE.trans (CovAE.one cove_39_28) (CovAE.trans (CovAE.one cove_39_29) (CovAE.trans (CovAE.one cove_39_30) (CovAE.trans (CovAE.one cove_39_31) (CovAE.trans (CovAE.one cove_39_32) (CovAE.trans (CovAE.one cove_39_33) (CovAE.trans (CovAE.one cove_39_34) (CovAE.trans (CovAE.one cove_39_35) (CovAE.one cove_39_36)))))))))))))))))))))))))))))))))))

/-! ### `N = 40` -/

theorem che_40_2_0 : chkE 40 2 3 4 (decH 18 22349965098802818605180038738736358556648861778976703256563009176706732951037516947184495664589007428178441930401666714992514395654373316853621761842463204306616964045141475441866347356292202408858762746649219616744139064942765014288648062553868121149210467227479575176479593486092603918593372625700646918012570238051091632280153003961177763282510644139986994568931695462656283572752236083564857620420194600661350519723084371798543590093567156815057167812530646943376524843933371764205078797006199027154713083145371518844733620783904943754055193658652211708106624669733246024363640126604096383035305003375117179048466777114028986589051705546488796263576080013812304088952404761237766268610370525732136785392492977434096116636455306258022454088900962804040146174038504639217400935584500815147473383949936589111291308677238260987282842255007439370798313419727604997935725045062324735231528457109571795549414419701600207340323556007669817281750837615287594425042302224178552781193347) = true := by decide +kernel
theorem che_40_2_1 : chkE 40 2 4 27 (decH 40 1456748460665370616154539454197253099686381200113175231699330590284547050591187971228631783519092219089044865762220314882276844765442392771868259925291158257438949227457928007695181199918675570790203520086354519530286314847572435540720584470612887337363884404012060981813284499616255421397306631330974758228928420981284429156108401748498056979018571295741477952324802629328155843836213617446679089977234154443538563) = true := by decide +kernel
theorem che_40_2_2 : chkE 40 2 27 29 (decH 13 6195173019962370841001340266441596804874028932175743549252441255719431458979550836649558789530773590400076689508372778005152804915287782818326943678595) = true := by decide +kernel
theorem che_40_2_3 : chkE 40 2 29 30 (decH 6 107942064960033897937286473793901607860788686902626493893817525282854866394805621442411236433538078294816812234562697250666702342499469780883537013593950245978911409445632786109496259559631473228001729490929234828501375062931335582788563229777793707402150048634358777140034761615070266812245882680748115617805944243016818108124771148264383906980818260100733999373158013527760581576318174434443151473110507967105) = true := by decide +kernel
theorem che_40_2_4 : chkE 40 2 30 31 (decH 6 107942064960031037026669189371517456735545616881420714946700150638337980782737877394400272775559832123002968751513468407125227553316631490257825635957262436872940841892691583693598052641101665577682060883902688247918722942537581133033386779967551682084985798525431480518007291374247940622995890546937733177428092671060296304098056149745749744892346590857450629188541642306815543671482326311019727376485255090817) = true := by decide +kernel
theorem che_40_2_5 : chkE 40 2 31 32 (decH 5 7112166345060592053850864706343184572713988015668188477670361790771823703083362202538236187575238703003943954565261040961726749886813456779531164321884261068044041735999580906883005770416036340951550649118890204172631573875628499458522365771536831471619944761246883003986191412477199824181376731131451319579565648562693918282369) = true := by decide +kernel
theorem che_40_2_6 : chkE 40 2 32 33 (decH 5 7526686159554787956882147732520969900982890710704755833838323268027686057084361965556688602350993590399641356971403157807182134328285441495250038519678281042612093259094861726593004427285795148689678387453511373683358979883752098316845360061766007080697900540225900261059369302266196215749099479141628802252805636771156272403073) = true := by decide +kernel
theorem che_40_2_7 : chkE 40 2 33 34 (decH 4 495923845941250821360310900838736371223662138862695487724261999496109385369996228538264319195630843035581960366796146562989167317640007594557127047297040149935495222297370717878884628258214370550024964971578177045850772114766947323444973413978753) = true := by decide +kernel
theorem che_40_2_8 : chkE 40 2 34 36 (decH 6 114233273935258021041906106159921930675819906772905383551194046710584763513072379597406577921537848448206829462027011119192270620366786012609564589404663029354085516748527845432256179194725203711985915182121103293442386093271219318323293053972838496305646525490209332098880880874503159325643808174837203789015564492563940040721695105992974510936906623398114849430021944678810562876653008131079187030811347391105) = true := by decide +kernel
theorem che_40_2_9 : chkE 40 2 36 40 (decH 5 479824207449000464706384552177598118709466872270853050470959901959039718004769111375117474887281687158927770439323911524266056976761298626444799019142771922508762922450701000494533247017118406260559722338909079604430790692642316345011450145111397036131757403545773071699916265523590037829064406852102367789410370851772356104833) = true := by decide +kernel
theorem cove_40_2 : CovBE 40 2 3 40 :=
  CovBE.trans (CovBE.of_chk che_40_2_0) (CovBE.trans (CovBE.of_chk che_40_2_1) (CovBE.trans (CovBE.of_chk che_40_2_2) (CovBE.trans (CovBE.of_chk che_40_2_3) (CovBE.trans (CovBE.of_chk che_40_2_4) (CovBE.trans (CovBE.of_chk che_40_2_5) (CovBE.trans (CovBE.of_chk che_40_2_6) (CovBE.trans (CovBE.of_chk che_40_2_7) (CovBE.trans (CovBE.of_chk che_40_2_8) (CovBE.of_chk che_40_2_9)))))))))

theorem che_40_3_0 : chkE 40 3 4 5 (decH 16 372575190097073453370063548826771389307397048308705330847734851116743292654424152187336166692087268237776654448610349409140967972152957898577491144795658020316722020777282069617911450735491985640802917132895979473702674448375575131849622114826750469340347115360635656553963532095042402938517308977266731065858879347963933237759337723358829203557178934384673411) = true := by decide +kernel
theorem che_40_3_1 : chkE 40 3 5 23 (decH 25 1237738897889888239015440612825347121542540668584248243733593708678923239358890954971228869666881683236897536877740384759312136326163987246944420085180322478969204790387008691789082115831387563056988762132801296802120815590106138434911285045716764061575681807778880445625186374339121629859714844078218167319427633839794398501289982275101968175481064132858042446492502186315848526955013393050371658163574918642418307) = true := by decide +kernel
theorem che_40_3_2 : chkE 40 3 23 28 (decH 37 84457950038683420131327018963820575295570795692800103457781338322901801663692594536297232609584356575674800752159437532187932405635199748162073480489269218680961533201987671722604683783567808781808466076463555410572541946458548000251242508066694929247330652233902259562060650630900086330440058761313490559757465220212207941477910421259408041077942308911672729437323478045994231211430591172106734368841140657917645913570871420842670792986329441061685228467110929269379) = true := by decide +kernel
theorem che_40_3_3 : chkE 40 3 28 30 (decH 12 17608870969217404250198679576747140604293714459371522296731286871636862742012838173206652523781193908923574424592496560497088902992869341586688771340925119151888666976092993826488649670683152751207598950477196244232781714371403043469393348365541455944318169834944931211649068445962982536609203522083634357300213433310272711748767533373157130156585630351491) = true := by decide +kernel
theorem che_40_3_4 : chkE 40 3 30 31 (decH 6 107942064960031037026669189371517456735545616881420714946692132659028838331648039164490709042535505073623988479100361195974811966687102125096144093596024529947826079736570142509330529983922432757216059647042980658232074240427037309554744737989957159212040134899683864725741907944790806000889839554210543356663089168413400462090657467110678821963785333452474696816000011074856864495711107189368291474313503494785) = true := by decide +kernel
theorem che_40_3_5 : chkE 40 3 31 32 (decH 5 169358936376540014375597815151301205809778185363803311091760448200439825953847380769293157454785615566619474074663526653475912074453304188422296932865896819422697013477999711443025516867270086087297) = true := by decide +kernel
theorem che_40_3_6 : chkE 40 3 32 33 (decH 5 7526686159554787956882147732520969900982890710704755833770701568042320905551262473087374476716581132667017802139024187051767874801024659482524357823405838807339241630796194391758871187993175159576931282811496501216436727983579078384150505971236491750969292523514904764263877368063429064017737948734223255995077805001781425984129) = true := by decide +kernel
theorem che_40_3_7 : chkE 40 3 33 34 (decH 4 2354539237936446390626000374620807761855797358270982790681440835514538988862655470849015576405179866902985439481892826891040739481320869966076310848693096169433709918948350102983297) = true := by decide +kernel
theorem che_40_3_8 : chkE 40 3 34 36 (decH 6 571720726809773178765018538810359934728217144542872795201757946064452147228032276893930562822928336707500066825492317735566894483371213424783859181932067788437010030678472194369726572114256092431738394541962148655568929200713900025001281936490585128610417676658487963522300226412762192478759045326370306374512801170878234188242059853208257729153) = true := by decide +kernel
theorem che_40_3_9 : chkE 40 3 36 40 (decH 4 523236033058326644920283545957671621190673804549651636644959289860867095168811071459597076885013666212391205738628056627996429912670315010829172576655261473092567334320304947423524342588677242062983440258202968105673682674360135737817086286156417) = true := by decide +kernel
theorem cove_40_3 : CovBE 40 3 4 40 :=
  CovBE.trans (CovBE.of_chk che_40_3_0) (CovBE.trans (CovBE.of_chk che_40_3_1) (CovBE.trans (CovBE.of_chk che_40_3_2) (CovBE.trans (CovBE.of_chk che_40_3_3) (CovBE.trans (CovBE.of_chk che_40_3_4) (CovBE.trans (CovBE.of_chk che_40_3_5) (CovBE.trans (CovBE.of_chk che_40_3_6) (CovBE.trans (CovBE.of_chk che_40_3_7) (CovBE.trans (CovBE.of_chk che_40_3_8) (CovBE.of_chk che_40_3_9)))))))))

theorem che_40_4_0 : chkE 40 4 5 6 (decH 15 1266646070223231669314954898064078580732829361950551738733209099956860658769479945994035353840929873183392278725085673233075072275210673220392533409572726402000641921971063321154322341806411879396330563574378288854861672341617445345575298574039311609227270599549308265524208777729545780950057204625208056429310294931958455804424971963367396340355481674203477115216714301522723054158938357398210536166308037923857612006604224877706361411234419425094561377008166002719024651223852513221545663369076882184292458330646259948897928822692349978634292646309359302112921634263099234352273435947757788446823095246036190323345334788376181334314296189185312332141320332683245705317249586540588236581911354657058327083812737659487327716196558918913994973808609317214783103489746580299194835183274852218341894964099) = true := by decide +kernel
theorem che_40_4_1 : chkE 40 4 6 24 (decH 35 636264531599683639713715081086521778451258437659847901193164188727180236085332212638623226971549523134215916931300994208847410604597629555899795243090274904211422316214496180268145594958101467087063421361413672098659415511927712137394878479637091313972593879677843456898677763690639365116030834084984376663702710321492535991214057825950085907266720178635556676105067137251321485418204273515814454239356857243212693850073783364756101976789585044553740379215695448878994619044051092751971245801744384434844056263059509249830115714257799408844214563658846911500435461) = true := by decide +kernel
theorem che_40_4_2 : chkE 40 4 24 29 (decH 35 1281826814106083882260134441055364373015027351679805775231704771727969112188919249989541315543451714204802575534552936103453778027611519892056401319631640653038148543140139253143085566652207931430137391682313791790704788197240088400973538025652150774383696454216826452023225587911913100626644746703504899446452709343435625894950081322506608608699250061576603314583729091044379466622279614233209223570535377338813849405011619544756763958501609047114841761918006974457346706693487974928541288179190397230085738354620199573687931240507912651693522731139) = true := by decide +kernel
theorem che_40_4_3 : chkE 40 4 29 32 (decH 15 127136225368296615516628888842461821478347140222943838350893394487587069368033852624631648536418739730824125678025545904740246460351675766713409282800231476761664153892773902481629962104883176120280398700976483359779177407074941720715675208968627268647841361029154444099093213462725518833624647873091737050439020001529403938070439352439198519770983572440103673741605661701352739633705605647709728480428075450520368944929072734556801) = true := by decide +kernel
theorem che_40_4_4 : chkE 40 4 32 36 (decH 13 4855968943381258416827111753007216091345439524014623200651733539526852684921748812796443528185282061637476909375391581324666707232654271525987859950259815399218433722435861646010133422703512361496477619211667221473158120110694748369143157536454225670544214655257977931613500757292568288657146352366205426625469983166081324120296835294474367631227511100132933582552360999339407055647267791200381053677271094492742894089061577615121211905690590379008925462077837953) = true := by decide +kernel
theorem che_40_4_5 : chkE 40 4 36 40 (decH 2 255829339401141761962047011761252797498984106331192155916663573651473857929335425) = true := by decide +kernel
theorem cove_40_4 : CovBE 40 4 5 40 :=
  CovBE.trans (CovBE.of_chk che_40_4_0) (CovBE.trans (CovBE.of_chk che_40_4_1) (CovBE.trans (CovBE.of_chk che_40_4_2) (CovBE.trans (CovBE.of_chk che_40_4_3) (CovBE.trans (CovBE.of_chk che_40_4_4) (CovBE.of_chk che_40_4_5)))))

theorem che_40_5_0 : chkE 40 5 6 8 (decH 25 74729603655778954429953327883409687951471731072110542576110250523328682811532002627169387155296740445768241122225838376143547250269487936307628954602190609133552342157098313237401879633864536418096854066809844717243704524426719398704217784729002468863377003051512403435826772354369276374534399948797770818463293184693385361396767871623560938270706493185202294553761161966487513557129774211) = true := by decide +kernel
theorem che_40_5_1 : chkE 40 5 8 24 (decH 31 2853483986166848645887635050226382732445673178090354320875692131659375184257621835245036389160297612070173328374173454022754799051727632077990989459730185451480564032688518105959974491849960234961489295050412576334577647949787357089023193342098968596130059099183786687899799703793571025665728832697304416787878430764681934343271006954850064152150045924830643246750456579096906494720573605217697303770169273277048494897447252494082228109282925631624636427290084819314279855514311802198508966759430294148106896821622915205) = true := by decide +kernel
theorem che_40_5_2 : chkE 40 5 24 29 (decH 35 11524485551489913889600630264253147742596608601926357329092474713821535655458545140389775351620460847803888759810159558478043675442072591885896456460453415489917166549040107616291999080060816335557964568812865455969922640801268991709177178999663143978778483496821051143560503738864878459839749448847935755208897550479505720786478373074440836460385653037707838873529547192148090727712326661229533957963652777945580392781171206678974767800564213957503718447155430183132404611297510675553791308580082720801049067651) = true := by decide +kernel
theorem che_40_5_3 : chkE 40 5 29 31 (decH 11 3882800747386027839694490732428151954902904077471906006344974369986544291051381103891388132932244140471686221025937278123972551990739138879759065791304340408799717344670533542384105265386519519436949268356278080190623869529272606645706670529960011959682946716259861647460399116599468398632030870362141825880668958316354704811058423562580670059283338649987971568257) = true := by decide +kernel
theorem che_40_5_4 : chkE 40 5 31 34 (decH 12 54748432469099994429086774714628083881072830025349990033255079742408946223023906642462226041210003267660228098830333495331760918541946654385498046394504124782225134975809472566219166970886884702902508230914253396540980265365578340732498835112253185637198397054063868711102009880305576629529175976584911135412044891178843803626192898436941304891241593124002934665018865862094356490799351513372303673129063117607832588042953702251919044242672325249) = true := by decide +kernel
theorem che_40_5_5 : chkE 40 5 34 40 (decH 4 2354547152509293472202116335260809904361649580702297623764092862825657712701307492210035035296310718796864615352012825293448343646716880072678655420055612012627435277409988400042625) = true := by decide +kernel
theorem cove_40_5 : CovBE 40 5 6 40 :=
  CovBE.trans (CovBE.of_chk che_40_5_0) (CovBE.trans (CovBE.of_chk che_40_5_1) (CovBE.trans (CovBE.of_chk che_40_5_2) (CovBE.trans (CovBE.of_chk che_40_5_3) (CovBE.trans (CovBE.of_chk che_40_5_4) (CovBE.of_chk che_40_5_5)))))

theorem che_40_6_0 : chkE 40 6 7 8 (decH 12 1788263896427380833369234382788450585659305240464790500237042712464401074107799641536187359870572614744214359391154064366924443514709647778535889731100692254871003059290560470837154968653890333365680269436120207575678967662533878104966246679716272655651734195563877312673856455970492366006803417127701812814096098942161029372495327459018906294999197084619400961217316671304753082558996456991751031210694722522341678818304452150532348517150229931164246446918352259158862723184598032332043198571093101585794495446124312740388978019998980459397712073820339468556960776089141682592047178810503404828882001839997054906989088392579) = true := by decide +kernel
theorem che_40_6_1 : chkE 40 6 8 24 (decH 39 18237481418820629985304173617050030344425845997072399213616242905831102279357460136716095829076572268122734199470852609567085013900820320587323419891583552912991346628807368803339686844423839971733185579473016404094695817885498229199046162866280485962136946108157037551691878363745157175964817396423043510056633951294419245618264482196172023722067163620628074000531999922656231999013745320432542488105624481109366636589083080255851138721012332577851806521203181429353027561087724505253783938431636541397153491166115265131253546800866987053880633764491953839145435727303825079399176305378304875976835240017930665209151278939044610053) = true := by decide +kernel
theorem che_40_6_2 : chkE 40 6 24 30 (decH 40 28356649092726028173770045554556696624149149582853635920360988883542152353981265353844263365709166595001206228578464951892566658620686813004332354344657399752755589063072364997056476604432340158120192977746957078912679629908638632285583730331039359513199159987171772052817269766667350199978341613382792938142390566261244516647179919842944813120518354712943285152595362796763027149527838025050308765289120671152201201297453574154718584272963895866656946457292133599419005863545606331636588489478799659408860772904360307444385119444090711441761878244974081037079117982685957686939063661894228637927467742786176499613827) = true := by decide +kernel
theorem che_40_6_3 : chkE 40 6 30 40 (decH 16 6295513929236783122413588498566097694481600615749173233291108484004786748795117406152089545713105721584409183305883303770695921398853005028163827900933439832934829879391112155979428365967954266716367590226808470467147254420959489360761252013567773330243917447793548226488963989455662456549890486646038557750825500755203538912661691209011285481337491258059839490874340247280853251474820366728260696580376104425135056418953980761607051514497) = true := by decide +kernel
theorem cove_40_6 : CovBE 40 6 7 40 :=
  CovBE.trans (CovBE.of_chk che_40_6_0) (CovBE.trans (CovBE.of_chk che_40_6_1) (CovBE.trans (CovBE.of_chk che_40_6_2) (CovBE.of_chk che_40_6_3)))

theorem che_40_7_0 : chkE 40 7 8 12 (decH 35 861590333294976396215289134498537198042758383900751527525060832551614072011058168071425226292439882768031276195012639924157237475317135549953462398612686168116735141280159860856378284272191166782785393576681448629929829191335717388303707901285878670335179314672527468582221272006167241893145643926514624305698183355571400921206967651600201548719519798166543495812882559357284500874052493546645853250784304631419440550185519534928194312190531794727390542377886848969543110395642916869790254723) = true := by decide +kernel
theorem che_40_7_1 : chkE 40 7 12 27 (decH 37 203311492018077313861907560568555104971649164094273323916526083919269044466728314123486856581502606699708617178849297865189210126994425685971280683016432544874132781186972792407254866247240793614337217005323929296875102327681909271952599140875164974631118568753036874226727789770037311583506715176716670690100362081151832927693978454490655888922361108101633060545157754021285768285927477437164069271850683483909944554496602683718449751893904012930829388761293744134427450767332664543844359334869892983873731602461541727093876609476960287796407423559341949062) = true := by decide +kernel
theorem che_40_7_2 : chkE 40 7 27 33 (decH 27 503773217796588017843476757840902007930597414536927187263432910509838476484747712640455973070255629651033946754409577836779012890565220388489153577763787166701601775301469796763640424027853354796721597079912940286372633185838345992751867196781172208834138690222106062075752065902154539126743262068198325214168378523129670934338475739147173758430908395286150876157060939089625709193041776836471990957819761231730801731776522136803338078544621050560922173478563753829038046021706523464351667620377394029868850002669902639971359287839437971544707) = true := by decide +kernel
theorem che_40_7_3 : chkE 40 7 33 40 (decH 2 896878567555) = true := by decide +kernel
theorem cove_40_7 : CovBE 40 7 8 40 :=
  CovBE.trans (CovBE.of_chk che_40_7_0) (CovBE.trans (CovBE.of_chk che_40_7_1) (CovBE.trans (CovBE.of_chk che_40_7_2) (CovBE.of_chk che_40_7_3)))

theorem che_40_8_0 : chkE 40 8 9 11 (decH 16 7271088977779083812717021056129104589569930450128790909956152815789290573466104269283161313985855087116786346658485669170080048523637826667258439290670591631555880638354531685852226422436427184019922321480954017220753379366399829170967935077098072969691206777753527488451689256142883876714632288942481822241605467818318427689377772895484478068572824439518139113124310771219932874065822298401170551010984482329746828267414931331) = true := by decide +kernel
theorem che_40_8_1 : chkE 40 8 11 26 (decH 36 30510036873265857398569622147128782151991554014124539740734811862169079207190131283249340788369012859982247004205649096439301096561351182380956671524393145356056173902742840564302942904218930797554279744806647394651313900811091380272635527230776302521888899047289353578184553635692210678464284638113412691804814372929619504538975910133972990529917562348999185008231438563789388783998393389393669605453449762949991767620144084376382569902931657696302040292061681529642827507184635406021386590578207735963940741821231771832905460124456404914317521408021148125940729450826765078593542) = true := by decide +kernel
theorem che_40_8_2 : chkE 40 8 26 32 (decH 28 2733688194927783245406477662042123827627768140540147840628760017108319837172093301372426720142795109484254837512686362642877501551642338566412604883760337762998210238070995385787168585134111268606071081450899815371795974002780603358682128025177403950319902136373494620045590787313181024149955142062251113040710011554385502686456508666408560288721440552297759900932939318239742240533179470642457870614820693875657445690954125681736340708281623116775820048865503191162537667248259) = true := by decide +kernel
theorem che_40_8_3 : chkE 40 8 32 40 (decH 2 492978775157840909536384638405689425516539151122574944829467740781611906050134657) = true := by decide +kernel
theorem cove_40_8 : CovBE 40 8 9 40 :=
  CovBE.trans (CovBE.of_chk che_40_8_0) (CovBE.trans (CovBE.of_chk che_40_8_1) (CovBE.trans (CovBE.of_chk che_40_8_2) (CovBE.of_chk che_40_8_3)))

theorem che_40_9_0 : chkE 40 9 10 26 (decH 38 5889737442604310325181845833359783702763745427496271603686866842405566369930533690795524578861495627831606156092610266262011573509429853319466003955481658971296635686889479563397921527483254442474163349444487240400967643587180160789429038203924233664371317468442202663070700995121648725374392996982927044876217976158495646999130577299103473150258957964322178115060963260794451544197051392492776670218407276060362715545929860253265604441321479487079077984048375711431281288133770846873332051810452190798520318442625194750804000102528162125685213315) = true := by decide +kernel
theorem che_40_9_1 : chkE 40 9 26 40 (decH 22 269232737398755757120999211326912691571479461120347374373283808497879126688091968122113164015037681773703547338901016279885645792773643195311716978647458899492386956743784007151268409560387721814805794118015395166496431091988867493827130891324712198888741763826357437646965778568959223744405310096780435565984240837239131126266961317440453875529124107616569475) = true := by decide +kernel
theorem cove_40_9 : CovBE 40 9 10 40 :=
  CovBE.trans (CovBE.of_chk che_40_9_0) (CovBE.of_chk che_40_9_1)

theorem che_40_10_0 : chkE 40 10 11 30 (decH 33 38895309219014976417145745730912226318607154075645035492775601702757377435240079907010288096134000773192201271465168876953022420909523736889426816004144764944571880555315463371099610836631936433166846759510273943776167221479947484286460286681567393503976948706562673910145873730194392613938891183314817050437182061157346322026808368408661651420267801291268592333592025797134491811069399031535221393575625846642456376989570657288226397922428934989845318070929173298953243299974933583426778200909408082882124146025363176924313690306274920390066065983889335175555) = true := by decide +kernel
theorem che_40_10_1 : chkE 40 10 30 40 (decH 2 611549874534104709317628687335149885555723454525833001671271973742183738488787585) = true := by decide +kernel
theorem cove_40_10 : CovBE 40 10 11 40 :=
  CovBE.trans (CovBE.of_chk che_40_10_0) (CovBE.of_chk che_40_10_1)

theorem che_40_11_0 : chkE 40 11 12 40 (decH 20 484032225606147837427776240125716475947006055992951930907679318877693072811702917358273804600198345105963909583971629908944770255668582037020091429802832256868810881116315358899383808465478126248225098167197055488871564404221310869917870710583454964104101694210591363) = true := by decide +kernel
theorem cove_40_11 : CovBE 40 11 12 40 :=
  CovBE.of_chk che_40_11_0

theorem che_40_12_0 : chkE 40 12 13 40 (decH 7 22340976856449937976035485333323796141563482600495012243091834877171063156951939) = true := by decide +kernel
theorem cove_40_12 : CovBE 40 12 13 40 :=
  CovBE.of_chk che_40_12_0

theorem che_40_13_0 : chkE 40 13 14 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_13 : CovBE 40 13 14 40 :=
  CovBE.of_chk che_40_13_0

theorem che_40_14_0 : chkE 40 14 15 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_14 : CovBE 40 14 15 40 :=
  CovBE.of_chk che_40_14_0

theorem che_40_15_0 : chkE 40 15 16 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_15 : CovBE 40 15 16 40 :=
  CovBE.of_chk che_40_15_0

theorem che_40_16_0 : chkE 40 16 17 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_16 : CovBE 40 16 17 40 :=
  CovBE.of_chk che_40_16_0

theorem che_40_17_0 : chkE 40 17 18 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_17 : CovBE 40 17 18 40 :=
  CovBE.of_chk che_40_17_0

theorem che_40_18_0 : chkE 40 18 19 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_18 : CovBE 40 18 19 40 :=
  CovBE.of_chk che_40_18_0

theorem che_40_19_0 : chkE 40 19 20 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_19 : CovBE 40 19 20 40 :=
  CovBE.of_chk che_40_19_0

theorem che_40_20_0 : chkE 40 20 21 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_20 : CovBE 40 20 21 40 :=
  CovBE.of_chk che_40_20_0

theorem che_40_21_0 : chkE 40 21 22 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_21 : CovBE 40 21 22 40 :=
  CovBE.of_chk che_40_21_0

theorem che_40_22_0 : chkE 40 22 23 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_22 : CovBE 40 22 23 40 :=
  CovBE.of_chk che_40_22_0

theorem che_40_23_0 : chkE 40 23 24 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_23 : CovBE 40 23 24 40 :=
  CovBE.of_chk che_40_23_0

theorem che_40_24_0 : chkE 40 24 25 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_24 : CovBE 40 24 25 40 :=
  CovBE.of_chk che_40_24_0

theorem che_40_25_0 : chkE 40 25 26 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_25 : CovBE 40 25 26 40 :=
  CovBE.of_chk che_40_25_0

theorem che_40_26_0 : chkE 40 26 27 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_26 : CovBE 40 26 27 40 :=
  CovBE.of_chk che_40_26_0

theorem che_40_27_0 : chkE 40 27 28 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_27 : CovBE 40 27 28 40 :=
  CovBE.of_chk che_40_27_0

theorem che_40_28_0 : chkE 40 28 29 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_28 : CovBE 40 28 29 40 :=
  CovBE.of_chk che_40_28_0

theorem che_40_29_0 : chkE 40 29 30 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_29 : CovBE 40 29 30 40 :=
  CovBE.of_chk che_40_29_0

theorem che_40_30_0 : chkE 40 30 31 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_30 : CovBE 40 30 31 40 :=
  CovBE.of_chk che_40_30_0

theorem che_40_31_0 : chkE 40 31 32 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_31 : CovBE 40 31 32 40 :=
  CovBE.of_chk che_40_31_0

theorem che_40_32_0 : chkE 40 32 33 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_32 : CovBE 40 32 33 40 :=
  CovBE.of_chk che_40_32_0

theorem che_40_33_0 : chkE 40 33 34 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_33 : CovBE 40 33 34 40 :=
  CovBE.of_chk che_40_33_0

theorem che_40_34_0 : chkE 40 34 35 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_34 : CovBE 40 34 35 40 :=
  CovBE.of_chk che_40_34_0

theorem che_40_35_0 : chkE 40 35 36 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_35 : CovBE 40 35 36 40 :=
  CovBE.of_chk che_40_35_0

theorem che_40_36_0 : chkE 40 36 37 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_36 : CovBE 40 36 37 40 :=
  CovBE.of_chk che_40_36_0

theorem che_40_37_0 : chkE 40 37 38 40 (decH 1 0) = true := by decide +kernel
theorem cove_40_37 : CovBE 40 37 38 40 :=
  CovBE.of_chk che_40_37_0

theorem cove_40 : CovQE 40 :=
  CovQE.of_covAE (CovAE.trans (CovAE.one cove_40_2) (CovAE.trans (CovAE.one cove_40_3) (CovAE.trans (CovAE.one cove_40_4) (CovAE.trans (CovAE.one cove_40_5) (CovAE.trans (CovAE.one cove_40_6) (CovAE.trans (CovAE.one cove_40_7) (CovAE.trans (CovAE.one cove_40_8) (CovAE.trans (CovAE.one cove_40_9) (CovAE.trans (CovAE.one cove_40_10) (CovAE.trans (CovAE.one cove_40_11) (CovAE.trans (CovAE.one cove_40_12) (CovAE.trans (CovAE.one cove_40_13) (CovAE.trans (CovAE.one cove_40_14) (CovAE.trans (CovAE.one cove_40_15) (CovAE.trans (CovAE.one cove_40_16) (CovAE.trans (CovAE.one cove_40_17) (CovAE.trans (CovAE.one cove_40_18) (CovAE.trans (CovAE.one cove_40_19) (CovAE.trans (CovAE.one cove_40_20) (CovAE.trans (CovAE.one cove_40_21) (CovAE.trans (CovAE.one cove_40_22) (CovAE.trans (CovAE.one cove_40_23) (CovAE.trans (CovAE.one cove_40_24) (CovAE.trans (CovAE.one cove_40_25) (CovAE.trans (CovAE.one cove_40_26) (CovAE.trans (CovAE.one cove_40_27) (CovAE.trans (CovAE.one cove_40_28) (CovAE.trans (CovAE.one cove_40_29) (CovAE.trans (CovAE.one cove_40_30) (CovAE.trans (CovAE.one cove_40_31) (CovAE.trans (CovAE.one cove_40_32) (CovAE.trans (CovAE.one cove_40_33) (CovAE.trans (CovAE.one cove_40_34) (CovAE.trans (CovAE.one cove_40_35) (CovAE.trans (CovAE.one cove_40_36) (CovAE.one cove_40_37))))))))))))))))))))))))))))))))))))

/-! ## E*_3 for `N ≤ 40`, and for all `N` modulo the residual -/

/-- **E*_3 for every `N ≤ 40`**: every 3-subset `{a, b, c}` of `[2, N - 1]` is co-reachable. -/
theorem e3_le_40 : ∀ N, N ≤ 40 → E3 N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    have IH : ∀ q, q < N → E3 q := fun q hq => ih q hq (by omega)
    have hG : N ≠ 7 → Good3 N := fun h7 => good3_le_50 N (by omega) h7
    interval_cases N
    exacts [e3_of_covE IH hG cove_0, e3_of_covE IH hG cove_1, e3_of_covE IH hG cove_2, e3_of_covE IH hG cove_3, e3_of_covE IH hG cove_4, e3_of_covE IH hG cove_5, e3_of_covE IH hG cove_6, e3_of_covE IH hG cove_7, e3_of_covE IH hG cove_8, e3_of_covE IH hG cove_9, e3_of_covE IH hG cove_10, e3_of_covE IH hG cove_11, e3_of_covE IH hG cove_12, e3_of_covE IH hG cove_13, e3_of_covE IH hG cove_14, e3_of_covE IH hG cove_15, e3_of_covE IH hG cove_16, e3_of_covE IH hG cove_17, e3_of_covE IH hG cove_18, e3_of_covE IH hG cove_19, e3_of_covE IH hG cove_20, e3_of_covE IH hG cove_21, e3_of_covE IH hG cove_22, e3_of_covE IH hG cove_23, e3_of_covE IH hG cove_24, e3_of_covE IH hG cove_25, e3_of_covE IH hG cove_26, e3_of_covE IH hG cove_27, e3_of_covE IH hG cove_28, e3_of_covE IH hG cove_29, e3_of_covE IH hG cove_30, e3_of_covE IH hG cove_31, e3_of_covE IH hG cove_32, e3_of_covE IH hG cove_33, e3_of_covE IH hG cove_34, e3_of_covE IH hG cove_35, e3_of_covE IH hG cove_36, e3_of_covE IH hG cove_37, e3_of_covE IH hG cove_38, e3_of_covE IH hG cove_39, e3_of_covE IH hG cove_40]

/-- **E*_3 for every `N ≤ 40`**, set form. -/
theorem ekStar_three_le_40 {N : Nat} (hN : N ≤ 40) {D : Finset Nat}
    (hD : D ⊆ Finset.Icc 2 (N - 1)) (hc : D.card = 3) : CoReach N D :=
  coReach_of_e3 (e3_le_40 N hN) hD hc

/-- **E*_3 for all `N`, modulo the residual**: if for every `N > 40` the interior triples not
settled by `CoveredES` are co-reachable, then every 3-subset of `[2, N - 1]` is co-reachable
for every `N`, i.e. Conjecture E*_3 (`EkStar.EkStarConj 3`) holds. -/
theorem ekStar_three_of_residual (hres : ∀ N, 40 < N → ResidualE N) :
    EkStar.EkStarConj 3 :=
  ekStarConj_three_of (e3_of_residualE e3_le_40 hres)

end EkStar3
end Folds
