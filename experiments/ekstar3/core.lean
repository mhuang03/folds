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

