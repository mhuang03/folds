import Folds.SuperExp7
import Folds.HypH

/-!
# Small residues of Hypothesis H, and the all-`N` bound from small residues only

`experiments/superexp8/PROOFS.txt`.

* **Theorem R in Lean** (`goodL_oddR`, the odd near-reduction of `experiments/hyph`): for
  `q = 2m + 1`, `ν = 2w`, `w < m`, the odds-first parity block
  `π = (2i - 1 for i in α) ++ reverse (2j for j in β)` is good for `(q, ν)` whenever
  `α` is good for `(m + 1, w)`, `β` is good for `(m, w)`, and the images `σα`, `σβ` avoid the
  (few) exceptional pairs of the maps `psiW w`, `chiW w` (Live4's `Agree`).
* **New cases of H, every modulus** (`hypH_two`, `hypH_four`, `hypH_three_even`, mirrors):
  `H(q, 2)` for every `q ≥ 3`, `H(q, 4)` for every `q ≥ 5`, `H(q, 3)` for every even `q ≥ 4`,
  and `H(q, q - 2)`, `H(q, q - 4)`, `H(q, q - 3)` (even `q`).  For `w ∈ {1, 2}` each map has
  at most one exceptional pair, which reversal (`prec_or_reverse`) always satisfies.
* **Compositions** (`semiCount_two_mod`, ...): `a(n+1)^2 a(n)^(q-2) ≤ a(nq + 2)` etc. for
  every `q`.
* **Small residues suffice** (`allN_of_smallH`): if `H(q, ρ)` holds whenever `16 ρ < q`, then
  `N^N ≤ 2^(15 N) a(N)^12` for EVERY `N ≥ 1` (exponent `1/12`).  The proven small residues
  (bounded `ρ`) do NOT give this: PROOFS.txt, section 1 (counting), and section 3 (parity
  trees stop at `ρ = 8` for `q ≡ ±1 mod 16`).  The unconditional all-`N` exponent stays `1/16`.
-/

namespace Folds
namespace SuperExp8

open Live2 Live3 Live4 GComp SuperExp7

/-! ## Theorem R: the odd near-reduction -/

def oddE (i : Nat) : Nat := 2 * i - 1

def evE (j : Nat) : Nat := 2 * j

/-- `sig (2m+1) (2w)` on the odd class, in the coordinates of `sig (m+1) w`. -/
def psiW (w y : Nat) : Nat := if y ≤ w then 2 * y else 2 * y - 1

/-- `sig (2m+1) (2w)` on the even class, in the coordinates of `sig m w`. -/
def chiW (w z : Nat) : Nat := if z ≤ w then 2 * z - 1 else 2 * z

theorem sig_oddE {m w i : Nat} (hw : w < m) (hi : 1 ≤ i ∧ i ≤ m + 1) :
    sig (2 * m + 1) (2 * w) (oddE i) = psiW w (sig (m + 1) w i) := by
  rw [sig_eq (by omega) (by unfold oddE; omega), sig_eq (by omega) hi]
  unfold oddE psiW
  split_ifs <;> omega

theorem sig_evE {m w j : Nat} (hw : w < m) (hj : 1 ≤ j ∧ j ≤ m) :
    sig (2 * m + 1) (2 * w) (evE j) = chiW w (sig m w j) := by
  rw [sig_eq (by omega) (by unfold evE; omega), sig_eq (by omega) hj]
  unfold evE chiW
  split_ifs <;> omega

theorem agree_oddE {m i j : Nat} (hi1 : 1 ≤ i) (hik : i ≤ m + 1) (hj1 : 1 ≤ j) (hjk : j ≤ m + 1) :
    Agree (2 * m + 1) (m + 1) oddE i j := by
  unfold Agree oddE reach
  omega

theorem agree_evE {m i j : Nat} (hi1 : 1 ≤ i) (hik : i ≤ m) (hj1 : 1 ≤ j) (hjk : j ≤ m) :
    Agree (2 * m + 1) m evE i j := by
  unfold Agree evE reach
  omega

/-- The exceptional pairs of a map: where `Agree` fails. -/
def NotAgree (Q k : Nat) (φ : Nat → Nat) (i j : Nat) : Prop := ¬ Agree Q k φ i j

theorem semiSymmetric_map_exact {Q k : Nat} {φ : Nat → Nat} {β : List Nat}
    (hf : IsFoldSeq k β) (hv : SemiSymmetric k β)
    (hinj : ∀ a b, 1 ≤ a → a ≤ k → 1 ≤ b → b ≤ k → φ a = φ b → a = b)
    (hag : ∀ i j, 1 ≤ i → i ≤ k → 1 ≤ j → j ≤ k → i ≠ j → Agree Q k φ i j) :
    SemiSymmetric Q (β.map φ) :=
  semiSymmetric_near (e := fun _ _ => False) (fun _ hx => (mem_range'_of_perm hf).1 hx)
    (nodup_of_foldSeq hf) hv (fun _ _ _ _ h => h) hinj
    fun i j h1 h2 h3 h4 h5 _ => hag i j h1 h2 h3 h4 h5

theorem semiSymmetric_map_prec {Q k : Nat} {φ : Nat → Nat} {β : List Nat}
    (hf : IsFoldSeq k β) (hv : SemiSymmetric k β) (hp : Prec (NotAgree Q k φ) β)
    (hinj : ∀ a b, 1 ≤ a → a ≤ k → 1 ≤ b → b ≤ k → φ a = φ b → a = b) :
    SemiSymmetric Q (β.map φ) :=
  semiSymmetric_near (fun _ hx => (mem_range'_of_perm hf).1 hx) (nodup_of_foldSeq hf) hv hp hinj
    fun i j _ _ _ _ _ h => by unfold NotAgree at h; exact not_not.1 h

/-- **Theorem R** (odd near-reduction).  `q = 2m + 1`, `ν = 2w`, `w < m`. -/
theorem goodL_oddR {m w : Nat} (hw : w < m) {α β : List Nat}
    (hα : GoodL (m + 1) w α) (hβ : GoodL m w β)
    (h1 : Prec (NotAgree (2 * m + 1) (m + 1) (psiW w)) (α.map (sig (m + 1) w)))
    (h2 : Prec (NotAgree (2 * m + 1) m (chiW w)) (β.map (sig m w))) :
    GoodL (2 * m + 1) (2 * w) (α.map oddE ++ (β.map evE).reverse) := by
  obtain ⟨hfa, hva, hsa⟩ := hα
  obtain ⟨hfb, hvb, hsb⟩ := hβ
  have hba : ∀ x ∈ α, 1 ≤ x ∧ x ≤ m + 1 := fun x hx => (mem_range'_of_perm hfa).1 hx
  have hbb : ∀ x ∈ β, 1 ≤ x ∧ x ≤ m := fun x hx => (mem_range'_of_perm hfb).1 hx
  have hfa' := isFoldSeq_map_sig (show w < m + 1 by omega) hfa
  have hfb' := isFoldSeq_map_sig hw hfb
  -- the complete sequence
  have hπf : IsFoldSeq (2 * m + 1) (α.map oddE ++ (β.map evE).reverse) := by
    refine perm_range'_of_nodup_subset ?_ ?_ ?_
    · rw [List.nodup_append]
      refine ⟨nodup_map_of_injOn (nodup_of_foldSeq hfa) fun a ha b hb h => by
          unfold oddE at h; have := hba a ha; have := hba b hb; omega,
        List.nodup_reverse.2 (nodup_map_of_injOn (nodup_of_foldSeq hfb) fun a _ b _ h => by
          unfold evE at h; omega), ?_⟩
      intro a ha b hb e
      rw [List.mem_reverse] at hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
      have := hba i hi
      unfold oddE evE at e; omega
    · intro z hz
      rw [List.mem_append, List.mem_reverse] at hz
      rcases hz with hz | hz
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz; have := hba i hi; unfold oddE; omega
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz; have := hbb j hj; unfold evE; omega
    · simp [hfa.length_eq, hfb.length_eq]; omega
  refine ⟨hπf, ?_, ?_⟩
  · refine semiSymmetric_append_rev hπf ?_ ?_
    · exact semiSymmetric_map_exact hfa hva (fun a b _ _ _ _ h => by unfold oddE at h; omega)
        fun i j h1 h2 h3 h4 _ => agree_oddE h1 h2 h3 h4
    · rw [List.reverse_reverse]
      exact semiSymmetric_map_exact hfb hvb (fun a b _ _ _ _ h => by unfold evE at h; omega)
        fun i j h1 h2 h3 h4 _ => agree_evE h1 h2 h3 h4
  · have ex : (α.map oddE).map (sig (2 * m + 1) (2 * w)) =
        (α.map (sig (m + 1) w)).map (psiW w) := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun i hi => sig_oddE hw (hba i hi)
    have ey : (β.map evE).map (sig (2 * m + 1) (2 * w)) =
        (β.map (sig m w)).map (chiW w) := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun j hj => sig_evE hw (hbb j hj)
    have hσf := isFoldSeq_map_sig (show 2 * w < 2 * m + 1 by omega) hπf
    rw [List.map_append, List.map_reverse, ex, ey] at hσf ⊢
    refine semiSymmetric_append_rev hσf ?_ ?_
    · refine semiSymmetric_map_prec hfa' hsa h1 fun a b _ _ _ _ h => ?_
      unfold psiW at h; split_ifs at h <;> omega
    · rw [List.reverse_reverse]
      refine semiSymmetric_map_prec hfb' hsb h2 fun a b _ _ _ _ h => ?_
      unfold chiW at h; split_ifs at h <;> omega

/-! ## One exceptional pair: reversal -/

/-- If `e` relates at most the single pair `(a, b)`, then a nodup list or its reverse has no
`e`-violation. -/
theorem prec_or_reverse {e : Nat → Nat → Prop} {a b : Nat} (he : ∀ i j, e i j → i = a ∧ j = b)
    {L : List Nat} (hnd : L.Nodup) : Prec e L ∨ Prec e L.reverse := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨c1, c2⟩ := hc
  unfold Prec at c1 c2
  push Not at c1 c2
  obtain ⟨p, hp, j, hj, hej⟩ := c1
  obtain ⟨p', hp', j', hj', hej'⟩ := c2
  obtain ⟨ea, eb⟩ := he _ _ hej
  obtain ⟨ea', eb'⟩ := he _ _ hej'
  obtain ⟨i, hi, hji⟩ := List.mem_iff_getElem.1 hj
  obtain ⟨i', hi', hji'⟩ := List.mem_iff_getElem.1 hj'
  rw [List.getElem_take] at hji
  rw [List.getElem_take, List.getElem_reverse] at hji'
  rw [List.getElem_reverse] at ea'
  simp only [List.length_take, List.length_reverse] at hi hi' hp'
  have k1 : i = L.length - 1 - i' :=
    (hnd.getElem_inj_iff).1 (hji.trans (eb.trans (eb'.symm.trans hji'.symm)))
  have k2 : p = L.length - 1 - p' := (hnd.getElem_inj_iff).1 (ea.trans ea'.symm)
  omega

theorem goodL_prec_of_pair {n w : Nat} (hw : w < n) {e : Nat → Nat → Prop} {a b : Nat}
    (he : ∀ i j, e i j → i = a ∧ j = b) {α : List Nat} (hα : GoodL n w α) :
    ∃ α', GoodL n w α' ∧ Prec e (α'.map (sig n w)) := by
  have hnd := nodup_of_foldSeq (isFoldSeq_map_sig hw hα.1)
  rcases prec_or_reverse he hnd with h | h
  · exact ⟨α, hα, h⟩
  · exact ⟨α.reverse, hα.reverse hw, by rw [List.map_reverse]; exact h⟩

theorem prec_of_none {e : Nat → Nat → Prop} (he : ∀ i j, ¬ e i j) {α : List Nat} :
    Prec e α := fun _ _ j _ => he _ j

/-- Restricting the relation to distinct pairs inside the strip. -/
def InStrip (k : Nat) (e : Nat → Nat → Prop) (i j : Nat) : Prop :=
  e i j ∧ 1 ≤ i ∧ i ≤ k ∧ 1 ≤ j ∧ j ≤ k ∧ i ≠ j

theorem prec_of_inStrip {k : Nat} {e : Nat → Nat → Prop} {L : List Nat} (hf : IsFoldSeq k L)
    (h : Prec (InStrip k e) L) : Prec e L := by
  intro p hp j hj he
  have hnd := nodup_of_foldSeq hf
  have h1 := (mem_range'_of_perm hf).1 (List.getElem_mem hp)
  have h2 := (mem_range'_of_perm hf).1 (List.mem_of_mem_take hj)
  refine h p hp j hj ⟨he, h1.1, h1.2, h2.1, h2.2, fun e => ?_⟩
  obtain ⟨i, hi, hji⟩ := List.mem_iff_getElem.1 hj
  rw [List.getElem_take] at hji
  simp only [List.length_take] at hi
  have := (hnd.getElem_inj_iff).1 (hji.trans e.symm)
  omega

/-! ## Exceptional pairs for `w = 1, 2` -/

theorem exc_psi_one {m : Nat} (hm : 2 ≤ m) :
    ∀ i j, InStrip (m + 1) (NotAgree (2 * m + 1) (m + 1) (psiW 1)) i j → i = 1 ∧ j = 2 := by
  intro i j h
  obtain ⟨h, h1, h2, h3, h4, h5⟩ := h
  unfold NotAgree Agree psiW reach at h
  split_ifs at h <;> omega

theorem exc_chi_one {m : Nat} (hm : 2 ≤ m) :
    ∀ i j, ¬ InStrip m (NotAgree (2 * m + 1) m (chiW 1)) i j := by
  intro i j h
  obtain ⟨h, h1, h2, h3, h4, h5⟩ := h
  unfold NotAgree Agree chiW reach at h
  split_ifs at h <;> omega

theorem exc_psi_two {m : Nat} (hm : 3 ≤ m) :
    ∀ i j, InStrip (m + 1) (NotAgree (2 * m + 1) (m + 1) (psiW 2)) i j → i = 2 ∧ j = 4 := by
  intro i j h
  obtain ⟨h, h1, h2, h3, h4, h5⟩ := h
  unfold NotAgree Agree psiW reach at h
  split_ifs at h <;> omega

theorem exc_chi_two {m : Nat} (hm : 3 ≤ m) :
    ∀ i j, InStrip m (NotAgree (2 * m + 1) m (chiW 2)) i j → i = 2 ∧ j = 3 := by
  intro i j h
  obtain ⟨h, h1, h2, h3, h4, h5⟩ := h
  unfold NotAgree Agree chiW reach at h
  split_ifs at h <;> omega

/-- Theorem R with at most one exceptional pair on each side: any good sequences of
`(m + 1, w)` and `(m, w)` will do, after reversing them if necessary. -/
theorem hypH_oddR_pairs {m w : Nat} (hw : w < m) {a b c d : Nat}
    (hA : ∃ α, GoodL (m + 1) w α) (hB : ∃ β, GoodL m w β)
    (h1 : ∀ i j, InStrip (m + 1) (NotAgree (2 * m + 1) (m + 1) (psiW w)) i j → i = a ∧ j = b)
    (h2 : ∀ i j, InStrip m (NotAgree (2 * m + 1) m (chiW w)) i j → i = c ∧ j = d) :
    HypH (2 * m + 1) (2 * w) := by
  obtain ⟨α, hα⟩ := hA
  obtain ⟨β, hβ⟩ := hB
  obtain ⟨α', hα', hp1⟩ := goodL_prec_of_pair (show w < m + 1 by omega) h1 hα
  obtain ⟨β', hβ', hp2⟩ := goodL_prec_of_pair hw h2 hβ
  have hg := goodL_oddR hw hα' hβ'
    (prec_of_inStrip (isFoldSeq_map_sig (show w < m + 1 by omega) hα'.1) hp1)
    (prec_of_inStrip (isFoldSeq_map_sig hw hβ'.1) hp2)
  exact ⟨_, (goodL_iff (show 2 * w < 2 * m + 1 by omega)).1 hg⟩

/-! ## New cases of H for every modulus -/

theorem goodL_of_hypH {q ρ : Nat} (hρ : ρ < q) (h : HypH q ρ) : ∃ π, GoodL q ρ π := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π, (goodL_iff hρ).2 hπ⟩

theorem goodL_one_exists {n : Nat} (hn : 2 ≤ n) : ∃ π, GoodL n 1 π := by
  obtain ⟨t, π, hπ, -⟩ := good_one_exists n hn
  exact ⟨π, hπ⟩

/-- **`H(q, 2)` for every `q ≥ 3`.** -/
theorem hypH_two : ∀ q, 3 ≤ q → HypH q 2 := by
  intro q hq
  rcases Nat.even_or_odd' q with ⟨m, rfl | rfl⟩
  · have h := hypH_comp (j := 2) (m := m) (c := 1) (e := 0) (by norm_num) (by omega) (by omega)
      (by norm_num) (hypH_zero (by norm_num)) (hypH_one (by omega)) (fun h => absurd h (by omega))
    rwa [show m * 2 = 2 * m by ring] at h
  · rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | hm
    · exact hypH_neg_one (q := 3) (by norm_num)
    · have h := hypH_oddR_pairs (w := 1) (by omega) (goodL_one_exists (by omega))
        (goodL_one_exists hm) (exc_psi_one hm) (c := 0) (d := 0)
        fun i j h => absurd h (exc_chi_one hm i j)
      simpa using h

/-- **`H(q, 4)` for every `q ≥ 5`.** -/
theorem hypH_four : ∀ q, 5 ≤ q → HypH q 4 := by
  intro q hq
  rcases Nat.even_or_odd' q with ⟨m, rfl | rfl⟩
  · have h := hypH_comp (j := 2) (m := m) (c := 2) (e := 0) (by norm_num) (by omega) (by omega)
      (by norm_num) (hypH_zero (by norm_num)) (hypH_two m (by omega))
      (fun h => absurd h (by omega))
    rwa [show m * 2 = 2 * m by ring] at h
  · rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm
    · exact hypH_neg_one (q := 5) (by norm_num)
    · have h := hypH_oddR_pairs (w := 2) (by omega)
        (goodL_of_hypH (by omega) (hypH_two (m + 1) (by omega)))
        (goodL_of_hypH (by omega) (hypH_two m (by omega))) (exc_psi_two hm) (exc_chi_two hm)
      simpa using h

/-- **`H(q, 3)` for every even `q ≥ 4`.** -/
theorem hypH_three_even : ∀ m, 2 ≤ m → HypH (2 * m) 3 := by
  intro m hm
  rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
  · exact hypH_neg_one (q := 4) (by norm_num)
  · have h := hypH_comp (j := 2) (m := m) (c := 1) (e := 1) (by norm_num) (by omega) (by omega)
      (by norm_num) (hypH_one (le_refl 2)) (hypH_one (by omega))
      (fun _ => by rw [Nat.mod_eq_of_lt (by omega)]; exact hypH_two m (by omega))
    rwa [show m * 2 = 2 * m by ring] at h

theorem hypH_neg_two {q : Nat} (hq : 3 ≤ q) : HypH q (q - 2) :=
  hypH_mirror (by omega) (by omega) (by rw [Nat.mod_eq_of_lt (by omega)]) (hypH_two q hq)

theorem hypH_neg_four {q : Nat} (hq : 5 ≤ q) : HypH q (q - 4) :=
  hypH_mirror (by omega) (by omega) (by rw [Nat.mod_eq_of_lt (by omega)]) (hypH_four q hq)

theorem hypH_neg_three_even {m : Nat} (hm : 2 ≤ m) : HypH (2 * m) (2 * m - 3) :=
  hypH_mirror (by omega) (by omega) (by rw [Nat.mod_eq_of_lt (by omega)])
    (hypH_three_even m hm)

/-- The proven residues for a general modulus. -/
def SmallRes (q ρ : Nat) : Prop :=
  ρ = 0 ∨ ρ = 1 ∨ ρ = 2 ∨ ρ = 4 ∨ ρ + 1 = q ∨ ρ + 2 = q ∨ ρ + 4 = q ∨
    (q % 2 = 0 ∧ (ρ = 3 ∨ ρ + 3 = q))

theorem hypH_smallRes {q ρ : Nat} (hρ : ρ < q) (h : SmallRes q ρ) : HypH q ρ := by
  rcases Nat.eq_zero_or_pos ρ with h0 | h0
  · subst h0; exact hypH_zero (by omega)
  rcases h with rfl | rfl | rfl | rfl | h | h | h | ⟨he, rfl | h⟩
  · omega
  · exact hypH_one (by omega)
  · exact hypH_two q (by omega)
  · exact hypH_four q (by omega)
  · rw [show ρ = q - 1 by omega]; exact hypH_neg_one (q := q) (by omega)
  · rw [show ρ = q - 2 by omega]; exact hypH_neg_two (q := q) (by omega)
  · rw [show ρ = q - 4 by omega]; exact hypH_neg_four (q := q) (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m := ⟨q / 2, by omega⟩
    exact hypH_three_even m (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m := ⟨q / 2, by omega⟩
    rw [show ρ = 2 * m - 3 by omega]; exact hypH_neg_three_even (m := m) (by omega)

/-- **Compositions with small residues, every modulus.** -/
theorem semiCount_smallRes {q n ρ : Nat} (hρ : ρ < q) (h : SmallRes q ρ) :
    semiCount (n + 1) ^ ρ * semiCount n ^ (q - ρ) ≤ semiCount (n * q + ρ) :=
  semiCount_pow_of_hypH hρ (hypH_smallRes hρ h)

theorem semiCount_two_mod {q n : Nat} (hq : 3 ≤ q) :
    semiCount (n + 1) ^ 2 * semiCount n ^ (q - 2) ≤ semiCount (n * q + 2) :=
  semiCount_smallRes (ρ := 2) (by omega) (by unfold SmallRes; omega)

theorem semiCount_four_mod {q n : Nat} (hq : 5 ≤ q) :
    semiCount (n + 1) ^ 4 * semiCount n ^ (q - 4) ≤ semiCount (n * q + 4) :=
  semiCount_smallRes (ρ := 4) (by omega) (by unfold SmallRes; omega)

/-! ## Small residues suffice for the `1/12` bound -/

theorem pow_sqrt_bound {N r : Nat} (h : 64 * r ^ 2 ≤ N) : N ^ r ≤ 2 ^ N := by
  set s := Nat.sqrt N with hs
  have hs1 : s * s ≤ N := by have := Nat.sqrt_le' N; rw [pow_two] at this; exact this
  have hs2 : N < (s + 1) * (s + 1) := by
    have := Nat.lt_succ_sqrt' N; rw [pow_two] at this; exact this
  have h8 : 8 * r ≤ s := Nat.le_sqrt'.2 (by nlinarith)
  have hp : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
  have hN : N ≤ 2 ^ (2 * s) := by
    have := Nat.mul_le_mul hp hp
    rw [← pow_add, show s + s = 2 * s by ring] at this
    omega
  calc N ^ r ≤ (2 ^ (2 * s)) ^ r := Nat.pow_le_pow_left hN r
    _ = 2 ^ (2 * s * r) := by rw [← pow_mul]
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- **All `N` from small residues.**  If `H(q, ρ)` holds whenever `16 ρ < q`, then
`N^N ≤ 2^(15 N) a(N)^12` for every `N` (exponent `1/12`).  Only the residues
`ρ = N mod 2^j < 2^j ≤ q / 64` with `2^j ~ √N / 16` are used. -/
theorem allN_of_smallH (hH : ∀ q ρ, 16 * ρ < q → HypH q ρ) (N : Nat) :
    N ^ N ≤ 2 ^ (15 * N) * semiCount N ^ 12 := by
  have ha := Slip.semiCount_pos N
  by_cases hN : N < 64
  · calc N ^ N ≤ (2 ^ 6) ^ N := Nat.pow_le_pow_left (by omega) N
      _ = 2 ^ (6 * N) := by rw [← pow_mul]
      _ ≤ 2 ^ (15 * N) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ (15 * N) * semiCount N ^ 12 :=
          Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
  push Not at hN
  set L := Nat.log 2 N with hL
  have hL1 : 2 ^ L ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hL2 : N < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hL6 : 6 ≤ L := by
    by_contra h
    have : 2 ^ (L + 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set j := (L - 6) / 2 with hj
  set M := 2 ^ j with hM
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  have hMM : M * M = 2 ^ (2 * j) := by rw [hM, ← pow_add]; ring_nf
  have hlo : 64 * (M * M) ≤ N := by
    rw [hMM]
    calc 64 * 2 ^ (2 * j) = 2 ^ (2 * j + 6) := by rw [pow_add]; ring
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ N := hL1
  have hhi : N ≤ 256 * (M * M) := by
    rw [hMM]
    calc N ≤ 2 ^ (L + 1) := hL2.le
      _ ≤ 2 ^ (2 * j + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 256 * 2 ^ (2 * j) := by rw [pow_add]; ring
  have hMN : M * (M + 1) ≤ N := by nlinarith
  have hq : 64 * M ≤ N / M := (Nat.le_div_iff_mul_le (by omega)).2 (by nlinarith)
  have hr : N % M < M := Nat.mod_lt N (by omega)
  obtain ⟨-, hb⟩ := allN_of_hypH (j := j) (N := N) hMN
    (hH _ _ (show 16 * (N % M) < N / M by omega))
  rw [← hM] at hb
  set K := N / M * M with hK
  have hKN : K + N % M = N := Nat.div_add_mod' N M
  -- square the bound
  have hb2 : M ^ (2 * K) ≤ 64 ^ K * semiCount N ^ 12 := by
    have := Nat.mul_le_mul hb hb
    calc M ^ (2 * K) = M ^ K * M ^ K := by rw [two_mul, pow_add]
      _ ≤ _ := this
      _ = 64 ^ K * semiCount N ^ 12 := by
          rw [show (64 : Nat) = 8 * 8 by norm_num, mul_pow]; ring
  have hNK : N ^ K ≤ 2 ^ (14 * K) * semiCount N ^ 12 := by
    calc N ^ K ≤ (256 * (M * M)) ^ K := Nat.pow_le_pow_left hhi K
      _ = 256 ^ K * M ^ (2 * K) := by rw [mul_pow, ← pow_two, ← pow_mul, mul_comm 2 K]
      _ ≤ 256 ^ K * (64 ^ K * semiCount N ^ 12) := Nat.mul_le_mul_left _ hb2
      _ = 2 ^ (14 * K) * semiCount N ^ 12 := by
          rw [show (256 : Nat) = 2 ^ 8 by norm_num, show (64 : Nat) = 2 ^ 6 by norm_num,
            ← pow_mul, ← pow_mul, show 14 * K = 8 * K + 6 * K by ring, pow_add]; ring
  have hNr : N ^ (N % M) ≤ 2 ^ N := by
    have := Nat.mul_le_mul hr.le hr.le
    exact pow_sqrt_bound (by rw [pow_two]; omega)
  calc N ^ N = N ^ K * N ^ (N % M) := by rw [← pow_add, hKN]
    _ ≤ (2 ^ (14 * K) * semiCount N ^ 12) * 2 ^ N := Nat.mul_le_mul hNK hNr
    _ = 2 ^ (14 * K + N) * semiCount N ^ 12 := by rw [pow_add]; ring
    _ ≤ 2 ^ (15 * N) * semiCount N ^ 12 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))

end SuperExp8
end Folds

