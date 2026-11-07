import Folds.Live4
import Folds.SuperExp6
import Folds.SuperExp2
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Hypothesis H is the "good class" property of the liveness work

`experiments/superexp7/PROOFS.txt`.

SuperExp6 (`semiCount_gcomp`) composes the residue classes mod `q` of the `(nq + ρ)`-strip
whenever a class order `π` and `π.map (mst q ρ)` are both valid `q`-sequences ("hypothesis H"
for `(q, ρ)`).  Live4 calls a sequence `π` with `π` and `π.map (sig q ν)` valid `GoodL q ν π`.

* **Bridge** (`mst_eq_sig`, `goodL_iff`, `hypH_iff`): `mst q ρ = sig q ρ` on `[1, q]`, so
  `HypH q ρ ↔ ∃ π, GoodL q ρ π ↔ ∃ t, Good q ρ t`.  Every `Gd` derivation of Live4 is a proof
  of H (`hypH_of_gd`), and `semiCount_of_good` is the composition bound from a good class.
* **Proven cases** of H:
  - `ρ = 0`, `ρ = 1` and `ρ = q - 1` for every `q` (`hypH_zero`, `hypH_one`, `hypH_neg_one`);
  - every `ρ` for `q = 2^a` (`allH_pow_two`) and for `q ≤ 12` (`allH_le_12`);
  - every `ρ` for the primes `13, 17, 19, 23` (Live4 certificates, `allH_13` …);
  - block composition (`hypH_comp`): H for `(j, e)`, `(m, c)`, `(m, c+1)` gives H for
    `(m j, j c + e)`; hence `allH_mul`, and **every `ρ` for every `23`-smooth `q`**
    (`allH_smooth`); small and large residues (`hypH_low`, `hypH_high`) for `q = m j` with
    `j` smooth.
* Compositions (`semiCount_smooth`): `a(n)^(q-ρ) a(n+1)^ρ ≤ a(n q + ρ)` for every `23`-smooth
  `q` (in particular every `q ≤ 28`, `allH_le_28`) and every `ρ < q`, and for every `q ≥ 2`
  with `ρ ∈ {0, 1, q - 1}` (`semiCount_one_mod`, `semiCount_neg_one_mod`).
* The all-`N` step of SuperExp6 3.2 for one `N` (`allN_of_hypH`): with `M = 2^j`,
  `M (M + 1) ≤ N`, H for `(⌊N/M⌋, N mod M)` gives `M^K ≤ 8^K a(N)^6`, `K = ⌊N/M⌋ M ≥ NM/(M+1)`
  (exponent `1/12` for `M ≈ √N`); unconditional when `⌊N/M⌋` is `23`-smooth (`allN_smooth`).
  The proven cases of H do NOT cover every `N` (PROOFS.txt, section 3): the best
  unconditional all-`N` exponent is still `1/16` (SuperExp5).
-/

namespace Folds
namespace SuperExp7

open Live2 Live3 Live4 GComp

/-! ## The bridge -/

/-- The SuperExp6 involution is Live2's reflection `σ(t) = ((ρ - t) mod q) + 1`. -/
theorem mst_eq_sig {q ρ t : Nat} (hρ : ρ < q) (ht1 : 1 ≤ t) (htq : t ≤ q) :
    mst q ρ t = sig q ρ t := by
  unfold mst sig
  split
  · rw [show ρ + q - t = (ρ - t) + q * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem map_mst_eq {q ρ : Nat} (hρ : ρ < q) {π : List Nat} (hf : IsFoldSeq q π) :
    π.map (mst q ρ) = π.map (sig q ρ) :=
  List.map_congr_left fun t ht => by
    have := (mem_range'_of_perm hf).1 ht
    exact mst_eq_sig hρ this.1 this.2

/-- Hypothesis H of SuperExp6 for `(q, ρ)`: some class order works in `semiCount_gcomp`. -/
def HypH (q ρ : Nat) : Prop := ∃ π, π ∈ semiSeqs q ∧ SemiSymmetric q (π.map (mst q ρ))

/-- **Bridge.**  The SuperExp6 condition on a class order is exactly `GoodL`. -/
theorem goodL_iff {q ρ : Nat} (hρ : ρ < q) {π : List Nat} :
    GoodL q ρ π ↔ π ∈ semiSeqs q ∧ SemiSymmetric q (π.map (mst q ρ)) := by
  rw [mem_semiSeqs]
  constructor
  · rintro ⟨hf, h1, h2⟩
    exact ⟨⟨hf, h1⟩, by rw [map_mst_eq hρ hf]; exact h2⟩
  · rintro ⟨⟨hf, h1⟩, h2⟩
    exact ⟨hf, h1, by rw [← map_mst_eq hρ hf]; exact h2⟩

/-- **Bridge.**  H for `(q, ρ)` holds iff some class is good for `(q, ν = ρ)`. -/
theorem hypH_iff {q ρ : Nat} (hρ : ρ < q) : HypH q ρ ↔ ∃ t, Good q ρ t := by
  constructor
  · rintro ⟨π, h⟩
    have hg := (goodL_iff hρ).2 h
    cases π with
    | nil =>
      have := hg.1.length_eq
      simp at this; omega
    | cons a π' => exact ⟨a, _, hg, rfl⟩
  · rintro ⟨t, π, hg, -⟩
    exact ⟨π, (goodL_iff hρ).1 hg⟩

theorem hypH_of_good {q ρ t : Nat} (hρ : ρ < q) (h : Good q ρ t) : HypH q ρ :=
  (hypH_iff hρ).2 ⟨t, h⟩

/-- Every `Gd` derivation of Live4 proves H. -/
theorem hypH_of_gd {q ρ t : Nat} (hρ : ρ < q) (h : Gd q ρ t) : HypH q ρ :=
  hypH_of_good hρ h.good

/-- The composition bound of SuperExp6 from any proof of H. -/
theorem semiCount_of_hypH {q n ρ : Nat} (hρ : ρ < q) (h : HypH q ρ) :
    ∏ i : Fin q, semiCount (sz n ρ (i.val + 1)) ≤ semiCount (n * q + ρ) := by
  obtain ⟨π, hπ, hπm⟩ := h
  exact semiCount_gcomp (by omega) hρ hπ hπm

/-- The composition bound of SuperExp6 from a good class (Live4). -/
theorem semiCount_of_good {q n ρ t : Nat} (hρ : ρ < q) (h : Good q ρ t) :
    ∏ i : Fin q, semiCount (sz n ρ (i.val + 1)) ≤ semiCount (n * q + ρ) :=
  semiCount_of_hypH hρ (hypH_of_good hρ h)

/-! ## Uniform cases -/

theorem hypH_zero {q : Nat} (hq : 0 < q) : HypH q 0 :=
  hypH_of_good hq (good_zero (t := 1) ⟨le_rfl, hq⟩)

theorem hypH_one {q : Nat} (hq : 2 ≤ q) : HypH q 1 := by
  obtain ⟨t, ht⟩ := good_one_exists q hq
  exact hypH_of_good (by omega) ht

theorem hypH_neg_one {q : Nat} (hq : 2 ≤ q) : HypH q (q - 1) := by
  obtain ⟨t, ht⟩ := good_one_exists q hq
  exact hypH_of_good (by omega) (good_rot hq ht)

/-- The mirror `ρ ↦ q - ρ`. -/
theorem hypH_mirror {q ρ ρ' : Nat} (hρ : ρ < q) (hρ' : ρ' < q) (hs : (q - ρ) % q = ρ')
    (h : HypH q ρ) : HypH q ρ' := by
  obtain ⟨t, ht⟩ := (hypH_iff hρ).1 h
  have := good_mirror hρ ht
  rw [hs] at this
  exact hypH_of_good hρ' this

theorem hypH_of_fullOK {q ρ : Nat} {π : List Nat} (h : fullOK (q, ρ, π)) : HypH q ρ :=
  ⟨π, mem_semiSeqs.2 ⟨h.2.1, h.2.2.1⟩, by rw [map_mst_eq h.1 h.2.1]; exact h.2.2.2⟩

/-- **Block composition** (Live4 `good_comp`): H for `(j, e)`, `(m, c)` and, if `e > 0`,
`(m, c + 1 mod m)` gives H for `(m j, j c + e)`. -/
theorem hypH_comp {j m c e : Nat} (hj : 0 < j) (hm : 0 < m) (hc : c < m) (he : e < j)
    (hJ : HypH j e) (hA : HypH m c) (hB : 0 < e → HypH m ((c + 1) % m)) :
    HypH (m * j) (j * c + e) := by
  obtain ⟨a, ha⟩ := (hypH_iff he).1 hJ
  have hA' := (hypH_iff hc).1 hA
  have hB' : 0 < e → ∃ z, Good m ((c + 1) % m) z := fun h =>
    (hypH_iff (Nat.mod_lt _ hm)).1 (hB h)
  have hy : ∃ y, Good m (inner m c e a) y := by
    unfold inner
    split_ifs with h
    · exact hB' (by have := ha.bounds; omega)
    · exact hA'
  obtain ⟨y, hy⟩ := hy
  have hν : j * c + e < m * j := by
    have := Nat.mul_le_mul_left j (show c + 1 ≤ m by omega)
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm j m] at this
    omega
  exact hypH_of_good hν (good_comp hj hm hc he ha hy hA' hB')

/-! ## Moduli with every residue -/

/-- H holds for every residue mod `q`. -/
def AllH (q : Nat) : Prop := ∀ ρ, ρ < q → HypH q ρ

theorem allH_one : AllH 1 := fun ρ h => by
  obtain rfl : ρ = 0 := by omega
  exact hypH_zero (by norm_num)

/-- `AllH` is closed under products. -/
theorem allH_mul {m j : Nat} (hm : 0 < m) (hj : 0 < j) (hM : AllH m) (hJ : AllH j) :
    AllH (m * j) := by
  intro ν hν
  have hc : ν / j < m := by
    rw [Nat.div_lt_iff_lt_mul hj]; exact hν
  have e : ν = j * (ν / j) + ν % j := (Nat.div_add_mod ν j).symm
  rw [e]
  exact hypH_comp hj hm hc (Nat.mod_lt _ hj) (hJ _ (Nat.mod_lt _ hj)) (hM _ hc)
    fun _ => hM _ (Nat.mod_lt _ hm)

theorem allH_pow_two (a : Nat) : AllH (2 ^ a) := by
  intro ρ hρ
  exact hypH_of_good hρ (good_pow_two a ρ 1 hρ le_rfl (Nat.one_le_two_pow))

theorem allH_le_12 {q : Nat} (h2 : 2 ≤ q) (hq : q ≤ 12) : AllH q := by
  intro ρ hρ
  refine hypH_of_good hρ (good_table (s := 2) h2 hq hρ (by norm_num) h2 ?_)
  unfold excB
  rcases (by omega : q = 2 ∨ 3 ≤ q) with rfl | h3
  · rfl
  · have : (2 == q) = false := by simp; omega
    simp [this]

theorem allH_13 : AllH 13 := by
  intro ν hν
  interval_cases ν
  · exact hypH_zero (by norm_num)
  · exact hypH_one (by norm_num)
  · exact hypH_of_fullOK cert_13_3
  · exact hypH_of_fullOK cert_13_10
  · exact hypH_of_fullOK cert_13_17
  · exact hypH_of_fullOK cert_13_24
  · exact hypH_of_fullOK cert_13_31
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_13_31)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_13_24)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_13_17)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_13_10)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_13_3)
  · exact hypH_neg_one (q := 13) (by norm_num)

theorem allH_17 : AllH 17 := by
  intro ν hν
  interval_cases ν
  · exact hypH_zero (by norm_num)
  · exact hypH_one (by norm_num)
  · exact hypH_of_fullOK cert_17_4
  · exact hypH_of_fullOK cert_17_13
  · exact hypH_of_fullOK cert_17_22
  · exact hypH_of_fullOK cert_17_31
  · exact hypH_of_fullOK cert_17_40
  · exact hypH_of_fullOK cert_17_49
  · exact hypH_of_fullOK cert_17_58
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_17_58)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_17_49)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_17_40)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_17_31)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_17_22)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_17_13)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_17_4)
  · exact hypH_neg_one (q := 17) (by norm_num)

theorem allH_19 : AllH 19 := by
  intro ν hν
  interval_cases ν
  · exact hypH_zero (by norm_num)
  · exact hypH_one (by norm_num)
  · exact hypH_of_fullOK cert_19_4
  · exact hypH_of_fullOK cert_19_14
  · exact hypH_of_fullOK cert_19_24
  · exact hypH_of_fullOK cert_19_34
  · exact hypH_of_fullOK cert_19_44
  · exact hypH_of_fullOK cert_19_54
  · exact hypH_of_fullOK cert_19_64
  · exact hypH_of_fullOK cert_19_74
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_19_74)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_19_64)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_19_54)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_19_44)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_19_34)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_19_24)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_19_14)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_19_4)
  · exact hypH_neg_one (q := 19) (by norm_num)

theorem allH_23 : AllH 23 := by
  intro ν hν
  interval_cases ν
  · exact hypH_zero (by norm_num)
  · exact hypH_one (by norm_num)
  · exact hypH_of_fullOK cert_23_5
  · exact hypH_of_fullOK cert_23_17
  · exact hypH_of_fullOK cert_23_29
  · exact hypH_of_fullOK cert_23_41
  · exact hypH_of_fullOK cert_23_53
  · exact hypH_of_fullOK cert_23_65
  · exact hypH_of_fullOK cert_23_77
  · exact hypH_of_fullOK cert_23_89
  · exact hypH_of_fullOK cert_23_101
  · exact hypH_of_fullOK cert_23_113
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_23_113)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_23_101)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_23_89)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_23_77)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_23_65)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_23_53)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_23_41)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_23_29)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_23_17)
  · exact hypH_mirror (by norm_num) (by norm_num) (by norm_num) (hypH_of_fullOK cert_23_5)
  · exact hypH_neg_one (q := 23) (by norm_num)


/-- Every prime `p ≤ 23` has H for every residue. -/
theorem allH_prime {p : Nat} (hp : p.Prime) (h23 : p ≤ 23) : AllH p := by
  have h2 := hp.two_le
  by_cases h12 : p ≤ 12
  · exact allH_le_12 h2 h12
  · interval_cases p <;> first
      | exact allH_13 | exact allH_17 | exact allH_19 | exact allH_23
      | exact absurd hp (by norm_num)

/-- **Every `23`-smooth modulus has H for every residue.** -/
theorem allH_smooth : ∀ q, 0 < q → (∀ p, p.Prime → p ∣ q → p ≤ 23) → AllH q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq hs
    by_cases h1 : q = 1
    · subst h1; exact allH_one
    have hp := Nat.minFac_prime h1
    have hd := Nat.minFac_dvd q
    have hpos := hp.pos
    obtain ⟨m, hm⟩ := hd
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; omega
      · exact h
    have hlt : m < q := by
      have := hp.two_le
      rw [hm]; nlinarith
    have hM := ih m hlt hm0 fun p' hp' hd' => hs p' hp' (hm ▸ Dvd.dvd.mul_left hd' _)
    have hP := allH_prime hp (hs _ hp ⟨m, hm⟩)
    rw [hm, Nat.mul_comm]
    exact allH_mul hm0 hpos hM hP

/-- Every modulus `q ≤ 28` has H for every residue. -/
theorem allH_le_28 {q : Nat} (h1 : 0 < q) (h28 : q ≤ 28) : AllH q :=
  allH_smooth q h1 fun p hp hd => by
    have h2 : p ≤ 28 := (Nat.le_of_dvd h1 hd).trans h28
    by_contra h
    have h3 : 24 ≤ p := by omega
    interval_cases p <;> norm_num at hp

/-- Small residues: `ρ < j` with `j` an `AllH` divisor of `q = m j`. -/
theorem hypH_low {m j e : Nat} (hm : 0 < m) (hj : 0 < j) (hJ : AllH j) (he : e < j) :
    HypH (m * j) e := by
  have h := hypH_comp (c := 0) hj hm hm he (hJ e he) (hypH_zero hm) fun _ => by
    rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | h2
    · exact hypH_zero (by norm_num)
    · rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; exact hypH_one h2
  simpa using h

/-- Large residues: `ρ ≥ q - j` with `j` an `AllH` divisor of `q = m j`. -/
theorem hypH_high {m j e : Nat} (hm : 0 < m) (hj : 0 < j) (hJ : AllH j) (he : e < j) :
    HypH (m * j) (j * (m - 1) + e) := by
  refine hypH_comp hj hm (by omega) he (hJ e he) ?_ fun _ => ?_
  · rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | h2
    · exact hypH_zero (by norm_num)
    · exact hypH_neg_one h2
  · rw [Nat.sub_add_cancel hm, Nat.mod_self]; exact hypH_zero hm

/-! ## Compositions in power form -/

theorem prod_range_sz (f : Nat → Nat) (n ρ : Nat) : ∀ k,
    ∏ i ∈ Finset.range k, f (sz n ρ (i + 1)) = f (n + 1) ^ min k ρ * f n ^ (k - min k ρ)
  | 0 => by simp
  | k + 1 => by
    rw [Finset.prod_range_succ, prod_range_sz f n ρ k]
    unfold sz
    split_ifs with h
    · rw [show min (k + 1) ρ = min k ρ + 1 by omega, show k + 1 - (min k ρ + 1) = k - min k ρ by
        omega, pow_succ]
      ring
    · rw [show min (k + 1) ρ = min k ρ by omega, show k + 1 - min k ρ = (k - min k ρ) + 1 by
        omega, pow_succ]
      ring

theorem prod_sz (f : Nat → Nat) {q n ρ : Nat} (hρ : ρ ≤ q) :
    ∏ i : Fin q, f (sz n ρ (i.val + 1)) = f (n + 1) ^ ρ * f n ^ (q - ρ) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => f (sz n ρ (i + 1))) q, prod_range_sz,
    Nat.min_eq_right hρ]

/-- The composition bound in power form, from any proof of H. -/
theorem semiCount_pow_of_hypH {q n ρ : Nat} (hρ : ρ < q) (h : HypH q ρ) :
    semiCount (n + 1) ^ ρ * semiCount n ^ (q - ρ) ≤ semiCount (n * q + ρ) := by
  have := semiCount_of_hypH (n := n) hρ h
  rwa [prod_sz semiCount hρ.le] at this

/-- **Unconditional composition for smooth moduli.**  If every prime factor of `q` is at
most `23`, then for every `N`, `a(⌊N/q⌋ + 1)^(N mod q) a(⌊N/q⌋)^(q - N mod q) ≤ a(N)`. -/
theorem semiCount_smooth {q : Nat} (hq : 0 < q) (hs : ∀ p, p.Prime → p ∣ q → p ≤ 23) (N : Nat) :
    semiCount (N / q + 1) ^ (N % q) * semiCount (N / q) ^ (q - N % q) ≤ semiCount N := by
  have h := semiCount_pow_of_hypH (n := N / q) (Nat.mod_lt N hq)
    (allH_smooth q hq hs _ (Nat.mod_lt N hq))
  rwa [Nat.div_add_mod'] at h

/-- `ρ ∈ {0, 1, q - 1}`: compositions for every modulus `q ≥ 2`. -/
theorem semiCount_one_mod {q n : Nat} (hq : 2 ≤ q) :
    semiCount (n + 1) * semiCount n ^ (q - 1) ≤ semiCount (n * q + 1) := by
  simpa using semiCount_pow_of_hypH (n := n) (by omega) (hypH_one hq)

theorem semiCount_neg_one_mod {q n : Nat} (hq : 2 ≤ q) :
    semiCount (n + 1) ^ (q - 1) * semiCount n ≤ semiCount (n * q + (q - 1)) := by
  have := semiCount_pow_of_hypH (n := n) (by omega) (hypH_neg_one hq)
  rwa [show q - (q - 1) = 1 by omega, pow_one] at this

/-! ## The all-`N` composition with class sizes `2^j` and `2^j + 1` -/

/-- `a(2^j + 1)^6 ≥ (2^j / 8)^(2^j)` (from `a(2n+1) ≥ a(n) a(n+1)` and SuperExp2). -/
theorem pow_le_semiCount_succ_pow_six (j : Nat) :
    (2 ^ j) ^ (2 ^ j) ≤ 8 ^ (2 ^ j) * semiCount (2 ^ j + 1) ^ 6 := by
  induction j with
  | zero =>
    have : 0 < semiCount 2 ^ 6 := Nat.pow_pos (Slip.semiCount_pos 2)
    norm_num
    omega
  | succ j ih =>
    have h1 := Slip.pow_le_semiCount_pow_six j
    have hodd := semiCount_odd (n := 2 ^ j) Nat.one_le_two_pow
    have hle : semiCount (2 ^ j) * semiCount (2 ^ j + 1) ≤ semiCount (2 ^ (j + 1) + 1) := by
      rw [show 2 ^ (j + 1) + 1 = 2 * 2 ^ j + 1 by ring]; omega
    have hP : (2 ^ j) ^ (2 ^ j) * (2 ^ j) ^ (2 ^ j) ≤
        (2 ^ (2 ^ j) * 8 ^ (2 ^ j)) * (semiCount (2 ^ j) * semiCount (2 ^ j + 1)) ^ 6 := by
      calc (2 ^ j) ^ (2 ^ j) * (2 ^ j) ^ (2 ^ j)
          ≤ (2 ^ (2 ^ j) * semiCount (2 ^ j) ^ 6) * (8 ^ (2 ^ j) * semiCount (2 ^ j + 1) ^ 6) :=
            Nat.mul_le_mul h1 ih
        _ = _ := by ring
    have hx : (2:Nat) ^ (j + 1) = 2 * 2 ^ j := by ring
    have e1 : (2 ^ (j + 1)) ^ (2 ^ (j + 1)) =
        4 ^ (2 ^ j) * ((2 ^ j) ^ (2 ^ j) * (2 ^ j) ^ (2 ^ j)) := by
      rw [hx, pow_mul, show (2 * 2 ^ j) ^ 2 = 4 * (2 ^ j * 2 ^ j) by ring, mul_pow, mul_pow]
    have e2 : (8:Nat) ^ (2 ^ (j + 1)) = 4 ^ (2 ^ j) * (2 ^ (2 ^ j) * 8 ^ (2 ^ j)) := by
      rw [hx, pow_mul, ← mul_pow, ← mul_pow]; norm_num
    rw [e1, e2, Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ (hP.trans (Nat.mul_le_mul_left _ ?_))
    exact Nat.pow_le_pow_left hle 6

/-- **The all-`N` composition, for one pair.**  Let `M = 2^j`, `q M ≤ N < q (M + 1)`.  If H
holds for `(q, N - q M)`, then `M^(qM) ≤ 8^(qM) a(N)^6`, i.e. `a(N) ≥ (M/8)^(qM/6)`. -/
theorem pow_le_semiCount_pow_six_of_hypH {N q j : Nat} (h1 : q * 2 ^ j ≤ N)
    (h2 : N < q * (2 ^ j + 1)) (hH : HypH q (N - q * 2 ^ j)) :
    (2 ^ j) ^ (q * 2 ^ j) ≤ 8 ^ (q * 2 ^ j) * semiCount N ^ 6 := by
  set M := 2 ^ j with hMdef
  set ρ := N - q * M with hρdef
  have hρ : ρ < q := by
    have : q * (M + 1) = q * M + q := by ring
    omega
  have hc := semiCount_pow_of_hypH (n := M) hρ hH
  rw [show M * q + ρ = N by rw [hρdef, Nat.mul_comm]; omega] at hc
  have a1 := Slip.pow_le_semiCount_pow_six j
  rw [← hMdef] at a1
  have a2 := pow_le_semiCount_succ_pow_six j
  rw [← hMdef] at a2
  have a1' : M ^ M ≤ 8 ^ M * semiCount M ^ 6 :=
    a1.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) _))
  have hq : q * M = M * ρ + M * (q - ρ) := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hρ.le, Nat.mul_comm]
  calc M ^ (q * M) = (M ^ M) ^ ρ * (M ^ M) ^ (q - ρ) := by rw [hq, Nat.pow_add, Nat.pow_mul,
        Nat.pow_mul]
    _ ≤ (8 ^ M * semiCount (M + 1) ^ 6) ^ ρ * (8 ^ M * semiCount M ^ 6) ^ (q - ρ) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left a2 _) (Nat.pow_le_pow_left a1' _)
    _ = 8 ^ (q * M) * (semiCount (M + 1) ^ ρ * semiCount M ^ (q - ρ)) ^ 6 := by
        rw [hq, Nat.pow_add, Nat.pow_mul, Nat.pow_mul, Nat.mul_pow, Nat.mul_pow, Nat.mul_pow]
        ring
    _ ≤ 8 ^ (q * M) * semiCount N ^ 6 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc 6)

/-- The canonical choice `q = ⌊N/M⌋`, `ρ = N mod M` when `M (M + 1) ≤ N`. -/
theorem canonical_q {N M : Nat} (hM : 0 < M) (h : M * (M + 1) ≤ N) :
    N / M * M ≤ N ∧ N < N / M * (M + 1) ∧ N - N / M * M = N % M := by
  have hd := Nat.div_add_mod' N M
  have hr := Nat.mod_lt N hM
  have hq : M + 1 ≤ N / M := (Nat.le_div_iff_mul_le hM).2 (by rw [Nat.mul_comm]; exact h)
  refine ⟨by omega, ?_, by omega⟩
  have : N / M * (M + 1) = N / M * M + N / M := by ring
  omega

/-- **Conditional all-`N` bound (exponent `1/12`).**  If H holds for the pair
`(⌊N/M⌋, N mod M)`, `M = 2^j`, `M (M + 1) ≤ N`, then `M^K ≤ 8^K a(N)^6` with
`K = ⌊N/M⌋ M ≥ N M / (M + 1)`.  Taking `M` maximal (`M > (√N - 1)/2`) gives
`ln a(N) ≥ (N/12) ln N - O(N)`; see PROOFS.txt.  Unconditional whenever `⌊N/M⌋` is `23`-smooth,
`N mod M ∈ {0, 1}`, or `⌊N/M⌋` has an `AllH` divisor `> N mod M` (`hypH_low`). -/
theorem allN_of_hypH {N j : Nat} (h : 2 ^ j * (2 ^ j + 1) ≤ N)
    (hH : HypH (N / 2 ^ j) (N % 2 ^ j)) :
    N * 2 ^ j ≤ (N / 2 ^ j * 2 ^ j) * (2 ^ j + 1) ∧
      (2 ^ j) ^ (N / 2 ^ j * 2 ^ j) ≤ 8 ^ (N / 2 ^ j * 2 ^ j) * semiCount N ^ 6 := by
  obtain ⟨c1, c2, c3⟩ := canonical_q (N := N) (M := 2 ^ j) (Nat.two_pow_pos j) h
  refine ⟨?_, pow_le_semiCount_pow_six_of_hypH c1 c2 (by rw [c3]; exact hH)⟩
  have := Nat.mul_lt_mul_of_pos_right c2 (Nat.two_pow_pos j)
  have e : N / 2 ^ j * (2 ^ j + 1) * 2 ^ j = N / 2 ^ j * 2 ^ j * (2 ^ j + 1) := by ring
  omega

/-- Unconditional instance: if `⌊N / 2^j⌋` is `23`-smooth (and `2^j (2^j + 1) ≤ N`), the
`1/12`-type bound holds at `N`. -/
theorem allN_smooth {N j : Nat} (h : 2 ^ j * (2 ^ j + 1) ≤ N)
    (hs : ∀ p, p.Prime → p ∣ N / 2 ^ j → p ≤ 23) :
    (2 ^ j) ^ (N / 2 ^ j * 2 ^ j) ≤ 8 ^ (N / 2 ^ j * 2 ^ j) * semiCount N ^ 6 := by
  have hq : 0 < N / 2 ^ j := by
    have := (canonical_q (N := N) (M := 2 ^ j) (Nat.two_pow_pos j) h).2.1
    rcases Nat.eq_zero_or_pos (N / 2 ^ j) with h0 | h0
    · rw [h0] at this; omega
    · exact h0
  have hρ : N % 2 ^ j < N / 2 ^ j := by
    have := (canonical_q (N := N) (M := 2 ^ j) (Nat.two_pow_pos j) h).2.1
    have := Nat.div_add_mod' N (2 ^ j)
    have : N / 2 ^ j * (2 ^ j + 1) = N / 2 ^ j * 2 ^ j + N / 2 ^ j := by ring
    omega
  exact (allN_of_hypH h (allH_smooth _ hq hs _ hρ)).2

end SuperExp7
end Folds
