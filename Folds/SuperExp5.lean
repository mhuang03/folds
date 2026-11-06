import Folds.SuperExp3
import Folds.SuperExp4

/-!
# Odd-`N` slips: exponent `1/16` for all `N`

Notation of `Folds/SuperExp.lean` and `Folds/SuperExp2.lean`.

**Odd slip lemma** (`oddSlip_mem_semiSeqs`, derived from the general slip lemma
`GSlip.blocks_mem_semiSeqs_iff`).  Let `N = 2n + 1`, `d` a `{0,1}`-indicator with `d 0 = 0`
(slip set `D ⊆ [1, n]`), `τ ∈ V_n`, `σ ∈ V_{n+1}`.  Then
`τ.map (i ↦ 2i + d i) ++ σ.map (i ↦ 2i - 1 - d (i-1))` is a valid sequence of the `N`-strip if
for every `k ∈ D`

* `τ` places `k` before `qq n k = 2k mod* n`,
* `σ` places `pp (n+1) k = (2k+1) mod* (n+1)` before `k + 1`,
* (wrap condition, at the doubling preimage of the slipped crease, which exists because `2` is
  invertible mod `N`) if `k ≢ n (mod 2)`: `τ` places `(k+n+1)/2` before `k`;
  if `k ≡ n (mod 2)`: `σ` places `k + 1` before `(k+n+2)/2`.

Counting form: `oddSum n = ∑_{D ⊆ [1,n]} #condFo(n,D) · #condSo(n,D) ≤ a(2n+1)` (`oddSum_le`).

**Odd node** (`oddNodeA`, `oddNodeB`).  Of the two children `n`, `n + 1` of `2n + 1` one is
odd; put it in odds-first parity-block form `PB(α, β)` and slip at `k = 2i`,
`i ∈ ivals c p` (`⌊p/4⌋` indices, `2i ≤ p = ⌊n/2⌋`, one parity class).  The wrap panel then
has the right parity to be free, and each slip leaves exactly two order conditions, one on the
even child and one on a half of the odd child; reversal flips both, so averaging (`avg4`) gives

    a(e) · a(p) · a(p+1) · 2^{⌈⌊p/4⌋/4⌉} ≤ 4 · a(2n+1)      (e = the even child),

about `n/32` bits more than `a(2n+1) ≥ 2 a(n) a(n+1)`.

**All `N`** (`alln16_aux`, `self_pow_le_semiCount_pow_16`): with this odd-node bound in the
potential induction of `Folds/SuperExp4.lean` (surplus `7/4` per panel at even nodes):

    N^N ≤ 2^{12N} a(N)^{16}   for all N ≥ 1,   i.e.  a(N) ≥ (N/4096)^{N/16},

improving the exponent `1/17` of `Folds.Slip.Up.self_pow_le_semiCount_pow_17`.
Paper proofs and checks: `experiments/superexp5/PROOFS.txt`.
-/

namespace Folds
namespace Slip
namespace Odd

open GSlip Up

/-! ## The odd slip lemma -/

/-- Admissible slip indicator for odd sizes: values in `{0, 1}`, `d 0 = 0`. -/
structure OAdm (d : Nat → Nat) : Prop where
  le_one : ∀ i, d i ≤ 1
  zero : d 0 = 0

/-- Counting function of the first block `i ↦ 2i + d i` (`i ∈ [1, n]`). -/
def kap (n : Nat) (d : Nat → Nat) (y : Nat) : Nat :=
  min n (y / 2 - if y % 2 = 0 then d (y / 2) else 0)

/-- Counting function of the second block `i ↦ 2i - 1 - d (i - 1)` (`i ∈ [1, n + 1]`). -/
def mu (n : Nat) (d : Nat → Nat) (y : Nat) : Nat :=
  min (n + 1) (y / 2 + if y % 2 = 0 then d (y / 2) else 1)

theorem kap_odd {n y : Nat} {d : Nat → Nat} (h : y % 2 = 1) : kap n d y = min n (y / 2) := by
  unfold kap; split <;> omega

theorem kap_even {n y : Nat} {d : Nat → Nat} (h : y % 2 = 0) :
    kap n d y = min n (y / 2 - d (y / 2)) := by
  unfold kap; split <;> omega

theorem mu_odd {n y : Nat} {d : Nat → Nat} (h : y % 2 = 1) :
    mu n d y = min (n + 1) (y / 2 + 1) := by
  unfold mu; split <;> omega

theorem mu_even {n y : Nat} {d : Nat → Nat} (h : y % 2 = 0) :
    mu n d y = min (n + 1) (y / 2 + d (y / 2)) := by
  unfold mu; split <;> omega

section Lemma
variable {n : Nat} {d : Nat → Nat}

theorem blockF (hd : OAdm d) : Block (2 * n + 1) n (slipF d) (kap n d) where
  pos x h1 _ := by unfold slipF; omega
  le x _ h2 := by have := hd.le_one x; unfold slipF; omega
  mono x y _ _ h := by have := hd.le_one x; have := hd.le_one y; unfold slipF; omega
  count x y h1 h2 := by
    have hx := hd.le_one x
    unfold slipF kap
    rcases Nat.even_or_odd' y with ⟨m, rfl | rfl⟩
    · rw [show 2 * m / 2 = m by omega, ite_eq_left (by omega)]
      have hm := hd.le_one m
      by_cases hxm : x = m
      · subst hxm; omega
      · omega
    · rw [show (2 * m + 1) / 2 = m by omega, ite_eq_right (by omega)]; omega
  cle y := by unfold kap; omega

theorem blockS (hd : OAdm d) : Block (2 * n + 1) (n + 1) (slipS d) (mu n d) where
  pos x h1 _ := by
    have := hd.zero; unfold slipS
    rcases Nat.lt_or_ge x 2 with h | h
    · rw [show x = 1 by omega, show 2 * 1 - 1 - d (1 - 1) = 1 - d 0 by rfl, hd.zero]
    · have := hd.le_one (x - 1); omega
  le x _ h2 := by unfold slipS; omega
  mono x y h1 _ h := by
    have := hd.le_one (x - 1); have := hd.le_one (y - 1); unfold slipS; omega
  count x y h1 h2 := by
    have hx := hd.le_one (x - 1)
    have h0 := hd.zero
    unfold slipS mu
    rcases Nat.even_or_odd' y with ⟨m, rfl | rfl⟩
    · rw [show 2 * m / 2 = m by omega, ite_eq_left (by omega)]
      have hm := hd.le_one m
      by_cases hxm : x = m + 1
      · subst hxm; rw [show m + 1 - 1 = m by omega]; omega
      · omega
    · rw [show (2 * m + 1) / 2 = m by omega, ite_eq_right (by omega)]; omega
  cle y := by unfold mu; omega

theorem split (hd : OAdm d) :
    Split (2 * n + 1) n (n + 1) (slipF d) (kap n d) (slipS d) (mu n d) where
  bf := blockF hd
  bg := blockS hd
  disj x y h1 _ h3 _ := by
    have := hd.le_one x; have := hd.le_one (y - 1)
    unfold slipF slipS
    by_cases hxy : y - 1 = x
    · rw [hxy]; omega
    · omega
  sum := by omega

theorem ext_lt {N m z : Nat} {μ : Nat → Nat} (h : z < N) : ext N m μ z = μ z := by
  unfold ext; rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]; simp

theorem ext_ge {N m z : Nat} {μ : Nat → Nat} (h1 : N ≤ z) (h2 : z < 2 * N) :
    ext N m μ z = m + μ (z - N) := by
  unfold ext
  have hN : 0 < N := by omega
  rw [Nat.div_eq_sub_div hN h1, Nat.div_eq_of_lt (by omega), Nat.mod_eq_sub_mod h1,
    Nat.mod_eq_of_lt (by omega)]
  ring

theorem below_range' (n y : Nat) : below (List.range' 1 n) y = min y n := by
  induction n with
  | zero => simp [below]
  | succ n ih =>
    unfold below at *
    rw [List.range'_concat, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil]
    split <;> simp_all <;> omega

theorem cycBelow_range' {n : Nat} (hn : 0 < n) (w : Nat) : cycBelow n (List.range' 1 n) w = w := by
  unfold cycBelow
  rw [below_range', List.length_range', Nat.min_eq_left (Nat.mod_lt _ hn).le]
  have := Nat.div_add_mod w n
  rw [Nat.mul_comm] at this
  omega

/-- First block of the odd slip lemma. -/
theorem firstCond_odd (hd : OAdm d) {τ : List Nat} (hτ : τ ∈ semiSeqs n)
    (hF : ∀ k (hk : k < τ.length), d τ[k] = 1 → qq n τ[k] ∉ τ.take k)
    (hW : ∀ k (hk : k < τ.length), d τ[k] = 0 → n + 1 ≤ 2 * τ[k] →
      d (2 * τ[k] - n - 1) = 1 → 2 * τ[k] - n - 1 ∉ τ.take k) :
    FirstCond (2 * n + 1) n (slipF d) (kap n d) τ := by
  obtain ⟨hf, hs⟩ := mem_semiSeqs.1 hτ
  have hnd := nodup_of_foldSeq hf
  intro k hk
  have hjr : 1 ≤ τ[k] ∧ τ[k] ≤ n := (mem_range'_of_perm hf).1 (List.getElem_mem hk)
  have hTr : ∀ x ∈ τ.take k, 1 ≤ x ∧ x ≤ n := fun x hx =>
    (mem_range'_of_perm hf).1 (List.mem_of_mem_take hx)
  have hTnd : (τ.take k).Nodup := take_nodup hnd k
  have hjT : τ[k] ∉ τ.take k := fun h => absurd ((getElem_mem_take_iff hnd hk).1 h) (lt_irrefl k)
  have hn : 0 < n := by omega
  have step : cycBelow n (τ.take k) (2 * τ[k] - 1) = 2 * below (τ.take k) (τ[k] - 1) :=
    (semiStep_iff_cyclicStep hTnd hTr hjr.1 hjr.2 hjT).1 (hs k hk)
  have succ := fun y => cycBelow_succ hn hTnd hTr y
  have hF' := hF k hk
  have hW' := hW k hk
  generalize τ[k] = j at hjr hjT step hF' hW' ⊢
  generalize τ.take k = T at hTr hTnd step succ hF' hW' hjT ⊢
  rw [← step]
  unfold slipF
  have hdj := hd.le_one j
  rcases Nat.lt_or_ge (2 * (2 * j + d j) - 1) (2 * n + 1) with hlt | hge
  · rw [ext_lt hlt]
    unfold kap
    rw [ite_eq_right (by omega)]
    rcases (by omega : d j = 0 ∨ d j = 1) with h0 | h1
    · rw [h0]; congr 1; omega
    · have e := succ (2 * j - 1)
      rw [show 2 * j - 1 + 1 = 2 * j by omega] at e
      have hq : (2 * j - 1) % n + 1 ∉ T := hF' h1
      rw [ite_eq_right hq, Nat.add_zero] at e
      rw [h1, show min n ((2 * (2 * j + 1) - 1) / 2 - 0) = 2 * j by omega, e]
  · rw [ext_ge hge (by omega)]
    unfold kap
    rw [ite_eq_left (by omega)]
    rcases (by omega : d j = 0 ∨ d j = 1) with h0 | h1
    · rw [h0, show (2 * (2 * j + 0) - 1 - (2 * n + 1)) / 2 = 2 * j - n - 1 by omega]
      have hw := hd.le_one (2 * j - n - 1)
      rcases (by omega : d (2 * j - n - 1) = 0 ∨ d (2 * j - n - 1) = 1) with w0 | w1
      · rw [w0]; congr 1; omega
      · have hz : n ≤ 2 * j - 2 := by
          by_contra hc
          rw [show 2 * j - n - 1 = 0 by omega, hd.zero] at w1
          omega
        have e := succ (2 * j - 2)
        rw [show 2 * j - 2 + 1 = 2 * j - 1 by omega,
          show (2 * j - 2) % n = 2 * j - 2 - n by
            rw [Nat.mod_eq_sub_mod hz, Nat.mod_eq_of_lt (by omega)],
          show 2 * j - 2 - n + 1 = 2 * j - n - 1 by omega,
          ite_eq_right (hW' h0 (by omega) w1), Nat.add_zero] at e
        rw [w1, show n + min n (2 * j - n - 1 - 1) = 2 * j - 2 by omega, e]
    · rw [h1, show (2 * (2 * j + 1) - 1 - (2 * n + 1)) / 2 = 2 * j - n by omega]
      have hw := hd.le_one (2 * j - n)
      rcases (by omega : d (2 * j - n) = 0 ∨ d (2 * j - n) = 1) with w0 | w1
      · have e := succ (2 * j - 1)
        rw [show 2 * j - 1 + 1 = 2 * j by omega] at e
        have hq : (2 * j - 1) % n + 1 ∉ T := hF' h1
        rw [ite_eq_right hq, Nat.add_zero] at e
        rw [w0, show n + min n (2 * j - n - 0) = 2 * j by omega, e]
      · have hz : 1 ≤ 2 * j - n := by
          by_contra hc
          rw [show 2 * j - n = 0 by omega, hd.zero] at w1
          omega
        rw [w1]; congr 1; omega

/-- Second block of the odd slip lemma (on top of the complete first block). -/
theorem secondCond_odd (hn : 1 ≤ n) (hd : OAdm d) {σ : List Nat} (hσ : σ ∈ semiSeqs (n + 1))
    (hS : ∀ k (hk : k < σ.length), d (σ[k] - 1) = 1 → pp (n + 1) (σ[k] - 1) ∈ σ.take k)
    (hW : ∀ k (hk : k < σ.length), d (σ[k] - 1) = 0 → n + 2 ≤ 2 * σ[k] →
      d (2 * σ[k] - n - 2) = 1 → 2 * σ[k] - n - 1 ∈ σ.take k) :
    SecondCond (2 * n + 1) (n + 1) ((List.range' 1 n).map (slipF d)) (slipS d) (mu n d) σ := by
  obtain ⟨hf, hs⟩ := mem_semiSeqs.1 hσ
  have hnd := nodup_of_foldSeq hf
  have hr : ∀ x ∈ List.range' 1 n, 1 ≤ x ∧ x ≤ n := fun x hx => by
    rw [List.mem_range'_1] at hx; omega
  have hn0 : 0 < n := by omega
  have hFc : ∀ z, cycBelow (2 * n + 1) ((List.range' 1 n).map (slipF d)) z =
      ext (2 * n + 1) n (kap n d) z := fun z => by
    rw [cycBelow_map (blockF hd) hn0 hr, cycBelow_range' hn0]
  have hFb : ∀ y, below ((List.range' 1 n).map (slipF d)) y = kap n d y := fun y => by
    rw [below_map (blockF hd) hr, below_range', Nat.min_eq_left ((blockF hd).cle y)]
  intro k hk
  rw [hFc, hFb]
  have hjr : 1 ≤ σ[k] ∧ σ[k] ≤ n + 1 := (mem_range'_of_perm hf).1 (List.getElem_mem hk)
  have hUr : ∀ x ∈ σ.take k, 1 ≤ x ∧ x ≤ n + 1 := fun x hx =>
    (mem_range'_of_perm hf).1 (List.mem_of_mem_take hx)
  have hUnd : (σ.take k).Nodup := take_nodup hnd k
  have hjU : σ[k] ∉ σ.take k := fun h => absurd ((getElem_mem_take_iff hnd hk).1 h) (lt_irrefl k)
  have step : cycBelow (n + 1) (σ.take k) (2 * σ[k] - 1) = 2 * below (σ.take k) (σ[k] - 1) :=
    (semiStep_iff_cyclicStep hUnd hUr hjr.1 hjr.2 hjU).1 (hs k hk)
  have succ := fun y => cycBelow_succ (by omega : 0 < n + 1) hUnd hUr y
  have hS' := hS k hk
  have hW' := hW k hk
  generalize σ[k] = j at hjr hjU step hS' hW' ⊢
  generalize σ.take k = U at hUr hUnd step succ hS' hW' hjU ⊢
  unfold slipS
  have he := hd.le_one (j - 1)
  -- the first-block count at `g j - 1`
  have hk1 : kap n d (2 * j - 1 - d (j - 1) - 1) = j - 1 - d (j - 1) := by
    rcases (by omega : d (j - 1) = 0 ∨ d (j - 1) = 1) with e0 | e1
    · rw [e0, show 2 * j - 1 - 0 - 1 = 2 * (j - 1) by omega, kap_even (by omega),
        show 2 * (j - 1) / 2 = j - 1 by omega, e0]
      omega
    · have hj2 : 2 ≤ j := by
        by_contra hc; rw [show j - 1 = 0 by omega, hd.zero] at e1; omega
      rw [e1, show 2 * j - 1 - 1 - 1 = 2 * (j - 2) + 1 by omega, kap_odd (by omega)]
      omega
  rw [hk1]
  have hj1 : 1 ≤ 2 * j - 1 - d (j - 1) := by
    rcases Nat.lt_or_ge j 2 with h | h
    · rw [show j - 1 = 0 by omega, hd.zero]; omega
    · omega
  have hz1 : (2 * (2 * j - 1 - d (j - 1)) - 1) % 2 = 1 := by omega
  rcases Nat.lt_or_ge (2 * (2 * j - 1 - d (j - 1)) - 1) (2 * n + 1) with hlt | hge
  · rw [ext_lt hlt, ext_lt hlt, kap_odd hz1, mu_odd hz1]
    rcases (by omega : d (j - 1) = 0 ∨ d (j - 1) = 1) with e0 | e1
    · rw [e0, show min n ((2 * (2 * j - 1 - 0) - 1) / 2) = 2 * j - 2 by omega,
        show min (n + 1) ((2 * (2 * j - 1 - 0) - 1) / 2 + 1) = 2 * j - 1 by omega]
      omega
    · have e := succ (2 * j - 2)
      rw [show 2 * j - 2 + 1 = 2 * j - 1 by omega] at e
      have hp : (2 * (j - 1)) % (n + 1) + 1 ∈ U := hS' e1
      rw [show 2 * (j - 1) = 2 * j - 2 by omega] at hp
      rw [ite_eq_left hp] at e
      rw [e1, show min n ((2 * (2 * j - 1 - 1) - 1) / 2) = 2 * j - 3 by omega,
        show min (n + 1) ((2 * (2 * j - 1 - 1) - 1) / 2 + 1) = 2 * j - 2 by omega]
      omega
  · have hz0 : (2 * (2 * j - 1 - d (j - 1)) - 1 - (2 * n + 1)) % 2 = 0 := by omega
    rw [ext_ge hge (by omega), ext_ge hge (by omega), kap_even hz0, mu_even hz0]
    rcases (by omega : d (j - 1) = 0 ∨ d (j - 1) = 1) with e0 | e1
    · rw [e0, show (2 * (2 * j - 1 - 0) - 1 - (2 * n + 1)) / 2 = 2 * j - n - 2 by omega]
      have hw := hd.le_one (2 * j - n - 2)
      rcases (by omega : d (2 * j - n - 2) = 0 ∨ d (2 * j - n - 2) = 1) with w0 | w1
      · rw [w0, show min n (2 * j - n - 2 - 0) = 2 * j - n - 2 by omega,
          show min (n + 1) (2 * j - n - 2 + 0) = 2 * j - n - 2 by omega,
          show n + 1 + (2 * j - n - 2) = 2 * j - 1 by omega]
        omega
      · have hm1 : 1 ≤ 2 * j - n - 2 := by
          by_contra hc; rw [show 2 * j - n - 2 = 0 by omega, hd.zero] at w1; omega
        have e := succ (2 * j - 1)
        rw [show 2 * j - 1 + 1 = 2 * j by omega,
          show (2 * j - 1) % (n + 1) = 2 * j - n - 2 by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega,
          show 2 * j - n - 2 + 1 = 2 * j - n - 1 by omega,
          ite_eq_left (hW' e0 (by omega) w1)] at e
        rw [w1, show min n (2 * j - n - 2 - 1) = 2 * j - n - 3 by omega,
          show min (n + 1) (2 * j - n - 2 + 1) = 2 * j - n - 1 by omega,
          show n + 1 + (2 * j - n - 1) = 2 * j by omega, e]
        omega
    · have hj2 : 2 ≤ j := by
        by_contra hc; rw [show j - 1 = 0 by omega, hd.zero] at e1; omega
      rw [e1, show (2 * (2 * j - 1 - 1) - 1 - (2 * n + 1)) / 2 = 2 * j - n - 3 by omega]
      have hw := hd.le_one (2 * j - n - 3)
      have e := succ (2 * j - 2)
      rw [show 2 * j - 2 + 1 = 2 * j - 1 by omega] at e
      have hp : (2 * (j - 1)) % (n + 1) + 1 ∈ U := hS' e1
      rw [show 2 * (j - 1) = 2 * j - 2 by omega] at hp
      rw [ite_eq_left hp] at e
      rcases (by omega : d (2 * j - n - 3) = 0 ∨ d (2 * j - n - 3) = 1) with w0 | w1
      · rw [w0, show min n (2 * j - n - 3 - 0) = 2 * j - n - 3 by omega,
          show min (n + 1) (2 * j - n - 3 + 0) = 2 * j - n - 3 by omega,
          show n + 1 + (2 * j - n - 3) = 2 * j - 2 by omega]
        omega
      · have hm1 : 1 ≤ 2 * j - n - 3 := by
          by_contra hc; rw [show 2 * j - n - 3 = 0 by omega, hd.zero] at w1; omega
        rw [w1, show min n (2 * j - n - 3 - 1) = 2 * j - n - 4 by omega,
          show min (n + 1) (2 * j - n - 3 + 1) = 2 * j - n - 2 by omega,
          show n + 1 + (2 * j - n - 2) = 2 * j - 1 by omega]
        omega

/-- **Odd slip lemma** (`N = 2n + 1`).  For `k ∈ D` the slip exchanges `2k` and `2k + 1`
between the evens (first block, order `τ ∈ V_n`) and the odds (second block, order
`σ ∈ V_{n+1}`).  Sufficient conditions: `τ` places `k` before `2k mod* n`; `σ` places
`(2k+1) mod* (n+1)` before `k + 1`; and the wrap condition at the doubling preimage:
`τ` places `j = (k+n+1)/2` before `k` (`k ≢ n mod 2`), resp. `σ` places `k + 1` before
`j = (k+n+2)/2` (`k ≡ n mod 2`). -/
theorem oddSlip_mem_semiSeqs (hn : 1 ≤ n) (hd : OAdm d) {τ σ : List Nat}
    (hτ : τ ∈ semiSeqs n) (hσ : σ ∈ semiSeqs (n + 1))
    (hF : ∀ k (hk : k < τ.length), d τ[k] = 1 → qq n τ[k] ∉ τ.take k)
    (hW : ∀ k (hk : k < τ.length), d τ[k] = 0 → n + 1 ≤ 2 * τ[k] →
      d (2 * τ[k] - n - 1) = 1 → 2 * τ[k] - n - 1 ∉ τ.take k)
    (hS : ∀ k (hk : k < σ.length), d (σ[k] - 1) = 1 → pp (n + 1) (σ[k] - 1) ∈ σ.take k)
    (hW' : ∀ k (hk : k < σ.length), d (σ[k] - 1) = 0 → n + 2 ≤ 2 * σ[k] →
      d (2 * σ[k] - n - 2) = 1 → 2 * σ[k] - n - 1 ∈ σ.take k) :
    τ.map (slipF d) ++ σ.map (slipS d) ∈ semiSeqs (2 * n + 1) :=
  (blocks_mem_semiSeqs_iff (split hd) (mem_semiSeqs.1 hτ).1 (mem_semiSeqs.1 hσ).1).2
    ⟨firstCond_odd hd hτ hF hW, secondCond_odd hn hd hσ hS hW'⟩

end Lemma

/-! ## Counting form -/

theorem slipF_inj {d : Nat → Nat} (hd : ∀ i, d i ≤ 1) : Function.Injective (slipF d) :=
  fun x y e => by
    have := hd x; have := hd y; unfold slipF at e; omega

theorem slipS_inj {d : Nat → Nat} (hd : OAdm d) : Function.Injective (slipS d) := fun x y e => by
  have h0 := hd.zero
  have hx := hd.le_one (x - 1); have hy := hd.le_one (y - 1)
  unfold slipS at e
  rcases Nat.lt_or_ge x 2 with h1 | h1 <;> rcases Nat.lt_or_ge y 2 with h2 | h2
  · rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;>
      rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> simp_all
  · rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl
    · omega
    · rw [show 1 - 1 = 0 by rfl, h0] at e; omega
  · rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl
    · omega
    · rw [show 1 - 1 = 0 by rfl, h0] at e; omega
  · omega

theorem oadm_ind {n : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 n) : OAdm (ind D) where
  le_one i := by unfold ind; split <;> omega
  zero := by
    unfold ind; rw [ite_eq_right_iff.2]; intro h; have := Finset.mem_Icc.1 (hD h); omega

open Classical in
/-- First-block sequences of the odd slip lemma for the slip set `D`. -/
noncomputable def condFo (n : Nat) (D : Finset Nat) : Finset (List Nat) :=
  (semiSeqs n).filter fun τ =>
    (∀ k (hk : k < τ.length), ind D τ[k] = 1 → qq n τ[k] ∉ τ.take k) ∧
    (∀ k (hk : k < τ.length), ind D τ[k] = 0 → n + 1 ≤ 2 * τ[k] →
      ind D (2 * τ[k] - n - 1) = 1 → 2 * τ[k] - n - 1 ∉ τ.take k)

open Classical in
/-- Second-block sequences of the odd slip lemma for the slip set `D`. -/
noncomputable def condSo (n : Nat) (D : Finset Nat) : Finset (List Nat) :=
  (semiSeqs (n + 1)).filter fun σ =>
    (∀ k (hk : k < σ.length), ind D (σ[k] - 1) = 1 → pp (n + 1) (σ[k] - 1) ∈ σ.take k) ∧
    (∀ k (hk : k < σ.length), ind D (σ[k] - 1) = 0 → n + 2 ≤ 2 * σ[k] →
      ind D (2 * σ[k] - n - 2) = 1 → 2 * σ[k] - n - 1 ∈ σ.take k)

/-- The odd slip sum `∑_{D ⊆ [1, n]} #condFo(n, D) · #condSo(n, D)`. -/
noncomputable def oddSum (n : Nat) : Nat :=
  ∑ D ∈ (Finset.Icc 1 n).powerset, (condFo n D).card * (condSo n D).card

/-- **Odd slip lemma, counting form**: `oddSum n ≤ a(2n + 1)`. -/
theorem oddSum_le {n : Nat} (hn : 1 ≤ n) : oddSum n ≤ semiCount (2 * n + 1) := by
  have hsub : ((Finset.Icc 1 n).powerset.sigma fun D => condFo n D ×ˢ condSo n D).image
      slipMap ⊆ semiSeqs (2 * n + 1) := by
    intro x hx
    obtain ⟨⟨D, τ, σ⟩, hy, rfl⟩ := Finset.mem_image.1 hx
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.mem_product, condFo, condSo,
      Finset.mem_filter] at hy
    obtain ⟨hD, ⟨hτ, hq, hw⟩, ⟨hσ, hp, hw'⟩⟩ := hy
    exact oddSlip_mem_semiSeqs hn (oadm_ind hD) hτ hσ hq hw hp hw'
  have hinj : Set.InjOn slipMap
      (((Finset.Icc 1 n).powerset.sigma fun D => condFo n D ×ˢ condSo n D :
        Finset ((_ : Finset Nat) × (List Nat × List Nat))) : Set _) := by
    rintro ⟨D, τ, σ⟩ hx ⟨D', τ', σ'⟩ hx' e
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_powerset,
      Finset.mem_product, condFo, condSo, Finset.mem_filter, mem_semiSeqs] at hx hx'
    obtain ⟨hD, ⟨⟨hτ, -⟩, -⟩, ⟨⟨hσ, -⟩, -⟩⟩ := hx
    obtain ⟨hD', ⟨⟨hτ', -⟩, -⟩, ⟨⟨hσ', -⟩, -⟩⟩ := hx'
    have hA := oadm_ind hD; have hA' := oadm_ind hD'
    unfold slipMap at e; simp only at e
    have l1 : (τ.map (slipF (ind D))).length = (τ'.map (slipF (ind D'))).length := by
      simp [hτ.length_eq, hτ'.length_eq]
    obtain ⟨e1, e2⟩ := List.append_inj e l1
    have key : ∀ (E : Finset Nat) (ρ : List Nat), E ⊆ Finset.Icc 1 n → IsFoldSeq n ρ →
        ∀ i, i ∈ E ↔ (1 ≤ i ∧ i ≤ n ∧ 2 * i + 1 ∈ ρ.map (slipF (ind E))) := by
      intro E ρ hE hρ i
      constructor
      · intro hi
        have := Finset.mem_Icc.1 (hE hi)
        refine ⟨this.1, this.2, List.mem_map.2 ⟨i, (mem_range'_of_perm hρ).2 (by omega), ?_⟩⟩
        unfold slipF ind; rw [ite_eq_left_iff.2 (fun h => absurd hi h)]
      · rintro ⟨-, -, h⟩
        obtain ⟨x, -, hx⟩ := List.mem_map.1 h
        unfold slipF ind at hx
        split at hx
        · have : x = i := by omega
          subst this; assumption
        · omega
    have hDD : D = D' := by
      ext i; rw [key D τ hD hτ i, key D' τ' hD' hτ' i, e1]
    subst hDD
    have hττ : τ = τ' := (List.map_injective_iff.2 (slipF_inj hA.le_one)) e1
    have hσσ : σ = σ' := (List.map_injective_iff.2 (slipS_inj hA)) e2
    subst hττ; subst hσσ; rfl
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_sigma] at this
  simpa [Finset.card_product, semiCount, oddSum] using this

/-- Doubled slip sets `2U`, `U ⊆ I` with `I ⊆ [1, n/2]`: any families inside `condFo`,
`condSo` give a lower bound for `a(2n + 1)`. -/
theorem family_le {n : Nat} (hn : 1 ≤ n) (I : Finset Nat) (hI : ∀ i ∈ I, 1 ≤ i ∧ 2 * i ≤ n)
    (F S : Finset Nat → Finset (List Nat))
    (hF : ∀ U ⊆ I, F U ⊆ condFo n (U.image (2 * ·)))
    (hS : ∀ U ⊆ I, S U ⊆ condSo n (U.image (2 * ·))) :
    ∑ U ∈ I.powerset, (F U).card * (S U).card ≤ semiCount (2 * n + 1) := by
  have hinj : Function.Injective (fun U : Finset Nat => U.image (2 * ·)) :=
    Finset.image_injective (fun x y e => by omega)
  calc ∑ U ∈ I.powerset, (F U).card * (S U).card
      ≤ ∑ U ∈ I.powerset, (condFo n (U.image (2 * ·))).card *
          (condSo n (U.image (2 * ·))).card := by
        refine Finset.sum_le_sum fun U hU => ?_
        rw [Finset.mem_powerset] at hU
        exact Nat.mul_le_mul (Finset.card_le_card (hF U hU)) (Finset.card_le_card (hS U hU))
    _ = ∑ D ∈ I.powerset.image (fun U : Finset Nat => U.image (2 * ·)),
          (condFo n D).card * (condSo n D).card := by
        rw [Finset.sum_image (fun x _ y _ e => hinj e)]
    _ ≤ oddSum n := by
        unfold oddSum
        refine Finset.sum_le_sum_of_subset fun D hD => ?_
        obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hD
        rw [Finset.mem_powerset] at hU ⊢
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
        have := hI i (hU hi)
        rw [Finset.mem_Icc]; omega
    _ ≤ semiCount (2 * n + 1) := oddSum_le hn

/-! ## The odd node: one child in parity-block form, averaging on the other -/

/-- Slip indices `i = 2t + c`, `t < ⌊p/4⌋` (so `2i ≤ p`, `i ≡ c mod 2`). -/
def ivals (c p : Nat) : Finset Nat := (Finset.range (p / 4)).image fun t => 2 * t + c

theorem card_ivals (c p : Nat) : (ivals c p).card = p / 4 := by
  unfold ivals
  rw [Finset.card_image_of_injective _ (fun x y e => by
    have : 2 * x + c = 2 * y + c := e
    omega), Finset.card_range]

theorem mem_ivals {c p i : Nat} (hi : i ∈ ivals c p) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) :
    1 ≤ i ∧ 2 * i ≤ p ∧ i % 2 = c % 2 := by
  unfold ivals at hi
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hi
  rw [Finset.mem_range] at ht
  omega

theorem mem_dblU {U : Finset Nat} {x : Nat} : x ∈ U.image (2 * ·) ↔ ∃ i ∈ U, 2 * i = x := by
  simp

theorem ind_dbl {U : Finset Nat} {x : Nat} (h : ind (U.image (2 * ·)) x = 1) :
    ∃ i ∈ U, 2 * i = x := by
  unfold ind at h; split at h
  · exact mem_dblU.1 (by assumption)
  · omega

/-- `¬ NotBefore l a b` gives `b` before the position of `a`. -/
theorem mem_take_of_not_notBefore {l : List Nat} (hnd : l.Nodup) {a b k : Nat}
    (hk : k < l.length) (hka : l[k] = a) (h : ¬ NotBefore l a b) : b ∈ l.take k := by
  by_contra hn
  apply h
  intro k2 hk2 e2 hm2
  have : k2 = k := (List.Nodup.getElem_inj_iff hnd).1 (e2.trans hka.symm)
  subst this
  exact hn hm2

section CaseA
/-! `n = 2p + 1`: the first block (size `n`, odd) is `PB(α, β)`; slips at `k = 2i`,
`i ≡ p (mod 2)`; conditions `β : i before 2i`, `σ : 4i+1 before 2i+1`; the wrap panel
`i + p + 1` is odd, hence free. -/

theorem famA_F {p : Nat} {U : Finset Nat} (hU : U ⊆ ivals (2 - p % 2) p) {α β : List Nat}
    (hα : α ∈ semiSeqs (p + 1)) (hβ : β ∈ semiSeqs p) (hβU : ∀ i ∈ U, NotBefore β i (2 * i)) :
    blockMap 1 (α, β) ∈ condFo (2 * p + 1) (U.image (2 * ·)) := by
  have hαf := (mem_semiSeqs.1 hα).1
  have hβf := (mem_semiSeqs.1 hβ).1
  have hUi : ∀ i ∈ U, 1 ≤ i ∧ 2 * i ≤ p ∧ i % 2 = p % 2 := fun i hi => by
    have := mem_ivals (hU hi) (by omega) (by omega); omega
  unfold condFo
  rw [Finset.mem_filter]
  refine ⟨blockMap_mem_gen (x := 2 * p + 1) (by rwa [show (2 * p + 1 + 1) / 2 = p + 1 by omega])
    (by rwa [show (2 * p + 1) / 2 = p by omega]), ?_, ?_⟩
  · rw [blockMap_eq]
    intro k hk hd
    obtain ⟨i, hiU, hix⟩ := ind_dbl hd
    have hb := hUi i hiU
    rcases Nat.lt_or_ge k α.length with hkA | hkA
    · have hkA' : k < (α.map (scale 1)).length := by simpa using hkA
      have hi1 : 1 ≤ α[k] := ((mem_range'_of_perm hαf).1 (List.getElem_mem _)).1
      have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * α[k] - 1 := by
        rw [List.getElem_append_left hkA']; simp [scale]
      rw [e] at hix
      omega
    · have hkA' : (α.map (scale 1)).length ≤ k := by simpa using hkA
      have hβl : k - α.length < β.length := by simp at hk; omega
      have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * β[k - α.length] := by
        rw [List.getElem_append_right hkA']; simp [scale]
      rw [e] at hix ⊢
      have hβi : β[k - α.length] = i := by omega
      rw [hβi, qq_small (by omega) (by omega)]
      intro hmem
      rw [List.take_append, List.take_of_length_le hkA'] at hmem
      rcases List.mem_append.1 hmem with hm | hm
      · have := mem_map_scale_one_odd hαf hm; omega
      · rw [List.length_map, ← List.map_take] at hm
        obtain ⟨z, hz, hz2⟩ := List.mem_map.1 hm
        unfold scale at hz2
        have hz' : z = 2 * i := by omega
        exact hβU i hiU (k - α.length) hβl hβi (hz' ▸ hz)
  · rw [blockMap_eq]
    intro k hk _ hle hd
    obtain ⟨i, hiU, hix⟩ := ind_dbl hd
    have hb := hUi i hiU
    rcases Nat.lt_or_ge k α.length with hkA | hkA
    · have hkA' : k < (α.map (scale 1)).length := by simpa using hkA
      intro hmem
      rw [List.take_append_of_le_length hkA'.le] at hmem
      have := mem_map_scale_one_odd hαf (List.mem_of_mem_take hmem)
      omega
    · have hkA' : (α.map (scale 1)).length ≤ k := by simpa using hkA
      have hβl : k - α.length < β.length := by simp at hk; omega
      have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * β[k - α.length] := by
        rw [List.getElem_append_right hkA']; simp [scale]
      rw [e] at hix hle
      omega

theorem famA_S {p : Nat} {U : Finset Nat} (hU : U ⊆ ivals (2 - p % 2) p) {σ : List Nat}
    (hσ : σ ∈ semiSeqs (2 * p + 1 + 1))
    (hσU : ∀ i ∈ U, ¬ NotBefore σ (2 * i + 1) (4 * i + 1)) :
    σ ∈ condSo (2 * p + 1) (U.image (2 * ·)) := by
  have hσf := (mem_semiSeqs.1 hσ).1
  have hnd := nodup_of_foldSeq hσf
  have hUi : ∀ i ∈ U, 1 ≤ i ∧ 2 * i ≤ p ∧ i % 2 = p % 2 := fun i hi => by
    have := mem_ivals (hU hi) (by omega) (by omega); omega
  unfold condSo
  rw [Finset.mem_filter]
  refine ⟨hσ, ?_, ?_⟩
  · intro k hk hd
    obtain ⟨i, hiU, hix⟩ := ind_dbl hd
    have hb := hUi i hiU
    have h1 : 1 ≤ σ[k] := ((mem_range'_of_perm hσf).1 (List.getElem_mem hk)).1
    rw [← hix, pp_small (y := 2 * p + 1 + 1) (k := 2 * i) (by omega)]
    exact mem_take_of_not_notBefore (a := 2 * i + 1) hnd hk (by omega)
      (by rw [show 2 * (2 * i) + 1 = 4 * i + 1 by ring]; exact hσU i hiU)
  · intro k hk _ hle hd
    obtain ⟨i, hiU, hix⟩ := ind_dbl hd
    omega

/-- **Odd node, `n = 2p + 1`**:
`a(p+1) · a(p) · a(2p+2) · 2^{⌈⌊p/4⌋/4⌉} ≤ 4 · a(4p + 3)`. -/
theorem oddNodeA (p : Nat) :
    semiCount (p + 1) * (semiCount p * semiCount (2 * p + 2) * 2 ^ ((p / 4 + 3) / 4)) ≤
      4 * semiCount (2 * (2 * p + 1) + 1) := by
  classical
  set c := 2 - p % 2 with hc
  set I := ivals c p with hI
  have hIb : ∀ i ∈ I, 1 ≤ i ∧ 2 * i ≤ p := fun i hi => by
    have := mem_ivals hi (by omega) (by omega); omega
  have avg := avg4 (semiSeqs p) (semiSeqs (2 * p + 1 + 1)) I
    (fun β i => NotBefore β i (2 * i)) (fun σ i => ¬ NotBefore σ (2 * i + 1) (4 * i + 1))
    List.reverse List.reverse
    (fun x hx => reverse_mem_semiSeqs hx) (fun x _ => List.reverse_reverse x)
    (fun x hx => reverse_mem_semiSeqs hx) (fun x _ => List.reverse_reverse x) ?_ ?_
  rotate_left
  · intro x hx i hi
    have hb := hIb i hi
    have hf := (mem_semiSeqs.1 hx).1
    exact notBefore_reverse (nodup_of_foldSeq hf) ((mem_range'_of_perm hf).2 (by omega))
      ((mem_range'_of_perm hf).2 (by omega)) (by omega)
  · intro x hx i hi
    have hb := hIb i hi
    have hf := (mem_semiSeqs.1 hx).1
    rw [notBefore_reverse (nodup_of_foldSeq hf) ((mem_range'_of_perm hf).2 (by omega))
      ((mem_range'_of_perm hf).2 (by omega)) (by omega)]
  rw [hI, card_ivals] at avg
  have fam := family_le (n := 2 * p + 1) (by omega) I (fun i hi => by
      have := hIb i hi; omega)
    (fun U => (semiSeqs (p + 1) ×ˢ (semiSeqs p).filter fun β => ∀ i ∈ U, NotBefore β i (2 * i)).image
      (blockMap 1))
    (fun U => (semiSeqs (2 * p + 1 + 1)).filter fun σ =>
      ∀ i ∈ U, ¬ NotBefore σ (2 * i + 1) (4 * i + 1))
    (fun U hU z hz => by
      obtain ⟨⟨α, β⟩, hab, rfl⟩ := Finset.mem_image.1 hz
      rw [Finset.mem_product, Finset.mem_filter] at hab
      exact famA_F hU hab.1 hab.2.1 hab.2.2)
    (fun U hU σ hσ => by
      rw [Finset.mem_filter] at hσ
      exact famA_S hU hσ.1 hσ.2)
  have hcard : ∀ U : Finset Nat, ((semiSeqs (p + 1) ×ˢ (semiSeqs p).filter fun β =>
      ∀ i ∈ U, NotBefore β i (2 * i)).image (blockMap 1)).card =
      semiCount (p + 1) * ((semiSeqs p).filter fun β => ∀ i ∈ U, NotBefore β i (2 * i)).card := by
    intro U
    rw [card_image_blockMap_gen (x := 2 * p + 1)
      (by rw [show (2 * p + 1 + 1) / 2 = p + 1 by omega])
      (by rw [show (2 * p + 1) / 2 = p by omega]; exact Finset.filter_subset _ _)]
    rfl
  simp only [hcard] at fam
  calc semiCount (p + 1) * (semiCount p * semiCount (2 * p + 2) * 2 ^ ((p / 4 + 3) / 4))
      ≤ semiCount (p + 1) * (4 * ∑ U ∈ I.powerset,
          ((semiSeqs p).filter fun β => ∀ i ∈ U, NotBefore β i (2 * i)).card *
          ((semiSeqs (2 * p + 1 + 1)).filter fun σ =>
            ∀ i ∈ U, ¬ NotBefore σ (2 * i + 1) (4 * i + 1)).card) := by
        apply Nat.mul_le_mul_left
        unfold semiCount
        exact avg
    _ = 4 * ∑ U ∈ I.powerset, semiCount (p + 1) *
          ((semiSeqs p).filter fun β => ∀ i ∈ U, NotBefore β i (2 * i)).card *
          ((semiSeqs (2 * p + 1 + 1)).filter fun σ =>
            ∀ i ∈ U, ¬ NotBefore σ (2 * i + 1) (4 * i + 1)).card := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun U _ => by ring
    _ ≤ 4 * semiCount (2 * (2 * p + 1) + 1) := Nat.mul_le_mul_left _ fam

end CaseA

section CaseB
/-! `n = 2p`: the second block (size `n + 1`, odd) is `PB(α, β)`; slips at `k = 2i`,
`i ≢ p (mod 2)`; conditions `τ : 2i before 4i`, `α : 2i+1 before i+1`; the wrap panel
`i + p + 1` is even, hence comes after the whole odd block. -/

theorem famB_F {p : Nat} {U : Finset Nat} (hU : U ⊆ ivals (1 + p % 2) p) {τ : List Nat}
    (hτ : τ ∈ semiSeqs (2 * p)) (hτU : ∀ i ∈ U, NotBefore τ (2 * i) (4 * i)) :
    τ ∈ condFo (2 * p) (U.image (2 * ·)) := by
  have hUi : ∀ i ∈ U, 1 ≤ i ∧ 2 * i ≤ p ∧ i % 2 = (1 + p % 2) % 2 := fun i hi =>
    mem_ivals (hU hi) (by omega) (by omega)
  unfold condFo
  rw [Finset.mem_filter]
  refine ⟨hτ, ?_, ?_⟩
  · intro k hk hd
    obtain ⟨i, hiU, hix⟩ := ind_dbl hd
    have hb := hUi i hiU
    rw [← hix, qq_small (x := 2 * p) (k := 2 * i) (by omega) (by omega),
      show 2 * (2 * i) = 4 * i by ring]
    exact hτU i hiU k hk hix.symm
  · intro k hk _ hle hd
    obtain ⟨i, hiU, hix⟩ := ind_dbl hd
    omega

theorem famB_S {p : Nat} {U : Finset Nat} (hU : U ⊆ ivals (1 + p % 2) p) {α β : List Nat}
    (hα : α ∈ semiSeqs (p + 1)) (hαU : ∀ i ∈ U, ¬ NotBefore α (i + 1) (2 * i + 1))
    (hβ : β ∈ semiSeqs p) :
    blockMap 1 (α, β) ∈ condSo (2 * p) (U.image (2 * ·)) := by
  have hαf := (mem_semiSeqs.1 hα).1
  have hβf := (mem_semiSeqs.1 hβ).1
  have hnd := nodup_of_foldSeq hαf
  have hUi : ∀ i ∈ U, 1 ≤ i ∧ 2 * i ≤ p ∧ i % 2 = (1 + p % 2) % 2 := fun i hi =>
    mem_ivals (hU hi) (by omega) (by omega)
  unfold condSo
  rw [Finset.mem_filter]
  refine ⟨blockMap_mem_gen (x := 2 * p + 1) (by rwa [show (2 * p + 1 + 1) / 2 = p + 1 by omega])
    (by rwa [show (2 * p + 1) / 2 = p by omega]), ?_, ?_⟩
  · rw [blockMap_eq]
    intro k hk hd
    obtain ⟨i, hiU, hix⟩ := ind_dbl hd
    have hb := hUi i hiU
    rcases Nat.lt_or_ge k α.length with hkA | hkA
    · have hkA' : k < (α.map (scale 1)).length := by simpa using hkA
      have hi1 : 1 ≤ α[k] := ((mem_range'_of_perm hαf).1 (List.getElem_mem _)).1
      have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * α[k] - 1 := by
        rw [List.getElem_append_left hkA']; simp [scale]
      rw [e] at hix ⊢
      have hαi : α[k] = i + 1 := by omega
      rw [← hix, pp_small (y := 2 * p + 1) (k := 2 * i) (by omega),
        List.take_append_of_le_length hkA'.le, ← List.map_take]
      have hm := mem_take_of_not_notBefore hnd hkA hαi (hαU i hiU)
      exact List.mem_map.2 ⟨_, hm, by unfold scale; omega⟩
    · have hkA' : (α.map (scale 1)).length ≤ k := by simpa using hkA
      have hβl : k - α.length < β.length := by simp at hk; omega
      have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * β[k - α.length] := by
        rw [List.getElem_append_right hkA']; simp [scale]
      rw [e] at hix
      omega
  · rw [blockMap_eq]
    intro k hk _ hle hd
    obtain ⟨i, hiU, hix⟩ := ind_dbl hd
    have hb := hUi i hiU
    rcases Nat.lt_or_ge k α.length with hkA | hkA
    · have hkA' : k < (α.map (scale 1)).length := by simpa using hkA
      have hi1 : 1 ≤ α[k] := ((mem_range'_of_perm hαf).1 (List.getElem_mem _)).1
      have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * α[k] - 1 := by
        rw [List.getElem_append_left hkA']; simp [scale]
      rw [e] at hix hle
      omega
    · have hkA' : (α.map (scale 1)).length ≤ k := by simpa using hkA
      have hβl : k - α.length < β.length := by simp at hk; omega
      have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * β[k - α.length] := by
        rw [List.getElem_append_right hkA']; simp [scale]
      rw [e] at hix hle ⊢
      rw [List.take_append, List.take_of_length_le hkA']
      refine List.mem_append_left _ (List.mem_map.2 ⟨i + 1,
        (mem_range'_of_perm hαf).2 ⟨by omega, by omega⟩, ?_⟩)
      unfold scale; omega

/-- **Odd node, `n = 2p`**:
`a(2p) · a(p+1) · a(p) · 2^{⌈⌊p/4⌋/4⌉} ≤ 4 · a(4p + 1)`. -/
theorem oddNodeB (p : Nat) (hp : 1 ≤ p) :
    semiCount p * (semiCount (2 * p) * semiCount (p + 1) * 2 ^ ((p / 4 + 3) / 4)) ≤
      4 * semiCount (2 * (2 * p) + 1) := by
  classical
  set c := 1 + p % 2 with hc
  set I := ivals c p with hI
  have hIb : ∀ i ∈ I, 1 ≤ i ∧ 2 * i ≤ p := fun i hi => by
    have := mem_ivals hi (by omega) (by omega); omega
  have avg := avg4 (semiSeqs (2 * p)) (semiSeqs (p + 1)) I
    (fun τ i => NotBefore τ (2 * i) (4 * i)) (fun α i => ¬ NotBefore α (i + 1) (2 * i + 1))
    List.reverse List.reverse
    (fun x hx => reverse_mem_semiSeqs hx) (fun x _ => List.reverse_reverse x)
    (fun x hx => reverse_mem_semiSeqs hx) (fun x _ => List.reverse_reverse x) ?_ ?_
  rotate_left
  · intro x hx i hi
    have hb := hIb i hi
    have hf := (mem_semiSeqs.1 hx).1
    exact notBefore_reverse (nodup_of_foldSeq hf) ((mem_range'_of_perm hf).2 (by omega))
      ((mem_range'_of_perm hf).2 (by omega)) (by omega)
  · intro x hx i hi
    have hb := hIb i hi
    have hf := (mem_semiSeqs.1 hx).1
    rw [notBefore_reverse (nodup_of_foldSeq hf) ((mem_range'_of_perm hf).2 (by omega))
      ((mem_range'_of_perm hf).2 (by omega)) (by omega)]
  rw [hI, card_ivals] at avg
  have fam := family_le (n := 2 * p) (by omega) I (fun i hi => by
      have := hIb i hi; omega)
    (fun U => (semiSeqs (2 * p)).filter fun τ => ∀ i ∈ U, NotBefore τ (2 * i) (4 * i))
    (fun U => (((semiSeqs (p + 1)).filter fun α => ∀ i ∈ U, ¬ NotBefore α (i + 1) (2 * i + 1)) ×ˢ
      semiSeqs p).image (blockMap 1))
    (fun U hU τ hτ => by
      rw [Finset.mem_filter] at hτ
      exact famB_F hU hτ.1 hτ.2)
    (fun U hU z hz => by
      obtain ⟨⟨α, β⟩, hab, rfl⟩ := Finset.mem_image.1 hz
      rw [Finset.mem_product, Finset.mem_filter] at hab
      exact famB_S hU hab.1.1 hab.1.2 hab.2)
  have hcard : ∀ U : Finset Nat, ((((semiSeqs (p + 1)).filter fun α =>
      ∀ i ∈ U, ¬ NotBefore α (i + 1) (2 * i + 1)) ×ˢ semiSeqs p).image (blockMap 1)).card =
      ((semiSeqs (p + 1)).filter fun α => ∀ i ∈ U, ¬ NotBefore α (i + 1) (2 * i + 1)).card *
        semiCount p := by
    intro U
    rw [card_image_blockMap_gen (x := 2 * p + 1)
      (by rw [show (2 * p + 1 + 1) / 2 = p + 1 by omega]; exact Finset.filter_subset _ _)
      (by rw [show (2 * p + 1) / 2 = p by omega])]
    rfl
  simp only [hcard] at fam
  calc semiCount p * (semiCount (2 * p) * semiCount (p + 1) * 2 ^ ((p / 4 + 3) / 4))
      ≤ semiCount p * (4 * ∑ U ∈ I.powerset,
          ((semiSeqs (2 * p)).filter fun τ => ∀ i ∈ U, NotBefore τ (2 * i) (4 * i)).card *
          ((semiSeqs (p + 1)).filter fun α =>
            ∀ i ∈ U, ¬ NotBefore α (i + 1) (2 * i + 1)).card) := by
        apply Nat.mul_le_mul_left
        unfold semiCount
        exact avg
    _ = 4 * ∑ U ∈ I.powerset,
          ((semiSeqs (2 * p)).filter fun τ => ∀ i ∈ U, NotBefore τ (2 * i) (4 * i)).card *
          (((semiSeqs (p + 1)).filter fun α =>
            ∀ i ∈ U, ¬ NotBefore α (i + 1) (2 * i + 1)).card * semiCount p) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun U _ => by ring
    _ ≤ 4 * semiCount (2 * (2 * p) + 1) := Nat.mul_le_mul_left _ fam

end CaseB

/-! ## All `N`: `N^N ≤ 2^{12N} a(N)^{16}` -/

section AllN16

theorem small_slipSum16 {n : Nat} (hn : n ≤ 512) :
    (2 * n) ^ (2 * n) * 2 ^ (7 * n / 2) ≤ 2 ^ (24 * n) * slipSum n ^ 16 := by
  have e1 : (2 * n) ^ (2 * n) * 2 ^ (4 * n) = (8 * n) ^ (2 * n) := by
    rw [show 8 * n = 2 * n * 4 by ring, Nat.mul_pow (2 * n) 4, Nat.pow_mul 4 2 n,
      show (4 : Nat) ^ 2 = 2 ^ 4 by norm_num, ← Nat.pow_mul, Nat.mul_comm 4 n]
  have e2 : (2 : Nat) ^ (24 * n) = 4096 ^ (2 * n) := by
    rw [show (4096 : Nat) = 2 ^ 12 by norm_num, ← Nat.pow_mul]; ring_nf
  calc (2 * n) ^ (2 * n) * 2 ^ (7 * n / 2) ≤ (2 * n) ^ (2 * n) * 2 ^ (4 * n) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = (8 * n) ^ (2 * n) := e1
    _ ≤ 4096 ^ (2 * n) := Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ (24 * n) := e2.symm
    _ ≤ 2 ^ (24 * n) * slipSum n ^ 16 :=
        Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (slipSum_pos n))

theorem arith16_iv {N y r : Nat} (hy : y = N ∨ y = N + 1) (h3 : N ≤ 2 * r + 2) (hr : 13 ≤ r) :
    N + y + 2 + 7 * r + 12 * ((N + 1) / 2 + N / 2 + (y + 1) / 2 + y / 2) ≤
      16 * ((r + 1) / 2) + 7 * (r / 2) + 12 * (N + y) := by
  rw [show (N + 1) / 2 + N / 2 + (y + 1) / 2 + y / 2 = N + y by omega]
  have e3 : (r + 1) / 2 + r / 2 = r := by omega
  have e4 : r ≤ 2 * ((r + 1) / 2) := by omega
  generalize (r + 1) / 2 = t at e3 e4 ⊢
  generalize r / 2 = r' at e3 e4 ⊢
  subst e3
  have : y ≤ N + 1 := by omega
  omega

theorem arith16_iii {m : Nat} (hm : 256 ≤ m) :
    4 * (2 * m + 1) + 34 + 7 * (2 * m + 1) / 2 ≤
      7 * m / 4 + 7 * (m / 2) + 16 * ((m + 1) / 2 + (m / 2 + 3) / 4) := by
  omega

theorem arith16_oddA {p : Nat} (hp : 1000 ≤ p) :
    6 * p + 38 ≤ 7 * (2 * p + 2) / 4 + 7 * p / 4 + 16 * ((p / 4 + 3) / 4) := by
  omega

theorem arith16_oddB {p : Nat} (hp : 1000 ≤ p) :
    6 * p + 36 ≤ 7 * (2 * p) / 4 + 7 * p / 4 + 16 * ((p / 4 + 3) / 4) := by
  omega

/-- The induction behind `self_pow_le_semiCount_pow_16`: for `N ≥ 1`,
(i) `N^N ≤ 2^{12N} a(N)^16`, (ii) the same with a surplus `2^{⌊7N/4⌋}` for even `N`,
(iii) `(2N)^{2N} 2^{⌊7N/2⌋} ≤ 2^{24N} B(N)^16`,
(iv) `N^N y^y 2^{7r} ≤ 2^{12(N+y)} M(N,y,r)^16` for `y ∈ {N, N+1}`, `2r ≤ N`, `2r+1 ≤ y`,
`N ≤ 2r + 2`. -/
theorem alln16_aux : ∀ N, 1 ≤ N →
    N ^ N ≤ 2 ^ (12 * N) * semiCount N ^ 16 ∧
      (N % 2 = 0 → N ^ N * 2 ^ (7 * N / 4) ≤ 2 ^ (12 * N) * semiCount N ^ 16) ∧
      (2 * N) ^ (2 * N) * 2 ^ (7 * N / 2) ≤ 2 ^ (24 * N) * slipSum N ^ 16 ∧
      (∀ y r, (y = N ∨ y = N + 1) → 2 * r ≤ N → 2 * r + 1 ≤ y → N ≤ 2 * r + 2 →
        N ^ N * y ^ y * 2 ^ (7 * r) ≤ 2 ^ (12 * (N + y)) * mSum N y r ^ 16) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN
  have hpow : ∀ k, 0 < 2 ^ k := fun k => Nat.two_pow_pos k
  -- the two children of an odd node, one of them even (with its surplus)
  have Pair : ∀ n, 1 ≤ n → n + 1 < N →
      n ^ n * (n + 1) ^ (n + 1) * 2 ^ (7 * n / 4) ≤
        2 ^ (12 * (2 * n + 1)) * (semiCount n * semiCount (n + 1)) ^ 16 := by
    intro n hn1 hnN
    rcases Nat.even_or_odd n with ⟨s, hs⟩ | ⟨s, hs⟩
    · have E := (ih n (by omega) hn1).2.1 (by omega)
      have Q1 := (ih (n + 1) (by omega) (by omega)).1
      calc n ^ n * (n + 1) ^ (n + 1) * 2 ^ (7 * n / 4) =
            (n ^ n * 2 ^ (7 * n / 4)) * (n + 1) ^ (n + 1) := by ring
        _ ≤ (2 ^ (12 * n) * semiCount n ^ 16) * (2 ^ (12 * (n + 1)) * semiCount (n + 1) ^ 16) := by
            gcongr
        _ = 2 ^ (12 * (2 * n + 1)) * (semiCount n * semiCount (n + 1)) ^ 16 := by ring
    · have E := (ih (n + 1) (by omega) (by omega)).2.1 (by omega)
      have Q0 := (ih n (by omega) hn1).1
      calc n ^ n * (n + 1) ^ (n + 1) * 2 ^ (7 * n / 4)
          ≤ n ^ n * (n + 1) ^ (n + 1) * 2 ^ (7 * (n + 1) / 4) := by gcongr; omega
        _ = n ^ n * ((n + 1) ^ (n + 1) * 2 ^ (7 * (n + 1) / 4)) := by ring
        _ ≤ (2 ^ (12 * n) * semiCount n ^ 16) * (2 ^ (12 * (n + 1)) * semiCount (n + 1) ^ 16) := by
            gcongr
        _ = 2 ^ (12 * (2 * n + 1)) * (semiCount n * semiCount (n + 1)) ^ 16 := by ring
  -- (iv)
  have IV : ∀ y r, (y = N ∨ y = N + 1) → 2 * r ≤ N → 2 * r + 1 ≤ y → N ≤ 2 * r + 2 →
      N ^ N * y ^ y * 2 ^ (7 * r) ≤ 2 ^ (12 * (N + y)) * mSum N y r ^ 16 := by
    intro y r hy h1 h2 h3
    rcases Nat.lt_or_ge r 13 with hr | hr
    · have hN32 : N ≤ 32 := by omega
      have hy32 : y ≤ 32 := by omega
      calc N ^ N * y ^ y * 2 ^ (7 * r) ≤ 32 ^ N * 32 ^ y * 2 ^ (7 * N + 7 * y) := by
            gcongr
            omega
        _ = 2 ^ (12 * (N + y)) * 1 := by
            rw [show (32 : Nat) = 2 ^ 5 by norm_num, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add,
              ← Nat.pow_add]; ring_nf
        _ ≤ 2 ^ (12 * (N + y)) * mSum N y r ^ 16 :=
            Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (mSum_pos N y r))
    · have key := mSum_chain (x := N) (y := y) (r := r) h1 h2
      have Qx1 := (ih ((N + 1) / 2) (by omega) (by omega)).1
      have Qy2 := (ih (y / 2) (by omega) (by omega)).1
      have M' := (ih (N / 2) (by omega) (by omega)).2.2.2 ((y + 1) / 2) (r / 2) (by omega)
        (by omega) (by omega) (by omega)
      have sx := self_pow_split N
      have sy := self_pow_split y
      have harith := arith16_iv hy h3 hr
      clear ih Pair
      set x1 := (N + 1) / 2 with hx1
      set x2 := N / 2 with hx2
      set y1 := (y + 1) / 2 with hy1
      set y2 := y / 2 with hy2
      set t := (r + 1) / 2 with ht
      set r' := r / 2 with hr'
      refine Nat.le_of_mul_le_mul_right (c := 2 ^ (7 * r')) ?_ (hpow _)
      calc N ^ N * y ^ y * 2 ^ (7 * r) * 2 ^ (7 * r')
          ≤ (2 ^ (N + 1) * (x1 ^ x1 * x2 ^ x2)) * (2 ^ (y + 1) * (y1 ^ y1 * y2 ^ y2)) *
              2 ^ (7 * r) * 2 ^ (7 * r') := by gcongr
        _ = 2 ^ (N + y + 2 + 7 * r) * (x1 ^ x1 * y2 ^ y2) * (x2 ^ x2 * y1 ^ y1 * 2 ^ (7 * r')) := by
            ring
        _ ≤ 2 ^ (N + y + 2 + 7 * r) * ((2 ^ (12 * x1) * semiCount x1 ^ 16) *
              (2 ^ (12 * y2) * semiCount y2 ^ 16)) *
              (2 ^ (12 * (x2 + y1)) * mSum x2 y1 r' ^ 16) := by
            gcongr
        _ = 2 ^ (N + y + 2 + 7 * r + 12 * (x1 + x2 + y1 + y2)) *
              (semiCount x1 * semiCount y2 * mSum x2 y1 r') ^ 16 := by ring
        _ ≤ 2 ^ (16 * t + 7 * r' + 12 * (N + y)) *
              (semiCount x1 * semiCount y2 * mSum x2 y1 r') ^ 16 := by
            exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) harith)
        _ = 2 ^ (12 * (N + y)) * (2 ^ t * (semiCount x1 * semiCount y2 * mSum x2 y1 r')) ^ 16 *
              2 ^ (7 * r') := by ring
        _ ≤ 2 ^ (12 * (N + y)) * mSum N y r ^ 16 * 2 ^ (7 * r') := by gcongr
  -- (iii)
  have III : (2 * N) ^ (2 * N) * 2 ^ (7 * N / 2) ≤ 2 ^ (24 * N) * slipSum N ^ 16 := by
    rcases Nat.lt_or_ge 512 N with hl | hs
    swap
    · exact small_slipSum16 hs
    rcases Nat.even_or_odd N with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- N = 2m: the chain recursion
      rw [show N = 2 * m by omega] at ⊢
      have hm1 : 1 ≤ m := by omega
      have Qm := (ih m (by omega) hm1).1
      have Bm := (ih m (by omega) hm1).2.2.1
      have key := slipSum_chain hm1
      have e : (2 * (2 * m)) ^ (2 * (2 * m)) * 2 ^ (7 * (2 * m) / 2) * 2 ^ (7 * m / 2) =
          2 ^ (13 * m) * ((2 * m) ^ (2 * m) * 2 ^ (7 * m / 2)) * (m ^ m) ^ 2 := by
        rw [show 7 * (2 * m) / 2 = 7 * m by omega, Nat.mul_pow 2 (2 * m) (2 * (2 * m)),
          show (2 * m) ^ (2 * (2 * m)) = (2 * m) ^ (2 * m) * (2 * m) ^ (2 * m) by
            rw [← Nat.pow_add]; congr 1; ring,
          show (2 * m) ^ (2 * m) = 2 ^ (2 * m) * (m ^ m) ^ 2 by
            rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm m 2, Nat.pow_mul]]
        rw [show (2 : Nat) ^ (2 * (2 * m)) = 2 ^ (4 * m) by ring_nf]
        ring
      refine Nat.le_of_mul_le_mul_right (c := 2 ^ (7 * m / 2)) ?_ (hpow _)
      rw [e]
      calc 2 ^ (13 * m) * ((2 * m) ^ (2 * m) * 2 ^ (7 * m / 2)) * (m ^ m) ^ 2
          ≤ 2 ^ (13 * m) * (2 ^ (24 * m) * slipSum m ^ 16) *
              (2 ^ (12 * m) * semiCount m ^ 16) ^ 2 := by
            gcongr
        _ = 2 ^ (45 * m) * (2 ^ m * (semiCount m ^ 2 * slipSum m)) ^ 16 := by ring
        _ ≤ 2 ^ (45 * m) * slipSum (2 * m) ^ 16 := by gcongr
        _ ≤ 2 ^ (24 * (2 * m)) * slipSum (2 * m) ^ 16 * 2 ^ (7 * m / 2) := by
            rw [Nat.mul_right_comm, ← Nat.pow_add]
            exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
    · -- N = 2m+1: upper slips with averaging, the restricted chain below
      subst hm
      have hm256 : 256 ≤ m := by omega
      have hm1 : 1 ≤ m := by omega
      have P2 := Pair m hm1 (by omega)
      have Mb := (ih m (by omega) hm1).2.2.2 (m + 1) (m / 2) (Or.inr rfl) (by omega) (by omega)
        (by omega)
      have Bup := slipSum_odd_up m
      have Wg := wSum_ge m
      have sp := self_pow_split (2 * m + 1)
      rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1) / 2 = m by omega] at sp
      have har := arith16_iii hm256
      clear ih Pair IV
      set N := 2 * m + 1 with hN
      set a0 := semiCount m
      set a1 := semiCount (m + 1)
      set M := mSum m (m + 1) (m / 2)
      set B := slipSum N
      set W := wSum m
      set c' := (m / 2 + 3) / 4
      set u := (m + 1) / 2
      have hX : 2 ^ (u + c') * (a0 * a1 * M) ≤ 4 * B := by
        calc 2 ^ (u + c') * (a0 * a1 * M) = 2 ^ u * ((a1 * a0 * 2 ^ c') * M) := by
              rw [Nat.pow_add]; ring
          _ ≤ 2 ^ u * ((4 * W) * M) := by gcongr
          _ = 4 * (2 ^ u * (W * M)) := by ring
          _ ≤ 4 * B := by gcongr
      refine Nat.le_of_mul_le_mul_right (c := 2 ^ (7 * m / 4 + 7 * (m / 2) + 16 * (u + c'))) ?_
        (hpow _)
      calc (2 * N) ^ (2 * N) * 2 ^ (7 * N / 2) * 2 ^ (7 * m / 4 + 7 * (m / 2) + 16 * (u + c'))
          = 2 ^ (2 * N + 7 * N / 2) * (N ^ N * N ^ N) *
              2 ^ (7 * m / 4 + 7 * (m / 2) + 16 * (u + c')) := by
            rw [Nat.mul_pow, show 2 * N = N + N by ring, Nat.pow_add N N N, Nat.pow_add]; ring
        _ ≤ 2 ^ (2 * N + 7 * N / 2) * ((2 ^ (N + 1) * ((m + 1) ^ (m + 1) * m ^ m)) *
              (2 ^ (N + 1) * ((m + 1) ^ (m + 1) * m ^ m))) *
              2 ^ (7 * m / 4 + 7 * (m / 2) + 16 * (u + c')) := by gcongr
        _ = 2 ^ (4 * N + 2 + 7 * N / 2) * (m ^ m * (m + 1) ^ (m + 1) * 2 ^ (7 * m / 4)) *
              (m ^ m * (m + 1) ^ (m + 1) * 2 ^ (7 * (m / 2))) * (2 ^ (u + c')) ^ 16 := by
            rw [show 4 * N + 2 + 7 * N / 2 = (2 * N + 7 * N / 2) + (N + 1) + (N + 1) by omega,
              Nat.pow_add, Nat.pow_add, Nat.pow_add, Nat.pow_add, ← Nat.pow_mul]
            ring
        _ ≤ 2 ^ (4 * N + 2 + 7 * N / 2) * (2 ^ (12 * (2 * m + 1)) * (a0 * a1) ^ 16) *
              (2 ^ (12 * (m + (m + 1))) * M ^ 16) * (2 ^ (u + c')) ^ 16 := by gcongr
        _ = 2 ^ (4 * N + 2 + 7 * N / 2 + 24 * N) * (2 ^ (u + c') * (a0 * a1 * M)) ^ 16 := by
            rw [show 12 * (m + (m + 1)) = 12 * N by omega, show 12 * (2 * m + 1) = 12 * N by omega]
            rw [show 4 * N + 2 + 7 * N / 2 + 24 * N = (4 * N + 2 + 7 * N / 2) + 12 * N + 12 * N by
              omega, Nat.pow_add, Nat.pow_add]
            ring
        _ ≤ 2 ^ (4 * N + 2 + 7 * N / 2 + 24 * N) * (4 * B) ^ 16 := by gcongr
        _ = 2 ^ (24 * N) * B ^ 16 * 2 ^ (4 * N + 34 + 7 * N / 2) := by
            rw [Nat.mul_pow, show (4 : Nat) ^ 16 = 2 ^ 32 by norm_num,
              show 4 * N + 34 + 7 * N / 2 = (4 * N + 2 + 7 * N / 2) + 32 by omega,
              show 4 * N + 2 + 7 * N / 2 + 24 * N = (4 * N + 2 + 7 * N / 2) + 24 * N by omega,
              Nat.pow_add, Nat.pow_add]
            ring
        _ ≤ 2 ^ (24 * N) * B ^ 16 * 2 ^ (7 * m / 4 + 7 * (m / 2) + 16 * (u + c')) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) har)
  refine ⟨?_, ?_, III, IV⟩
  · -- (i)
    rcases Nat.lt_or_ge 4096 N with hl | hs
    swap
    · -- small `N`: `N^N ≤ 4096^N`
      calc N ^ N ≤ 4096 ^ N := Nat.pow_le_pow_left hs _
        _ = 2 ^ (12 * N) := by rw [show (4096 : Nat) = 2 ^ 12 by norm_num, ← Nat.pow_mul]
        _ ≤ 2 ^ (12 * N) * semiCount N ^ 16 :=
            Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (semiCount_pos N))
    rcases Nat.even_or_odd N with ⟨n, hn⟩ | ⟨n, hn⟩
    · rw [show N = 2 * n by omega] at ⊢
      have hn1 : 1 ≤ n := by omega
      have Bn := (ih n (by omega) hn1).2.2.1
      have := slipSum_le hn1
      calc (2 * n) ^ (2 * n) ≤ (2 * n) ^ (2 * n) * 2 ^ (7 * n / 2) :=
            Nat.le_mul_of_pos_right _ (hpow _)
        _ ≤ 2 ^ (24 * n) * slipSum n ^ 16 := Bn
        _ ≤ 2 ^ (12 * (2 * n)) * semiCount (2 * n) ^ 16 := by
            rw [show 12 * (2 * n) = 24 * n by ring]; gcongr
    · -- odd `N = 2n + 1`: the odd slip lemma at the top
      subst hn
      rcases Nat.even_or_odd n with ⟨p, hp⟩ | ⟨p, hp⟩
      · -- `n = 2p`: odd child `2p + 1 = (p, p+1)`, even child `2p`
        rw [show n = 2 * p by omega]
        have hp1 : 1000 ≤ p := by omega
        have Ev := (ih (2 * p) (by omega) (by omega)).2.1 (by omega)
        have P2 := Pair p (by omega) (by omega)
        have key := oddNodeB p (by omega)
        have s1 := self_pow_split (2 * (2 * p) + 1)
        rw [show (2 * (2 * p) + 1 + 1) / 2 = 2 * p + 1 by omega,
          show (2 * (2 * p) + 1) / 2 = 2 * p by omega] at s1
        have s2 := self_pow_split (2 * p + 1)
        rw [show (2 * p + 1 + 1) / 2 = p + 1 by omega, show (2 * p + 1) / 2 = p by omega] at s2
        have har := arith16_oddB hp1
        clear ih Pair IV III
        set N := 2 * (2 * p) + 1 with hN
        set G := (p / 4 + 3) / 4
        set Y := 7 * (2 * p) / 4 + 7 * p / 4 + 16 * G with hY
        refine Nat.le_of_mul_le_mul_right (c := 2 ^ Y) ?_ (hpow _)
        calc N ^ N * 2 ^ Y
            ≤ (2 ^ (N + 1) * ((2 * p + 1) ^ (2 * p + 1) * (2 * p) ^ (2 * p))) * 2 ^ Y := by
              gcongr
          _ ≤ (2 ^ (N + 1) * ((2 ^ (2 * p + 1 + 1) * ((p + 1) ^ (p + 1) * p ^ p)) *
                (2 * p) ^ (2 * p))) * 2 ^ Y := by gcongr
          _ = 2 ^ (N + 2 * p + 3) * ((2 * p) ^ (2 * p) * 2 ^ (7 * (2 * p) / 4)) *
                (p ^ p * (p + 1) ^ (p + 1) * 2 ^ (7 * p / 4)) * (2 ^ G) ^ 16 := by
              rw [hY, show N + 2 * p + 3 = (N + 1) + (2 * p + 1 + 1) by omega, Nat.pow_add,
                Nat.pow_add, Nat.pow_add, ← Nat.pow_mul]
              ring
          _ ≤ 2 ^ (N + 2 * p + 3) * (2 ^ (12 * (2 * p)) * semiCount (2 * p) ^ 16) *
                (2 ^ (12 * (2 * p + 1)) * (semiCount p * semiCount (p + 1)) ^ 16) *
                (2 ^ G) ^ 16 := by gcongr
          _ = 2 ^ (N + 2 * p + 3 + 12 * N) *
                (semiCount p * (semiCount (2 * p) * semiCount (p + 1) * 2 ^ G)) ^ 16 := by
              rw [show N + 2 * p + 3 + 12 * N = (N + 2 * p + 3) + 12 * (2 * p) + 12 * (2 * p + 1)
                by omega, Nat.pow_add, Nat.pow_add]
              ring
          _ ≤ 2 ^ (N + 2 * p + 3 + 12 * N) * (4 * semiCount N) ^ 16 := by gcongr
          _ = 2 ^ (12 * N) * semiCount N ^ 16 * 2 ^ (N + 2 * p + 35) := by
              rw [Nat.mul_pow, show (4 : Nat) ^ 16 = 2 ^ 32 by norm_num,
                show N + 2 * p + 35 = (N + 2 * p + 3) + 32 by omega,
                show N + 2 * p + 3 + 12 * N = (N + 2 * p + 3) + 12 * N by omega,
                Nat.pow_add, Nat.pow_add]
              ring
          _ ≤ 2 ^ (12 * N) * semiCount N ^ 16 * 2 ^ Y :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      · -- `n = 2p + 1`: odd child `2p + 1 = (p, p+1)`, even child `2p + 2`
        rw [show n = 2 * p + 1 by omega]
        have hp1 : 1000 ≤ p := by omega
        have Ev := (ih (2 * p + 2) (by omega) (by omega)).2.1 (by omega)
        have P2 := Pair p (by omega) (by omega)
        have key := oddNodeA p
        have s1 := self_pow_split (2 * (2 * p + 1) + 1)
        rw [show (2 * (2 * p + 1) + 1 + 1) / 2 = 2 * p + 2 by omega,
          show (2 * (2 * p + 1) + 1) / 2 = 2 * p + 1 by omega] at s1
        have s2 := self_pow_split (2 * p + 1)
        rw [show (2 * p + 1 + 1) / 2 = p + 1 by omega, show (2 * p + 1) / 2 = p by omega] at s2
        have har := arith16_oddA hp1
        clear ih Pair IV III
        set N := 2 * (2 * p + 1) + 1 with hN
        set G := (p / 4 + 3) / 4
        set Y := 7 * (2 * p + 2) / 4 + 7 * p / 4 + 16 * G with hY
        refine Nat.le_of_mul_le_mul_right (c := 2 ^ Y) ?_ (hpow _)
        calc N ^ N * 2 ^ Y
            ≤ (2 ^ (N + 1) * ((2 * p + 2) ^ (2 * p + 2) * (2 * p + 1) ^ (2 * p + 1))) * 2 ^ Y := by
              gcongr
          _ ≤ (2 ^ (N + 1) * ((2 * p + 2) ^ (2 * p + 2) *
                (2 ^ (2 * p + 1 + 1) * ((p + 1) ^ (p + 1) * p ^ p)))) * 2 ^ Y := by gcongr
          _ = 2 ^ (N + 2 * p + 3) * ((2 * p + 2) ^ (2 * p + 2) * 2 ^ (7 * (2 * p + 2) / 4)) *
                (p ^ p * (p + 1) ^ (p + 1) * 2 ^ (7 * p / 4)) * (2 ^ G) ^ 16 := by
              rw [hY, show N + 2 * p + 3 = (N + 1) + (2 * p + 1 + 1) by omega, Nat.pow_add,
                Nat.pow_add, Nat.pow_add, ← Nat.pow_mul]
              ring
          _ ≤ 2 ^ (N + 2 * p + 3) * (2 ^ (12 * (2 * p + 2)) * semiCount (2 * p + 2) ^ 16) *
                (2 ^ (12 * (2 * p + 1)) * (semiCount p * semiCount (p + 1)) ^ 16) *
                (2 ^ G) ^ 16 := by gcongr
          _ = 2 ^ (N + 2 * p + 3 + 12 * N) *
                (semiCount (p + 1) * (semiCount p * semiCount (2 * p + 2) * 2 ^ G)) ^ 16 := by
              rw [show N + 2 * p + 3 + 12 * N =
                (N + 2 * p + 3) + 12 * (2 * p + 2) + 12 * (2 * p + 1) by omega,
                Nat.pow_add, Nat.pow_add]
              ring
          _ ≤ 2 ^ (N + 2 * p + 3 + 12 * N) * (4 * semiCount N) ^ 16 := by gcongr
          _ = 2 ^ (12 * N) * semiCount N ^ 16 * 2 ^ (N + 2 * p + 35) := by
              rw [Nat.mul_pow, show (4 : Nat) ^ 16 = 2 ^ 32 by norm_num,
                show N + 2 * p + 35 = (N + 2 * p + 3) + 32 by omega,
                show N + 2 * p + 3 + 12 * N = (N + 2 * p + 3) + 12 * N by omega,
                Nat.pow_add, Nat.pow_add]
              ring
          _ ≤ 2 ^ (12 * N) * semiCount N ^ 16 * 2 ^ Y :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  · -- (ii)
    intro he
    obtain ⟨n, rfl⟩ : ∃ n, N = 2 * n := ⟨N / 2, by omega⟩
    have hn1 : 1 ≤ n := by omega
    have Bn := (ih n (by omega) hn1).2.2.1
    have := slipSum_le hn1
    calc (2 * n) ^ (2 * n) * 2 ^ (7 * (2 * n) / 4) = (2 * n) ^ (2 * n) * 2 ^ (7 * n / 2) := by
          rw [show 7 * (2 * n) / 4 = 7 * n / 2 by omega]
      _ ≤ 2 ^ (24 * n) * slipSum n ^ 16 := Bn
      _ ≤ 2 ^ (12 * (2 * n)) * semiCount (2 * n) ^ 16 := by
          rw [show 12 * (2 * n) = 24 * n by ring]; gcongr

/-- **Super-exponential lower bound with exponent 1/16 for all `N`**:
`N^N ≤ 2^{12N} a(N)^{16}`, i.e. `a(N) ≥ (N/4096)^{N/16}`. -/
theorem self_pow_le_semiCount_pow_16 {N : Nat} (hN : 1 ≤ N) :
    N ^ N ≤ 2 ^ (12 * N) * semiCount N ^ 16 :=
  (alln16_aux N hN).1

end AllN16

end Odd
end Slip
end Folds
