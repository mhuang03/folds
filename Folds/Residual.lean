import Folds.ArithCover
import Mathlib.Data.Rat.Floor

/-!
# The residual of `ArithCover`: lattice points in the witness polygon

`experiments/residual/PROOFS.txt`.

For a family `(K, L, R, α, β, smax, amin)` of `Live8.dirOK` and a pair `(a, c)` (left index,
right distance), the witnesses `s` are the integers between the lower bounds
`(aK - α + 1)/(L + 1)`, `(cK - β + 1)/(R + 1)`, `R`, `2` and the upper bounds `(aK - α)/L`,
`(cK - β)/R`, `smax`.  If every upper bound exceeds every lower bound by at least `1` (twelve
affine conditions on `(a, c)`, `famCons`), a witness exists (`dirOK_of_cons`).  So the pair
passes `dirAny` as soon as the polygon `Π = {famCons ≥ 0}` contains a lattice point, and that
holds, position-free, as soon as `Π` contains a fundamental parallelogram of `ℤ²`
(`exists_lattice_point`): `ParOK`.

* `Aff`, `famCons`, `dirOK_of_cons`: the pair lemma.
* `exists_lattice_point`: a fundamental parallelogram with all four corners in `Π` contains a
  lattice point of `Π`.
* `RegionPF`: some family and orientation whose polygon contains a fundamental parallelogram;
  `dirAny_of_regionPF`.
* `Proven2`, `Residual2`, `residual_of_residual2`, `conjectureC_of_residual2`.
-/

namespace Folds
namespace Residual

open Live2 Live8 ArithCover

/-! ## Affine functions and fundamental parallelograms -/

/-- An affine function `A a + C c + D` on `ℚ²`. -/
structure Aff where
  A : ℚ
  C : ℚ
  D : ℚ

/-- Evaluation of an affine function. -/
def Aff.eval (f : Aff) (a c : ℚ) : ℚ := f.A * a + f.C * c + f.D

/-- `u - l - 1`. -/
def Aff.gap (u l : Aff) : Aff := ⟨u.A - l.A, u.C - l.C, u.D - l.D - 1⟩

theorem Aff.eval_gap (u l : Aff) (a c : ℚ) : (u.gap l).eval a c = u.eval a c - l.eval a c - 1 := by
  unfold Aff.gap Aff.eval; ring

/-- An affine function that is nonnegative at the four corners of a parallelogram is nonnegative
on it. -/
theorem Aff.nonneg_par (f : Aff) (Pa Pc p1 q1 p2 q2 t1 t2 : ℚ) (ht1 : 0 ≤ t1) (ht1' : t1 ≤ 1)
    (ht2 : 0 ≤ t2) (ht2' : t2 ≤ 1)
    (h00 : 0 ≤ f.eval Pa Pc) (h10 : 0 ≤ f.eval (Pa + p1) (Pc + q1))
    (h01 : 0 ≤ f.eval (Pa + p2) (Pc + q2)) (h11 : 0 ≤ f.eval (Pa + p1 + p2) (Pc + q1 + q2)) :
    0 ≤ f.eval (Pa + t1 * p1 + t2 * p2) (Pc + t1 * q1 + t2 * q2) := by
  have key : f.eval (Pa + t1 * p1 + t2 * p2) (Pc + t1 * q1 + t2 * q2) =
      (1 - t1) * (1 - t2) * f.eval Pa Pc + t1 * (1 - t2) * f.eval (Pa + p1) (Pc + q1) +
        (1 - t1) * t2 * f.eval (Pa + p2) (Pc + q2) + t1 * t2 * f.eval (Pa + p1 + p2) (Pc + q1 + q2) := by
    unfold Aff.eval; ring
  rw [key]
  have a1 : 0 ≤ 1 - t1 := by linarith
  have a2 : 0 ≤ 1 - t2 := by linarith
  have := mul_nonneg (mul_nonneg a1 a2) h00
  have := mul_nonneg (mul_nonneg ht1 a2) h10
  have := mul_nonneg (mul_nonneg a1 ht2) h01
  have := mul_nonneg (mul_nonneg ht1 ht2) h11
  linarith

/-- Every fundamental parallelogram `P + [0,1] w₁ + [0,1] w₂` (`det (w₁, w₂) = 1`) contains a
lattice point. -/
theorem exists_lattice (Pa Pc δ : ℚ) (p1 q1 p2 q2 : ℤ) (hdet : p1 * q2 - p2 * q1 = 1) :
    ∃ (a c : ℤ) (t1 t2 : ℚ), 0 ≤ t1 ∧ t1 ≤ 1 ∧ 0 ≤ t2 ∧ t2 ≤ 1 ∧
      (a : ℚ) = Pa + t1 * p1 + t2 * (p2 + δ * p1) ∧
      (c : ℚ) = Pc + t1 * q1 + t2 * (q2 + δ * q1) := by
  set l2 : ℚ := p1 * Pc - q1 * Pa with hl2
  set t2 : ℚ := Int.ceil l2 - l2 with ht2
  set l1 : ℚ := Pa * q2 - Pc * p2 + t2 * δ with hl1
  have hd : ((p1 : ℚ) * q2 - p2 * q1) = 1 := by exact_mod_cast hdet
  refine ⟨(Int.ceil l1) * p1 + (Int.ceil l2) * p2, (Int.ceil l1) * q1 + (Int.ceil l2) * q2,
    (Int.ceil l1) - l1, t2,
    by linarith [Int.le_ceil l1], by linarith [Int.ceil_lt_add_one l1],
    by linarith [Int.le_ceil l2], by linarith [Int.ceil_lt_add_one l2], ?_, ?_⟩
  · push_cast
    have e2 : (Int.ceil l2 : ℚ) = l2 + t2 := by rw [ht2]; ring
    rw [e2, hl1, hl2]
    linear_combination Pa * hd
  · push_cast
    have e2 : (Int.ceil l2 : ℚ) = l2 + t2 := by rw [ht2]; ring
    rw [e2, hl1, hl2]
    linear_combination Pc * hd

/-- `ParOK cs`: the polygon `{f ≥ 0 : f ∈ cs}` contains a fundamental parallelogram of `ℤ²`,
with sides `w₁` and `w₂ + δ w₁` (`det (w₁, w₂) = 1`, `δ` rational): all four corners satisfy
every constraint. -/
def ParOK (cs : List Aff) : Prop :=
  ∃ (Pa Pc δ : ℚ) (p1 q1 p2 q2 : ℤ), p1 * q2 - p2 * q1 = 1 ∧
    ∀ f ∈ cs, 0 ≤ f.eval Pa Pc ∧ 0 ≤ f.eval (Pa + p1) (Pc + q1) ∧
      0 ≤ f.eval (Pa + (p2 + δ * p1)) (Pc + (q2 + δ * q1)) ∧
      0 ≤ f.eval (Pa + p1 + (p2 + δ * p1)) (Pc + q1 + (q2 + δ * q1))

/-- **Lattice point in a polygon containing a fundamental parallelogram.** -/
theorem exists_lattice_point {cs : List Aff} (h : ParOK cs) :
    ∃ a c : ℤ, ∀ f ∈ cs, 0 ≤ f.eval a c := by
  obtain ⟨Pa, Pc, δ, p1, q1, p2, q2, hdet, hc⟩ := h
  obtain ⟨a, c, t1, t2, h1, h1', h2, h2', ea, ec⟩ := exists_lattice Pa Pc δ p1 q1 p2 q2 hdet
  refine ⟨a, c, fun f hf => ?_⟩
  obtain ⟨c1, c2, c3, c4⟩ := hc f hf
  rw [ea, ec]
  exact f.nonneg_par Pa Pc p1 q1 (p2 + δ * p1) (q2 + δ * q1) t1 t2 h1 h1' h2 h2' c1 c2 c3 c4

/-! ## The pair lemma: the witness polygon of a family -/

/-- Upper bound `(aK - α)/L` of the witness `s`. -/
def affU1 (K L α : ℕ) : Aff := ⟨(K : ℚ) / L, 0, -(α : ℚ) / L⟩
/-- Upper bound `(cK - β)/R`. -/
def affU2 (K R β : ℕ) : Aff := ⟨0, (K : ℚ) / R, -(β : ℚ) / R⟩
/-- Lower bound `(aK - α + 1)/(L + 1)`. -/
def affL1 (K L α : ℕ) : Aff := ⟨(K : ℚ) / (L + 1), 0, (1 - (α : ℚ)) / (L + 1)⟩
/-- Lower bound `(cK - β + 1)/(R + 1)`. -/
def affL2 (K R β : ℕ) : Aff := ⟨0, (K : ℚ) / (R + 1), (1 - (β : ℚ)) / (R + 1)⟩
/-- A constant. -/
def affC (k : ℚ) : Aff := ⟨0, 0, k⟩

/-- **The witness polygon** of the family `(K, L, R, α, β, smax, amin)`: every upper bound of `s`
exceeds every lower bound by at least `1`, and `a ≥ amin`. -/
def famCons (K L R α β smax amin : ℕ) : List Aff :=
  [(affU1 K L α).gap (affL1 K L α), (affU1 K L α).gap (affL2 K R β),
    (affU1 K L α).gap (affC R), (affU1 K L α).gap (affC 2),
    (affU2 K R β).gap (affL1 K L α), (affU2 K R β).gap (affL2 K R β),
    (affU2 K R β).gap (affC R), (affU2 K R β).gap (affC 2),
    (affC smax).gap (affL1 K L α), (affC smax).gap (affL2 K R β),
    (affC smax).gap (affC R), (affC smax).gap (affC 2), ⟨1, 0, -(amin : ℚ)⟩]

/-- **The pair lemma**: a lattice point of the witness polygon gives a witness `s`. -/
theorem wit_of_cons {K L R α β smax amin : ℕ} {a c : ℤ} (hK : 0 < K) (hL : 1 ≤ L) (hR : 1 ≤ R)
    (h : ∀ f ∈ famCons K L R α β smax amin, 0 ≤ f.eval a c) :
    ∃ a' c' s : ℕ, (a' : ℤ) = a ∧ (c' : ℤ) = c ∧ amin ≤ a' ∧ 2 ≤ s ∧ s ≤ smax ∧ R ≤ s ∧
      s * L + α ≤ a' * K ∧ a' * K + 1 ≤ s * (L + 1) + α ∧
      s * R + β ≤ c' * K ∧ c' * K + 1 ≤ s * R + β + s := by
  simp only [famCons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h
  obtain ⟨g11, g12, g13, g14, g21, g22, g23, g24, g31, g32, g33, g34, g5⟩ := h
  simp only [Aff.eval_gap] at g11 g12 g13 g14 g21 g22 g23 g24 g31 g32 g33 g34
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have hRq : (0 : ℚ) < R := by exact_mod_cast hR
  have hL1 : (0 : ℚ) < L + 1 := by linarith
  have hR1 : (0 : ℚ) < R + 1 := by linarith
  have eU1 : (affU1 K L α).eval a c = (K * a - α) / L := by unfold affU1 Aff.eval; field_simp; ring
  have eU2 : (affU2 K R β).eval a c = (K * c - β) / R := by unfold affU2 Aff.eval; field_simp; ring
  have eL1 : (affL1 K L α).eval a c = (K * a - α + 1) / (L + 1) := by
    unfold affL1 Aff.eval; field_simp; ring
  have eL2 : (affL2 K R β).eval a c = (K * c - β + 1) / (R + 1) := by
    unfold affL2 Aff.eval; field_simp; ring
  have eC : ∀ k : ℚ, (affC k).eval a c = k := fun k => by unfold affC Aff.eval; ring
  simp only [eU1, eU2, eL1, eL2, eC] at g11 g12 g13 g14 g21 g22 g23 g24 g31 g32 g33 g34
  simp only [Aff.eval] at g5
  set u1 : ℚ := (K * a - α) / L with hu1
  set u2 : ℚ := (K * c - β) / R with hu2
  set l1 : ℚ := (K * a - α + 1) / (L + 1) with hl1
  set l2 : ℚ := (K * c - β + 1) / (R + 1) with hl2
  set m : ℚ := max (max l1 l2) (max (R : ℚ) 2) with hm
  have hm2 : (2 : ℚ) ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
  have hmR : (R : ℚ) ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have hm1 : l1 ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
  have hm2' : l2 ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
  have up1 : m + 1 ≤ u1 := by
    have : m ≤ u1 - 1 := max_le (max_le (by linarith) (by linarith)) (max_le (by linarith) (by linarith))
    linarith
  have up2 : m + 1 ≤ u2 := by
    have : m ≤ u2 - 1 := max_le (max_le (by linarith) (by linarith)) (max_le (by linarith) (by linarith))
    linarith
  have up3 : m + 1 ≤ smax := by
    have : m ≤ smax - 1 := max_le (max_le (by linarith) (by linarith)) (max_le (by linarith) (by linarith))
    linarith
  set s := ⌈m⌉₊ with hs
  have hs1 : m ≤ s := Nat.le_ceil m
  have hs2 : (s : ℚ) < m + 1 := Nat.ceil_lt_add_one (by linarith)
  -- a, c are positive
  have ha : (0 : ℚ) ≤ a := by
    have h3 : (3 : ℚ) * L + α ≤ K * a := by
      have := (le_div_iff₀ hLq).1 (show (3 : ℚ) ≤ u1 by linarith)
      linarith
    by_contra hc'
    push Not at hc'
    have : (K : ℚ) * a < 0 := mul_neg_of_pos_of_neg hKq hc'
    have : (0 : ℚ) ≤ α := by positivity
    linarith
  have hc0 : (0 : ℚ) ≤ c := by
    have h3 : (3 : ℚ) * R + β ≤ K * c := by
      have := (le_div_iff₀ hRq).1 (show (3 : ℚ) ≤ u2 by linarith)
      linarith
    by_contra hc'
    push Not at hc'
    have : (K : ℚ) * c < 0 := mul_neg_of_pos_of_neg hKq hc'
    have : (0 : ℚ) ≤ β := by positivity
    linarith
  obtain ⟨a', rfl⟩ := Int.eq_ofNat_of_zero_le (by exact_mod_cast ha : (0 : ℤ) ≤ a)
  obtain ⟨c', rfl⟩ := Int.eq_ofNat_of_zero_le (by exact_mod_cast hc0 : (0 : ℤ) ≤ c)
  push_cast at *
  refine ⟨a', c', s, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (show (amin : ℚ) ≤ a' by linarith)
  · exact_mod_cast (show (2 : ℚ) ≤ s by linarith)
  · exact_mod_cast (show (s : ℚ) ≤ smax by linarith)
  · exact_mod_cast (show (R : ℚ) ≤ s by linarith)
  · have := (le_div_iff₀ hLq).1 (show (s : ℚ) ≤ u1 by linarith)
    simp only [Int.cast_natCast] at this
    exact_mod_cast (show (s : ℚ) * L + α ≤ a' * K by linarith)
  · have := (div_le_iff₀ hL1).1 (show l1 ≤ s by linarith)
    simp only [Int.cast_natCast] at this
    exact_mod_cast (show (a' : ℚ) * K + 1 ≤ s * (L + 1) + α by linarith)
  · have := (le_div_iff₀ hRq).1 (show (s : ℚ) ≤ u2 by linarith)
    simp only [Int.cast_natCast] at this
    exact_mod_cast (show (s : ℚ) * R + β ≤ c' * K by linarith)
  · have := (div_le_iff₀ hR1).1 (show l2 ≤ s by linarith)
    simp only [Int.cast_natCast] at this
    exact_mod_cast (show (c' : ℚ) * K + 1 ≤ s * R + β + s by linarith)

/-! ## The three families, both orientations -/

/-- Family `Z(N, s - 1)` in orientation `(x, y)`. -/
def consZ (N x y : ℕ) : List Aff := famCons (N + 2) x y 0 1 ((N + 2) / 2) 2
/-- Family `X(N, s, 0)` in orientation `(x, y)`. -/
def consX0 (N x y : ℕ) : List Aff := famCons N x (y - 2) 0 1 ((N + 1) / 2) 1
/-- Family `X(N, s, 1)` in orientation `(x, y)`. -/
def consX1 (N x y : ℕ) : List Aff := famCons N x (y - 2) 1 0 (N / 2) 2

theorem a_le_of_wit {K x s smax α a : ℕ} (hK : 0 < K) (hα : α ≤ 1) (hsm : s ≤ smax)
    (hsK : smax ≤ K) (h : a * K + 1 ≤ s * (x + 1) + α) : a ≤ x + 1 := by
  have h1 : s * (x + 1) ≤ K * (x + 1) := Nat.mul_le_mul_right _ (le_trans hsm hsK)
  have h2 : a * K ≤ (x + 1) * K := by nlinarith
  exact Nat.le_of_mul_le_mul_right h2 hK

theorem dirAny_of_consZ {N x y : ℕ} {a c : ℤ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : ∀ f ∈ consZ N x y, 0 ≤ f.eval a c) : dirAny N x y = true := by
  obtain ⟨a', c', s, -, -, ha, hs, hsm, hRs, h1, h2, h3, h4⟩ :=
    wit_of_cons (by omega) hx hy h
  have hax := a_le_of_wit (K := N + 2) (α := 0) (by omega) (by omega) hsm (by omega) h2
  exact dirAny_of_dirAll (a := a') (by omega) hax
    (dirAll_Z ha (dirOK_of_wit (by omega) hx hs hRs hsm h1 h2 h3 h4))

theorem dirAny_of_consX0 {N x y : ℕ} {a c : ℤ} (hx : 1 ≤ x) (hy : 3 ≤ y) (hN : 0 < N)
    (h : ∀ f ∈ consX0 N x y, 0 ≤ f.eval a c) : dirAny N x y = true := by
  obtain ⟨a', c', s, -, -, ha, hs, hsm, hRs, h1, h2, h3, h4⟩ :=
    wit_of_cons hN hx (by omega) h
  have hax := a_le_of_wit (K := N) (α := 0) hN (by omega) hsm (by omega) h2
  have ha1 : 1 ≤ a' := by
    by_contra h0
    have : a' = 0 := by omega
    subst this
    have : s * x ≥ 2 := by nlinarith
    omega
  exact dirAny_of_dirAll (a := a') ha1 hax
    (dirAll_X0 (by omega) (dirOK_of_wit hN hx hs hRs hsm h1 h2 h3 h4))

theorem dirAny_of_consX1 {N x y : ℕ} {a c : ℤ} (hx : 1 ≤ x) (hy : 3 ≤ y) (hN : 0 < N)
    (h : ∀ f ∈ consX1 N x y, 0 ≤ f.eval a c) : dirAny N x y = true := by
  obtain ⟨a', c', s, -, -, ha, hs, hsm, hRs, h1, h2, h3, h4⟩ :=
    wit_of_cons hN hx (by omega) h
  have hax := a_le_of_wit (K := N) (α := 1) hN le_rfl hsm (by omega) h2
  exact dirAny_of_dirAll (a := a') (by omega) hax
    (dirAll_X1 ha (by omega) (dirOK_of_wit hN hx hs hRs hsm h1 h2 h3 h4))

/-! ## The parallelogram region and the new residual -/

/-- **Region PF**: in some family and orientation the witness polygon contains a fundamental
parallelogram of `ℤ²` (position-free: no fractional part enters). -/
def RegionPF (N u u' : ℕ) : Prop :=
  ParOK (consZ N u' u) ∨ (3 ≤ u ∧ ParOK (consX0 N u' u)) ∨ (3 ≤ u ∧ ParOK (consX1 N u' u)) ∨
    ParOK (consZ N u u') ∨ (3 ≤ u' ∧ ParOK (consX0 N u u')) ∨ (3 ≤ u' ∧ ParOK (consX1 N u u'))

theorem covered_of_regionPF {N u u' : ℕ} (hN : 0 < N) (hu : 1 ≤ u) (hu' : 1 ≤ u')
    (h : RegionPF N u u') : dirAny N u u' = true ∨ dirAny N u' u = true := by
  rcases h with h | ⟨h3, h⟩ | ⟨h3, h⟩ | h | ⟨h3, h⟩ | ⟨h3, h⟩
  · obtain ⟨a, c, hac⟩ := exists_lattice_point h
    exact Or.inr (dirAny_of_consZ hu' hu hac)
  · obtain ⟨a, c, hac⟩ := exists_lattice_point h
    exact Or.inr (dirAny_of_consX0 hu' h3 hN hac)
  · obtain ⟨a, c, hac⟩ := exists_lattice_point h
    exact Or.inr (dirAny_of_consX1 hu' h3 hN hac)
  · obtain ⟨a, c, hac⟩ := exists_lattice_point h
    exact Or.inl (dirAny_of_consZ hu hu' hac)
  · obtain ⟨a, c, hac⟩ := exists_lattice_point h
    exact Or.inl (dirAny_of_consX0 hu h3 hN hac)
  · obtain ⟨a, c, hac⟩ := exists_lattice_point h
    exact Or.inl (dirAny_of_consX1 hu h3 hN hac)

/-- The proven regions: those of `ArithCover` and the new ones. -/
def Proven2 (N u u' : ℕ) : Prop := Proven N u u' ∨ RegionPF N u u'

theorem covered_of_proven2 {N u u' : ℕ} (hN : 0 < N) (hu : 1 ≤ u) (hu' : 1 ≤ u')
    (h : Proven2 N u u') : dirAny N u u' = true ∨ dirAny N u' u = true := by
  rcases h with h | h
  · exact covered_of_proven h
  · exact covered_of_regionPF hN hu hu' h

/-- **The new residual statement**: `ArithCover N` for the pairs outside `Proven2`. -/
def Residual2 (N : ℕ) : Prop :=
  ∀ u v, 2 ≤ u → u < v → u + v ≤ N + 1 → (u + v) % 2 = 1 → 2 * u + 2 ≤ v →
    N + u + 3 ≤ 2 * v → ¬ Special N u (N + 1 - v) → ¬ Proven2 N u (N + 1 - v) →
        dirAny N u (N + 1 - v) = true ∨ dirAny N (N + 1 - v) u = true

theorem residual_of_residual2 {N : ℕ} (h : Residual2 N) : Residual N := by
  intro u v h1 h2 h3 h4 h5 h6 h7 h8
  by_cases hP : Proven2 N u (N + 1 - v)
  · exact covered_of_proven2 (by omega) (by omega) (by omega) hP
  exact h u v h1 h2 h3 h4 h5 h6 h7 hP

/-- **Conjecture C (2-prefixes) for all `N`, modulo `Residual2 N` for `N > 300`.** -/
theorem conjectureC_of_residual2 (hR : ∀ N, 300 < N → Residual2 N) {N m₁ m₂ : ℕ}
    (h1 : 1 ≤ m₁ ∧ m₁ ≤ N) (h2 : 1 ≤ m₂ ∧ m₂ ≤ N) (h12 : m₁ ≠ m₂)
    (hval : SemiSymmetric N [m₁, m₂]) :
    Extends N [m₁, m₂] ↔ deadB N (min m₁ m₂) (max m₁ m₂) = false :=
  conjectureC_of_residual (fun N hN => residual_of_residual2 (hR N hN)) h1 h2 h12 hval

end Residual
end Folds
