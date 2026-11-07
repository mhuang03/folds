import Folds.SymRatio
import Mathlib.Tactic

/-!
# The shift automaton behind the doubling defect of `θ(n)/(2θ(⌊n/2⌋)θ(⌈n/2⌉))`

See `experiments/symratio2/PROOFS.txt`.  Theorem W of `SymRatio` writes `θ(N)` through the
counts `Π_{N,q}(S,T)`, which depend on the windows `S, T` only through the **linkage
pattern** `(k,i) ↦ Linked N y_k u_i` of the lifted entries.  This file proves the exact
arithmetic behind the `4^{-j}` rate and the exceptional role of `3`:

* `linkGH`: linkage at size `L` with the two progression windows shifted by `g` and `h`
  (`1+g ≤ 2y-u ≤ L+g` or `1+h ≤ 2u-y ≤ L+h`); `linked_iff_linkGH`: `g = h = 0` is `Linked`.
* `linkS_unlift` (**unlifting lemma**, four independent shifts, any size `2L+e`):
  lifting both entries (`y = 2Y-b`, `u = 2U-c`) is the same as halving the size and
  moving the shifts by `⌊(g + 2b - c)/2⌋`, `⌊(h + 2c - b)/2⌋` (plus `e` on the upper ends).
  `linkGH_unlift` is the even case, `linked_lift_iff` the top level of Theorem J:
  `Linked (2L) (lift q Y) (lift (1-q) U) ↔ linkGH L (∓1) (±1) Y U`.
* `patt_lift`: the same for whole windows (`Fin 6 → ℤ`), so every function of the linkage
  pattern (in particular `Π`) satisfies `F_{lift S, lift T} = F_{S,T} ∘ step`.
* The automaton on functions `F : ℤ → ℤ → ℚ` of the shifts: `T F = (1/4) Σ_{b,c} F ∘ step`.
  `delta_T`: the functional `Δ` is an eigenvector with eigenvalue `1/4`; `pi_T`: `πF` is
  invariant; `p0_T`: one step from the top state `{(-1,1),(1,-1)}` gives `πF + ΔF/24`.
  `fair_closed_form`: for every `k ≥ 1`, `p0 (T^[k] F) = πF + ΔF / (6·4^k)` — the
  **fair-bit model** of the doubling recursion is exactly `Φ + A·4^{-k}`.
* `w1_lift`, `w2_lift`, `delta_lift_eq_zero`: `Δ = w1 + w2`, and the two mixed differences
  `w1, w2` are carried into each other (or killed) by one lift, for ANY function of the
  linkage pattern.  So `w1 = w2 = 0` on all window pairs at size `L` implies the same at
  size `2L`, hence at every `L·2^j`.
* `w1_cell`, `w2_cell`, `w1_cell_eq_zero_of_three_dvd`: for a single pair `(y,u)` the mixed
  difference of the linkage indicator is `1` exactly at the "1/3-pairs"
  `(2y-u, 2u-y) ∈ {(L,1), (0,L+1)}` (so `3y = 2L+1` or `3y = L+1`), and `0` when `3 ∣ L`.
No `sorry`, no `native_decide`.
-/

namespace Folds
namespace SymRatio2

open SymStructure SymStructure2

/-! ## Shifted linkage and the unlifting lemma -/

/-- Linkage at size `L` with the upper/lower ends of the two progression windows shifted:
`2y - u ∈ [1 + glo, L + ghi]` or `2u - y ∈ [1 + hlo, L + hhi]`. -/
def linkS (L glo ghi hlo hhi y u : ℤ) : Prop :=
  (1 + glo ≤ 2 * y - u ∧ 2 * y - u ≤ L + ghi) ∨ (1 + hlo ≤ 2 * u - y ∧ 2 * u - y ≤ L + hhi)

/-- Linkage with both windows shifted rigidly by `g` and `h`. -/
def linkGH (L g h y u : ℤ) : Prop := linkS L g g h h y u

instance (L glo ghi hlo hhi y u : ℤ) : Decidable (linkS L glo ghi hlo hhi y u) := by
  unfold linkS; infer_instance

instance (L g h y u : ℤ) : Decidable (linkGH L g h y u) := by unfold linkGH; infer_instance

theorem linked_iff_linkGH (N y u : ℕ) : Linked N y u ↔ linkGH N 0 0 y u := by
  unfold Linked linkGH linkS; omega

/-- **Unlifting lemma.**  For any integers, lifting both entries (`y = 2Y - b`,
`u = 2U - c`) at size `2L + e` is linkage at size `L` with the shifts moved. -/
theorem linkS_unlift (L e glo ghi hlo hhi Y U b c : ℤ) :
    linkS (2 * L + e) glo ghi hlo hhi (2 * Y - b) (2 * U - c) ↔
      linkS L ((glo + 2 * b - c) / 2) ((ghi + e + 2 * b - c) / 2)
        ((hlo + 2 * c - b) / 2) ((hhi + e + 2 * c - b) / 2) Y U := by
  unfold linkS; omega

/-- One step of the shift automaton: `g ↦ ⌊(g + 2b - c)/2⌋`. -/
def step (g b c : ℤ) : ℤ := (g + 2 * b - c) / 2

/-- The even case: rigid shifts stay rigid. -/
theorem linkGH_unlift (L g h Y U b c : ℤ) :
    linkGH (2 * L) g h (2 * Y - b) (2 * U - c) ↔ linkGH L (step g b c) (step h c b) Y U := by
  have := linkS_unlift L 0 g g h h Y U b c
  simp only [add_zero] at this
  exact this

/-- The top level of Theorem J: the `D`-entries are lifted by `q`, the `C`-entries by
`1 - q`; the comparison at size `2L` becomes a shifted comparison at size `L`. -/
theorem linked_lift_iff (L Y U : ℕ) (hY : 1 ≤ Y) (hU : 1 ≤ U) :
    (Linked (2 * L) (lift 0 Y) (lift 1 U) ↔ linkGH L (-1) 1 Y U) ∧
      (Linked (2 * L) (lift 1 Y) (lift 0 U) ↔ linkGH L 1 (-1) Y U) := by
  unfold Linked linkGH linkS lift; constructor <;> omega

/-! ## Whole windows -/

/-- The linkage pattern of two windows at size `L` with shifts `g, h`. -/
def patt (L g h : ℤ) (y u : Fin 6 → ℤ) : Fin 6 → Fin 6 → Bool :=
  fun k i => decide (linkGH L g h (y k) (u i))

/-- Lift every entry of a window by `b`. -/
def liftW (b : ℤ) (y : Fin 6 → ℤ) : Fin 6 → ℤ := fun k => 2 * y k - b

theorem patt_lift (L g h b c : ℤ) (y u : Fin 6 → ℤ) :
    patt (2 * L) g h (liftW b y) (liftW c u) = patt L (step g b c) (step h c b) y u := by
  funext k i
  simp only [patt, liftW]
  exact decide_eq_decide.mpr (linkGH_unlift L g h (y k) (u i) b c)

/-! ## The automaton on functions of the shifts -/

/-- One fair step: average of `F ∘ step` over the four bit pairs. -/
def T (F : ℤ → ℤ → ℚ) : ℤ → ℤ → ℚ := fun g h =>
  (F (step g 0 0) (step h 0 0) + F (step g 0 1) (step h 1 0) +
    F (step g 1 0) (step h 0 1) + F (step g 1 1) (step h 1 1)) / 4

/-- The amplitude functional of the `1/4`-mode. -/
def Δ (F : ℤ → ℤ → ℚ) : ℚ :=
  F (-1) 0 + F 0 (-1) + F 0 1 + F 1 0 - F (-1) 1 - F 1 (-1) - 2 * F 0 0

/-- The stationary law `(1/12)·(1,2,1,4,1,2,1)` on `(-1,0),(-1,1),(0,-1),(0,0),(0,1),(1,-1),(1,0)`. -/
def πF (F : ℤ → ℤ → ℚ) : ℚ :=
  (F (-1) 0 + 2 * F (-1) 1 + F 0 (-1) + 4 * F 0 0 + F 0 1 + 2 * F 1 (-1) + F 1 0) / 12

/-- The top state: `q = 0` gives shifts `(-1, 1)`, `q = 1` gives `(1, -1)`. -/
def p0 (F : ℤ → ℤ → ℚ) : ℚ := (F (-1) 1 + F 1 (-1)) / 2

/-- The two mixed differences; `Δ = w1 + w2`. -/
def w1 (F : ℤ → ℤ → ℚ) : ℚ := F (-1) 0 - F (-1) 1 - F 0 0 + F 0 1
def w2 (F : ℤ → ℤ → ℚ) : ℚ := F 0 (-1) - F 0 0 - F 1 (-1) + F 1 0

theorem delta_eq (F : ℤ → ℤ → ℚ) : Δ F = w1 F + w2 F := by unfold Δ w1 w2; ring

/-- `Δ` is a left eigenvector of the automaton with eigenvalue `1/4`. -/
theorem delta_T (F : ℤ → ℤ → ℚ) : Δ (T F) = Δ F / 4 := by
  simp only [Δ, T, step]; norm_num; ring

/-- `π` is stationary. -/
theorem pi_T (F : ℤ → ℤ → ℚ) : πF (T F) = πF F := by
  simp only [πF, T, step]; norm_num; ring

/-- One step from the top state. -/
theorem p0_T (F : ℤ → ℤ → ℚ) : p0 (T F) = πF F + Δ F / 24 := by
  simp only [p0, T, πF, Δ, step]; norm_num; ring

/-- **Fair-bit closed form.**  `p0 (T^[k] F) = π F + Δ F / (6 · 4^k)` for `k ≥ 1`. -/
theorem fair_closed_form (F : ℤ → ℤ → ℚ) (k : ℕ) (hk : 1 ≤ k) :
    p0 (T^[k] F) = πF F + Δ F / (6 * 4 ^ k) := by
  induction k generalizing F with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · show p0 (T F) = _
      rw [p0_T]; norm_num
    · rw [Function.iterate_succ_apply, ih (T F) hn, pi_T, delta_T, pow_succ]
      field_simp

/-- The successive differences of the fair-bit model are exactly geometric with ratio `1/4`. -/
theorem fair_diff (F : ℤ → ℤ → ℚ) (k : ℕ) (hk : 1 ≤ k) :
    p0 (T^[k + 1] F) - p0 (T^[k] F) = -(Δ F) / (8 * 4 ^ k) := by
  rw [fair_closed_form F k hk, fair_closed_form F (k + 1) (by omega), pow_succ]
  field_simp; ring

/-! ## The mixed differences under one lift -/

/-- The function of the shifts obtained from a function `Φ` of the linkage pattern. -/
def ofPatt (Φ : (Fin 6 → Fin 6 → Bool) → ℚ) (L : ℤ) (y u : Fin 6 → ℤ) : ℤ → ℤ → ℚ :=
  fun g h => Φ (patt L g h y u)

theorem ofPatt_lift (Φ : (Fin 6 → Fin 6 → Bool) → ℚ) (L b c : ℤ) (y u : Fin 6 → ℤ) :
    ofPatt Φ (2 * L) (liftW b y) (liftW c u) =
      fun g h => ofPatt Φ L y u (step g b c) (step h c b) := by
  funext g h; simp only [ofPatt, patt_lift]

/-- `w1` after one lift: it becomes `w2` for the bits `(b,c) = (1,0)` and vanishes otherwise. -/
theorem w1_lift (Φ : (Fin 6 → Fin 6 → Bool) → ℚ) (L : ℤ) (y u : Fin 6 → ℤ) (b c : ℤ)
    (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    w1 (ofPatt Φ (2 * L) (liftW b y) (liftW c u)) =
      if b = 1 ∧ c = 0 then w2 (ofPatt Φ L y u) else 0 := by
  rw [ofPatt_lift]
  rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp only [w1, w2, step] <;> norm_num

/-- `w2` after one lift: it becomes `w1` for `(b,c) = (0,1)` and vanishes otherwise. -/
theorem w2_lift (Φ : (Fin 6 → Fin 6 → Bool) → ℚ) (L : ℤ) (y u : Fin 6 → ℤ) (b c : ℤ)
    (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    w2 (ofPatt Φ (2 * L) (liftW b y) (liftW c u)) =
      if b = 0 ∧ c = 1 then w1 (ofPatt Φ L y u) else 0 := by
  rw [ofPatt_lift]
  rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp only [w1, w2, step] <;> norm_num

/-- **Propagation.**  If `w1` and `w2` vanish on a pair of windows at size `L`, they vanish
on every lift of it at size `2L`; by induction on every `j`-fold lift at size `L·2^j`. -/
theorem w_lift_eq_zero (Φ : (Fin 6 → Fin 6 → Bool) → ℚ) (L : ℤ) (y u : Fin 6 → ℤ)
    (h1 : w1 (ofPatt Φ L y u) = 0) (h2 : w2 (ofPatt Φ L y u) = 0) (b c : ℤ)
    (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    w1 (ofPatt Φ (2 * L) (liftW b y) (liftW c u)) = 0 ∧
      w2 (ofPatt Φ (2 * L) (liftW b y) (liftW c u)) = 0 := by
  rw [w1_lift Φ L y u b c hb hc, w2_lift Φ L y u b c hb hc]
  constructor <;> split_ifs <;> first | assumption | rfl

/-- Iterated lifts: bits `bs j, cs j` for the `j`-th lift. -/
def liftsW : List ℤ → (Fin 6 → ℤ) → (Fin 6 → ℤ)
  | [], y => y
  | b :: bs, y => liftW b (liftsW bs y)

theorem w_lifts_eq_zero (Φ : (Fin 6 → Fin 6 → Bool) → ℚ) (L : ℤ) (y u : Fin 6 → ℤ)
    (h1 : w1 (ofPatt Φ L y u) = 0) (h2 : w2 (ofPatt Φ L y u) = 0) :
    ∀ (bs cs : List ℤ), bs.length = cs.length → (∀ b ∈ bs, b = 0 ∨ b = 1) →
      (∀ c ∈ cs, c = 0 ∨ c = 1) →
      w1 (ofPatt Φ (2 ^ bs.length * L) (liftsW bs y) (liftsW cs u)) = 0 ∧
        w2 (ofPatt Φ (2 ^ bs.length * L) (liftsW bs y) (liftsW cs u)) = 0
  | [], [], _, _, _ => by simpa [liftsW] using And.intro h1 h2
  | b :: bs, c :: cs, hl, hb, hc => by
    have ih := w_lifts_eq_zero Φ L y u h1 h2 bs cs (by simpa using hl)
      (fun x hx => hb x (by simp [hx])) (fun x hx => hc x (by simp [hx]))
    have e : (2 : ℤ) ^ (b :: bs).length * L = 2 * (2 ^ bs.length * L) := by
      simp [pow_succ]; ring
    rw [e]
    exact w_lift_eq_zero Φ _ _ _ ih.1 ih.2 b c (hb b (by simp)) (hc c (by simp))
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

theorem delta_lift_eq_zero (Φ : (Fin 6 → Fin 6 → Bool) → ℚ) (L : ℤ) (y u : Fin 6 → ℤ)
    (h1 : w1 (ofPatt Φ L y u) = 0) (h2 : w2 (ofPatt Φ L y u) = 0) (b c : ℤ)
    (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    Δ (ofPatt Φ (2 * L) (liftW b y) (liftW c u)) = 0 := by
  obtain ⟨e1, e2⟩ := w_lift_eq_zero Φ L y u h1 h2 b c hb hc
  rw [delta_eq, e1, e2]; norm_num

/-! ## A single cell: the interaction is a 1/3-phenomenon -/

/-- The linkage indicator of one pair as a function of the shifts. -/
def cell (L y u : ℤ) : ℤ → ℤ → ℚ := fun g h => if linkGH L g h y u then 1 else 0

theorem w1_cell (L y u : ℤ) (hL : 1 ≤ L) :
    w1 (cell L y u) =
      (if 2 * y - u = L ∧ 2 * u - y = 1 then 1 else 0) +
        (if 2 * y - u = 0 ∧ 2 * u - y = L + 1 then 1 else 0) := by
  simp only [w1, cell, linkGH, linkS]
  split_ifs <;> (try norm_num) <;> omega

theorem w2_cell (L y u : ℤ) (hL : 1 ≤ L) :
    w2 (cell L y u) =
      (if 2 * u - y = L ∧ 2 * y - u = 1 then 1 else 0) +
        (if 2 * u - y = 0 ∧ 2 * y - u = L + 1 then 1 else 0) := by
  simp only [w2, cell, linkGH, linkS]
  split_ifs <;> (try norm_num) <;> omega

/-- At sizes divisible by 3 no single pair couples the two shifts. -/
theorem w1_cell_eq_zero_of_three_dvd (L y u : ℤ) (hL : 1 ≤ L) (h3 : 3 ∣ L) :
    w1 (cell L y u) = 0 ∧ w2 (cell L y u) = 0 := by
  rw [w1_cell L y u hL, w2_cell L y u hL]
  obtain ⟨m, rfl⟩ := h3
  constructor <;> split_ifs <;> (try norm_num) <;> omega

/-- For `L ≡ 1 (mod 3)` the pair `((2L+1)/3, (L+2)/3)` couples them. -/
theorem w1_cell_one_third (m : ℤ) (hm : 0 ≤ m) :
    w1 (cell (3 * m + 1) (2 * m + 1) (m + 1)) = 1 := by
  rw [w1_cell _ _ _ (by omega)]
  split_ifs <;> (try norm_num) <;> omega

/-- For `L ≡ 2 (mod 3)` the pair `((L+1)/3, (2L+2)/3)` couples them. -/
theorem w1_cell_two_thirds (m : ℤ) (hm : 0 ≤ m) :
    w1 (cell (3 * m + 2) (m + 1) (2 * m + 2)) = 1 := by
  rw [w1_cell _ _ _ (by omega)]
  split_ifs <;> (try norm_num) <;> omega

end SymRatio2
end Folds
