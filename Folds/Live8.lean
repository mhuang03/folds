import Folds.Live7

/-!
# Live pairs, part 8: towards the covering statement for all `N`

`experiments/live8/PROOFS.txt`.

* `settled7_beatty`, `settled7_z`: constructors for `Settled7`.
* `samePar_settled`: every same-parity pair (`u ≡ v mod 2`) is settled, for every `N ≥ 65`
  (slope-2 copies `X(N, n, h)`, `Z(N, n)` and their corners).
* `coverAt_of_mixed`: the covering statement `CoverAt E7 N` follows from the statement
  `MixedCover N` about the mixed-parity wide pairs only.
-/

namespace Folds
namespace Live8

open Live2 Live4 Adjacent Live5 Live6 Live7

/-! ## Constructors for `Settled7` -/

theorem settled7_beatty {N p h a b u v : Nat} (hp : 1 ≤ p) (hh : h + 2 * p ≤ N + 1) (h1 : h ≤ 1)
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ p) (hd : deadB p a b = false)
    (e1 : beatty N p h a = u) (e2 : beatty N p h b = v) : Settled7 N u v :=
  Or.inl (Or.inr (Or.inr (Or.inl ⟨p, h, a, b, hp, hh, h1, ha, hab, hb, hd, e1, e2⟩)))

theorem settled7_z {N p a b u v : Nat} (hp : 1 ≤ p) (hpN : 2 * p ≤ N)
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ p) (hd : deadB p a b = false)
    (e1 : zF N p a = u) (e2 : zF N p b = v) : Settled7 N u v :=
  Or.inr ⟨p, a, b, hp, hpN, ha, hab, hb, hd, e1, e2⟩

theorem settled7_inward {N u v : Nat} (h : v ≤ 2 * u + 1 ∨ 2 * v ≤ N + u + 2) :
    Settled7 N u v :=
  Or.inl (Or.inl h)

theorem settled7_one {N : Nat} (h1 : N % 2 = 1) (h7 : N ≠ 7) : Settled7 N 1 N :=
  Or.inl (Or.inr (Or.inl ⟨rfl, rfl, h1, h7⟩))

theorem deadB_false_of_lt {p a b : Nat} (h : 2 ≤ a) : deadB p a b = false := by
  unfold deadB
  have : (a == 1) = false := by simp; omega
  rw [this, Bool.false_and, Bool.false_and]

theorem deadB_false_of_ne {p a b : Nat} (h : b ≠ p) : deadB p a b = false := by
  unfold deadB
  have : (b == p) = false := by simp [h]
  rw [this, Bool.and_false, Bool.false_and]

theorem deadB_false_odd {p a b : Nat} (hodd : p % 2 = 1) (h7 : p ≠ 7) : deadB p a b = false := by
  unfold deadB
  have h1 : (p % 2 == 0) = false := by simp; omega
  have h2 : (p == 7) = false := by simp [h7]
  rw [h1, h2, Bool.false_and, Bool.false_or, Bool.and_false]

/-! ## Slope-2 copies -/

theorem beatty_even {n r : Nat} (hn : 1 ≤ n) : beatty (2 * n) n 0 r = 2 * r := by
  unfold beatty
  rw [Nat.sub_zero, show r * (2 * n) = 2 * r * n by ring]
  exact Nat.mul_div_cancel _ (by omega)

theorem beatty_odd {n r : Nat} (hn : 1 ≤ n) (hr : 1 ≤ r) : beatty (2 * n) n 1 r = 2 * r - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  unfold beatty
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  have e : (k + 1) * (2 * n) = (2 * k + 1) * n + n := by ring
  have e2 : (2 * k + 1 + 1) * n = (2 * k + 1) * n + n := by ring
  apply Nat.div_eq_of_lt_le <;> omega

theorem beatty_odd' {n r : Nat} (hr : 1 ≤ r) (hrn : r ≤ n + 1) :
    beatty (2 * n + 1) (n + 1) 0 r = 2 * r - 1 := by
  unfold beatty
  rw [Nat.sub_zero]
  apply Nat.div_eq_of_lt_le
  · have : (2 * r - 1) * (n + 1) + (n + 1 - r) = r * (2 * n + 1) := by
      rcases r with _ | r
      · omega
      · rw [show 2 * (r + 1) - 1 = 2 * r + 1 by omega, show n + 1 - (r + 1) = n - r by omega]
        zify [show r ≤ n by omega]
        ring
    omega
  · have : (2 * r - 1 + 1) * (n + 1) = r * (2 * n + 1) + r := by
      rw [show 2 * r - 1 + 1 = 2 * r by omega]; ring
    omega

theorem zF_even' {n k : Nat} (hk : k ≤ n) : zF (2 * n + 1) n k = 2 * k := by
  unfold zF beatty
  rw [Nat.sub_zero]
  apply Nat.div_eq_of_lt_le
  · have : 2 * k * (n + 1) + k = k * (2 * n + 1 + 2) := by ring
    omega
  · have : (2 * k + 1) * (n + 1) = k * (2 * n + 1 + 2) + (n + 1 - k) := by
      zify [(by omega : k ≤ n + 1)]; ring
    omega

/-- The corner `(2, N)` for `N ≡ 0 mod 4`: the image of `(1, p)` under `X(N, p, 0)`,
`p = N/2 - 1` odd. -/
theorem settled7_two_N {N : Nat} (hN : 20 ≤ N) (h4 : N % 4 = 0) : Settled7 N 2 N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = 2 * n + 2 := ⟨N / 2 - 1, by omega⟩
  refine settled7_beatty (p := n) (h := 0) (a := 1) (b := n) (by omega) (by omega) (by omega)
    le_rfl (by omega) le_rfl (deadB_false_odd (by omega) (by omega)) ?_ ?_
  · unfold beatty
    rw [Nat.sub_zero, Nat.one_mul]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · unfold beatty
    rw [Nat.sub_zero, Nat.mul_comm]
    exact Nat.mul_div_cancel _ (by omega)

/-- The corner `(2, N - 1)` for `N ≡ 1 mod 4`: the image of `(1, p)` under `Z(N, p)`,
`p = (N - 3)/2` odd. -/
theorem settled7_two_N1 {N : Nat} (hN : 21 ≤ N) (h4 : N % 4 = 1) : Settled7 N 2 (N - 1) := by
  obtain ⟨p, rfl⟩ : ∃ p, N = 2 * p + 3 := ⟨(N - 3) / 2, by omega⟩
  obtain ⟨e1, e2⟩ := zF_corner (N := 2 * p + 3) (p := p) (c := 2) (by omega) (by omega)
  refine settled7_z (p := p) (a := 1) (b := p) (by omega) (by omega) le_rfl (by omega) le_rfl
    (deadB_false_odd (by omega) (by omega)) e1 ?_
  rw [e2]; omega

/-- **Same-parity pairs are settled** (`N ≥ 65`): by the slope-2 copies `X(N, n, h)` (`N = 2n`),
`X(N, n + 1, 0)` and `Z(N, n)` (`N = 2n + 1`), or the corners. -/
theorem samePar_settled {N u v : Nat} (hN : 65 ≤ N) (hu : 1 ≤ u) (huv : u < v) (hv : v ≤ N)
    (hpar : u % 2 = v % 2) (hd : deadB N u v = false) :
    Settled7 N u v ∨ Settled7 N (N + 1 - v) (N + 1 - u) := by
  rcases Nat.even_or_odd' N with ⟨n, hn | hn⟩
  · subst hn
    rcases Nat.even_or_odd' u with ⟨a, ha | ha⟩
    · -- both even: X(2n, n, 0)
      obtain ⟨b, rfl⟩ : ∃ b, v = 2 * b := ⟨v / 2, by omega⟩
      subst ha
      by_cases hc : a = 1 ∧ b = n
      · -- (2, N): dead preimage iff n even
        rw [hc.1, hc.2]
        by_cases h4 : n % 2 = 0
        · exact Or.inl (settled7_two_N (by omega) (by omega))
        · exact Or.inl (settled7_beatty (p := n) (h := 0) (a := 1) (b := n) (by omega) (by omega)
            (by omega) le_rfl (by omega) le_rfl (deadB_false_odd (by omega) (by omega))
            (beatty_even (by omega)) (beatty_even (by omega)))
      · refine Or.inl (settled7_beatty (p := n) (h := 0) (a := a) (b := b) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) ?_ (beatty_even (by omega))
          (beatty_even (by omega)))
        unfold deadB; simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]; omega
    · -- both odd: X(2n, n, 1)
      obtain ⟨b, hb⟩ : ∃ b, v = 2 * b + 1 := ⟨v / 2, by omega⟩
      subst ha hb
      by_cases hc : a = 0 ∧ b + 1 = n
      · -- (1, N - 1): its mirror is (2, N)
        right
        rw [show 2 * n + 1 - (2 * b + 1) = 2 by omega, show 2 * n + 1 - (2 * a + 1) = 2 * n by omega]
        by_cases h4 : n % 2 = 0
        · exact settled7_two_N (by omega) (by omega)
        · exact settled7_beatty (p := n) (h := 0) (a := 1) (b := n) (by omega) (by omega)
            (by omega) le_rfl (by omega) le_rfl (deadB_false_odd (by omega) (by omega))
            (beatty_even (by omega)) (beatty_even (by omega))
      · refine Or.inl (settled7_beatty (p := n) (h := 1) (a := a + 1) (b := b + 1) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_)
        · unfold deadB; simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]; omega
        · rw [beatty_odd (by omega) (by omega)]; omega
        · rw [beatty_odd (by omega) (by omega)]; omega
  · subst hn
    rcases Nat.even_or_odd' u with ⟨a, ha | ha⟩
    · -- both even: Z(2n+1, n)
      obtain ⟨b, rfl⟩ : ∃ b, v = 2 * b := ⟨v / 2, by omega⟩
      subst ha
      by_cases hc : a = 1 ∧ b = n
      · rw [hc.1, hc.2]
        by_cases h4 : n % 2 = 0
        · exact Or.inl (by
            have := settled7_two_N1 (N := 2 * n + 1) (by omega) (by omega)
            rwa [show 2 * n + 1 - 1 = 2 * n by omega] at this)
        · exact Or.inl (settled7_z (p := n) (a := 1) (b := n) (by omega) (by omega) le_rfl
            (by omega) le_rfl (deadB_false_odd (by omega) (by omega)) (zF_even' (by omega))
            (zF_even' le_rfl))
      · refine Or.inl (settled7_z (p := n) (a := a) (b := b) (by omega) (by omega) (by omega)
          (by omega) (by omega) ?_ (zF_even' (by omega)) (zF_even' (by omega)))
        unfold deadB; simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]; omega
    · -- both odd: X(2n+1, n+1, 0)
      obtain ⟨b, hb⟩ : ∃ b, v = 2 * b + 1 := ⟨v / 2, by omega⟩
      subst ha hb
      by_cases hc : a = 0 ∧ b = n
      · rw [hc.1, hc.2]
        exact Or.inl (by simpa using settled7_one (N := 2 * n + 1) (by omega) (by omega))
      · refine Or.inl (settled7_beatty (p := n + 1) (h := 0) (a := a + 1) (b := b + 1) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_)
        · unfold deadB; simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]; omega
        · rw [beatty_odd' (by omega) (by omega)]; omega
        · rw [beatty_odd' (by omega) (by omega)]; omega

/-! ## Reduction to the mixed-parity wide pairs -/

/-- The covering statement for the **mixed-parity wide pairs** (`u + v` odd, Theorem G fails,
`u + v ≤ N + 1`): each is settled, or its mirror is. -/
def MixedCover (N : Nat) : Prop :=
  ∀ u v, 1 ≤ u → u < v → u + v ≤ N + 1 → (u + v) % 2 = 1 → 2 * u + 2 ≤ v →
    N + u + 3 ≤ 2 * v → deadB N u v = false →
      Settled7 N u v ∨ Settled7 N (N + 1 - v) (N + 1 - u)

theorem deadB_mirror {N u v : Nat} (_hu : 1 ≤ u) (huv : u < v) (hv : v ≤ N)
    (hd : deadB N u v = false) : deadB N (N + 1 - v) (N + 1 - u) = false := by
  unfold deadB at hd ⊢
  simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hd ⊢
  rcases hd with (hd | hd) | hd
  · left; right; omega
  · left; left; omega
  · right; exact hd

/-- **`CoverAt E7 N` from the mixed-parity statement** (`N ≥ 65`): Theorem G, the same-parity
pairs (`samePar_settled`) and the mirror take care of everything else. -/
theorem coverAt_of_mixed {N : Nat} (hN : 65 ≤ N) (h : MixedCover N) : CoverAt E7 N := by
  intro u v hu huv hv hd
  by_cases hin : v ≤ 2 * u + 1 ∨ 2 * v ≤ N + u + 2
  · exact Or.inl (settled7_inward hin)
  by_cases hpar : u % 2 = v % 2
  · rcases samePar_settled hN hu huv hv hpar hd with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  by_cases hs : u + v ≤ N + 1
  · rcases h u v hu huv hs (by omega) (by omega) (by omega) hd with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · -- the mirror pair
    have hd' := deadB_mirror hu huv hv hd
    by_cases hin' : N + 1 - u ≤ 2 * (N + 1 - v) + 1 ∨ 2 * (N + 1 - u) ≤ N + (N + 1 - v) + 2
    · exact Or.inr (Or.inl (settled7_inward hin'))
    · rcases h (N + 1 - v) (N + 1 - u) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) hd' with h1 | h1
      · exact Or.inr (Or.inl h1)
      · left
        rwa [show N + 1 - (N + 1 - u) = u by omega, show N + 1 - (N + 1 - v) = v by omega] at h1

/-- **Conjecture C for all `N`, modulo the mixed-parity statement for `N ≥ 65`.** -/
theorem coReach_of_mixed (h : ∀ N, 65 ≤ N → MixedCover N) :
    ∀ N u v, 1 ≤ u → u < v → v ≤ N → deadB N u v = false → CoReach N {u, v} :=
  coReach_of_cover_large fun N hN => coverAt_of_mixed hN (h N hN)

/-! ## A certificate checker for the mixed-parity wide pairs at one `N`

A certificate `c` for a pair `(u, v)` packs an orientation `o = c % 2` (the pair itself or its
mirror), a family `f = (c / 2) % 4` (`X(N, p, 0)`, `X(N, p, 1)`, `Z(N, p)`, or a fallback to the
full search `settled7B`) and `p = c / 8`.  The indices are the candidate indices `candB`, `candZ`
of Live7; the images are re-checked, so soundness is immediate.  The certificates of one `u`
are packed into one `Nat` in base `2^16`. -/

def beattyW (N p h x y : Nat) : Bool :=
  decide (1 ≤ p) && decide (h + 2 * p ≤ N + 1) && decide (1 ≤ candB N p h x) &&
    decide (candB N p h x < candB N p h y) && decide (candB N p h y ≤ p) &&
    !deadB p (candB N p h x) (candB N p h y) &&
    beatty N p h (candB N p h x) == x && beatty N p h (candB N p h y) == y

def zW (N p x y : Nat) : Bool :=
  decide (1 ≤ p) && decide (2 * p ≤ N) && decide (1 ≤ candZ N p x) &&
    decide (candZ N p x < candZ N p y) && decide (candZ N p y ≤ p) &&
    !deadB p (candZ N p x) (candZ N p y) &&
    zF N p (candZ N p x) == x && zF N p (candZ N p y) == y

theorem settled7_of_beattyW {N p h x y : Nat} (h1 : h ≤ 1) (hw : beattyW N p h x y = true) :
    Settled7 N x y := by
  unfold beattyW at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, hh⟩, ha⟩, hab⟩, hb⟩, hd⟩, e1⟩, e2⟩ := hw
  exact settled7_beatty hp hh h1 ha hab hb hd e1 e2

theorem settled7_of_zW {N p x y : Nat} (hw : zW N p x y = true) : Settled7 N x y := by
  unfold zW at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, hh⟩, ha⟩, hab⟩, hb⟩, hd⟩, e1⟩, e2⟩ := hw
  exact settled7_z hp hh ha hab hb hd e1 e2

/-- Check a witness for the pair `x < y`: family `f` (`0, 1`: `X(N, p, f)`; otherwise `Z(N, p)`). -/
def chkXY (N x y f p : Nat) : Bool :=
  if f = 0 then beattyW N p 0 x y else if f = 1 then beattyW N p 1 x y else zW N p x y

theorem chkXY_sound {N x y f p : Nat} (h : chkXY N x y f p = true) : Settled7 N x y := by
  unfold chkXY at h
  split_ifs at h
  · exact settled7_of_beattyW (by omega) h
  · exact settled7_of_beattyW le_rfl h
  · exact settled7_of_zW h

/-- Check one certificate for the pair `(u, v)`. -/
def chkCert (N u v c : Nat) : Bool :=
  if (c / 2) % 4 = 3 then settled7B N u v || settled7B N (N + 1 - v) (N + 1 - u)
  else if c % 2 = 0 then chkXY N u v ((c / 2) % 4) (c / 8)
  else chkXY N (N + 1 - v) (N + 1 - u) ((c / 2) % 4) (c / 8)

theorem chkCert_sound {N u v c : Nat} (h : chkCert N u v c = true) :
    Settled7 N u v ∨ Settled7 N (N + 1 - v) (N + 1 - u) := by
  unfold chkCert at h
  split_ifs at h
  · simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact Or.inl (settled7_of_B h)
    · exact Or.inr (settled7_of_B h)
  · exact Or.inl (chkXY_sound h)
  · exact Or.inr (chkXY_sound h)


/-- Check the pairs `(u, w)`, `v ≤ w < v + k`, consuming one certificate (a base `2^16` place
of `c`) for each `w` with `u + w` odd. -/
def chkU (N u : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | k + 1, v, c =>
    if (u + v) % 2 = 1 then
      (deadB N u v || chkCert N u v (c % 65536)) && chkU N u k (v + 1) (c / 65536)
    else chkU N u k (v + 1) c

theorem chkU_sound {N u : Nat} : ∀ k v c, chkU N u k v c = true → ∀ w, v ≤ w → w < v + k →
    (u + w) % 2 = 1 → deadB N u w = false →
      Settled7 N u w ∨ Settled7 N (N + 1 - w) (N + 1 - u) := by
  intro k
  induction k with
  | zero => intro v c _ w h1 h2; omega
  | succ k ih =>
    intro v c h w h1 h2 hw hd
    unfold chkU at h
    split_ifs at h with hv
    · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨h3, h4⟩ := h
      by_cases hwv : w = v
      · subst hwv
        rcases h3 with h3 | h3
        · rw [hd] at h3; exact absurd h3 (by simp)
        · exact chkCert_sound h3
      · exact ih (v + 1) _ h4 w (by omega) (by omega) hw hd
    · by_cases hwv : w = v
      · subst hwv; omega
      · exact ih (v + 1) _ h w (by omega) (by omega) hw hd

/-- The smallest `v` of a wide pair `(u, v)`. -/
def vLo (N u : Nat) : Nat := max (2 * u + 2) ((N + u + 4) / 2)

/-- Check all `u ≥ u₀`, one packed certificate per `u`. -/
def goU (N : Nat) : Nat → List Nat → Bool
  | u, [] => decide (N < 3 * u + 1)
  | u, c :: cs => chkU N u (N + 2 - u - vLo N u) (vLo N u) c && goU N (u + 1) cs

theorem goU_sound {N : Nat} : ∀ cs u₀, goU N u₀ cs = true → ∀ u v, u₀ ≤ u → u < v →
    u + v ≤ N + 1 → (u + v) % 2 = 1 → 2 * u + 2 ≤ v → N + u + 3 ≤ 2 * v →
    deadB N u v = false → Settled7 N u v ∨ Settled7 N (N + 1 - v) (N + 1 - u) := by
  intro cs
  induction cs with
  | nil =>
    intro u₀ h u v hu _ hs _ h1 h2 _
    unfold goU at h
    simp only [decide_eq_true_eq] at h
    omega
  | cons c cs ih =>
    intro u₀ h u v hu huv hs hp h1 h2 hd
    unfold goU at h
    simp only [Bool.and_eq_true] at h
    by_cases hu' : u = u₀
    · subst hu'
      exact chkU_sound _ _ _ h.1 v (by unfold vLo; omega) (by unfold vLo; omega) hp hd
    · exact ih (u₀ + 1) h.2 u v (by omega) huv hs hp h1 h2 hd

/-- The certificate check at one `N`. -/
def mixedB (N : Nat) (cs : List Nat) : Bool := goU N 1 cs

theorem mixedCover_of_B {N : Nat} {cs : List Nat} (h : mixedB N cs = true) : MixedCover N :=
  fun u v hu huv hs hp h1 h2 hd => goU_sound cs 1 h u v hu huv hs hp h1 h2 hd

/-! ## Sliding windows: a rotation lemma

For `s₁ ≤ s ≤ s₂` the windows `[sR + β, sR + β + s - 1]` overlap or abut as soon as `R ≤ s₁`,
so their union is `[s₁R + β, s₂R + β + s₂ - 1]`; if that has length `≥ K` it contains a multiple
of `K`. -/

theorem slide {K R β s₁ s₂ : Nat} (hK : 0 < K) (hR : R ≤ s₁) (h12 : s₁ ≤ s₂)
    (hlen : s₁ * R + β + K ≤ s₂ * R + β + s₂) :
    ∃ s c, s₁ ≤ s ∧ s ≤ s₂ ∧ s * R + β ≤ c * K ∧ c * K + 1 ≤ s * R + β + s := by
  set c := (s₁ * R + β + K - 1) / K with hc
  have hc1 : s₁ * R + β ≤ c * K := by
    have := Nat.lt_mul_div_succ (s₁ * R + β + K - 1) hK
    rw [← hc] at this
    have e : K * (c + 1) = c * K + K := by ring
    omega
  have hc2 : c * K ≤ s₁ * R + β + K - 1 := by
    have := Nat.div_mul_le_self (s₁ * R + β + K - 1) K
    rw [← hc] at this
    exact this
  rcases Nat.eq_zero_or_pos R with hR0 | hRp
  · subst hR0
    refine ⟨s₂, c, h12, le_rfl, ?_, ?_⟩ <;> simp only [Nat.mul_zero, Nat.zero_add] at * <;> omega
  · set s := min s₂ ((c * K - β) / R) with hs
    have hsR : s * R ≤ c * K - β := by
      calc s * R ≤ (c * K - β) / R * R := Nat.mul_le_mul_right _ (min_le_right _ _)
        _ ≤ c * K - β := Nat.div_mul_le_self _ _
    have hs1 : s₁ ≤ s := by
      refine le_min h12 ?_
      rw [Nat.le_div_iff_mul_le hRp]
      omega
    refine ⟨s, c, hs1, min_le_left _ _, by omega, ?_⟩
    by_cases hlt : s < s₂
    · -- then s = ⌊(cK - β)/R⌋, so (s + 1) R + β > cK
      have hs' : s = (c * K - β) / R := by
        rcases min_cases s₂ ((c * K - β) / R) with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [← hs] at h1; omega
        · rw [← hs] at h1; exact h1
      have := Nat.lt_mul_div_succ (c * K - β) hRp
      rw [← hs'] at this
      have e : R * (s + 1) = s * R + R := by ring
      have : R ≤ s := le_trans hR hs1
      omega
    · have hss : s = s₂ := le_antisymm (min_le_left _ _) (by omega)
      rw [hss]
      have : s₁ * R ≤ s₂ * R := Nat.mul_le_mul_right _ h12
      omega

/-! ## The direct rotation lemma for `Z(N, q - 1)`

Fix the index `a` of `u`; for `q` with `qu ≤ aM ≤ qu + q - 1` (`M = N + 2`) the element `u` is
`zF N (q-1) a`, and `v = N + 1 - u'` is an element of `Z(N, q - 1)` iff some `cM` lies in
`[qu' + 1, qu' + q]`.  These windows slide by `u'` as `q` increases. -/

theorem settled_directZ {N u u' a s₁ s₂ : Nat} (hu : 1 ≤ u) (ha : 2 ≤ a) (huu : u + u' ≤ N)
    (hs₁ : 2 ≤ s₁) (hR : u' ≤ s₁) (h12 : s₁ ≤ s₂) (hs₂ : 2 * s₂ ≤ N + 2)
    (hI1 : s₂ * u ≤ a * (N + 2)) (hI2 : a * (N + 2) + 1 ≤ s₁ * (u + 1))
    (hlen : s₁ * u' + 1 + (N + 2) ≤ s₂ * u' + 1 + s₂) : Settled7 N u (N + 1 - u') := by
  obtain ⟨s, c, hs1, hs2, hc1, hc2⟩ := slide (K := N + 2) (by omega) hR h12 hlen
  -- q = s, p = s - 1, b = s - c
  have hsu : s * u ≤ a * (N + 2) := le_trans (Nat.mul_le_mul_right _ hs2) hI1
  have hsu2 : a * (N + 2) + 1 ≤ s * (u + 1) := le_trans hI2 (Nat.mul_le_mul_right _ hs1)
  have hc0 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, Nat.zero_mul] at hc1; omega
    · exact h
  -- a + c < s
  have hac : a + c < s := by
    by_contra hcon
    push Not at hcon
    have h1 : s * (N + 2) ≤ (a + c) * (N + 2) := Nat.mul_le_mul_right _ hcon
    have h2 : s * (u + u' + 2) ≤ s * (N + 2) := Nat.mul_le_mul_left _ (by omega)
    have e1 : (a + c) * (N + 2) = a * (N + 2) + c * (N + 2) := by ring
    have e2 : s * (u + u' + 2) = s * (u + 1) + s * u' + s := by ring
    omega
  have hp : s - 1 + 1 = s := by omega
  refine settled7_z (p := s - 1) (a := a) (b := s - c) (by omega) (by omega) (by omega)
    (by omega) (by omega) (deadB_false_of_lt ha) ?_ ?_
  · unfold zF beatty
    rw [Nat.sub_zero, hp]
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm]; exact hsu
    · have : (u + 1) * s = s * (u + 1) := Nat.mul_comm _ _
      omega
  · unfold zF beatty
    rw [Nat.sub_zero, hp]
    have e : (s - c) * (N + 2) + c * (N + 2) = s * (N + 2) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    have e2 : s * (N + 2) = s * (N + 1 - u') + s * u' + s := by
      rw [← Nat.mul_add, ← Nat.mul_add_one]; congr 1; omega
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm (N + 1 - u')]; omega
    · have e3 : (N + 1 - u' + 1) * s = s * (N + 1 - u') + s := by ring
      omega

/-- **An explicit direct region** (`Z(N, q - 1)`, `a = ⌊u/2⌋`).  With `M = N + 2`, `r = u mod 2`:
if `(u - r) M (u + u' + 1) ≥ 2 (u + 1) (M u + 2 u u' + u)` and
`(u M - r M - 2u + 2)(u' + 1) ≥ 2u (u'² + M)`, then `(u, N + 1 - u')` is settled. -/
theorem settled_directZ_region {N u u' : Nat} (hu : 4 ≤ u) (huu' : u ≤ u') (huu : u + u' ≤ N)
    (hA : (u - u % 2) * (N + 2) * (u + u' + 1) ≥ 2 * (u + 1) * ((N + 2) * u + 2 * u * u' + u))
    (hB : (u * (N + 2) - u % 2 * (N + 2) - 2 * u + 2) * (u' + 1) ≥ 2 * u * (u' * u' + (N + 2))) :
    Settled7 N u (N + 1 - u') := by
  set M := N + 2 with hM
  set a := u / 2 with ha
  set T := a * M with hT
  have h2a : 2 * a = u - u % 2 := by omega
  have h2T : 2 * T = (u - u % 2) * M := by rw [hT, ← Nat.mul_assoc, h2a]
  set S2 := T / u with hS2
  set S1 := (T + 1 + u) / (u + 1) with hS1
  -- floor facts
  have fS2 : T < u * (S2 + 1) := Nat.lt_mul_div_succ T (by omega)
  have fS2' : S2 * u ≤ T := Nat.div_mul_le_self T u
  have fS1 : S1 * (u + 1) ≤ T + 1 + u := Nat.div_mul_le_self _ _
  have fS1' : T + 1 + u < (u + 1) * (S1 + 1) := Nat.lt_mul_div_succ _ (by omega)
  have hS2M : 2 * S2 ≤ M := by
    have : 2 * S2 * u ≤ M * u := by
      calc 2 * S2 * u = 2 * (S2 * u) := by ring
        _ ≤ 2 * T := by omega
        _ = (u - u % 2) * M := h2T
        _ ≤ u * M := Nat.mul_le_mul_right _ (by omega)
        _ = M * u := by ring
    exact Nat.le_of_mul_le_mul_right this (by omega)
  -- (i) S1 u' + M ≤ S2 (u' + 1)
  have key1 : S1 * u' + M ≤ S2 * (u' + 1) := by
    have hA' : T * (u + u' + 1) * 2 ≥ 2 * (u + 1) * (M * u + 2 * u * u' + u) := by
      have : 2 * T * (u + u' + 1) = (u - u % 2) * M * (u + u' + 1) := by rw [h2T]
      nlinarith
    -- multiply the goal by u (u + 1)
    have hu1 : 0 < u * (u + 1) := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hu1
    have g1 : u * (u + 1) * (S1 * u' + M) ≤ u * u' * (T + 1 + u) + u * (u + 1) * M := by
      have e : u * (u + 1) * (S1 * u' + M) = u * u' * (S1 * (u + 1)) + u * (u + 1) * M := by ring
      have := Nat.mul_le_mul_left (u * u') fS1
      omega
    have g2 : (u + 1) * (u' + 1) * (T + 1 - u) ≤ u * (u + 1) * (S2 * (u' + 1)) := by
      have : T + 1 - u ≤ u * S2 := by
        have : u * (S2 + 1) = u * S2 + u := by ring
        omega
      calc (u + 1) * (u' + 1) * (T + 1 - u) ≤ (u + 1) * (u' + 1) * (u * S2) :=
            Nat.mul_le_mul_left _ this
        _ = u * (u + 1) * (S2 * (u' + 1)) := by ring
    have hTu : u ≤ T + 1 := by
      have h2 : 2 ≤ a := by omega
      have : 2 * M ≤ a * M := Nat.mul_le_mul_right _ h2
      omega
    have g3 : u * u' * (T + 1 + u) + u * (u + 1) * M ≤ (u + 1) * (u' + 1) * (T + 1 - u) := by
      zify [hTu] at hA' ⊢
      nlinarith
    omega
  -- (ii) u'² + M ≤ S2 (u' + 1)
  have key2 : u' * u' + M ≤ S2 * (u' + 1) := by
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 2 * u by omega)
    have g1 : (2 * T + 2 - 2 * u) * (u' + 1) ≤ 2 * u * (S2 * (u' + 1)) := by
      have : 2 * T + 2 - 2 * u ≤ 2 * (u * S2) := by
        have : u * (S2 + 1) = u * S2 + u := by ring
        omega
      calc (2 * T + 2 - 2 * u) * (u' + 1) ≤ 2 * (u * S2) * (u' + 1) :=
            Nat.mul_le_mul_right _ this
        _ = 2 * u * (S2 * (u' + 1)) := by ring
    have : 2 * T + 2 - 2 * u = u * M - u % 2 * M - 2 * u + 2 := by
      have e : (u - u % 2) * M = u * M - u % 2 * M := Nat.sub_mul _ _ _
      have h2 : 2 ≤ a := by omega
      have : 2 * M ≤ a * M := Nat.mul_le_mul_right _ h2
      rw [← e, ← h2T]; omega
    rw [this] at g1
    exact le_trans hB g1
  -- apply the direct lemma with s₁ = max S1 u', s₂ = S2
  have e2 : S2 * (u' + 1) = S2 * u' + S2 := by ring
  have hmax : max S1 u' * u' + M ≤ S2 * u' + S2 := by
    rcases le_total S1 u' with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  have h12 : max S1 u' ≤ S2 := by
    by_contra hc
    push Not at hc
    have h3 := Nat.mul_le_mul_right u' (show S2 + 1 ≤ max S1 u' from hc)
    have e3 : (S2 + 1) * u' = S2 * u' + u' := by ring
    omega
  refine settled_directZ (a := a) (s₁ := max S1 u') (s₂ := S2) (by omega) (by omega) huu
    (by omega) (le_max_right _ _) h12 (by omega) fS2' ?_ (by omega)
  calc T + 1 ≤ S1 * (u + 1) := by
        have : (u + 1) * (S1 + 1) = S1 * (u + 1) + u + 1 := by ring
        omega
    _ ≤ max S1 u' * (u + 1) := Nat.mul_le_mul_right _ (le_max_left _ _)

/-! ## An explicit family: `N` even, `u` and `u' = N + 1 - v` even -/

/-- `Z(N, N/2 - 1)` (`N` even) is `{2k : k < N/4} ∪ {2k + 1 : N/4 ≤ k < N/2}`: every pair
(`u` even `< N/2`, `v` odd `> N/2`) with `(u, v) ≠ (2, N - 1)` is settled; `(2, N - 1)` is a
corner of `Z(N, p)`, `p ∈ {N/2 - 1, N/2 - 2}` odd. -/
theorem settled_evenEven {N u v : Nat} (hN : 20 ≤ N) (hNe : N % 2 = 0) (hu : 1 ≤ u)
    (hue : u % 2 = 0) (hve : v % 2 = 1) (hu2 : 2 * u < N) (hv2 : N < 2 * v) (hvN : v + 1 ≤ N) :
    Settled7 N u v := by
  obtain ⟨q, rfl⟩ : ∃ q, N = 2 * q := ⟨N / 2, by omega⟩
  by_cases hc : u = 2 ∧ v = 2 * q - 1
  · obtain ⟨rfl, rfl⟩ := hc
    -- corner: Z(N, p), p odd, 2(p + 1) < N + 2 < 3(p + 1)
    obtain ⟨p, hp1, hp2, hpo, hp7⟩ : ∃ p, p < q ∧ 2 * q + 2 < 3 * (p + 1) ∧ p % 2 = 1 ∧ p ≠ 7 :=
      if h : q % 2 = 0 then ⟨q - 1, by omega, by omega, by omega, by omega⟩
      else ⟨q - 2, by omega, by omega, by omega, by omega⟩
    obtain ⟨e1, e2⟩ := zF_corner (N := 2 * q) (p := p) (c := 2) (by omega) (by omega)
    refine settled7_z (p := p) (a := 1) (b := p) (by omega) (by omega) le_rfl (by omega) le_rfl
      (deadB_false_odd hpo hp7) e1 ?_
    rw [e2]; omega
  · -- the copy Z(2q, q - 1): zF k = 2k + ⌊2k/q⌋
    have hz : ∀ k, k < q → zF (2 * q) (q - 1) k = 2 * k + 2 * k / q := by
      intro k hk
      unfold zF beatty
      rw [Nat.sub_zero, show q - 1 + 1 = q by omega]
      have e : k * (2 * q + 2) = (2 * k) * q + 2 * k := by ring
      rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega)]
      ring
    have ha := hz (u / 2) (by omega)
    have hb := hz ((v - 1) / 2) (by omega)
    rw [show 2 * (u / 2) / q = 0 from Nat.div_eq_of_lt (by omega)] at ha
    rw [show 2 * ((v - 1) / 2) / q = 1 from Nat.div_eq_of_lt_le (by omega) (by omega)] at hb
    refine settled7_z (p := q - 1) (a := u / 2) (b := (v - 1) / 2) (by omega) (by omega)
      (by omega) (by omega) (by omega) ?_ (by rw [ha]; omega) (by rw [hb]; omega)
    unfold deadB
    simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    omega

end Live8
end Folds
