import Folds.Live8

/-!
# The arithmetic covering statement `ArithCover`: witnesses, sliding lemmas, proven regions

`experiments/arithcover/PROOFS.txt`.
-/

namespace Folds
namespace ArithCover

open Live8

/-! ## Witnesses for `dirOK` -/

/-- Position-free form of `dirOK`: an `s`-range `[s₁, s₂]` inside the true range, whose union
of windows has at least `K` elements. -/
theorem dirOK_of_slide {K L R α β smax a s₁ s₂ : Nat} (hK : 0 < K) (hL : 1 ≤ L)
    (hs : 2 ≤ s₁) (hRs : R ≤ s₁) (h12 : s₁ ≤ s₂) (hsm : s₂ ≤ smax)
    (h1 : s₂ * L + α ≤ a * K) (h2 : a * K + 1 ≤ s₁ * (L + 1) + α)
    (hlen : s₁ * R + β + K ≤ s₂ * R + β + s₂) : dirOK K L R α β smax a = true := by
  unfold dirOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hS2 : s₂ ≤ min ((a * K - α) / L) smax := by
    refine le_min ?_ hsm
    rw [Nat.le_div_iff_mul_le hL]; omega
  have hS1 : max (max ((a * K - α + 1 + L) / (L + 1)) R) 2 ≤ s₁ := by
    refine max_le (max_le ?_ hRs) hs
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    have : (L + 1) * s₁ = s₁ * (L + 1) := Nat.mul_comm _ _
    omega
  refine ⟨le_trans hS1 (le_trans h12 hS2), ?_⟩
  set S1 := max (max ((a * K - α + 1 + L) / (L + 1)) R) 2 with hS1d
  set S2 := min ((a * K - α) / L) smax with hS2d
  set hi := S2 * R + β + S2 - 1 with hhi
  have e := Nat.div_add_mod hi K
  have hm := Nat.mod_lt hi hK
  have a1 : S1 * R ≤ s₁ * R := Nat.mul_le_mul_right _ hS1
  have a2 : s₂ * R ≤ S2 * R := Nat.mul_le_mul_right _ hS2
  have : hi / K * K = K * (hi / K) := Nat.mul_comm _ _
  omega

/-- A single witness `s` (with left index `a` and right distance `c`) makes `dirOK` true. -/
theorem dirOK_of_wit {K L R α β smax a s c : Nat} (hK : 0 < K) (hL : 1 ≤ L)
    (hs : 2 ≤ s) (hRs : R ≤ s) (hsm : s ≤ smax)
    (h1 : s * L + α ≤ a * K) (h2 : a * K + 1 ≤ s * (L + 1) + α)
    (h3 : s * R + β ≤ c * K) (h4 : c * K + 1 ≤ s * R + β + s) :
    dirOK K L R α β smax a = true := by
  unfold dirOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hS2 : s ≤ min ((a * K - α) / L) smax := by
    refine le_min ?_ hsm
    rw [Nat.le_div_iff_mul_le hL]; omega
  have hS1 : max (max ((a * K - α + 1 + L) / (L + 1)) R) 2 ≤ s := by
    refine max_le (max_le ?_ hRs) hs
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    have : (L + 1) * s = s * (L + 1) := Nat.mul_comm _ _
    omega
  refine ⟨le_trans hS1 hS2, ?_⟩
  set S1 := max (max ((a * K - α + 1 + L) / (L + 1)) R) 2 with hS1d
  set S2 := min ((a * K - α) / L) smax with hS2d
  have a1 : S1 * R ≤ s * R := Nat.mul_le_mul_right _ hS1
  have a2 : s * R ≤ S2 * R := Nat.mul_le_mul_right _ hS2
  have hc : c ≤ (S2 * R + β + S2 - 1) / K := by
    rw [Nat.le_div_iff_mul_le hK]; omega
  have := Nat.mul_le_mul_right K hc
  omega

/-! ## From `dirAll` to `dirAny` -/

theorem dirAny_of_dirAll {N x y a : Nat} (ha : 1 ≤ a) (hax : a ≤ x + 1)
    (h : dirAll N x y a = true) : dirAny N x y = true := by
  unfold dirAny
  rw [List.any_eq_true]
  exact ⟨a, by rw [List.mem_range'_1]; omega, h⟩

theorem dirAll_Z {N x y a : Nat} (ha : 2 ≤ a)
    (h : dirOK (N + 2) x y 0 1 ((N + 2) / 2) a = true) : dirAll N x y a = true := by
  unfold dirAll
  simp only [show ¬ a = 1 by omega, ↓reduceIte, h, Bool.true_or]

theorem dirAll_X0 {N x y a : Nat} (hy : 2 ≤ y)
    (h : dirOK N x (y - 2) 0 1 ((N + 1) / 2) a = true) : dirAll N x y a = true := by
  unfold dirAll
  split_ifs <;> simp [h, hy]

theorem dirAll_X1 {N x y a : Nat} (ha : 2 ≤ a) (hy : 2 ≤ y)
    (h : dirOK N x (y - 2) 1 0 (N / 2) a = true) : dirAll N x y a = true := by
  unfold dirAll
  simp only [show ¬ a = 1 by omega, ↓reduceIte, h, hy, decide_true, Bool.and_true, Bool.or_true]

/-- A witness in the family `Z` (modulus `M = N + 2`) gives `dirAny`. -/
theorem dirAny_of_witZ {N x y a s c : Nat} (hx : 1 ≤ x) (ha : 2 ≤ a) (hs : 2 ≤ s)
    (hRs : y ≤ s) (hsm : 2 * s ≤ N + 2)
    (h1 : s * x ≤ a * (N + 2)) (h2 : a * (N + 2) + 1 ≤ s * (x + 1))
    (h3 : s * y + 1 ≤ c * (N + 2)) (h4 : c * (N + 2) + 1 ≤ s * y + 1 + s) :
    dirAny N x y = true := by
  have hax : a ≤ x + 1 := by
    by_contra hc
    push Not at hc
    have : (x + 2) * (N + 2) ≤ a * (N + 2) := Nat.mul_le_mul_right _ hc
    have : 2 * (s * (x + 1)) ≤ (N + 2) * (x + 1) := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hsm
    nlinarith
  refine dirAny_of_dirAll (a := a) (by omega) hax (dirAll_Z ha ?_)
  exact dirOK_of_wit (s := s) (c := c) (by omega) hx hs hRs (by omega) (by omega) (by omega)
    (by omega) (by omega)

/-! ## Theorem B: the two-class slide (near the inward boundary, orientation `(u', u)`, `Z`)

With `2x + n = M = N + 2` (`x = u'`, `n = M - 2u'` small), for a denominator `s` and
`t = s - 2a`: `2(aM - sx) = sn - tM`.  So `x` is the `a`-th element of `Z(N, s - 1)` iff some
`t ≡ s (mod 2)` has `tM ∈ [s(n - 2) + 2, sn]`.  For `s` of a fixed parity these windows move by
`2(n - 2)` resp. `2n` and overlap as soon as `s ≥ n - 1`; the unions for the two parities share
`[(s₁ + 1)(n - 2) + 2, (s₂ - 1)n]`, so a multiple `tM` there (of either parity) is caught. -/

/-- The parity slide: some `s ≡ t (mod 2)` in `[s₁, s₂]` has `T ∈ [s(n-2) + 2, sn]`. -/
theorem parity_slide {n s₁ s₂ t T : Nat} (hn : 3 ≤ n) (hs1n : n ≤ s₁ + 1) (h12 : s₁ + 1 ≤ s₂)
    (hT1 : (s₁ + 1) * (n - 2) + 2 ≤ T) (hT2 : T ≤ (s₂ - 1) * n) :
    ∃ s, s₁ ≤ s ∧ s ≤ s₂ ∧ s % 2 = t % 2 ∧ s * (n - 2) + 2 ≤ T ∧ T ≤ s * n := by
  obtain ⟨P, rfl⟩ : ∃ P, n = P + 2 := ⟨n - 2, by omega⟩
  simp only [Nat.add_sub_cancel] at hT1 ⊢
  set s₀ := if s₁ % 2 = t % 2 then s₁ else s₁ + 1 with hs₀
  have h0a : s₁ ≤ s₀ := by rw [hs₀]; split_ifs <;> omega
  have h0b : s₀ ≤ s₁ + 1 := by rw [hs₀]; split_ifs <;> omega
  have h0c : s₀ % 2 = t % 2 := by rw [hs₀]; split_ifs <;> omega
  have h0d : s₀ * P + 2 ≤ T := le_trans (by nlinarith) hT1
  set k := min ((T - (s₀ * P + 2)) / (2 * P)) ((s₂ - s₀) / 2) with hk
  have hP : 0 < P := by omega
  refine ⟨s₀ + 2 * k, by omega, ?_, ?_, ?_, ?_⟩
  · have := min_le_right ((T - (s₀ * P + 2)) / (2 * P)) ((s₂ - s₀) / 2)
    omega
  · omega
  · have h1 := min_le_left ((T - (s₀ * P + 2)) / (2 * P)) ((s₂ - s₀) / 2)
    have h2 : k * (2 * P) ≤ T - (s₀ * P + 2) :=
      le_trans (Nat.mul_le_mul_right _ h1) (Nat.div_mul_le_self _ _)
    have e : (s₀ + 2 * k) * P = s₀ * P + k * (2 * P) := by ring
    omega
  · rcases min_cases ((T - (s₀ * P + 2)) / (2 * P)) ((s₂ - s₀) / 2) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [← hk] at h1
      have h2 := Nat.lt_mul_div_succ (T - (s₀ * P + 2)) (show 0 < 2 * P by omega)
      rw [← h1] at h2
      have e1 : 2 * P * (k + 1) = k * (2 * P) + 2 * P := by ring
      have e2 : (s₀ + 2 * k) * (P + 2) = (s₀ + 2 * k) * P + 2 * (s₀ + 2 * k) := by ring
      have e3 : (s₀ + 2 * k) * P = s₀ * P + k * (2 * P) := by ring
      omega
    · rw [← hk] at h1
      have : s₂ - 1 ≤ s₀ + 2 * k := by omega
      exact le_trans hT2 (Nat.mul_le_mul_right _ this)

/-- **Theorem B (abstract form).**  `x = u'`, `y = u`, `2x + n = N + 2`, right distance `c`
fixed (the denominators `s ∈ [s₁, s₂]` all have `y` at distance `c` from the end). -/
theorem dirAny_twoClass {N x y c n s₁ s₂ t : Nat} (hn : 2 * x + n = N + 2) (hn3 : 3 ≤ n)
    (hx : 1 ≤ x) (hs1n : n ≤ s₁ + 1) (hs1y : y ≤ s₁) (h12 : s₁ + 1 ≤ s₂)
    (hs2 : 2 * s₂ ≤ N + 2)
    (hc1 : c * (N + 2) ≤ s₁ * (y + 1)) (hc2 : s₂ * y + 1 ≤ c * (N + 2))
    (ht1 : (s₁ + 1) * (n - 2) + 2 ≤ t * (N + 2)) (ht2 : t * (N + 2) ≤ (s₂ - 1) * n)
    (ha : 2 * (N + 2) ≤ s₁ * x) : dirAny N x y = true := by
  obtain ⟨s, hs1, hs2', hst, hw1, hw2⟩ :=
    parity_slide (t := t) hn3 hs1n h12 ht1 ht2
  set M := N + 2 with hM
  -- a = (s - t)/2
  have hsx : 2 * M ≤ s * x := le_trans ha (Nat.mul_le_mul_right _ hs1)
  have hsn : s * n + 2 * (s * x) = s * M := by rw [← hn]; ring
  have hts : t + 4 ≤ s := by
    by_contra hcon
    push Not at hcon
    have : s * M ≤ (t + 3) * M := Nat.mul_le_mul_right _ (by omega)
    have e : (t + 3) * M = t * M + 3 * M := by ring
    omega
  obtain ⟨a, ha'⟩ : ∃ a, s = t + 2 * a := ⟨(s - t) / 2, by omega⟩
  have hs2'' : 2 ≤ s := by omega
  have hP : s * (n - 2) + 2 * s = s * n := by
    have h : n = (n - 2) + 2 := by omega
    conv_rhs => rw [h]
    ring
  have e1 : s * M = t * M + 2 * (a * M) := by rw [ha']; ring
  refine dirAny_of_witZ (a := a) (s := s) (c := c) hx (by omega) hs2'' (by omega) (by omega)
    ?_ ?_ ?_ ?_
  · -- s x ≤ a M  ⇔  t M ≤ s n
    show s * x ≤ a * M
    omega
  · -- a M + 1 ≤ s (x + 1)  ⇔  s (n - 2) + 2 ≤ t M
    show a * M + 1 ≤ s * (x + 1)
    have : s * (x + 1) = s * x + s := by ring
    omega
  · show s * y + 1 ≤ c * M
    have : s * y ≤ s₂ * y := Nat.mul_le_mul_right _ hs2'
    omega
  · show c * M + 1 ≤ s * y + 1 + s
    have : s₁ * (y + 1) ≤ s * (y + 1) := Nat.mul_le_mul_right _ hs1
    have e : s * (y + 1) = s * y + s := by ring
    omega


theorem regionB_len {u P s₁ s₂ T M : Nat} (hTu : u ≤ T) (f2 : s₁ * (u + 1) ≤ T + u)
    (f4 : T - u ≤ s₂ * u)
    (hB3 : u * ((2 * u + 1) * (P + 2) - 2 * u) + u * (u + 1) * (2 * (P + 2) + M - 1) ≤
      T * (P + 2 + 2 * u)) :
    u * (u + 1) * (s₁ * P + M + 2 * (P + 2)) ≤ u * (u + 1) * (s₂ * (P + 2) + 1) := by
  have g1 : u * (u + 1) * (s₁ * P) ≤ u * P * (T + u) := by
    calc u * (u + 1) * (s₁ * P) = u * P * (s₁ * (u + 1)) := by ring
      _ ≤ u * P * (T + u) := Nat.mul_le_mul_left _ f2
  have g2 : (u + 1) * (P + 2) * (T - u) ≤ u * (u + 1) * (s₂ * (P + 2)) := by
    calc (u + 1) * (P + 2) * (T - u) ≤ (u + 1) * (P + 2) * (s₂ * u) := Nat.mul_le_mul_left _ f4
      _ = u * (u + 1) * (s₂ * (P + 2)) := by ring
  have h1 : 2 * u ≤ (2 * u + 1) * (P + 2) := by nlinarith
  have h2 : 1 ≤ 2 * (P + 2) + M := by omega
  zify [hTu, h1, h2] at g1 g2 hB3 ⊢
  linarith

/-- **Theorem B (region form).**  `c = ⌊u/2⌋`, `n = M - 2u'` (`M = N + 2`): under four
polynomial conditions the pair passes `dirAny` in the orientation `(u', u)` (family `Z`). -/
theorem dirAny_regionB {N u u' n : Nat} (hu : 3 ≤ u) (hn : 2 * u' + n = N + 2) (hn3 : 3 ≤ n)
    (hB1 : (u + 1) * (n - 1) ≤ u / 2 * (N + 2))
    (hB2 : u * (u + 1) ≤ u / 2 * (N + 2))
    (hB3 : u * ((2 * u + 1) * n - 2 * u) + u * (u + 1) * (2 * n + (N + 2) - 1) ≤
      u / 2 * (N + 2) * (n + 2 * u))
    (hB4 : 2 * (u + 1) ≤ u / 2 * u') : dirAny N u' u = true := by
  have hu' : 1 ≤ u' := Nat.pos_of_ne_zero (by rintro rfl; simp at hB4)
  set c := u / 2 with hc
  set M := N + 2 with hM
  set T := c * M with hT
  have hc2 : 2 * c ≤ u := by omega
  have hcpos : 1 ≤ c := by omega
  have hTpos : 1 ≤ T := Nat.one_le_iff_ne_zero.2 (by positivity)
  set s₁ := (T + u) / (u + 1) with hs₁
  set s₂ := (T - 1) / u with hs₂
  have f1 : T ≤ s₁ * (u + 1) := by
    have := Nat.lt_mul_div_succ (T + u) (show 0 < u + 1 by omega)
    rw [← hs₁] at this
    have e : (u + 1) * (s₁ + 1) = s₁ * (u + 1) + u + 1 := by ring
    omega
  have f2 : s₁ * (u + 1) ≤ T + u := Nat.div_mul_le_self _ _
  have f3 : s₂ * u ≤ T - 1 := Nat.div_mul_le_self _ _
  have f4 : T - u ≤ s₂ * u := by
    have := Nat.lt_mul_div_succ (T - 1) (show 0 < u by omega)
    rw [← hs₂] at this
    have e : u * (s₂ + 1) = s₂ * u + u := by ring
    omega
  have hs1n : n ≤ s₁ + 1 := by
    have : (n - 1) * (u + 1) ≤ s₁ * (u + 1) := by
      have : (n - 1) * (u + 1) = (u + 1) * (n - 1) := Nat.mul_comm _ _
      omega
    have := Nat.le_of_mul_le_mul_right this (by omega)
    omega
  have hs1u : u ≤ s₁ := by
    have : u * (u + 1) ≤ s₁ * (u + 1) := le_trans hB2 f1
    exact Nat.le_of_mul_le_mul_right this (by omega)
  have hs2M : 2 * s₂ ≤ M := by
    have : 2 * s₂ * u < M * u := by
      have : M * u ≥ 2 * c * M := by
        calc M * u ≥ M * (2 * c) := Nat.mul_le_mul_left _ hc2
          _ = 2 * c * M := by ring
      have e : 2 * s₂ * u = 2 * (s₂ * u) := by ring
      have e2 : 2 * c * M = 2 * T := by rw [hT]; ring
      omega
    exact le_of_lt (Nat.lt_of_mul_lt_mul_right this)
  have ha : 2 * M ≤ s₁ * u' := by
    have h1 : (u + 1) * (2 * M) ≤ T * u' := by
      calc (u + 1) * (2 * M) = 2 * (u + 1) * M := by ring
        _ ≤ c * u' * M := Nat.mul_le_mul_right _ hB4
        _ = T * u' := by rw [hT]; ring
    have h2 : T * u' ≤ s₁ * (u + 1) * u' := Nat.mul_le_mul_right _ f1
    have h3 : (u + 1) * (2 * M) ≤ (u + 1) * (s₁ * u') := by
      have : s₁ * (u + 1) * u' = (u + 1) * (s₁ * u') := by ring
      omega
    exact Nat.le_of_mul_le_mul_left h3 (by omega)
  -- the length: s₂ n - s₁ (n - 2) ≥ M + 2n - 1
  obtain ⟨P, hP⟩ : ∃ P, n = P + 2 := ⟨n - 2, by omega⟩
  have hlen : s₁ * P + M + 2 * n ≤ s₂ * n + 1 := by
    have hTu : u ≤ T := by
      have : u ≤ u * (u + 1) := Nat.le_mul_of_pos_right u (by omega)
      omega
    have key := regionB_len (s₁ := s₁) (s₂ := s₂) (T := T) (M := M) hTu f2 f4
      (by rw [hT, ← hP]; exact hB3)
    rw [← hP] at key
    exact Nat.le_of_mul_le_mul_left key (by positivity)
  have h12 : s₁ + 1 ≤ s₂ := by
    by_contra hcon
    push Not at hcon
    have : s₂ * n ≤ s₁ * n := Nat.mul_le_mul_right _ (by omega)
    have e : s₁ * n = s₁ * P + 2 * s₁ := by rw [hP]; ring
    have : 2 * s₁ ≤ M + 1 := by
      have : 2 * s₁ * (u + 1) ≤ (M + 1) * (u + 1) := by
        have e2 : 2 * c * M = 2 * T := by rw [hT]; ring
        have : 2 * c * M ≤ u * M := Nat.mul_le_mul_right _ hc2
        nlinarith
      exact Nat.le_of_mul_le_mul_right this (by omega)
    omega
  set A := (s₁ + 1) * (n - 2) + 2 with hA
  set t := (A + M - 1) / M with ht
  have ht1 : A ≤ t * M := by
    have := Nat.lt_mul_div_succ (A + M - 1) (show 0 < M by omega)
    rw [← ht] at this
    have e : M * (t + 1) = t * M + M := by ring
    omega
  have ht2 : t * M ≤ (s₂ - 1) * n := by
    have h1 : t * M ≤ A + M - 1 := Nat.div_mul_le_self _ _
    have e1 : (s₂ - 1) * n + n = s₂ * n := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    have e2 : A = s₁ * P + P + 2 := by rw [hA, hP]; simp only [Nat.add_sub_cancel]; ring
    omega
  exact dirAny_twoClass (c := c) (n := n) (s₁ := s₁) (s₂ := s₂) (t := t) hn hn3 hu' hs1n
    hs1u h12 hs2M f1 (by show s₂ * u + 1 ≤ T; omega) ht1 ht2 ha

end ArithCover
end Folds
