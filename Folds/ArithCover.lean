import Folds.Live8

/-!
# The arithmetic covering statement `ArithCover`: witnesses, sliding lemmas, proven regions

`experiments/arithcover/PROOFS.txt`.

* `dirOK_of_wit`, `dirOK_of_slide`, `dirOK_of_cover`, `dirOK_direct`: sufficient conditions for
  `Live8.dirOK` (with `Live8.dirOK_spec`: `dirOK` is exactly the existence of a witness `s`).
* `parity_slide`, `dirAny_twoClass`, `dirAny_regionB`: **Theorem B** (two-class slide near the
  inward boundary, orientation `(u', u)`, family `Z`, right distance `c = ⌊u/2⌋`).
* `dirAny_nearBoundary`: every pair with `3 ≤ u ≤ √N`, `8u' ≥ 3N + 2` (`N ≥ 301`, not special)
  passes `dirAny` — this contains the residual family of `Live8` section 4(d).
* Regions `RegionB`, `RegionB2`, `RegionD`, `RegionD0`, `RegionW` (`Proven`), `covered_of_proven`;
  `dirAny_diff` (difference lemma, `Q = P = 1`).
* `arithCover_of_residual`, `conjectureC_of_residual`: Conjecture C for all `N` follows from
  `Residual N` (`ArithCover N` for the pairs outside `Proven`) for `N > 300`.  `Residual` is
  **not** proven (about 40% of the mixed wide pairs: the wedge and corner with `u ≳ √N`).
-/

namespace Folds
namespace ArithCover

open Live2 Live8

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


/-- `dirOK` from an `s`-range inside the true range and a multiple `cK` inside the union of its
windows. -/
theorem dirOK_of_cover {K L R α β smax a s₁ s₂ c : Nat} (hK : 0 < K) (hL : 1 ≤ L)
    (hs : 2 ≤ s₁) (hRs : R ≤ s₁) (h12 : s₁ ≤ s₂) (hsm : s₂ ≤ smax)
    (h1 : s₂ * L + α ≤ a * K) (h2 : a * K + 1 ≤ s₁ * (L + 1) + α)
    (hc1 : s₁ * R + β ≤ c * K) (hc2 : c * K + 1 ≤ s₂ * R + β + s₂) :
    dirOK K L R α β smax a = true := by
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
  have a1 : S1 * R ≤ s₁ * R := Nat.mul_le_mul_right _ hS1
  have a2 : s₂ * R ≤ S2 * R := Nat.mul_le_mul_right _ hS2
  have hc : c ≤ (S2 * R + β + S2 - 1) / K := by
    rw [Nat.le_div_iff_mul_le hK]; omega
  have := Nat.mul_le_mul_right K hc
  omega

/-- **The direct lemma with polynomial hypotheses** (`α = 0`, index `a`, `T = aK`):
`hA` covers the branch `s₁ = ⌈(T + 1)/(L + 1)⌉`, `hB` the branch `s₁ = R`. -/
theorem dirOK_direct {K L R β smax a : Nat} (hK : 0 < K) (hL : 1 ≤ L) (hR : 2 ≤ R)
    (hT : L ≤ a * K + 1) (hsm : a * K / L ≤ smax) (hsmK : smax ≤ K)
    (hA : L * (a * K + 1 + L) * R + L * (L + 1) * K ≤ (L + 1) * (a * K + 1 - L) * (R + 1))
    (hB : L * (R * R + K) ≤ (a * K + 1 - L) * (R + 1)) :
    dirOK K L R 0 β smax a = true := by
  set T := a * K with hTd
  set S2 := T / L with hS2
  set S1 := (T + 1 + L) / (L + 1) with hS1
  have fS2 : T < L * (S2 + 1) := Nat.lt_mul_div_succ T (by omega)
  have fS2' : S2 * L ≤ T := Nat.div_mul_le_self T L
  have fS1 : S1 * (L + 1) ≤ T + 1 + L := Nat.div_mul_le_self _ _
  have fS1' : T + 1 + L < (L + 1) * (S1 + 1) := Nat.lt_mul_div_succ _ (by omega)
  have g2 : T + 1 - L ≤ L * S2 := by
    have : L * (S2 + 1) = L * S2 + L := by ring
    omega
  -- branch A: S1 * R + K ≤ S2 * (R + 1)
  have key1 : S1 * R + K ≤ S2 * (R + 1) := by
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < L * (L + 1) by positivity)
    calc L * (L + 1) * (S1 * R + K) = L * R * (S1 * (L + 1)) + L * (L + 1) * K := by ring
      _ ≤ L * R * (T + 1 + L) + L * (L + 1) * K := by
          have := Nat.mul_le_mul_left (L * R) fS1; omega
      _ = L * (T + 1 + L) * R + L * (L + 1) * K := by ring
      _ ≤ (L + 1) * (T + 1 - L) * (R + 1) := hA
      _ ≤ (L + 1) * (L * S2) * (R + 1) := by
          apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_left _ g2
      _ = L * (L + 1) * (S2 * (R + 1)) := by ring
  -- branch B: R * R + K ≤ S2 * (R + 1)
  have key2 : R * R + K ≤ S2 * (R + 1) := by
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < L by omega)
    calc L * (R * R + K) ≤ (T + 1 - L) * (R + 1) := hB
      _ ≤ L * S2 * (R + 1) := Nat.mul_le_mul_right _ g2
      _ = L * (S2 * (R + 1)) := by ring
  have e2 : S2 * (R + 1) = S2 * R + S2 := by ring
  have hmax : max S1 R * R + β + K ≤ S2 * R + β + S2 := by
    rcases le_total S1 R with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  have h12 : max S1 R ≤ S2 := by
    by_contra hc
    push Not at hc
    have h3 := Nat.mul_le_mul_right R (show S2 + 1 ≤ max S1 R from hc)
    have e3 : (S2 + 1) * R = S2 * R + R := by ring
    have := le_trans hsm hsmK
    omega
  have hS1u : T + 1 ≤ max S1 R * (L + 1) := by
    calc T + 1 ≤ S1 * (L + 1) := by
          have : (L + 1) * (S1 + 1) = S1 * (L + 1) + L + 1 := by ring
          omega
      _ ≤ max S1 R * (L + 1) := Nat.mul_le_mul_right _ (le_max_left _ _)
  exact dirOK_of_slide (s₁ := max S1 R) (s₂ := S2) hK hL (le_trans hR (le_max_right _ _))
    (le_max_right _ _) h12 hsm (by simpa using fS2') (by simpa using hS1u) hmax

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

/-- **Region D** (`Live8.settled_directZ_region`, as a `dirAny` statement): orientation
`(u, u')`, family `Z`, `a = ⌊u/2⌋`. -/
theorem dirAny_regionD {N u u' : Nat} (hu : 4 ≤ u) (huu' : u ≤ u') (huu : u + u' ≤ N)
    (hA : (u - u % 2) * (N + 2) * (u + u' + 1) ≥ 2 * (u + 1) * ((N + 2) * u + 2 * u * u' + u))
    (hB : (u * (N + 2) - u % 2 * (N + 2) - 2 * u + 2) * (u' + 1) ≥ 2 * u * (u' * u' + (N + 2))) :
    dirAny N u u' = true := by
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
  have hmax' : max S1 u' * u' + 1 + M ≤ S2 * u' + 1 + S2 := by omega
  have hS1u : T + 1 ≤ max S1 u' * (u + 1) := by
    calc T + 1 ≤ S1 * (u + 1) := by
          have : (u + 1) * (S1 + 1) = S1 * (u + 1) + u + 1 := by ring
          omega
      _ ≤ max S1 u' * (u + 1) := Nat.mul_le_mul_right _ (le_max_left _ _)
  refine dirAny_of_dirAll (a := a) (by omega) (by omega) (dirAll_Z (by omega) ?_)
  exact dirOK_of_slide (s₁ := max S1 u') (s₂ := S2) (by omega) (by omega)
    (le_trans (by omega) (le_max_right _ _)) (le_max_right _ _) h12 (by omega)
    (by simpa using fS2') (by simpa using hS1u) hmax'

/-! ## The difference lemma (`Q = P = 1`, near the diagonal)

Orientation `(x, y)`, `y = x + d`, family `Z`: fix `j = c - a`; then
`Y - X = jM - sd - 1 =: D(s)` with `X = aM - sx`, `Y = cM - sy - 1`.  On an `s`-range where
`|D(s)| ≤ Δ` it suffices that `X ∈ [Δ, s - 1 - Δ]`, i.e. `aM ∈ [sx + Δ, sx + s - 1 - Δ]`; these
windows slide by `x` and overlap as soon as `s ≥ x + 2Δ`. -/

/-- Sliding windows of length `s - e`: `[sR + β, sR + β + s - 1 - e]`, contiguous for
`s ≥ R + e`. -/
theorem slideE {K R β e s₁ s₂ c : Nat} (hR : R + e ≤ s₁) (h12 : s₁ ≤ s₂)
    (hc1 : s₁ * R + β ≤ c * K) (hc2 : c * K + 1 + e ≤ s₂ * R + β + s₂) :
    ∃ s, s₁ ≤ s ∧ s ≤ s₂ ∧ s * R + β ≤ c * K ∧ c * K + 1 + e ≤ s * R + β + s := by
  rcases Nat.eq_zero_or_pos R with hR0 | hRp
  · subst hR0
    exact ⟨s₂, h12, le_rfl, by simp only [Nat.mul_zero, Nat.zero_add] at *; omega, hc2⟩
  · set s := min s₂ ((c * K - β) / R) with hs
    have hsR : s * R ≤ c * K - β := by
      calc s * R ≤ (c * K - β) / R * R := Nat.mul_le_mul_right _ (min_le_right _ _)
        _ ≤ c * K - β := Nat.div_mul_le_self _ _
    have hs1 : s₁ ≤ s := by
      refine le_min h12 ?_
      rw [Nat.le_div_iff_mul_le hRp]
      omega
    refine ⟨s, hs1, min_le_left _ _, by omega, ?_⟩
    by_cases hlt : s < s₂
    · have hs' : s = (c * K - β) / R := by
        rcases min_cases s₂ ((c * K - β) / R) with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [← hs] at h1; omega
        · rw [← hs] at h1; exact h1
      have := Nat.lt_mul_div_succ (c * K - β) hRp
      rw [← hs'] at this
      have e : R * (s + 1) = s * R + R := by ring
      omega
    · have hss : s = s₂ := le_antisymm (min_le_left _ _) (by omega)
      rw [hss]; exact hc2

/-- **The difference lemma** (`Z`, orientation `(x, y)`, `y = x + d`, fixed `j = c - a`). -/
theorem dirAny_diff {N x y d j Δ s₁ s₂ a : Nat} (hd : x + d = y) (hx : 1 ≤ x)
    (hs : 2 ≤ s₁) (hy : y ≤ s₁) (hcont : x + 2 * Δ ≤ s₁) (h12 : s₁ ≤ s₂)
    (hsm : 2 * s₂ ≤ N + 2) (hD1 : j * (N + 2) ≤ s₁ * d + 1 + Δ)
    (hD2 : s₂ * d + 1 ≤ j * (N + 2) + Δ) (ha1 : s₁ * x + Δ ≤ a * (N + 2))
    (ha2 : a * (N + 2) + 1 + 2 * Δ ≤ s₂ * x + Δ + s₂) (ha : 2 ≤ a) :
    dirAny N x y = true := by
  obtain ⟨s, hs1, hs2, hw1, hw2⟩ := slideE (K := N + 2) (R := x) (β := Δ) (e := 2 * Δ) (c := a)
    hcont h12 ha1 ha2
  have e1 : s * y = s * x + s * d := by rw [← hd]; ring
  have g1 : s₁ * d ≤ s * d := Nat.mul_le_mul_right _ hs1
  have g2 : s * d ≤ s₂ * d := Nat.mul_le_mul_right _ hs2
  have e2 : (a + j) * (N + 2) = a * (N + 2) + j * (N + 2) := by ring
  refine dirAny_of_witZ (a := a) (s := s) (c := a + j) hx ha (by omega) (by omega) (by omega)
    (by omega) (by have : s * (x + 1) = s * x + s := by ring
                   omega) (by omega) (by omega)


/-- **Region B2**: Theorem B with `s₁ = n - 1` (the contiguity is then automatic). -/
theorem dirAny_regionB2 {N u u' n : Nat} (hu : 3 ≤ u) (hn : 2 * u' + n = N + 2)
    (hn3 : u + 3 ≤ n)
    (hs : u / 2 * (N + 2) ≤ (n - 1) * (u + 1))
    (hlen : u * (n * (n - 2) + (N + 2) + 1) ≤ (u / 2 * (N + 2) - 2 * u) * n)
    (ha : 2 * (N + 2) ≤ (n - 1) * u') : dirAny N u' u = true := by
  have hu' : 1 ≤ u' := Nat.pos_of_ne_zero (by rintro rfl; simp at ha)
  set c := u / 2 with hc
  set M := N + 2 with hM
  set T := c * M with hT
  have hc2 : 2 * c ≤ u := by omega
  have hcpos : 1 ≤ c := by omega
  have hTpos : 1 ≤ T := Nat.one_le_iff_ne_zero.2 (by positivity)
  set s₂ := (T - 1) / u with hs₂
  have f3 : s₂ * u ≤ T - 1 := Nat.div_mul_le_self _ _
  have f4 : T - u ≤ s₂ * u := by
    have := Nat.lt_mul_div_succ (T - 1) (show 0 < u by omega)
    rw [← hs₂] at this
    have e : u * (s₂ + 1) = s₂ * u + u := by ring
    omega
  have hs2M : 2 * s₂ ≤ M := by
    have : 2 * s₂ * u < M * u := by
      have : M * u ≥ 2 * c * M := by
        calc M * u ≥ M * (2 * c) := Nat.mul_le_mul_left _ hc2
          _ = 2 * c * M := by ring
      have e : 2 * s₂ * u = 2 * (s₂ * u) := by ring
      have e2 : 2 * c * M = 2 * T := by rw [hT]; ring
      omega
    exact le_of_lt (Nat.lt_of_mul_lt_mul_right this)
  -- (s₂ - 1) n ≥ n (n - 2) + M + 1
  have hl : n * (n - 2) + M + 1 ≤ (s₂ - 1) * n := by
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < u by omega)
    calc u * (n * (n - 2) + M + 1) ≤ (T - 2 * u) * n := hlen
      _ ≤ (u * (s₂ - 1)) * n := by
          apply Nat.mul_le_mul_right
          have hTM : M ≤ T := Nat.le_mul_of_pos_left M hcpos
          have hs2pos : 1 ≤ s₂ := by
            by_contra h
            push Not at h
            have h0 : s₂ = 0 := by omega
            rw [h0] at f4
            omega
          have : u * (s₂ - 1) + u = s₂ * u := by
            have h5 := Nat.sub_add_cancel hs2pos
            calc u * (s₂ - 1) + u = u * (s₂ - 1 + 1) := by ring
              _ = u * s₂ := by rw [h5]
              _ = s₂ * u := by ring
          omega
      _ = u * ((s₂ - 1) * n) := by ring
  have h12 : n - 1 + 1 ≤ s₂ := by
    by_contra hcon
    push Not at hcon
    have : (s₂ - 1) * n ≤ (n - 2) * n := Nat.mul_le_mul_right _ (by omega)
    have e : n * (n - 2) = (n - 2) * n := Nat.mul_comm _ _
    omega
  set A := (n - 1 + 1) * (n - 2) + 2 with hA
  set t := (A + M - 1) / M with ht
  have ht1 : A ≤ t * M := by
    have := Nat.lt_mul_div_succ (A + M - 1) (show 0 < M by omega)
    rw [← ht] at this
    have e : M * (t + 1) = t * M + M := by ring
    omega
  have ht2 : t * M ≤ (s₂ - 1) * n := by
    have h1 : t * M ≤ A + M - 1 := Nat.div_mul_le_self _ _
    have e2 : A = n * (n - 2) + 2 := by rw [hA, Nat.sub_add_cancel (by omega)]
    omega
  exact dirAny_twoClass (c := c) (n := n) (s₁ := n - 1) (s₂ := s₂) (t := t) hn (by omega) hu'
    (by omega) (by omega) h12 hs2M hs (by show s₂ * u + 1 ≤ T; omega) ht1 ht2 ha

/-- **Region D0**: orientation `(u, u')`, family `X(N, s, 0)`, left index `a = 1`. -/
theorem dirAny_regionD0 {N u u' : Nat} (hu : 2 ≤ u) (hu' : 4 ≤ u') (hN : u ≤ N)
    (hA : u * (N + 1 + u) * (u' - 2) + u * (u + 1) * N ≤ (u + 1) * (N + 1 - u) * (u' - 2 + 1))
    (hB : u * ((u' - 2) * (u' - 2) + N) ≤ (N + 1 - u) * (u' - 2 + 1)) :
    dirAny N u u' = true := by
  refine dirAny_of_dirAll (a := 1) le_rfl (by omega) (dirAll_X0 (by omega) ?_)
  refine dirOK_direct (by omega) (by omega) (by omega) (by omega) ?_ (by omega) (by simpa using hA)
    (by simpa using hB)
  simp only [Nat.one_mul]
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have : u * ((N + 1) / 2) + (u - 1) ≥ N := by
    have := Nat.div_add_mod (N + 1) 2
    have := Nat.mod_lt (N + 1) (show 0 < 2 by omega)
    nlinarith
  omega

/-- **Region W**: orientation `(u', u)`, family `X(N, s, 0)`, left index `a`, right distance
`c = a - 1` (the near-diagonal pairs with small `u' - u`). -/
theorem dirAny_regionW {N u u' a : Nat} (hu : 2 ≤ u) (ha : 2 ≤ a) (ha2 : 2 * a ≤ u')
    (hu'N : u' ≤ N) (hW3 : 2 * u' * u' + u' ≤ a * N + 1) (hR : (u - 2) * (u' + 1) ≤ a * N)
    (hW1 : (a * N + u' + 1) * (u - 2) + (u' + 1) ≤ (a - 1) * N * (u' + 1))
    (hW2 : (a - 1) * N * u' ≤ (a * N + 1 - u') * (u - 2 + 1)) :
    dirAny N u' u = true := by
  have hu' : 4 ≤ u' := by omega
  have hN : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hW1
    · exact h
  set T := a * N with hT
  set s₁ := (T + 1 + u') / (u' + 1) with hs₁
  set s₂ := T / u' with hs₂
  have f1 : s₁ * (u' + 1) ≤ T + 1 + u' := Nat.div_mul_le_self _ _
  have f1' : T + 1 + u' < (u' + 1) * (s₁ + 1) := Nat.lt_mul_div_succ _ (by omega)
  have f2 : s₂ * u' ≤ T := Nat.div_mul_le_self _ _
  have f2' : T < u' * (s₂ + 1) := Nat.lt_mul_div_succ _ (by omega)
  have g1 : T + 1 ≤ s₁ * (u' + 1) := by
    have : (u' + 1) * (s₁ + 1) = s₁ * (u' + 1) + u' + 1 := by ring
    omega
  have g2 : T + 1 - u' ≤ s₂ * u' := by
    have : u' * (s₂ + 1) = s₂ * u' + u' := by ring
    omega
  have hTN : 2 * N ≤ T := Nat.mul_le_mul_right _ ha
  -- containment
  have hc1 : s₁ * (u - 2) + 1 ≤ (a - 1) * N := by
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < u' + 1 by omega)
    calc (s₁ * (u - 2) + 1) * (u' + 1) = (s₁ * (u' + 1)) * (u - 2) + (u' + 1) := by ring
      _ ≤ (T + 1 + u') * (u - 2) + (u' + 1) := by
          have := Nat.mul_le_mul_right (u - 2) f1; omega
      _ = (a * N + u' + 1) * (u - 2) + (u' + 1) := by rw [hT]; ring
      _ ≤ (a - 1) * N * (u' + 1) := hW1
  have hc2 : (a - 1) * N ≤ s₂ * (u - 2 + 1) := by
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < u' by omega)
    calc (a - 1) * N * u' ≤ (T + 1 - u') * (u - 2 + 1) := hW2
      _ ≤ s₂ * u' * (u - 2 + 1) := Nat.mul_le_mul_right _ g2
      _ = s₂ * (u - 2 + 1) * u' := by ring
  have hs1 : 2 ≤ s₁ := by
    by_contra hcon
    push Not at hcon
    have : s₁ * (u' + 1) ≤ 1 * (u' + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hRs : u - 2 ≤ s₁ := by
    by_contra hcon
    push Not at hcon
    have : s₁ * (u' + 1) + (u' + 1) ≤ (u - 2) * (u' + 1) := by
      have := Nat.mul_le_mul_right (u' + 1) (show s₁ + 1 ≤ u - 2 by omega)
      have e : (s₁ + 1) * (u' + 1) = s₁ * (u' + 1) + (u' + 1) := by ring
      omega
    omega
  have h12 : s₁ ≤ s₂ := by
    by_contra hcon
    push Not at hcon
    have h3 : (s₂ + 1) * (u' + 1) ≤ s₁ * (u' + 1) := Nat.mul_le_mul_right _ hcon
    have e3 : (s₂ + 1) * (u' + 1) = s₂ * u' + s₂ + u' + 1 := by ring
    have h4 : s₂ * u' + s₂ ≤ T := by omega
    have h5 : (T + 1 - u') * (u' + 1) ≤ s₂ * u' * (u' + 1) := Nat.mul_le_mul_right _ g2
    have h6 : s₂ * u' * (u' + 1) ≤ T * u' := by
      have := Nat.mul_le_mul_right u' h4
      nlinarith
    have hTu : u' ≤ T + 1 := by nlinarith
    zify [hTu] at h5 h6 hW3
    nlinarith
  have hsm : s₂ ≤ (N + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    have : s₂ * u' * 2 ≤ T * 2 := Nat.mul_le_mul_right _ f2
    have : T * 2 ≤ (N + 1) * u' := by
      calc T * 2 = 2 * a * N := by rw [hT]; ring
        _ ≤ u' * N := Nat.mul_le_mul_right _ ha2
        _ ≤ (N + 1) * u' := by nlinarith
    have : s₂ * 2 * u' ≤ (N + 1) * u' := by nlinarith
    exact Nat.le_of_mul_le_mul_right this (by omega)
  refine dirAny_of_dirAll (a := a) (by omega) (by omega) (dirAll_X0 (by omega) ?_)
  exact dirOK_of_cover (s₁ := s₁) (s₂ := s₂) (c := a - 1) (by omega) (by omega) hs1 hRs h12 hsm
    (by simpa using f2) (by simpa using g1) hc1
    (by have e : s₂ * (u - 2 + 1) = s₂ * (u - 2) + s₂ := by ring
        omega)

/-! ## The proven regions and the residual statement -/

/-- Region B (`u' = N + 1 - v`, `n = N + 2 - 2u'`): Theorem B's hypotheses. -/
def RegionB (N u u' : Nat) : Prop :=
  3 ≤ u ∧ 2 * u' + 3 ≤ N + 2 ∧
    (u + 1) * (N + 2 - 2 * u' - 1) ≤ u / 2 * (N + 2) ∧ u * (u + 1) ≤ u / 2 * (N + 2) ∧
    u * ((2 * u + 1) * (N + 2 - 2 * u') - 2 * u) +
        u * (u + 1) * (2 * (N + 2 - 2 * u') + (N + 2) - 1) ≤
      u / 2 * (N + 2) * (N + 2 - 2 * u' + 2 * u) ∧
    2 * (u + 1) ≤ u / 2 * u'

/-- Region D: the hypotheses of `dirAny_regionD` (`Live8.settled_directZ_region`). -/
def RegionD (N u u' : Nat) : Prop :=
  4 ≤ u ∧ u ≤ u' ∧ u + u' ≤ N ∧
    (u - u % 2) * (N + 2) * (u + u' + 1) ≥ 2 * (u + 1) * ((N + 2) * u + 2 * u * u' + u) ∧
    (u * (N + 2) - u % 2 * (N + 2) - 2 * u + 2) * (u' + 1) ≥ 2 * u * (u' * u' + (N + 2))

theorem dirAny_of_RegionB {N u u' : Nat} (h : RegionB N u u') : dirAny N u' u = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact dirAny_regionB (n := N + 2 - 2 * u') h1 (by omega) (by omega) h3 h4 h5 h6

theorem dirAny_of_RegionD {N u u' : Nat} (h : RegionD N u u') : dirAny N u u' = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact dirAny_regionD h1 h2 h3 h4 h5

/-- Region B2 (`n = N + 2 - 2u'`): the hypotheses of `dirAny_regionB2`. -/
def RegionB2 (N u u' : Nat) : Prop :=
  3 ≤ u ∧ u + 3 + 2 * u' ≤ N + 2 ∧
    u / 2 * (N + 2) ≤ (N + 2 - 2 * u' - 1) * (u + 1) ∧
    u * ((N + 2 - 2 * u') * (N + 2 - 2 * u' - 2) + (N + 2) + 1) ≤
      (u / 2 * (N + 2) - 2 * u) * (N + 2 - 2 * u') ∧
    2 * (N + 2) ≤ (N + 2 - 2 * u' - 1) * u'

/-- Region D0: the hypotheses of `dirAny_regionD0`. -/
def RegionD0 (N u u' : Nat) : Prop :=
  2 ≤ u ∧ 4 ≤ u' ∧ u ≤ N ∧
    u * (N + 1 + u) * (u' - 2) + u * (u + 1) * N ≤ (u + 1) * (N + 1 - u) * (u' - 2 + 1) ∧
    u * ((u' - 2) * (u' - 2) + N) ≤ (N + 1 - u) * (u' - 2 + 1)

/-- Region W: the hypotheses of `dirAny_regionW` for some `a`. -/
def RegionW (N u u' : Nat) : Prop :=
  ∃ a, 2 ≤ u ∧ 2 ≤ a ∧ 2 * a ≤ u' ∧ u' ≤ N ∧ 2 * u' * u' + u' ≤ a * N + 1 ∧
    (u - 2) * (u' + 1) ≤ a * N ∧
    (a * N + u' + 1) * (u - 2) + (u' + 1) ≤ (a - 1) * N * (u' + 1) ∧
    (a - 1) * N * u' ≤ (a * N + 1 - u') * (u - 2 + 1)

/-- The union of the proven regions. -/
def Proven (N u u' : Nat) : Prop :=
  RegionB N u u' ∨ RegionB2 N u u' ∨ RegionD N u u' ∨ RegionD0 N u u' ∨ RegionW N u u'

theorem covered_of_proven {N u u' : Nat} (h : Proven N u u') :
    dirAny N u u' = true ∨ dirAny N u' u = true := by
  rcases h with h | ⟨h1, h2, h3, h4, h5⟩ | h | ⟨h1, h2, h3, h4, h5⟩ |
      ⟨a, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact Or.inr (dirAny_of_RegionB h)
  · exact Or.inr (dirAny_regionB2 (n := N + 2 - 2 * u') h1 (by omega) (by omega) h3 h4 h5)
  · exact Or.inl (dirAny_of_RegionD h)
  · exact Or.inl (dirAny_regionD0 h1 h2 h3 h4 h5)
  · exact Or.inr (dirAny_regionW h1 h2 h3 h4 h5 h6 h7 h8)

/-- **The residual statement**: `ArithCover N` restricted to the pairs outside the proven
regions. -/
def Residual (N : Nat) : Prop :=
  ∀ u v, 2 ≤ u → u < v → u + v ≤ N + 1 → (u + v) % 2 = 1 → 2 * u + 2 ≤ v →
    N + u + 3 ≤ 2 * v → ¬ Special N u (N + 1 - v) → ¬ Proven N u (N + 1 - v) →
        dirAny N u (N + 1 - v) = true ∨ dirAny N (N + 1 - v) u = true

theorem arithCover_of_residual {N : Nat} (h : Residual N) : ArithCover N := by
  intro u v h1 h2 h3 h4 h5 h6 h7
  by_cases hP : Proven N u (N + 1 - v)
  · exact covered_of_proven hP
  exact h u v h1 h2 h3 h4 h5 h6 h7 hP

/-- **Conjecture C (2-prefixes) for all `N`, modulo the residual statement for `N > 300`.** -/
theorem conjectureC_of_residual (hR : ∀ N, 300 < N → Residual N) {N m₁ m₂ : Nat}
    (h1 : 1 ≤ m₁ ∧ m₁ ≤ N) (h2 : 1 ≤ m₂ ∧ m₂ ≤ N) (h12 : m₁ ≠ m₂)
    (hval : SemiSymmetric N [m₁, m₂]) :
    Extends N [m₁, m₂] ↔ deadB N (min m₁ m₂) (max m₁ m₂) = false :=
  conjectureC_of_arith (fun N hN => arithCover_of_residual (hR N hN)) h1 h2 h12 hval

/-! ## Theorem B for all small `u` near the boundary (the residual set of `Live8` 4(d)) -/

/-- The length inequality of Theorem B, with `n = u + 3 + e` and `M ≥ max 303 (u² + 2)`. -/
theorem B3_int (u e M : ℤ) (hu : 3 ≤ u) (he : 0 ≤ e) (hM : 303 ≤ M) (hMu : u * u + 2 ≤ M)
    (hs : u = 3 → 1 ≤ e) :
    0 ≤ M * ((u - 1) * (u + 3 + e) - 4 * u) - (u + 3 + e) * (8 * u ^ 2 + 6 * u) + 6 * u ^ 2 + 2 * u := by
  have hB : 0 ≤ M * (u - 1) - 8 * u ^ 2 - 6 * u := by
    rcases le_or_gt u 9 with h9 | h9
    · nlinarith [mul_le_mul_of_nonneg_right hM (show (0:ℤ) ≤ u - 1 by linarith)]
    · nlinarith [mul_le_mul_of_nonneg_right hMu (show (0:ℤ) ≤ u - 1 by linarith)]
  have key : M * ((u - 1) * (u + 3 + e) - 4 * u) - (u + 3 + e) * (8 * u ^ 2 + 6 * u) + 6 * u ^ 2 + 2 * u
      = (M * ((u - 3) * (u + 1)) - (8 * u ^ 3 + 24 * u ^ 2 + 16 * u)) +
        e * (M * (u - 1) - 8 * u ^ 2 - 6 * u) := by ring
  rw [key]
  rcases eq_or_lt_of_le hu with h3 | h4
  · subst h3
    have := hs rfl
    nlinarith
  · have hA : 0 ≤ M * ((u - 3) * (u + 1)) - (8 * u ^ 3 + 24 * u ^ 2 + 16 * u) := by
      have hp : 0 ≤ (u - 3) * (u + 1) := by nlinarith
      rcases le_or_gt u 12 with h12 | h12
      · have := mul_le_mul_of_nonneg_right hM hp
        nlinarith
      · have := mul_le_mul_of_nonneg_right hMu hp
        nlinarith
    nlinarith [mul_nonneg he hB]

/-- **Corollary B′.**  For `N ≥ 301`, `3 ≤ u ≤ √N` and `u' ≥ 3N/8` (with `u + 2u' ≤ N - 1`), the pair
`(u, N + 1 - u')` lies in region B, except the special pair `u = 3`, `2u' + 4 = N`. -/
theorem regionB_of_small {N u u' : Nat} (hN : 301 ≤ N) (hu : 3 ≤ u) (huN : u * u ≤ N)
    (hw : u + 2 * u' + 1 ≤ N) (h38 : 3 * N + 2 ≤ 8 * u') (hs : ¬ (u = 3 ∧ 2 * u' + 4 = N)) :
    RegionB N u u' := by
  set c := u / 2 with hc
  have h4c : u + 1 ≤ 4 * c := by omega
  have hc2 : u ≤ 2 * c + 1 := by omega
  have h4u : 4 * u ≤ N + 2 := by nlinarith
  obtain ⟨e, he⟩ : ∃ e, N + 2 - 2 * u' = u + 3 + e := ⟨N + 2 - 2 * u' - (u + 3), by omega⟩
  refine ⟨hu, by omega, ?_, ?_, ?_, ?_⟩
  · -- B1
    have h1 : 4 * (N + 2 - 2 * u' - 1) ≤ N + 2 := by omega
    calc (u + 1) * (N + 2 - 2 * u' - 1) ≤ 4 * c * (N + 2 - 2 * u' - 1) :=
          Nat.mul_le_mul_right _ h4c
      _ = c * (4 * (N + 2 - 2 * u' - 1)) := by ring
      _ ≤ c * (N + 2) := Nat.mul_le_mul_left _ h1
  · -- B2
    calc u * (u + 1) ≤ u * (4 * c) := Nat.mul_le_mul_left _ h4c
      _ = c * (4 * u) := by ring
      _ ≤ c * (N + 2) := Nat.mul_le_mul_left _ h4u
  · -- B3
    rw [he]
    have hse : u = 3 → 1 ≤ e := by intro h3; subst h3; omega
    have key := B3_int (u : ℤ) (e : ℤ) ((N : ℤ) + 2) (by exact_mod_cast hu) (by positivity)
      (by have : (301 : ℤ) ≤ N := by exact_mod_cast hN
          linarith)
      (by have : ((u * u : Nat) : ℤ) ≤ N := by exact_mod_cast huN
          push_cast at this; linarith)
      (by intro h; exact_mod_cast hse (by exact_mod_cast h))
    have hsub1 : 2 * u ≤ (2 * u + 1) * (u + 3 + e) := by nlinarith
    have hsub2 : 1 ≤ 2 * (u + 3 + e) + (N + 2) := by omega
    have hcz : ((u : ℤ) - 1) ≤ 2 * (c : ℤ) := by
      have : u ≤ 2 * c + 1 := hc2
      zify at this; linarith
    zify [hsub1, hsub2]
    have hpos : (0 : ℤ) ≤ ((N : ℤ) + 2) * ((u : ℤ) + 3 + e + 2 * u) := by positivity
    have := mul_le_mul_of_nonneg_right hcz hpos
    nlinarith
  · -- B4
    have : 8 ≤ u' := by omega
    calc 2 * (u + 1) ≤ 2 * (4 * c) := Nat.mul_le_mul_left _ h4c
      _ = c * 8 := by ring
      _ ≤ c * u' := Nat.mul_le_mul_left _ this

/-- **The near-boundary pairs with small `u`** (in particular the residual family
`u ≤ √N`, `δ < u` of `Live8` section 4(d)): `dirAny` holds in the orientation `(u', u)`. -/
theorem dirAny_nearBoundary {N u u' : Nat} (hN : 301 ≤ N) (hu : 3 ≤ u) (huN : u * u ≤ N)
    (hw : u + 2 * u' + 1 ≤ N) (h38 : 3 * N + 2 ≤ 8 * u') (hs : ¬ (u = 3 ∧ 2 * u' + 4 = N)) :
    dirAny N u' u = true :=
  dirAny_of_RegionB (regionB_of_small hN hu huN hw h38 hs)

end ArithCover
end Folds
