import Folds.MaxMoves

namespace Folds

open Finset

/-- Splitting `[0, 2^a t)` by the 2-adic valuation (capped at `a`). -/
theorem sum_levels (f : Nat → Nat) (t : Nat) : ∀ a : Nat,
    ∑ k ∈ range (2 ^ a * t), f k =
      ∑ l ∈ range a, ∑ i ∈ range (2 ^ (a - 1 - l) * t), f (2 ^ l * (2 * i + 1)) +
        ∑ i ∈ range t, f (2 ^ a * i)
  | 0 => by simp
  | a + 1 => by
    have ih := sum_levels (fun k => f (2 * k)) t a
    rw [show 2 ^ (a + 1) * t = 2 * (2 ^ a * t) by ring, sum_range_two_mul f, Finset.sum_add_distrib,
      ih, Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, pow_zero, one_mul, Nat.sub_zero]
    have e1 : ∀ l ∈ range a, ∑ i ∈ range (2 ^ (a - 1 - l) * t), f (2 * (2 ^ l * (2 * i + 1))) =
        ∑ i ∈ range (2 ^ (a - (l + 1)) * t), f (2 ^ (l + 1) * (2 * i + 1)) := by
      intro l _
      rw [show a - (l + 1) = a - 1 - l by omega]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]; ring_nf
    rw [Finset.sum_congr rfl e1]
    have e2 : ∀ i ∈ range t, f (2 * (2 ^ a * i)) = f (2 ^ (a + 1) * i) := by
      intro i _; rw [pow_succ]; ring_nf
    rw [Finset.sum_congr rfl e2]
    ring

/-- **The chain inequality** behind the 2-adic bound, on the level sums.  Level `l < a`
(`a = b + 1`) has `n l` residues, total valid count `Z l` and total gap size `A l`; level `a`
(nonzero) has `Za`, `Aa`; the boundary gaps `0, s` have `Zb`, `B`. -/
theorem chain_two_adic (b : Nat) (t : Int) (Z A n : Nat → Int) (Za Aa Zb B : Int)
    (hn : ∀ l, l < b → n l = 2 * n (l + 1)) (hnb : n b = t) (hpos : 1 ≤ n 0)
    (h1 : ∀ l, l ≤ b → Z l + n l ≤ A l)
    (h2 : ∀ l, l < b → 2 * Z l ≤ 2 * A (l + 1) + n l)
    (h3 : 2 * Z b ≤ Aa + B + t + 1)
    (h4 : 2 * Za ≤ Aa + t - 1)
    (h5 : 2 * Zb ≤ B + 1) :
    2 * ((b : Int) + 3) * (∑ l ∈ range (b + 1), Z l + Za + Zb) ≤
      2 * ((b : Int) + 2) * (∑ l ∈ range (b + 1), A l + Aa + B) + 1 := by
  have inv : ∀ L, L ≤ b →
      2 * ((b : Int) + 3) * ∑ l ∈ range L, Z l ≤
        2 * ((b : Int) + 2) * ∑ l ∈ range L, A l + 2 * (L : Int) * A L +
          2 * n L * (2 * (b : Int) - 3 * L) - 4 * n 0 * b := by
    intro L
    induction L with
    | zero => intro _; simp; ring_nf; rfl
    | succ L ih =>
      intro hL
      have i := ih (by omega)
      have a1 := h1 L (by omega)
      have a2 := h2 L (by omega)
      have a3 := hn L (by omega)
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast
      have c1 : (0 : Int) ≤ 2 * ((b : Int) - L) := by
        have : (L : Int) < b := by exact_mod_cast (show L < b by omega)
        linarith
      have c2 : (0 : Int) ≤ (L : Int) + 1 := by positivity
      have m1 := mul_le_mul_of_nonneg_left a1 c1
      have m2 := mul_le_mul_of_nonneg_left a2 c2
      rw [a3] at m1 m2 i
      nlinarith
  have i := inv b le_rfl
  have a1 := h1 b le_rfl
  rw [hnb] at a1 i
  have hb0 : (0 : Int) ≤ b := by positivity
  have m1 : (0 : Int) ≤ (n 0 - 1) * b := mul_nonneg (by linarith) hb0
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  nlinarith

theorem sum_comp_le_of_injOn (n : Nat) (g φ : Nat → Nat) (hφ : ∀ i, i < n → φ i < n)
    (hinj : ∀ i, i < n → ∀ j, j < n → φ i = φ j → i = j) :
    ∑ i ∈ range n, g (φ i) ≤ ∑ i ∈ range n, g i := by
  rw [← Finset.sum_image (g := φ) (f := g) (fun i hi j hj e =>
    hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) e)]
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
  obtain ⟨i, hi, rfl⟩ := hx
  exact hφ i hi

/-- **The 2-adic charging inequality** (`s = 2^(b+1) t`, `t` odd): `(b+3) Σ z ≤ (b+2) Σ w`
for the valid counts `z k` and gap sizes `w k` (`k ∈ [0, s]`). -/
theorem arith_two_adic (b t : Nat) (ht : t % 2 = 1) (z w : Nat → Nat)
    (h0 : 2 * z 0 ≤ w 0)
    (h1 : ∀ k, 1 ≤ k → 2 * k < 2 ^ (b + 1) * t → 2 * z k ≤ w (2 * k) + 1)
    (hu : 2 * z (2 ^ b * t) ≤ w (2 ^ (b + 1) * t) + w 0 + 2)
    (h2 : ∀ k, 2 ^ (b + 1) * t < 2 * k → k < 2 ^ (b + 1) * t →
      2 * z k ≤ w (2 * k - 2 ^ (b + 1) * t) + 1)
    (hs : 2 * z (2 ^ (b + 1) * t) ≤ w (2 ^ (b + 1) * t) + 1)
    (hlt : ∀ k, 1 ≤ k → k < 2 ^ (b + 1) * t → z k + 1 ≤ w k) :
    (b + 3) * ∑ k ∈ range (2 ^ (b + 1) * t + 1), z k ≤
      (b + 2) * ∑ k ∈ range (2 ^ (b + 1) * t + 1), w k := by
  set s := 2 ^ (b + 1) * t with hsdef
  have ht1 : 1 ≤ t := by omega
  have hsP : s = 2 * 2 ^ b * t := by rw [hsdef, pow_succ]; ring
  -- level sums
  let n : Nat → Nat := fun l => 2 ^ (b - l) * t
  let Z : Nat → Nat := fun l => ∑ i ∈ range (n l), z (2 ^ l * (2 * i + 1))
  let A : Nat → Nat := fun l => ∑ i ∈ range (n l), w (2 ^ l * (2 * i + 1))
  let Za : Nat := ∑ i ∈ range (t - 1), z (2 ^ (b + 1) * (i + 1))
  let Aa : Nat := ∑ i ∈ range (t - 1), w (2 ^ (b + 1) * (i + 1))
  -- decomposition
  have dec : ∀ f : Nat → Nat, ∑ k ∈ range (s + 1), f k =
      ∑ l ∈ range (b + 1), ∑ i ∈ range (2 ^ (b - l) * t), f (2 ^ l * (2 * i + 1)) +
        ∑ i ∈ range (t - 1), f (2 ^ (b + 1) * (i + 1)) + (f 0 + f s) := by
    intro f
    rw [Finset.sum_range_succ, hsdef, sum_levels f t (b + 1)]
    have e : ∀ l ∈ range (b + 1), ∑ i ∈ range (2 ^ (b + 1 - 1 - l) * t), f (2 ^ l * (2 * i + 1)) =
        ∑ i ∈ range (2 ^ (b - l) * t), f (2 ^ l * (2 * i + 1)) := by
      intro l _; rw [show b + 1 - 1 - l = b - l by omega]
    rw [Finset.sum_congr rfl e]
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [Finset.sum_range_succ' (fun i => f (2 ^ (b + 1) * i)) t', Nat.add_sub_cancel, Nat.mul_zero]
    ring
  -- every level element lies in `[1, s)`
  have hrange : ∀ l, l ≤ b → ∀ i, i < n l → 1 ≤ 2 ^ l * (2 * i + 1) ∧ 2 ^ l * (2 * i + 1) < s := by
    intro l hl i hi
    have hP : 0 < 2 ^ l := by positivity
    have e : 2 ^ b = 2 ^ l * 2 ^ (b - l) := by rw [← pow_add]; congr 1; omega
    refine ⟨Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩
    have : 2 * i + 1 < 2 * (2 ^ (b - l) * t) := by simp only [n] at hi; omega
    have := Nat.mul_lt_mul_of_pos_left this hP
    rw [hsP, e]; linarith
  have H1 : ∀ l, l ≤ b → Z l + n l ≤ A l := by
    intro l hl
    have : ∑ i ∈ range (n l), (z (2 ^ l * (2 * i + 1)) + 1) ≤ A l :=
      Finset.sum_le_sum fun i hi => by
        have := hrange l hl i (Finset.mem_range.1 hi)
        exact hlt _ this.1 this.2
    rw [Finset.sum_add_distrib] at this
    simpa using this
  have H2 : ∀ l, l < b → 2 * Z l ≤ 2 * A (l + 1) + n l := by
    intro l hl
    set C := 2 ^ (b - (l + 1)) with hC
    have hP : 0 < 2 ^ l := by positivity
    have eQ : 2 ^ (b - l) = 2 * C := by rw [hC, ← pow_succ']; congr 1; omega
    have eS : s = 4 * 2 ^ l * C * t := by
      have : 2 ^ b = 2 ^ l * 2 * C := by rw [hC, ← pow_succ, ← pow_add]; congr 1; omega
      rw [hsP, this]; ring
    have e1 : ∀ i, 2 ^ (l + 1) * (2 * i + 1) = 2 * (2 ^ l * (2 * i + 1)) := by
      intro i; rw [pow_succ]; ring
    have k1 : ∀ i, i < C * t → 2 * z (2 ^ l * (2 * i + 1)) ≤ w (2 ^ (l + 1) * (2 * i + 1)) + 1 := by
      intro i hi
      have := Nat.mul_lt_mul_of_pos_left (show 2 * i + 1 < 2 * (C * t) by omega) hP
      rw [e1]
      apply h1 _ (Nat.one_le_iff_ne_zero.2 (by positivity))
      rw [eS]; linarith
    have k2 : ∀ i, i < C * t →
        2 * z (2 ^ l * (2 * (C * t + i) + 1)) ≤ w (2 ^ (l + 1) * (2 * i + 1)) + 1 := by
      intro i hi
      have e : 2 * (2 ^ l * (2 * (C * t + i) + 1)) = 2 ^ (l + 1) * (2 * i + 1) + s := by
        rw [eS, pow_succ]; ring
      have := Nat.mul_lt_mul_of_pos_left (show 2 * (C * t + i) + 1 < 4 * (C * t) by omega) hP
      have hpos : 0 < 2 ^ (l + 1) * (2 * i + 1) := by positivity
      have := h2 (2 ^ l * (2 * (C * t + i) + 1)) (by omega) (by rw [eS]; linarith)
      rwa [e, Nat.add_sub_cancel] at this
    show 2 * ∑ i ∈ range (2 ^ (b - l) * t), z (2 ^ l * (2 * i + 1)) ≤
      2 * ∑ i ∈ range (2 ^ (b - (l + 1)) * t), w (2 ^ (l + 1) * (2 * i + 1)) + 2 ^ (b - l) * t
    rw [eQ, show 2 * C * t = C * t + C * t by ring, Finset.sum_range_add, ← hC]
    have hsum := Finset.sum_le_sum (s := range (C * t)) (fun i hi =>
      add_le_add (k1 i (Finset.mem_range.1 hi)) (k2 i (Finset.mem_range.1 hi)))
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      ← Finset.mul_sum] at hsum
    omega
  have hP : 0 < 2 ^ b := by positivity
  have e2 : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ]; ring
  have Aa_eq : ∑ j ∈ range t, (if j = 0 then w 0 + w s + 1 else w (2 ^ (b + 1) * j)) =
      w 0 + w s + 1 + Aa := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, Aa, Nat.add_one_ne_zero, ite_false, ite_true]
    ring
  have H3 : 2 * Z b ≤ Aa + (w 0 + w s) + t + 1 := by
    let g : Nat → Nat := fun j => if j = 0 then w 0 + w s + 1 else w (2 ^ (b + 1) * j)
    let φ : Nat → Nat := fun i => if 2 * i + 1 < t then 2 * i + 1 else 2 * i + 1 - t
    have kk : ∀ i, i < t → 2 * z (2 ^ b * (2 * i + 1)) ≤ g (φ i) + 1 := by
      intro i hi
      by_cases c1 : 2 * i + 1 < t
      · have hφ : φ i = 2 * i + 1 := by simp only [φ, c1, ite_true]
        rw [hφ]
        simp only [g, Nat.add_one_ne_zero, ite_false]
        have := Nat.mul_lt_mul_of_pos_left c1 hP
        rw [e2, show 2 * 2 ^ b * (2 * i + 1) = 2 * (2 ^ b * (2 * i + 1)) by ring]
        exact h1 _ (Nat.one_le_iff_ne_zero.2 (by positivity)) (by rw [hsdef, e2]; linarith)
      · by_cases c2 : 2 * i + 1 = t
        · have hφ : φ i = 0 := by simp only [φ, c1, ite_false]; omega
          rw [hφ, c2]
          simp only [g, ite_true]
          omega
        · obtain ⟨d, hd⟩ : ∃ d, 2 * i + 1 = t + d := ⟨2 * i + 1 - t, by omega⟩
          have hφ : φ i = d := by simp only [φ, c1, ite_false]; omega
          have hd1 : d ≠ 0 := by omega
          rw [hφ]
          simp only [g, hd1, ite_false]
          have e : 2 * (2 ^ b * (2 * i + 1)) = 2 ^ (b + 1) * d + s := by
            rw [hd, hsP, e2]; ring
          have := Nat.mul_lt_mul_of_pos_left (show 2 * i + 1 < 2 * t by omega) hP
          have hpos : 0 < 2 ^ (b + 1) * d := by positivity
          have := h2 (2 ^ b * (2 * i + 1)) (by omega) (by rw [hsP]; linarith)
          rwa [e, Nat.add_sub_cancel] at this
    have hinj := sum_comp_le_of_injOn t g φ
      (fun i hi => by simp only [φ]; split_ifs <;> omega)
      (fun i hi j hj e => by simp only [φ] at e; split_ifs at e <;> omega)
    have hsum := Finset.sum_le_sum (s := range t) (fun i hi => kk i (Finset.mem_range.1 hi))
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      ← Finset.mul_sum] at hsum
    have hZ : Z b = ∑ i ∈ range t, z (2 ^ b * (2 * i + 1)) := by
      simp only [Z, n, Nat.sub_self, pow_zero, one_mul]
    rw [hZ]
    have := Aa_eq
    simp only [g] at hinj hsum
    omega
  have H4 : 2 * Za ≤ Aa + (t - 1) := by
    let ψ : Nat → Nat := fun i => if 2 * (i + 1) < t then 2 * (i + 1) - 1 else 2 * (i + 1) - t - 1
    let g : Nat → Nat := fun j => w (2 ^ (b + 1) * (j + 1))
    have kk : ∀ i, i < t - 1 → 2 * z (2 ^ (b + 1) * (i + 1)) ≤ g (ψ i) + 1 := by
      intro i hi
      by_cases c1 : 2 * (i + 1) < t
      · have hψ : ψ i + 1 = 2 * (i + 1) := by simp only [ψ, c1, ite_true]; omega
        simp only [g, hψ]
        have := Nat.mul_lt_mul_of_pos_left c1 hP
        rw [show 2 ^ (b + 1) * (2 * (i + 1)) = 2 * (2 ^ (b + 1) * (i + 1)) by ring]
        exact h1 _ (Nat.one_le_iff_ne_zero.2 (by positivity)) (by rw [hsdef, e2]; linarith)
      · obtain ⟨d, hd⟩ : ∃ d, 2 * (i + 1) = t + d := ⟨2 * (i + 1) - t, by omega⟩
        have hd1 : 1 ≤ d := by omega
        have hψ : ψ i + 1 = d := by simp only [ψ, c1, ite_false]; omega
        simp only [g, hψ]
        have e : 2 * (2 ^ (b + 1) * (i + 1)) = 2 ^ (b + 1) * d + s := by
          rw [hsdef, show 2 * (2 ^ (b + 1) * (i + 1)) = 2 ^ (b + 1) * (2 * (i + 1)) by ring, hd]
          ring
        have := Nat.mul_lt_mul_of_pos_left (show i + 1 < t by omega) hP
        have hpos : 0 < 2 ^ (b + 1) * d := by positivity
        have := h2 (2 ^ (b + 1) * (i + 1)) (by omega) (by rw [hsdef, e2]; linarith)
        rwa [e, Nat.add_sub_cancel] at this
    have hinj := sum_comp_le_of_injOn (t - 1) g ψ
      (fun i hi => by simp only [ψ]; split_ifs <;> omega)
      (fun i hi j hj e => by simp only [ψ] at e; split_ifs at e <;> omega)
    have hsum := Finset.sum_le_sum (s := range (t - 1)) (fun i hi => kk i (Finset.mem_range.1 hi))
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      ← Finset.mul_sum] at hsum
    have : Aa = ∑ i ∈ range (t - 1), g i := rfl
    have : Za = ∑ i ∈ range (t - 1), z (2 ^ (b + 1) * (i + 1)) := rfl
    omega
  have H5 : 2 * (z 0 + z s) ≤ w 0 + w s + 1 := by omega
  -- assemble in `ℤ`
  have key := chain_two_adic b t (fun l => (Z l : Int)) (fun l => (A l : Int)) (fun l => (n l : Int))
    Za Aa (z 0 + z s : Nat) (w 0 + w s : Nat)
    (fun l hl => by
      have : n l = 2 * n (l + 1) := by
        simp only [n]; rw [← mul_assoc, ← pow_succ']; congr 2; omega
      exact_mod_cast this)
    (by simp [n])
    (by simp only [n]; exact_mod_cast Nat.mul_pos (by positivity) (by omega))
    (fun l hl => by exact_mod_cast H1 l hl)
    (fun l hl => by exact_mod_cast H2 l hl)
    (by push_cast; exact_mod_cast H3)
    (by have := H4; zify [ht1] at this; linarith)
    (by exact_mod_cast H5)
  rw [dec z, dec w]
  change (b + 3) * (∑ l ∈ range (b + 1), Z l + Za + (z 0 + z s)) ≤
    (b + 2) * (∑ l ∈ range (b + 1), A l + Aa + (w 0 + w s))
  have h : 2 * ((b + 3) * (∑ l ∈ range (b + 1), Z l + Za + (z 0 + z s))) ≤
      2 * ((b + 2) * (∑ l ∈ range (b + 1), A l + Aa + (w 0 + w s))) + 1 := by
    zify; push_cast at key ⊢; linarith [key]
  generalize (b + 3) * (∑ l ∈ range (b + 1), Z l + Za + (z 0 + z s)) = X at h ⊢
  generalize (b + 2) * (∑ l ∈ range (b + 1), A l + Aa + (w 0 + w s)) = Y at h ⊢
  omega

section Gaps

variable {N : Nat} {S : List Nat} (hnd : S.Nodup) (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N)
include hnd hS

/-- **2-adic max-moves bound** (`b + 1 = v₂(|S|)`): if `|S| = 2^(b+1) t` with `t` odd, then
`(b + 3) · V(S) ≤ (b + 2) · N`. -/
theorem card_moves_two_adic' {b t : Nat} (hs : S.length = 2 ^ (b + 1) * t) (ht : t % 2 = 1) :
    (b + 3) * (moves N S).card ≤ (b + 2) * N := by
  set z : Nat → Nat := fun k => (validIn N S k).card with hz
  set w : Nat → Nat := fun k => (gapSet N S k).card with hw
  have hV := card_moves_eq_sum (N := N) (S := S)
  have hN := sum_gapSet (N := N) (S := S)
  rw [hs] at hV hN
  rw [hV]
  conv_rhs => rw [hN]
  have lo := validIn_lo_card hnd hS
  have hi := validIn_hi_card hnd hS
  have hi0 : ∀ k, 2 * k < S.length →
      ((validIn N S k).filter (fun m => ¬ 2 * m ≤ N)).card = 0 :=
    fun k hk => validIn_hi_empty hnd hS hk
  have spl := validIn_card_split (N := N) (S := S)
  rw [hs] at hi hi0
  have hspos : 0 < 2 ^ (b + 1) * t := Nat.mul_pos (by positivity) (by omega)
  have wbig : ∀ j, 2 ^ (b + 1) * t < j → w j = 0 := by
    intro j hj
    simp only [hw, Finset.card_eq_zero, gapSet, Finset.filter_eq_empty_iff]
    intro m _
    have := below_le_length S (m - 1)
    omega
  have e2 : 2 * (2 ^ b * t) = 2 ^ (b + 1) * t := by rw [pow_succ]; ring
  apply arith_two_adic b t ht z w
  · exact validIn_zero_card hnd hS (by omega)
  · intro k hk1 hk
    have a := lo k; have b' := hi0 k hk; have c := spl k
    simp only [hz, hw] at a b' c ⊢
    omega
  · have a := lo (2 ^ b * t); have b' := hi (2 ^ b * t); have c := spl (2 ^ b * t)
    simp only [hz, hw] at a b' c ⊢
    rw [e2, Nat.sub_self] at b'
    rw [e2] at a
    omega
  · intro k hk1 hk2
    have a := lo k; have b' := hi k; have c := spl k
    have d := wbig (2 * k) hk1
    simp only [hz, hw] at a b' c d ⊢
    omega
  · set s := 2 ^ (b + 1) * t
    have a := lo s; have b' := hi s; have c := spl s
    have d := wbig (2 * s) (by omega)
    simp only [hz, hw] at a b' c d ⊢
    rw [show 2 * s - s = s by omega] at b'
    omega
  · intro k _ hk
    have := validIn_card_lt hnd hS (k := k) (by omega)
    simpa [hz, hw] using this

/-- **2-adic max-moves bound.**  If `|S| = 2^a t` with `t` odd and `a ≥ 1`, then
`(a + 2) · V(S) ≤ (a + 1) · N`. -/
theorem card_moves_two_adic {a t : Nat} (ha : 1 ≤ a) (hs : S.length = 2 ^ a * t)
    (ht : t % 2 = 1) : (a + 2) * (moves N S).card ≤ (a + 1) * N := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  exact card_moves_two_adic' hnd hS hs ht

end Gaps

end Folds
