import Folds.Live5

/-!
# Live pairs, part 6: swapped Beatty copies and the copy `{1, 4, 6, …, N}`

`experiments/live6/PROOFS.txt`.

* `inward_pair`: the exact criterion of Theorem G for a pair `{u, v}`, `u < v`: it holds as
  soon as `v ≤ 2u + 1` or `2v ≤ N + u + 2` (`coReach_pair_inward`).
* `coReach_Y`, `coReach_chiY_transfer`: for `N = 2n`, `n` even, the set
  `{1, 4, 6, …, N} = chiY([n])` (`1 ↦ 1`, `y ↦ 2y`) is a window copy whose complement
  `{2, 3, 5, …, N - 1} = psiY([n])` has a semi-symmetric ordering (the image of a full
  sequence of `[n]` that places `n/2 + 1` before `1` before `2`); `coReach_one_half`: the pair
  `{1, N/2 + 2}` (`N ≡ 0 mod 4`) is co-reachable.
* `winEmb_swap`, `inward_swap`, `coReach_swap_transfer` (**swapped Beatty copies**): for `p`
  odd, `h ≤ 1`, `c ≥ 2` and `N + h ≥ 2cp + 1`, the right-aligned Beatty copy
  `X(N, p, h) = {⌊(rN - h)/p⌋}` with its last element `N - h` moved to `N - c` is still a window
  copy, and it satisfies Theorem G with the centre at `N - c`.
* `coReach_corner`: `{c + 1, N + 1 - ⌊(N - h)/p⌋}` is co-reachable for such `p ≠ 7`;
  `coReach_three`: `{3, N - 3}` is co-reachable for every `N ≥ 37`.
* `Cov6`: `Cov5` closed under the two new transfers.
* `coReach_of_cover`, `extends_iff_not_dead`: **Conjecture C modulo a covering statement.**
  If every non-dead pair of `[N]`, `N ≥ 13`, or its mirror is `Settled` (Theorem G, `{1, N}`,
  or the image of a non-dead pair of a smaller strip under a Beatty, swapped Beatty, `chiY` or
  doubling-split copy) or lies in a set `E` of pairs known to be co-reachable
  (`CoverLemma E`), then every non-dead pair is co-reachable, and a valid 2-prefix is live iff
  it is not dead.  The covering statement is purely arithmetic; numerically it holds for
  `N ≤ 520` with `E` = 55 small pairs and the pairs `(3, 2^k - 2)`, `(5, 2^k - 4)`.
-/

namespace Folds
namespace Live6

open Live2 Live4 Adjacent Live5

/-! ## Theorem G for pairs -/

theorem countP_single (a R : Nat) :
    (List.range' 1 R).countP (fun d => decide (d = a)) = if 1 ≤ a ∧ a ≤ R then 1 else 0 := by
  have := countP_range'_interval a a R
  rw [show (fun d => decide (a ≤ d ∧ d ≤ a)) = fun d => decide (d = a) by
    funext d; simp only [decide_eq_decide]; omega] at this
  rw [this]; split_ifs <;> omega

/-- Number of panels of a pair in an arm, as a sum of two indicator terms. -/
theorem countP_pair (R : Nat) (P Q : Nat → Prop) [DecidablePred P] [DecidablePred Q] (a b : Nat)
    (hP : ∀ d, 1 ≤ d → d ≤ R → (P d ↔ d = a)) (hQ : ∀ d, 1 ≤ d → d ≤ R → (Q d ↔ d = b))
    (hab : ∀ d, 1 ≤ d → d ≤ R → ¬ (d = a ∧ d = b)) :
    (List.range' 1 R).countP (fun d => decide (P d ∨ Q d)) =
      (if 1 ≤ a ∧ a ≤ R then 1 else 0) + (if 1 ≤ b ∧ b ≤ R then 1 else 0) := by
  rw [← countP_single, ← countP_single]
  apply le_antisymm
  · refine le_trans (le_of_eq (List.countP_congr fun d hd => ?_)) (countP_or_le _ _ _)
    rw [List.mem_range'_1] at hd
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rw [hP d hd.1 (by omega), hQ d hd.1 (by omega)]
  · refine countP_add_le _ _ _ _ (fun d hd => ?_) (fun d hd => ?_) (fun d hd => ?_)
    all_goals rw [List.mem_range'_1] at hd
    · simp only [decide_eq_true_eq]; exact hab d hd.1 (by omega)
    · simp only [decide_eq_true_eq]
      intro e; rw [hP d hd.1 (by omega)]; exact Or.inl e
    · simp only [decide_eq_true_eq]
      intro e; rw [hQ d hd.1 (by omega)]; exact Or.inr e

theorem leftCount_pair {N u v m : Nat} (huv : u ≠ v) :
    leftCount N ({u, v} : Finset Nat).toList m =
      (if 1 ≤ m - u ∧ m - u ≤ reach N m ∧ u < m then 1 else 0) +
      (if 1 ≤ m - v ∧ m - v ≤ reach N m ∧ v < m then 1 else 0) := by
  rw [leftCount_finset]
  have hr : reach N m ≤ m - 1 := by unfold reach; omega
  have e := countP_pair (reach N m) (fun d => m - d = u) (fun d => m - d = v)
    (if u < m then m - u else 0) (if v < m then m - v else 0)
    (fun d h1 h2 => by split_ifs <;> omega) (fun d h1 h2 => by split_ifs <;> omega)
    (fun d h1 h2 => by split_ifs <;> omega)
  have e2 : (List.range' 1 (reach N m)).countP (fun d => decide (m - d ∈ ({u, v} : Finset Nat))) =
      (List.range' 1 (reach N m)).countP (fun d => decide (m - d = u ∨ m - d = v)) :=
    List.countP_congr fun d _ => by simp
  rw [e2, e]
  split_ifs <;> omega

theorem rightCount_pair {N u v m : Nat} (huv : u ≠ v) :
    rightCount N ({u, v} : Finset Nat).toList m =
      (if 1 ≤ u - m ∧ u - m ≤ reach N m ∧ m < u then 1 else 0) +
      (if 1 ≤ v - m ∧ v - m ≤ reach N m ∧ m < v then 1 else 0) := by
  rw [rightCount_finset]
  have e := countP_pair (reach N m) (fun d => m + d = u) (fun d => m + d = v)
    (if m < u then u - m else 0) (if m < v then v - m else 0)
    (fun d h1 h2 => by split_ifs <;> omega) (fun d h1 h2 => by split_ifs <;> omega)
    (fun d h1 h2 => by split_ifs <;> omega)
  have e2 : (List.range' 1 (reach N m)).countP (fun d => decide (m + d ∈ ({u, v} : Finset Nat))) =
      (List.range' 1 (reach N m)).countP (fun d => decide (m + d = u ∨ m + d = v)) :=
    List.countP_congr fun d _ => by simp
  rw [e2, e]
  split_ifs <;> omega

/-- **Theorem G for a pair.**  `{u, v}` satisfies the criterion of Theorem G unless
`v ≥ 2u + 2` and `2v ≥ N + u + 3` (the "wide" pairs). -/
theorem inward_pair {N u v : Nat} (hu : 1 ≤ u) (huv : u < v) (hv : v ≤ N)
    (hc : v ≤ 2 * u + 1 ∨ 2 * v ≤ N + u + 2) : ∃ c2, Inward N c2 {u, v} := by
  rcases hc with hc | hc
  · refine ⟨2 * v + 1, fun m hm1 hmN hmB => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmB
    rw [leftCount_pair (by omega), rightCount_pair (by omega)]
    unfold reach
    refine ⟨by omega, fun h => ?_, fun h => ?_⟩ <;> split_ifs <;> omega
  · refine ⟨2 * u - 1, fun m hm1 hmN hmB => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmB
    rw [leftCount_pair (by omega), rightCount_pair (by omega)]
    unfold reach
    refine ⟨by omega, fun h => ?_, fun h => ?_⟩ <;> split_ifs <;> omega

theorem coReach_pair_inward {N u v : Nat} (hu : 1 ≤ u) (huv : u < v) (hv : v ≤ N)
    (hc : v ≤ 2 * u + 1 ∨ 2 * v ≤ N + u + 2) : CoReach N {u, v} := by
  obtain ⟨c2, h⟩ := inward_pair hu huv hv hc
  refine coReach_of_inward (fun x hx => ?_) h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rw [Finset.mem_Icc]; omega

/-! ## The copy `{1, 4, 6, …, N}` for `N ≡ 0 (mod 4)` -/

/-- `1 ↦ 2`, `y ↦ 2y - 1`: the complement `{2, 3, 5, …, N - 1}`. -/
def psiY (y : Nat) : Nat := if y = 1 then 2 else 2 * y - 1

/-- `1 ↦ 1`, `y ↦ 2y`: the copy `{1, 4, 6, …, N}`. -/
def chiY (y : Nat) : Nat := if y = 1 then 1 else 2 * y

/-- The pairs where `psiY` does not preserve the window relation. -/
def excY (n i j : Nat) : Prop := (i = 1 ∧ j = 2) ∨ (i = n / 2 + 1 ∧ j = 1)

theorem agree_psiY {n i j : Nat} (hn : 4 ≤ n) (he : n % 2 = 0) (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hj1 : 1 ≤ j) (hjn : j ≤ n) (_hij : i ≠ j) (hx : ¬ excY n i j) :
    Agree (2 * n) n psiY i j := by
  unfold excY at hx; unfold Agree psiY reach; split_ifs <;> omega

theorem psiY_inj {a b : Nat} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (e : psiY a = psiY b) : a = b := by
  unfold psiY at e; split_ifs at e <;> omega

theorem winEmb_chiY {n : Nat} (hn : 4 ≤ n) (he : n % 2 = 0) : WinEmb (2 * n) n chiY := by
  refine ⟨fun y h1 h2 => ?_, fun x y hx1 hxp hy1 hyp e => ?_, fun j y hj1 hjp hy1 hyp => ?_,
    fun j y hj1 hjp hy1 hyp => ?_⟩
  · unfold chiY; split_ifs <;> omega
  · unfold chiY at e; split_ifs at e <;> omega
  · unfold chiY reach; split_ifs <;> omega
  · unfold chiY reach; split_ifs <;> omega

theorem mem_image_psiY {n x : Nat} (hn : 4 ≤ n) :
    x ∈ (Finset.Icc 1 n).image psiY ↔ x = 2 ∨ (x % 2 = 1 ∧ 3 ≤ x ∧ x ≤ 2 * n - 1) := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rw [Finset.mem_Icc] at hy; unfold psiY; split_ifs <;> omega
  · intro h
    rcases h with rfl | h
    · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, by simp [psiY]⟩
    · exact ⟨(x + 1) / 2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by
        unfold psiY; split_ifs <;> omega⟩

theorem mem_image_chiY {n x : Nat} (hn : 4 ≤ n) :
    x ∈ (Finset.Icc 1 n).image chiY ↔ x = 1 ∨ (x % 2 = 0 ∧ 4 ≤ x ∧ x ≤ 2 * n) := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rw [Finset.mem_Icc] at hy; unfold chiY; split_ifs <;> omega
  · intro h
    rcases h with rfl | h
    · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, by simp [chiY]⟩
    · exact ⟨x / 2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by
        unfold chiY; split_ifs <;> omega⟩

theorem semiSymmetric_two_one (n : Nat) : SemiSymmetric n [2, 1] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  interval_cases k <;> simp [SemiStep, leftCount, rightCount, reach]

/-- **`{1, 4, 6, …, 2n}` is co-reachable** (`n` even, `n ≥ 4`): its complement is the image
under `psiY` of `τ ++ [1, 2]`, `τ` an ordering of `[3, n]` from scratch (Theorem G). -/
theorem coReach_Y {n : Nat} (hn : 4 ≤ n) (he : n % 2 = 0) :
    0 < g (2 * n) (Finset.Icc 1 (2 * n) \ (Finset.Icc 1 n).image chiY) := by
  obtain ⟨τ, hτn, hτs, hτv⟩ := coReach_list (coReach_interval (N := n) (a := 1) (b := 2)
    le_rfl (by omega) (by omega))
  have hτm : ∀ x, x ∈ τ ↔ 3 ≤ x ∧ x ≤ n := fun x => by
    rw [← List.mem_toFinset, hτs, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc]; omega
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = τ ++ [1, 2] := ⟨_, rfl⟩
  have hρn : ρ.Nodup := by
    rw [hρ, List.nodup_append]
    refine ⟨hτn, by simp, fun a ha b hb e => ?_⟩
    subst e
    rw [hτm] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    omega
  have hρs : ρ.toFinset = Finset.Icc 1 n := by
    ext x
    rw [List.mem_toFinset, hρ, List.mem_append, hτm, Finset.mem_Icc]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hρb : ∀ x ∈ ρ, 1 ≤ x ∧ x ≤ n := fun x hx => by
    have := List.mem_toFinset.2 hx; rw [hρs, Finset.mem_Icc] at this; exact this
  have hρf := isFoldSeq_of_toFinset hρn hρs
  have hρv : SemiSymmetric n ρ := by
    subst hρ
    exact semiSymmetric_append_rev hρf hτv (by simpa using semiSymmetric_two_one n)
  -- `n/2 + 1` (in `τ`) before `1` before `2`
  have hprec : Prec (excY n) ρ := by
    intro p hp j hj hex
    subst hρ
    rcases hex with ⟨ha, rfl⟩ | ⟨ha, rfl⟩
    · -- `ρ[p] = 1`: then `p = τ.length`, and `2 ∉ τ`
      have hp' : p = τ.length := by
        by_contra hne
        rcases Nat.lt_or_ge p τ.length with hlt | hge
        · have : (τ ++ [1, 2])[p] ∈ τ := by
            rw [List.getElem_append_left hlt]; exact List.getElem_mem _
          rw [ha, hτm] at this; omega
        · have hp1 : p - τ.length = 1 := by simp at hp; omega
          have : (τ ++ [1, 2])[p] = 2 := by
            rw [List.getElem_append_right hge]; simp [hp1]
          omega
      subst hp'
      rw [List.take_left] at hj
      rw [hτm] at hj; omega
    · -- `ρ[p] = n/2 + 1 ∈ τ`: `p < τ.length`, and `1 ∉ τ`
      have hpt : p < τ.length := by
        by_contra hge
        push Not at hge
        have : (τ ++ [1, 2])[p] ∈ [1, 2] := by
          rw [List.getElem_append_right hge]; exact List.getElem_mem _
        rw [ha] at this
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        omega
      rw [List.take_append_of_le_length hpt.le] at hj
      have := (hτm 1).1 (List.mem_of_mem_take hj)
      omega
  have hmap : SemiSymmetric (2 * n) (ρ.map psiY) :=
    semiSymmetric_near hρb hρn hρv hprec (fun a b ha1 _ hb1 _ e => psiY_inj ha1 hb1 e)
      (fun _ _ hi1 hin hj1 hjn hij hx => agree_psiY hn he hi1 hin hj1 hjn hij hx)
  unfold g
  rw [Finset.card_pos]
  refine ⟨ρ.map psiY, mem_semiOrders.2 ⟨⟨nodup_map_of_injOn hρn fun a ha b hb e =>
    psiY_inj (hρb a ha).1 (hρb b hb).1 e, ?_⟩, hmap⟩⟩
  ext x
  have hx : x ∈ ρ.map psiY ↔ x ∈ (Finset.Icc 1 n).image psiY := by
    rw [List.mem_map, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, e⟩
      exact ⟨a, by rw [← hρs, List.mem_toFinset]; exact ha, e⟩
    · rintro ⟨a, ha, e⟩
      exact ⟨a, by rw [← List.mem_toFinset, hρs]; exact ha, e⟩
  rw [List.mem_toFinset, hx, mem_image_psiY hn, Finset.mem_sdiff, mem_image_chiY hn,
    Finset.mem_Icc]
  omega

/-- **Transfer through `{1, 4, 6, …, 2n}`** (`n` even, `n ≥ 4`). -/
theorem coReach_chiY_transfer {n : Nat} (hn : 4 ≤ n) (he : n % 2 = 0) {D : Finset Nat}
    (hDs : D ⊆ Finset.Icc 1 n) (hD : CoReach n D) : CoReach (2 * n) (D.image chiY) :=
  coReach_winEmb (winEmb_chiY hn he) (coReach_Y hn he) hDs hD

/-- **`{1, N/2 + 2}` is co-reachable for `N ≡ 0 (mod 4)`, `N ≥ 8`**: the image under `chiY` of
`{1, N/4 + 1}` in `[N/2]`, which satisfies Theorem G. -/
theorem coReach_one_half {N : Nat} (hN : 8 ≤ N) (h4 : N % 4 = 0) :
    CoReach N {1, N / 2 + 2} := by
  have hD : CoReach (N / 2) {1, N / 4 + 1} :=
    coReach_pair_inward le_rfl (by omega) (by omega) (Or.inr (by omega))
  have := coReach_chiY_transfer (n := N / 2) (by omega) (by omega) (D := {1, N / 4 + 1})
    (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]; omega) hD
  rw [show 2 * (N / 2) = N by omega, Finset.image_insert, Finset.image_singleton] at this
  have e1 : chiY 1 = 1 := by simp [chiY]
  have e2 : chiY (N / 4 + 1) = N / 2 + 2 := by unfold chiY; split_ifs <;> omega
  rwa [e1, e2] at this

/-! ## Swapped Beatty copies -/

/-- The swapped Beatty map: the right-aligned Beatty copy `X(N, p, h)` with its last element
moved to `N - c`. -/
def swapF (N p h c r : Nat) : Nat := if r = p then N - c else beatty N p h r

/-- Hypotheses of the swap lemma: `p ≥ 3` odd, `h ≤ 1`, `c ≥ 2`, `N + h ≥ 2cp + 1`. -/
structure SwapHyp (N p h c : Nat) : Prop where
  p3 : 3 ≤ p
  odd : p % 2 = 1
  h1 : h ≤ 1
  c2 : 2 ≤ c
  big : 2 * c * p + 1 ≤ N + h

theorem SwapHyp.hh {N p h c : Nat} (H : SwapHyp N p h c) : h + 2 * p ≤ N + 1 := by
  have := H.big; have := H.c2; have := H.h1; have := H.p3
  nlinarith

theorem SwapHyp.N4 {N p h c : Nat} (H : SwapHyp N p h c) : 4 * p ≤ N ∧ 2 * c + 2 ≤ N := by
  have := H.big; have := H.c2; have := H.h1; have := H.p3
  constructor <;> nlinarith

theorem beatty_mono {N p h y z : Nat} (hyz : y ≤ z) : beatty N p h y ≤ beatty N p h z :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.mul_le_mul_right N hyz) h)

theorem beatty_top {N p h : Nat} (hp : 2 ≤ p) (h1 : h ≤ 1) (hN : 1 ≤ N) :
    beatty N p h p = N - h := by
  unfold beatty
  interval_cases h
  · rw [Nat.sub_zero, Nat.sub_zero, Nat.mul_div_cancel_left N (by omega)]
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [show M + 1 - 1 = M by omega]
    have e : p * (M + 1) = p * M + p := by ring
    have e2 : (M + 1) * p = p * M + p := by ring
    have e3 : M * p = p * M := Nat.mul_comm M p
    apply Nat.div_eq_of_lt_le
    · rw [e3, e]; omega
    · rw [e2, e]; omega

/-- The last-but-one element lies below `N - 2c`. -/
theorem swap_last {N p h c : Nat} (H : SwapHyp N p h c) :
    beatty N p h (p - 1) + 2 * c < N := by
  have big := H.big; have c2 := H.c2; have h1 := H.h1; have p3 := H.p3
  unfold beatty
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  rw [show p' + 1 - 1 = p' by omega]
  have hc : 2 * c ≤ N := by nlinarith
  obtain ⟨t, rfl⟩ : ∃ t, N = 2 * c + t := ⟨N - 2 * c, by omega⟩
  have key : p' * (2 * c + t) < t * (p' + 1) + h := by nlinarith
  have ht1 : 1 ≤ t := by nlinarith
  have ht : 1 ≤ t * (p' + 1) := Nat.mul_pos ht1 (by omega)
  have : (p' * (2 * c + t) - h) / (p' + 1) < t := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    omega
  omega

/-- The elements left of the middle stay at most `(N - c)/2`. -/
theorem swap_mid_lo {N p h c : Nat} (H : SwapHyp N p h c) :
    2 * beatty N p h (p / 2) + c ≤ N := by
  have big := H.big; have c2 := H.c2; have h1 := H.h1; have p3 := H.p3
  unfold beatty
  obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by have := H.odd; omega⟩
  rw [show (2 * k + 1) / 2 = k by omega]
  have hq := Nat.div_mul_le_self (k * N - h) (2 * k + 1)
  generalize (k * N - h) / (2 * k + 1) = q at hq ⊢
  have hq' : q * (2 * k + 1) ≤ k * N := le_trans hq (Nat.sub_le _ _)
  by_contra hcon
  have h2 : (N + 1) * (2 * k + 1) ≤ (2 * q + c) * (2 * k + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- The elements right of the middle lie beyond `N/2`. -/
theorem swap_mid_hi {N p h c : Nat} (H : SwapHyp N p h c) :
    N + 1 ≤ 2 * beatty N p h (p / 2 + 1) := by
  have hN4 := H.N4; have h1 := H.h1; have p3 := H.p3
  unfold beatty
  obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by have := H.odd; omega⟩
  rw [show (2 * k + 1) / 2 = k by omega]
  have hm := Nat.div_add_mod ((k + 1) * N - h) (2 * k + 1)
  have hlt := Nat.mod_lt ((k + 1) * N - h) (show 0 < 2 * k + 1 by omega)
  have hx : (k + 1) * N - h + h = (k + 1) * N := Nat.sub_add_cancel (by nlinarith)
  generalize ((k + 1) * N - h) / (2 * k + 1) = q at hm ⊢
  generalize ((k + 1) * N - h) % (2 * k + 1) = r at hm hlt
  generalize (k + 1) * N - h = x at hm hx
  by_contra hcon
  have h2 : (2 * q) * (2 * k + 1) ≤ N * (2 * k + 1) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem swap_facts {N p h c : Nat} (H : SwapHyp N p h c) {y : Nat} (_hy1 : 1 ≤ y)
    (hyp : y ≤ p - 1) :
    beatty N p h y + 2 * c < N ∧ ¬ (N - c + 1 ≤ 2 * beatty N p h y ∧ 2 * beatty N p h y ≤ N - h) := by
  refine ⟨lt_of_le_of_lt (Nat.add_le_add_right (beatty_mono hyp) _) (swap_last H), ?_⟩
  rcases Nat.lt_or_ge (p / 2) y with hy | hy
  · have := beatty_mono (N := N) (p := p) (h := h) (show p / 2 + 1 ≤ y by omega)
    have := swap_mid_hi H
    omega
  · have := beatty_mono (N := N) (p := p) (h := h) hy
    have := swap_mid_lo H
    omega

theorem swapF_lt {N p h c j : Nat} (hj : j < p) : swapF N p h c j = beatty N p h j :=
  by unfold swapF; split_ifs <;> first | rfl | omega

theorem swapF_top {N p h c : Nat} : swapF N p h c p = N - c := by
  unfold swapF; simp

/-- **The swapped Beatty set is a window copy.** -/
theorem winEmb_swap {N p h c : Nat} (H : SwapHyp N p h c) : WinEmb N p (swapF N p h c) := by
  have hh := H.hh
  have hN4 := H.N4
  have hp3 := H.p3
  have wb := winEmb_beatty (show 1 ≤ p by omega) hh
  have htop := beatty_top (N := N) (show 2 ≤ p by omega) H.h1 (by omega)
  refine ⟨fun y h1 h2 => ?_, fun x y hx1 hxp hy1 hyp e => ?_, fun j y hj1 hjp hy1 hyp => ?_,
    fun j y hj1 hjp hy1 hyp => ?_⟩
  · rcases Nat.lt_or_ge y p with hy | hy
    · rw [swapF_lt hy]; exact wb.bound y h1 h2
    · rw [show y = p by omega, swapF_top]; omega
  · rcases Nat.lt_or_ge x p with hx | hx <;> rcases Nat.lt_or_ge y p with hy | hy
    · rw [swapF_lt hx, swapF_lt hy] at e; exact wb.inj x y hx1 hxp hy1 hyp e
    · rw [swapF_lt hx, show y = p by omega, swapF_top] at e
      have := (swap_facts H hx1 (by omega)).1; omega
    · rw [swapF_lt hy, show x = p by omega, swapF_top] at e
      have := (swap_facts H hy1 (by omega)).1; omega
    · omega
  · rcases Nat.lt_or_ge j p with hj | hj <;> rcases Nat.lt_or_ge y p with hy | hy
    · rw [swapF_lt hj, swapF_lt hy]; exact wb.left j y hj1 hjp hy1 hyp
    · rw [swapF_lt hj, show y = p by omega, swapF_top]
      have := (swap_facts H hj1 (by omega)).1
      constructor <;> intro h' <;> omega
    · rw [swapF_lt hy, show j = p by omega, swapF_top]
      have := (swap_facts H hy1 (by omega)).1
      unfold reach
      constructor <;> intro h' <;> omega
    · rw [show j = p by omega, show y = p by omega]
      constructor <;> intro h' <;> omega
  · rcases Nat.lt_or_ge j p with hj | hj <;> rcases Nat.lt_or_ge y p with hy | hy
    · rw [swapF_lt hj, swapF_lt hy]; exact wb.right j y hj1 hjp hy1 hyp
    · have key := wb.right j p hj1 hjp (by omega) le_rfl
      rw [htop] at key
      rw [swapF_lt hj, show y = p by omega, swapF_top, ← key]
      obtain ⟨hA, hB⟩ := swap_facts H hj1 (by omega)
      rw [not_and_or, Nat.not_le, Nat.not_le] at hB
      have := H.h1; have := H.c2
      unfold reach
      constructor <;> intro h' <;> omega
    · rw [swapF_lt hy, show j = p by omega, swapF_top]
      have := (swap_facts H hy1 (by omega)).1
      constructor <;> intro h' <;> omega
    · rw [show j = p by omega, show y = p by omega]
      constructor <;> intro h' <;> omega

theorem mem_swap {N p h c x : Nat} (H : SwapHyp N p h c) :
    x ∈ (Finset.Icc 1 p).image (swapF N p h c) ↔
      x = N - c ∨ x ∈ (Finset.Icc 1 (p - 1)).image (beatty N p h) := by
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases Nat.lt_or_ge y p with h' | h'
    · exact Or.inr ⟨y, ⟨hy.1, by omega⟩, (swapF_lt h').symm⟩
    · exact Or.inl (by rw [show y = p by omega, swapF_top])
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · exact ⟨p, ⟨by have := H.p3; omega, le_rfl⟩, swapF_top⟩
    · exact ⟨y, ⟨hy.1, by omega⟩, swapF_lt (by have := H.p3; omega)⟩

theorem mem_beatty_top {N p h c x : Nat} (H : SwapHyp N p h c) :
    x ∈ (Finset.Icc 1 p).image (beatty N p h) ↔
      x = N - h ∨ x ∈ (Finset.Icc 1 (p - 1)).image (beatty N p h) := by
  have hN4 := H.N4
  have htop := beatty_top (N := N) (show 2 ≤ p by have := H.p3; omega) H.h1 (by omega)
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases Nat.lt_or_ge y p with h' | h'
    · exact Or.inr ⟨y, ⟨hy.1, by omega⟩, rfl⟩
    · exact Or.inl (by rw [show y = p by omega, htop])
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · exact ⟨p, ⟨by have := H.p3; omega, le_rfl⟩, htop⟩
    · exact ⟨y, ⟨hy.1, by omega⟩, rfl⟩

theorem lt_of_mem_low {N p h c x : Nat} (H : SwapHyp N p h c)
    (hx : x ∈ (Finset.Icc 1 (p - 1)).image (beatty N p h)) : x + 2 * c < N := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
  rw [Finset.mem_Icc] at hy
  exact (swap_facts H hy.1 hy.2).1

/-- **The swapped Beatty set satisfies Theorem G** with the centre at `N - c`: left of it,
the Beatty set already pulls every panel to the right and the move only adds to right arms;
right of it, nothing of the set lies in a right arm. -/
theorem inward_swap {N p h c : Nat} (H : SwapHyp N p h c) :
    Inward N (2 * (N - c)) ((Finset.Icc 1 p).image (swapF N p h c)) := by
  have hh := H.hh
  have hN4 := H.N4
  have h1 := H.h1
  have c2 := H.c2
  intro m hm1 hmN hmB
  have hmc : m ≠ N - c := fun e => hmB ((mem_swap H).2 (Or.inl e))
  have hmZ : m ∉ (Finset.Icc 1 (p - 1)).image (beatty N p h) := fun e =>
    hmB ((mem_swap H).2 (Or.inr e))
  refine ⟨by omega, fun hlt => ?_, fun hgt => ?_⟩
  · have hmX : m ∉ (Finset.Icc 1 p).image (beatty N p h) := by
      rw [mem_beatty_top H]; rintro (e | e)
      · omega
      · exact hmZ e
    have hb := (inward_beatty (show 1 ≤ p by have := H.p3; omega) hh h1 m hm1 hmN hmX).2.1
      (by omega)
    rw [leftCount_finset, rightCount_finset] at hb ⊢
    have hr : reach N m ≤ m - 1 := by unfold reach; omega
    have L : (List.range' 1 (reach N m)).countP
        (fun d => decide (m - d ∈ (Finset.Icc 1 p).image (swapF N p h c))) =
        (List.range' 1 (reach N m)).countP
        (fun d => decide (m - d ∈ (Finset.Icc 1 p).image (beatty N p h))) := by
      apply List.countP_congr; intro d hd; rw [List.mem_range'_1] at hd
      simp only [decide_eq_true_eq, mem_swap H, mem_beatty_top H]
      constructor <;> rintro (e | e)
      · omega
      · exact Or.inr e
      · omega
      · exact Or.inr e
    rw [L]
    set Z := (Finset.Icc 1 (p - 1)).image (beatty N p h)
    have R1 : (List.range' 1 (reach N m)).countP
        (fun d => decide (m + d ∈ (Finset.Icc 1 p).image (beatty N p h))) ≤
        (List.range' 1 (reach N m)).countP (fun d => decide (m + d ∈ Z)) +
        (List.range' 1 (reach N m)).countP (fun d => decide (d = N - h - m)) := by
      refine le_trans (le_of_eq (List.countP_congr fun d hd => ?_)) (countP_or_le _ _ _)
      rw [List.mem_range'_1] at hd
      simp only [Bool.or_eq_true, decide_eq_true_eq, mem_beatty_top H]
      constructor
      · rintro (e | e)
        · exact Or.inr (by omega)
        · exact Or.inl e
      · rintro (e | e)
        · exact Or.inr e
        · exact Or.inl (by omega)
    have R2 : (List.range' 1 (reach N m)).countP (fun d => decide (m + d ∈ Z)) +
        (List.range' 1 (reach N m)).countP (fun d => decide (d = N - c - m)) ≤
        (List.range' 1 (reach N m)).countP
        (fun d => decide (m + d ∈ (Finset.Icc 1 p).image (swapF N p h c))) := by
      refine countP_add_le _ _ _ _ (fun d hd => ?_) (fun d hd => ?_) (fun d hd => ?_)
      · simp only [decide_eq_true_eq]
        rintro ⟨e1, e2⟩
        have := lt_of_mem_low H e1
        omega
      · simp only [decide_eq_true_eq, mem_swap H]; exact Or.inr
      · rw [List.mem_range'_1] at hd
        simp only [decide_eq_true_eq, mem_swap H]; intro e; left; omega
    rw [countP_single] at R1 R2
    split_ifs at R1 R2 <;> omega
  · rw [rightCount_finset]
    have : (List.range' 1 (reach N m)).countP
        (fun d => decide (m + d ∈ (Finset.Icc 1 p).image (swapF N p h c))) = 0 := by
      rw [List.countP_eq_zero]
      intro d hd
      rw [List.mem_range'_1] at hd
      simp only [decide_eq_true_eq, mem_swap H]
      rintro (e | e)
      · omega
      · have := lt_of_mem_low H e; omega
    rw [this]; exact Nat.zero_le _

theorem coReach_swap {N p h c : Nat} (H : SwapHyp N p h c) :
    CoReach N ((Finset.Icc 1 p).image (swapF N p h c)) := by
  refine coReach_of_inward (fun x hx => ?_) (inward_swap H)
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
  rw [Finset.mem_Icc] at hy ⊢
  exact (winEmb_swap H).bound y hy.1 hy.2

/-- **Transfer through a swapped Beatty copy.** -/
theorem coReach_swap_transfer {N p h c : Nat} (H : SwapHyp N p h c) {D : Finset Nat}
    (hDs : D ⊆ Finset.Icc 1 p) (hD : CoReach p D) : CoReach N (D.image (swapF N p h c)) :=
  coReach_winEmb (winEmb_swap H) (coReach_swap H) hDs hD

/-- **Corner pairs.**  For `p ≥ 3` odd, `p ≠ 7`, `h ≤ 1`, `c ≥ 2` and `N + h ≥ 2cp + 1`, the pair
`{c + 1, N + 1 - ⌊(N - h)/p⌋}` is co-reachable: the mirror of the image of `{1, p}` under the
swapped Beatty copy. -/
theorem coReach_corner {N p h c : Nat} (H : SwapHyp N p h c) (hp7 : p ≠ 7) :
    CoReach N {c + 1, N + 1 - (N - h) / p} := by
  have hN4 := H.N4
  have h1p := coReach_one_N p H.odd hp7
  have := coReach_mirror (coReach_swap_transfer H (D := {1, p}) (fun x hx => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Icc]; have := H.p3; omega) h1p)
  rw [Finset.image_insert, Finset.image_singleton, Finset.image_insert,
    Finset.image_singleton, swapF_top, swapF_lt (by have := H.p3; omega)] at this
  have e : beatty N p h 1 = (N - h) / p := by unfold beatty; rw [Nat.one_mul]
  rw [e, show N + 1 - (N - c) = c + 1 by omega, Finset.pair_comm] at this
  exact this

/-- **`{3, N - 3}` is co-reachable for every `N ≥ 37`**: a corner pair with `c = 2`, `h = 1`
and `p` the odd number among `⌊(N-1)/4⌋, ⌊(N-1)/4⌋ - 1` (so `4p ≤ N - 1 < 5p`, `p ≥ 9`). -/
theorem coReach_three {N : Nat} (hN : 37 ≤ N) : CoReach N {3, N - 3} := by
  obtain ⟨p, hp⟩ : ∃ p, p = if (N - 1) / 4 % 2 = 1 then (N - 1) / 4 else (N - 1) / 4 - 1 :=
    ⟨_, rfl⟩
  have hp9 : 9 ≤ p ∧ p % 2 = 1 ∧ 4 * p ≤ N - 1 ∧ N - 1 < 5 * p := by
    rw [hp]; split_ifs <;> omega
  have H : SwapHyp N p 1 2 := ⟨by omega, hp9.2.1, le_rfl, le_rfl, by omega⟩
  have := coReach_corner H (by omega)
  have e : (N - 1) / p = 4 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rwa [e, show N + 1 - 4 = N - 3 by omega] at this

/-! ## The enlarged proven family -/

/-- `Cov6`: `Cov5` closed under residue transfers, multiples of `q`, Beatty copies, splits,
swapped Beatty copies, the copy `chiY` (`N ≡ 0 mod 4`) and the mirror. -/
inductive Cov6 : Nat → Finset Nat → Prop
  | cov5 {N : Nat} {D : Finset Nat} : Cov5 N D → Cov6 N D
  | res {q N s : Nat} {D : Finset Nat} : 2 ≤ q → q ≤ N → Good q (N % q) s →
      D ⊆ Finset.Icc 1 (ccount q s N) → Cov6 (ccount q s N) D → Cov6 N (D.image (cls q s))
  | mult {q N : Nat} {D : Finset Nat} : 2 ≤ q → q ≤ N → (N + 1) % q = 0 →
      D ⊆ Finset.Icc 1 (ccount q q N) → Cov6 (ccount q q N) D → Cov6 N (D.image (cls q q))
  | beatty {N p h : Nat} {D : Finset Nat} : 1 ≤ p → h + 2 * p ≤ N + 1 → h ≤ 1 →
      D ⊆ Finset.Icc 1 p → Cov6 p D → Cov6 N (D.image (beatty N p h))
  | split {N p q : Nat} {φ ψ : Nat → Nat} {D : Finset Nat} : Split N p q φ ψ →
      D ⊆ Finset.Icc 1 p → Cov6 p D → Cov6 N (D.image φ)
  | swap {N p h c : Nat} {D : Finset Nat} : SwapHyp N p h c →
      D ⊆ Finset.Icc 1 p → Cov6 p D → Cov6 N (D.image (swapF N p h c))
  | chiY {n : Nat} {D : Finset Nat} : 4 ≤ n → n % 2 = 0 →
      D ⊆ Finset.Icc 1 n → Cov6 n D → Cov6 (2 * n) (D.image chiY)
  | mirror {N : Nat} {D : Finset Nat} : Cov6 N D → Cov6 N (D.image (N + 1 - ·))

theorem Cov6.coReach {N : Nat} {D : Finset Nat} (h : Cov6 N D) : CoReach N D := by
  induction h with
  | cov5 h => exact h.coReach
  | res hq2 hqN hg hDs _ ih => exact coReach_good (by omega) hqN hg hDs ih
  | mult hq2 hqN hN hDs _ ih => exact coReach_mult_transfer (by omega) hqN hN hDs ih
  | beatty hp hh h1 hDs _ ih => exact coReach_beatty_transfer hp hh h1 hDs ih
  | split hs hDs _ ih => exact coReach_split hs hDs ih
  | swap H hDs _ ih => exact coReach_swap_transfer H hDs ih
  | chiY hn he hDs _ ih => exact coReach_chiY_transfer hn he hDs ih
  | mirror _ ih => exact coReach_mirror ih

/-- Every valid 2-prefix whose set is in the family is live. -/
theorem Cov6.extends {N u v : Nat} (h : Cov6 N {u, v}) (hu : 1 ≤ u ∧ u ≤ N)
    (hv : 1 ≤ v ∧ v ≤ N) (huv : u ≠ v) (hval : SemiSymmetric N [u, v]) :
    Extends N [u, v] := by
  rw [extends_iff_coReach (by simp [huv]) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption) hval]
  convert h.coReach using 2
  ext x; simp

/-! ## Conjecture C modulo a covering statement -/

/-- A pair `u < v` of `[N]` is *directly settled* if it satisfies Theorem G, is `{1, N}`
(`N` odd, `N ≠ 7`), or is the image of a NON-DEAD pair of a smaller strip under a
right-aligned Beatty copy, a swapped Beatty copy, the copy `chiY` or a doubling split. -/
def Settled (N u v : Nat) : Prop :=
  (v ≤ 2 * u + 1 ∨ 2 * v ≤ N + u + 2) ∨
  (u = 1 ∧ v = N ∧ N % 2 = 1 ∧ N ≠ 7) ∨
  (∃ p h a b, 1 ≤ p ∧ h + 2 * p ≤ N + 1 ∧ h ≤ 1 ∧ 1 ≤ a ∧ a < b ∧ b ≤ p ∧
    deadB p a b = false ∧ beatty N p h a = u ∧ beatty N p h b = v) ∨
  (∃ p h c a b, SwapHyp N p h c ∧ 1 ≤ a ∧ a < b ∧ b ≤ p ∧
    deadB p a b = false ∧ swapF N p h c a = u ∧ swapF N p h c b = v) ∨
  (∃ a b, N % 4 = 0 ∧ 8 ≤ N ∧ 1 ≤ a ∧ a < b ∧ b ≤ N / 2 ∧
    deadB (N / 2) a b = false ∧ chiY a = u ∧ chiY b = v) ∨
  (∃ j n a b, 1 ≤ j ∧ N = (2 * j + 1) * n ∧ 1 ≤ a ∧ a < b ∧
    ((b ≤ (j + 1) * n ∧ deadB ((j + 1) * n) a b = false ∧ oddRes j a = u ∧ oddRes j b = v) ∨
     (b ≤ j * n ∧ deadB (j * n) a b = false ∧ evenRes j a = u ∧ evenRes j b = v)))

/-- The covering statement with an exceptional set `E`: from `N = 13` on, every non-dead pair
or its mirror is directly settled, or lies in `E`.  (Numerically, for `13 ≤ N ≤ 520` the pairs
settled by neither are exactly 55 pairs (up to the mirror) with `N ≤ 103` and, for `N = 2^k`,
the pairs `(3, N - 2)` and `(5, N - 4)`: `experiments/live6/core.py`.) -/
def CoverLemma (E : Nat → Nat → Nat → Prop) : Prop :=
  ∀ N u v, 13 ≤ N → 1 ≤ u → u < v → v ≤ N → deadB N u v = false →
    Settled N u v ∨ Settled N (N + 1 - v) (N + 1 - u) ∨ E N u v

theorem coReach_image_pair {N : Nat} {φ : Nat → Nat} {a b u v : Nat}
    (h : CoReach N (({a, b} : Finset Nat).image φ)) (ha : φ a = u) (hb : φ b = v) :
    CoReach N {u, v} := by
  rwa [Finset.image_insert, Finset.image_singleton, ha, hb] at h

theorem pair_sub {a b p : Nat} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ p) :
    ({a, b} : Finset Nat) ⊆ Finset.Icc 1 p := fun x hx => by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rw [Finset.mem_Icc]; omega

/-- **Conjecture C modulo the covering statement**: if `CoverLemma` holds, every non-dead pair
is co-reachable.  Strong induction on `N`; base `N ≤ 12` (`Live2.coReach_base`). -/
theorem coReach_of_cover {E : Nat → Nat → Nat → Prop}
    (hX : ∀ N u v, E N u v → CoReach N {u, v}) (hcov : CoverLemma E) :
    ∀ N u v, 1 ≤ u → u < v → v ≤ N → deadB N u v = false → CoReach N {u, v} := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro u v hu huv hv hd
    by_cases h12 : N ≤ 12
    · exact coReach_base h12 hu huv hv hd
    have key : ∀ u v, 1 ≤ u → u < v → v ≤ N → Settled N u v → CoReach N {u, v} := by
      intro u v hu huv hv hS
      rcases hS with hS | hS | ⟨p, h, a, b, hp, hh, h1, ha, hab, hb, hdp, e1, e2⟩ |
        ⟨p, h, c, a, b, H, ha, hab, hb, hdp, e1, e2⟩ | ⟨a, b, h4, h8, ha, hab, hb, hdp, e1, e2⟩ |
        ⟨j, n, a, b, hj, hN, ha, hab, hS⟩
      · exact coReach_pair_inward hu huv hv hS
      · obtain ⟨rfl, rfl, hodd, h7⟩ := hS
        exact coReach_one_N _ hodd h7
      · exact coReach_image_pair (coReach_beatty_transfer hp hh h1 (pair_sub ha hab hb)
          (ih p (by omega) a b ha hab hb hdp)) e1 e2
      · have := H.N4
        exact coReach_image_pair (coReach_swap_transfer H (pair_sub ha hab hb)
          (ih p (by omega) a b ha hab hb hdp)) e1 e2
      · have := coReach_chiY_transfer (n := N / 2) (by omega) (by omega) (pair_sub ha hab hb)
          (ih (N / 2) (by omega) a b ha hab hb hdp)
        rw [show 2 * (N / 2) = N by omega] at this
        exact coReach_image_pair this e1 e2
      · have hn : 1 ≤ n := by
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · rw [h0, Nat.mul_zero] at hN; omega
          · exact h0
        have hjn : 1 ≤ j * n := Nat.mul_pos hj hn
        have e : (2 * j + 1) * n = (j + 1) * n + j * n := by ring
        have : j * n ≤ (j + 1) * n := Nat.mul_le_mul_right n (by omega)
        rcases hS with ⟨hb, hdp, e1, e2⟩ | ⟨hb, hdp, e1, e2⟩
        · have := coReach_split (split_res hj n).symm (pair_sub ha hab hb)
            (ih ((j + 1) * n) (by omega) a b ha hab hb hdp)
          rw [← hN] at this
          exact coReach_image_pair this e1 e2
        · have := coReach_split (split_res hj n) (pair_sub ha hab hb)
            (ih (j * n) (by omega) a b ha hab hb hdp)
          rw [← hN] at this
          exact coReach_image_pair this e1 e2
    rcases hcov N u v (by omega) hu huv hv hd with hS | hS | hS
    · exact key u v hu huv hv hS
    · have := coReach_mirror (key (N + 1 - v) (N + 1 - u) (by omega) (by omega) (by omega) hS)
      rw [Finset.image_insert, Finset.image_singleton,
        show N + 1 - (N + 1 - v) = v by omega, show N + 1 - (N + 1 - u) = u by omega,
        Finset.pair_comm] at this
      exact this
    · exact hX N u v hS

/-- **Conjecture C for valid 2-prefixes, modulo `CoverLemma E`** (with the pairs of `E`
co-reachable): a valid prefix `[m₁, m₂]` is live iff `{m₁, m₂}` is not one of the dead pairs
`{1, N}` (`N` even `≥ 4`) and `{1, 7}` (`N = 7`).  (The direction "dead ⇒ not live" is
unconditional: `WindowRule.not_extends_one_N`, `not_extends_seven`.) -/
theorem extends_iff_not_dead {E : Nat → Nat → Nat → Prop}
    (hX : ∀ N u v, E N u v → CoReach N {u, v}) (hcov : CoverLemma E) {N m₁ m₂ : Nat}
    (h1 : 1 ≤ m₁ ∧ m₁ ≤ N)
    (h2 : 1 ≤ m₂ ∧ m₂ ≤ N) (h12 : m₁ ≠ m₂) (hval : SemiSymmetric N [m₁, m₂]) :
    Extends N [m₁, m₂] ↔ deadB N (min m₁ m₂) (max m₁ m₂) = false := by
  constructor
  · intro hE
    by_contra hd
    rw [Bool.not_eq_false] at hd
    unfold deadB at hd
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨hmin, hmax⟩, hN⟩ := hd
    rcases hN with ⟨hev, h4⟩ | h7
    · have := not_extends_one_N (N := N) hev (by omega)
      rcases Nat.lt_or_ge m₁ m₂ with hlt | hge
      · rw [min_eq_left hlt.le] at hmin; rw [max_eq_right hlt.le] at hmax
        subst hmin hmax; exact this.1 hE
      · rw [min_eq_right hge] at hmin; rw [max_eq_left hge] at hmax
        subst hmin hmax; exact this.2 hE
    · subst h7
      have := not_extends_seven
      rcases Nat.lt_or_ge m₁ m₂ with hlt | hge
      · rw [min_eq_left hlt.le] at hmin; rw [max_eq_right hlt.le] at hmax
        subst hmin hmax; exact this.1 hE
      · rw [min_eq_right hge] at hmin; rw [max_eq_left hge] at hmax
        subst hmin hmax; exact this.2 hE
  · intro hd
    rw [extends_iff_coReach (by simp [h12]) (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> assumption) hval]
    have hset : [m₁, m₂].toFinset = {min m₁ m₂, max m₁ m₂} := by
      ext x; simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
        Finset.mem_singleton, insert_empty_eq]
      rcases Nat.lt_or_ge m₁ m₂ with hlt | hge
      · rw [min_eq_left hlt.le, max_eq_right hlt.le]
      · rw [min_eq_right hge, max_eq_left hge]; tauto
    rw [hset]
    exact coReach_of_cover hX hcov N _ _ (by omega) (by omega) (by omega) hd

end Live6
end Folds
