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

end Live6
end Folds
