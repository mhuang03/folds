import Folds.WindowRule
import Folds.Blocks
import Folds.Extremal
import Folds.RevMirror
import Folds.Growth

/-!
# Live prefixes

`Extends N p` (from `WindowRule.lean`): the partial sequence `p` can be completed to a
semi-symmetric fold sequence.

Live side.
* `extends_single`: **every panel is a live first step**, `Extends N [m]` for `1 ≤ m ≤ N`
  (parity blocks, strong induction on `N`); `exists_semiSymmetric`.
* Transfer lemmas: live prefixes of a smaller strip stay live through
  - the parity classes `y ↦ 2y - c` (`extends_scale`),
  - any window embedding whose complement is reachable from scratch (`extends_winEmb`,
    the *weak split*: complete the copy, then the rest reversed),
  - either half of a `Split` (`Split.extends`), e.g. the mod-3 split (`extends_three`),
  - the shifted parity block `shX` for `N = 2n` (`extends_shX`).
  `extends_congr`: liveness of a valid prefix only depends on its set of panels.

Dead side (with `not_extends_one_N` from `WindowRule.lean` these are all dead 2- and
3-prefixes for `N = 6` and `N ≥ 8`, see `experiments/live/`).
* `dead_block`, `not_extends_block`, `not_extends_three_block`: a prefix containing
  `1, 2j, 2j+1` (`j ≥ 2`, `4j ≤ N + 3`) but nothing of `[2, 2j-1]` is dead (the first
  panel of `[2, 2j-1]` sees one bisected panel on its left arm and `0` or `≥ 2` on its
  right arm); mirror images (`not_extends_block_mirror`).
* `not_extends_corner`: for odd `N ≥ 7` every prefix whose panels form a 3-subset of
  `{1, 2, N-1, N}` is dead.
* `not_extends_seven`: the sporadic dead 2-prefixes `[1, 7]`, `[7, 1]` for `N = 7`.
-/

namespace Folds

/-- **Parity transfer.**  A live prefix of the class-`c` world `[1..(N+c)/2]` stays live
after scaling into `[1..N]`: complete it there, then append any semi-symmetric sequence of
the other class. -/
theorem extends_scale {N c : Nat} (hc : c ≤ 1) {p : List Nat}
    (hp : Extends ((N + c) / 2) p)
    (hτ : ∃ τ, IsFoldSeq ((N + (1 - c)) / 2) τ ∧ SemiSymmetric ((N + (1 - c)) / 2) τ) :
    Extends N (p.map (scale c)) := by
  obtain ⟨σ, hσf, hσs, hpre⟩ := hp
  obtain ⟨τ, hτf, hτs⟩ := hτ
  exact ⟨_, hσf.blocks hc hτf, (semiSymmetric_blocks_iff hc hσf hτf).2 ⟨hσs, hτs⟩,
    (hpre.map _).trans (List.prefix_append _ _)⟩

theorem semiSymmetric_one : SemiSymmetric 1 [1] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  obtain rfl : k = 0 := by omega
  simp [SemiStep, leftCount, rightCount, reach]

/-- **Every panel is a live first step.** -/
theorem extends_single (N : Nat) : ∀ m, 1 ≤ m → m ≤ N → Extends N [m] := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro m hm1 hmN
    by_cases hN : N = 1
    · subst hN
      obtain rfl : m = 1 := by omega
      exact ⟨[1], List.Perm.refl _, semiSymmetric_one, List.prefix_refl _⟩
    · have hc : m % 2 ≤ 1 := by omega
      have h1 := ih ((N + m % 2) / 2) (by omega) ((m + m % 2) / 2) (by omega) (by omega)
      obtain ⟨τ, hτf, hτs, -⟩ :=
        ih ((N + (1 - m % 2)) / 2) (by omega) 1 le_rfl (by omega)
      have := extends_scale hc h1 ⟨τ, hτf, hτs⟩
      have e : scale (m % 2) ((m + m % 2) / 2) = m := by unfold scale; omega
      simpa [e] using this

/-- Every strip has a semi-symmetric fold sequence. -/
theorem exists_semiSymmetric (N : Nat) : ∃ a, IsFoldSeq N a ∧ SemiSymmetric N a := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨[], List.Perm.refl _, fun k hk => absurd hk (by simp)⟩
  · obtain ⟨a, hf, hs, -⟩ := extends_single N 1 le_rfl hN
    exact ⟨a, hf, hs⟩

/-! ## Transfer lemmas -/

/-- Liveness of a valid prefix depends only on its set of panels. -/
theorem extends_congr {N : Nat} {p q : List Nat} (hp : p.Nodup) (hq : q.Nodup)
    (hpr : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N) (hqr : ∀ x ∈ q, 1 ≤ x ∧ x ≤ N)
    (hpv : SemiSymmetric N p) (hqv : SemiSymmetric N q) (h : ∀ x, x ∈ p ↔ x ∈ q) :
    Extends N p ↔ Extends N q := by
  rw [extends_iff_g_pos hp hpr hpv, extends_iff_g_pos hq hqr hqv]
  have : p.toFinset = q.toFinset := by ext x; simp [h]
  rw [this]

/-- **Weak split.**  If `φ` window-embeds the `p`-strip into the `N`-strip and the panels
outside its image can be ordered semi-symmetrically from scratch, then every live prefix of
the `p`-strip stays live through `φ` (complete it in the copy, then the rest reversed). -/
theorem extends_winEmb {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ) {r : List Nat}
    (hr : Extends p r) (hY : 0 < g N (Finset.Icc 1 N \ (Finset.Icc 1 p).image φ)) :
    Extends N (r.map φ) := by
  obtain ⟨σ, hσf, hσs, hpre⟩ := hr
  have bσ : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ p := fun y hy => (mem_range'_of_perm hσf).1 hy
  have hndσ := nodup_of_foldSeq hσf
  have hnd := hφ.nodup_map hndσ bσ
  have hrange : ∀ x ∈ σ.map φ, 1 ≤ x ∧ x ≤ N := by
    intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hφ.bound y (bσ y hy).1 (bσ y hy).2
  have hval := (hφ.semiSymmetric_iff hndσ bσ).2 hσs
  have himg : (σ.map φ).toFinset = (Finset.Icc 1 p).image φ := by
    ext x
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, Finset.mem_Icc,
      mem_range'_of_perm hσf]
  have := (extends_iff_g_pos hnd hrange hval).2 (by rw [himg]; exact hY)
  obtain ⟨a, hf, hs, hpre'⟩ := this
  exact ⟨a, hf, hs, (hpre.map φ).trans hpre'⟩

/-- **Split transfer.**  Through either half of a split, live prefixes stay live. -/
theorem Split.extends {N p q : Nat} {φ ψ : Nat → Nat} (h : Split N p q φ ψ) {r : List Nat}
    (hr : Extends p r) : Extends N (r.map φ) := by
  obtain ⟨σ, hσf, hσs, hpre⟩ := hr
  obtain ⟨τ, hτf, hτs⟩ := exists_semiSymmetric q
  exact ⟨_, h.isFoldSeq hσf hτf, (h.semiSymmetric_iff hσf hτf).2 ⟨hσs, hτs⟩,
    (hpre.map φ).trans (List.prefix_append _ _)⟩

/-- Mod-3 split (`N = 3n`): live prefixes of the `n`-strip stay live through
`y ↦ 3y - 1`, those of the `2n`-strip through `y ↦ y + ⌊y/2⌋`. -/
theorem extends_three {n : Nat} {r : List Nat} :
    (Extends n r → Extends (3 * n) (r.map third)) ∧
      (Extends (2 * n) r → Extends (3 * n) (r.map twoThirds)) :=
  ⟨(threeSplit n).extends, (threeSplit n).symm.extends⟩

/-- **Shifted blocks** (`N = 2n`): live prefixes of the `(n-1)`-strip stay live through
`shX` (evens up to `n`, then odds). -/
theorem extends_shX {n : Nat} (hn : 2 ≤ n) {r : List Nat} (hr : Extends (n - 1) r) :
    Extends (2 * n) (r.map (shX (n / 2))) := by
  obtain ⟨σ, hσf, hσs, hpre⟩ := hr
  obtain ⟨τ, hτf, hτs, hτpre⟩ := extends_single (n + 1) 1 le_rfl (by omega)
  obtain ⟨t, rfl⟩ := hτpre
  have hmid : n % 2 = 0 → ∀ k (hk : k < ([1] ++ t).length), ([1] ++ t)[k] = n / 2 + 1 →
      1 ∈ ([1] ++ t).take k := by
    intro _ k hk e
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp at e; omega
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp
  obtain ⟨hf, hs, -⟩ := shifted_blocks hn hσf hσs hτf hτs hmid
  exact ⟨_, hf, hs, (hpre.map _).trans (List.prefix_append _ _)⟩

/-! ## Mirror invariance of `Extends` -/

theorem Extends.mirror {N : Nat} {p : List Nat} (h : Extends N p) :
    Extends N (p.map (N + 1 - ·)) := by
  obtain ⟨a, hf, hs, hpre⟩ := h
  exact ⟨_, hf.mirror, hs.mirror hf, hpre.map _⟩

/-! ## Dead blocks `{1, 2j, 2j+1}`

If panels `1`, `2j`, `2j+1` are bisected before every panel of `G = [2, 2j-1]`
(`j ≥ 2`, `4j ≤ N + 3`), the first panel `m` of `G` to be bisected sees exactly one
bisected panel (`1`) on its left arm `[1, m-1]`, and on its right arm `[m+1, 2m-1]` none
(`m ≤ j`) or at least two (`2j`, `2j+1`, when `m > j`). -/

theorem dead_block {N j : Nat} {a : List Nat} (hf : IsFoldSeq N a) (h : SemiSymmetric N a)
    (hj : 2 ≤ j) (hN : 4 * j ≤ N + 3) {k : Nat}
    (h1 : 1 ∈ a.take k) (h2 : 2 * j ∈ a.take k) (h3 : 2 * j + 1 ∈ a.take k) :
    ∃ m ∈ a.take k, 2 ≤ m ∧ m < 2 * j := by
  have hnd := nodup_of_foldSeq hf
  by_contra hcon
  push Not at hcon
  have hex : ∃ i, ∃ hi : i < a.length, 2 ≤ a[i] ∧ a[i] < 2 * j := by
    have h2a : 2 ∈ a := (mem_range'_of_perm hf).2 ⟨by omega, by
      have := (mem_range'_of_perm hf).1 (List.mem_of_mem_take h3); omega⟩
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 h2a
    exact ⟨i, hi, by omega, by omega⟩
  classical
  obtain ⟨i, hi, hm2, hmj, hmin⟩ : ∃ i, ∃ hi : i < a.length, 2 ≤ a[i] ∧ a[i] < 2 * j ∧
      ∀ i' (hi' : i' < a.length), i' < i → ¬ (2 ≤ a[i'] ∧ a[i'] < 2 * j) := by
    obtain ⟨hi, hP⟩ := Nat.find_spec hex
    exact ⟨Nat.find hex, hi, hP.1, hP.2, fun i' hi' hlt hP' => Nat.find_min hex hlt ⟨hi', hP'⟩⟩
  -- no panel of `G` before step `i`
  have hS : ∀ x ∈ a.take i, ¬ (2 ≤ x ∧ x < 2 * j) := by
    intro x hx
    obtain ⟨i', hi', e⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_take] at hi'
    rw [List.getElem_take] at e
    rw [← e]; exact hmin i' (by omega) (by omega)
  -- `k ≤ i`
  have hki : k ≤ i := by
    by_contra hlt
    exact absurd (hcon a[i] ((getElem_mem_take_iff hnd hi).2 (by omega)) hm2) (by omega)
  have sub : ∀ x ∈ a.take k, x ∈ a.take i := fun x hx => by
    obtain ⟨i', hi', e⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_take] at hi'
    rw [List.getElem_take] at e
    rw [← e]; exact (getElem_mem_take_iff hnd (by omega)).2 (by omega)
  have hs := h i hi
  have hndS := take_nodup hnd i
  generalize a[i] = m at hs hm2 hmj
  unfold SemiStep at hs
  rw [leftCount_eq hndS, rightCount_eq hndS] at hs
  have hr : reach N m = m - 1 := by unfold reach; omega
  rw [hr] at hs
  have L : (a.take i).countP (fun x => decide (m - (m - 1) ≤ x ∧ x < m)) = 1 := by
    have e : (a.take i).countP (fun x => decide (m - (m - 1) ≤ x ∧ x < m)) =
        (a.take i).countP (fun x => decide (1 ≤ x ∧ x < m)) := by
      apply List.countP_congr; intro x _; simp only [decide_eq_true_eq]; omega
    rw [e, countP_split_one hndS (sub 1 h1) m (by omega)]
    have : (a.take i).countP (fun z => decide (2 ≤ z ∧ z < m)) = 0 := by
      rw [List.countP_eq_zero]
      intro x hx; have := hS x hx; simp only [decide_eq_true_eq]; omega
    omega
  rw [L] at hs
  by_cases hmj' : m ≤ j
  · have : (a.take i).countP (fun x => decide (m < x ∧ x ≤ m + (m - 1))) = 0 := by
      rw [List.countP_eq_zero]
      intro x hx; have := hS x hx; simp only [decide_eq_true_eq]; omega
    omega
  · rw [countP_split _ _ (fun x => decide (x = 2 * j))] at hs
    have e1 : (a.take i).countP
        (fun x => decide (m < x ∧ x ≤ m + (m - 1)) && decide (x = 2 * j)) =
        (a.take i).countP (fun x => decide (x = 2 * j)) := by
      apply List.countP_congr; intro x _; simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by omega, h⟩
    rw [e1, countP_eq_nodup hndS, ite_pos' (sub _ h2)] at hs
    have : 0 < (a.take i).countP
        (fun x => decide (m < x ∧ x ≤ m + (m - 1)) && !decide (x = 2 * j)) :=
      List.countP_pos_iff.2 ⟨2 * j + 1, sub _ h3, by simp; omega⟩
    omega

/-- **Dead blocks.**  A prefix that contains `1`, `2j`, `2j+1` (`j ≥ 2`, `4j ≤ N + 3`)
but no panel of `[2, 2j-1]` cannot be completed. -/
theorem not_extends_block {N j : Nat} (hj : 2 ≤ j) (hN : 4 * j ≤ N + 3) {p : List Nat}
    (h1 : 1 ∈ p) (h2 : 2 * j ∈ p) (h3 : 2 * j + 1 ∈ p)
    (hG : ∀ m ∈ p, ¬ (2 ≤ m ∧ m < 2 * j)) : ¬ Extends N p := by
  rintro ⟨a, hf, hs, hpre⟩
  rw [List.prefix_iff_eq_take.1 hpre] at h1 h2 h3 hG
  obtain ⟨m, hm, hm2, hmj⟩ := dead_block hf hs hj hN h1 h2 h3
  exact hG m hm ⟨hm2, hmj⟩

/-- Mirror image: a prefix that contains `N`, `N+1-2j`, `N-2j` but no panel of
`[N+2-2j, N-1]` cannot be completed. -/
theorem not_extends_block_mirror {N j : Nat} (hj : 2 ≤ j) (hN : 4 * j ≤ N + 3)
    {p : List Nat} (hpN : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N)
    (h1 : N ∈ p) (h2 : N + 1 - 2 * j ∈ p) (h3 : N - 2 * j ∈ p)
    (hG : ∀ m ∈ p, ¬ (N + 2 - 2 * j ≤ m ∧ m ≤ N - 1)) : ¬ Extends N p := by
  intro h
  have hm := h.mirror
  refine not_extends_block (p := p.map (N + 1 - ·)) hj hN ?_ ?_ ?_ ?_ hm
  · exact List.mem_map.2 ⟨N, h1, by omega⟩
  · exact List.mem_map.2 ⟨N + 1 - 2 * j, h2, by omega⟩
  · exact List.mem_map.2 ⟨N - 2 * j, h3, by omega⟩
  · intro m hm'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm'
    have := hG x hx; have := hpN x hx; omega

/-- The dead 3-prefixes `(2j+1, 1, 2j)` (and, when valid, `(1, 2j+1, 2j)`) and their
mirror images. -/
theorem not_extends_three_block {N j : Nat} (hj : 2 ≤ j) (hN : 4 * j ≤ N + 3) :
    ¬ Extends N [2 * j + 1, 1, 2 * j] ∧ ¬ Extends N [1, 2 * j + 1, 2 * j] ∧
      ¬ Extends N [N - 2 * j, N, N + 1 - 2 * j] ∧ ¬ Extends N [N, N - 2 * j, N + 1 - 2 * j] := by
  refine ⟨not_extends_block hj hN (by simp) (by simp) (by simp)
      (by intro m hm; simp at hm; omega),
    not_extends_block hj hN (by simp) (by simp) (by simp) (by intro m hm; simp at hm; omega),
    not_extends_block_mirror hj hN (by simp; omega) (by simp) (by simp) (by simp)
      (by intro m hm; simp at hm; omega),
    not_extends_block_mirror hj hN (by simp; omega) (by simp) (by simp) (by simp)
      (by intro m hm; simp at hm; omega)⟩

/-! ## Dead corners for odd `N`: the 3-subsets of `{1, 2, N-1, N}` -/

/-- A prefix after which no step is valid cannot be completed. -/
theorem not_extends_of_stuck {N : Nat} {p : List Nat} (hlen : p.length < N)
    (h : ∀ m, 1 ≤ m → m ≤ N → m ∉ p → ¬ SemiStep N p m) : ¬ Extends N p := by
  rintro ⟨a, hf, hs, hpre⟩
  have hnd := nodup_of_foldSeq hf
  have hla : a.length = N := by rw [hf.length_eq]; simp
  have hk : p.length < a.length := by omega
  have e := List.prefix_iff_eq_take.1 hpre
  have hstep := hs p.length hk
  have hm := (mem_range'_of_perm hf).1 (List.getElem_mem hk)
  have hnot : a[p.length] ∉ a.take p.length := by
    rw [getElem_mem_take_iff hnd hk]; omega
  rw [← e] at hstep hnot
  exact h _ hm.1 hm.2 hnot hstep

/-- Only the listed panels of `T` are valid next steps after `S`: a prefix with the same
elements as `S`, followed by any panel, is followed by a panel in `T`. -/
theorem next_mem {N : Nat} {a : List Nat} (hf : IsFoldSeq N a) (hs : SemiSymmetric N a)
    {k : Nat} (hk : k < a.length) {S : List Nat} (hS : ∀ x, x ∈ a.take k ↔ x ∈ S)
    {P : Nat → Prop} (hP : ∀ m, 1 ≤ m → m ≤ N → m ∉ S → SemiStep N S m → P m) : P a[k] := by
  have hnd := nodup_of_foldSeq hf
  have hm := (mem_range'_of_perm hf).1 (List.getElem_mem hk)
  have hnot : a[k] ∉ a.take k := by rw [getElem_mem_take_iff hnd hk]; omega
  rw [hS] at hnot
  exact hP _ hm.1 hm.2 hnot ((semiStep_congr hS).1 (hs k hk))

theorem mem_take_succ_iff {a : List Nat} {k : Nat} (hk : k < a.length) (x : Nat) :
    x ∈ a.take (k + 1) ↔ x ∈ a.take k ∨ x = a[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.mem_append]
  simp

/-- Arithmetic form of a step after an explicit list of distinct panels. -/
theorem semiStep_list_iff {N m : Nat} {S : List Nat} (hnd : S.Nodup) :
    SemiStep N S m ↔
      S.countP (fun x => decide (m - min (m - 1) (N - m) ≤ x ∧ x < m)) =
        S.countP (fun x => decide (m < x ∧ x ≤ m + min (m - 1) (N - m))) := by
  unfold SemiStep; rw [leftCount_eq hnd, rightCount_eq hnd]; rfl

theorem stuck_one_two_N {N m : Nat} (hN : N % 2 = 1) (h5 : 5 ≤ N) (hm1 : 1 ≤ m)
    (hmN : m ≤ N) (hm : m ∉ [1, 2, N]) : ¬ SemiStep N [1, 2, N] m := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
  rw [semiStep_list_iff (by simp; omega)]
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split_ifs <;> omega

theorem stuck_one_N1_N {N m : Nat} (hN : N % 2 = 1) (h5 : 5 ≤ N) (hm1 : 1 ≤ m)
    (hmN : m ≤ N) (hm : m ∉ [1, N - 1, N]) : ¬ SemiStep N [1, N - 1, N] m := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
  rw [semiStep_list_iff (by simp; omega)]
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split_ifs <;> omega

theorem next_one_two_N1 {N m : Nat} (hN : N % 2 = 1) (h7 : 7 ≤ N) (hm1 : 1 ≤ m)
    (hmN : m ≤ N) (hm : m ∉ [1, 2, N - 1]) (h : SemiStep N [1, 2, N - 1] m) : m = N := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
  rw [semiStep_list_iff (by simp; omega)] at h
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq] at h
  split_ifs at h <;> omega

theorem next_one_two_N1_N {N m : Nat} (hN : N % 2 = 1) (h7 : 7 ≤ N) (hm1 : 1 ≤ m)
    (hmN : m ≤ N) (hm : m ∉ [1, 2, N - 1, N]) (h : SemiStep N [1, 2, N - 1, N] m) :
    2 * m = N + 1 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
  rw [semiStep_list_iff (by simp; omega)] at h
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq] at h
  split_ifs at h <;> omega

theorem stuck_one_two_mid {N m : Nat} (hN : N % 2 = 1) (h7 : 7 ≤ N) (hm1 : 1 ≤ m)
    (hmN : m ≤ N) (hm : m ∉ [1, 2, N - 1, N, (N + 1) / 2]) :
    ¬ SemiStep N [1, 2, N - 1, N, (N + 1) / 2] m := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
  rw [semiStep_list_iff (by simp; omega)]
  simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
  split_ifs <;> omega

/-- After `{1, 2, N-1}` (odd `N ≥ 7`) the only continuation is `N`, then the middle panel,
and then nothing. -/
theorem not_extends_corner3 {N : Nat} (hN : N % 2 = 1) (h7 : 7 ≤ N) {p : List Nat}
    (hp : p.Perm [1, 2, N - 1]) : ¬ Extends N p := by
  rintro ⟨a, hf, hs, hpre⟩
  have hla : a.length = N := by rw [hf.length_eq]; simp
  have e := List.prefix_iff_eq_take.1 hpre
  have hl3 : p.length = 3 := by rw [hp.length_eq]; simp
  have h3 : ∀ x, x ∈ a.take 3 ↔ x ∈ [1, 2, N - 1] := fun x => by
    rw [← hl3, ← e]; exact hp.mem_iff
  have a3 : a[3] = N := next_mem hf hs (by omega) h3 fun m hm1 hmN hm hst =>
    next_one_two_N1 hN h7 hm1 hmN hm hst
  have h4 : ∀ x, x ∈ a.take 4 ↔ x ∈ [1, 2, N - 1, N] := fun x => by
    rw [mem_take_succ_iff (by omega), h3, a3]; simp; tauto
  have a4 : 2 * a[4] = N + 1 := next_mem hf hs (by omega) h4 fun m hm1 hmN hm hst =>
    next_one_two_N1_N hN h7 hm1 hmN hm hst
  have h5 : ∀ x, x ∈ a.take 5 ↔ x ∈ [1, 2, N - 1, N, (N + 1) / 2] := fun x => by
    rw [mem_take_succ_iff (by omega), h4, show a[4] = (N + 1) / 2 by omega]; simp; tauto
  exact next_mem (P := fun _ => False) hf hs (by omega) h5 fun m hm1 hmN hm hst =>
    stuck_one_two_mid hN h7 hm1 hmN hm hst

/-- **Dead corners** (odd `N ≥ 7`): no prefix whose elements are `{1, 2, N}`,
`{1, N-1, N}`, `{1, 2, N-1}` or `{2, N-1, N}` can be completed.  The first two admit no
further step; after `{1, 2, N-1}` the only continuation is `N`, then the middle panel, and
then nothing; `{2, N-1, N}` is the mirror image of `{1, 2, N-1}`. -/
theorem not_extends_corner {N : Nat} (hN : N % 2 = 1) (h7 : 7 ≤ N) {p : List Nat}
    (hp : p.Perm [1, 2, N] ∨ p.Perm [1, N - 1, N] ∨ p.Perm [1, 2, N - 1] ∨
      p.Perm [2, N - 1, N]) : ¬ Extends N p := by
  rcases hp with hp | hp | hp | hp
  · refine not_extends_of_stuck (by rw [hp.length_eq]; simp; omega) fun m hm1 hmN hm hs => ?_
    rw [hp.mem_iff] at hm
    exact stuck_one_two_N hN (by omega) hm1 hmN hm ((semiStep_congr fun x => hp.mem_iff).1 hs)
  · refine not_extends_of_stuck (by rw [hp.length_eq]; simp; omega) fun m hm1 hmN hm hs => ?_
    rw [hp.mem_iff] at hm
    exact stuck_one_N1_N hN (by omega) hm1 hmN hm ((semiStep_congr fun x => hp.mem_iff).1 hs)
  · exact not_extends_corner3 hN h7 hp
  · intro h
    have hp' : (p.map (N + 1 - ·)).Perm [1, 2, N - 1] := by
      refine (hp.map (N + 1 - ·)).trans ?_
      simp only [List.map_cons, List.map_nil]
      rw [show N + 1 - 2 = N - 1 by omega, show N + 1 - (N - 1) = 2 by omega,
        show N + 1 - N = 1 by omega]
      exact (List.reverse_perm [N - 1, 2, 1]).symm
    exact not_extends_corner3 hN h7 hp' h.mirror

/-! ## The sporadic dead 2-prefix `(1, 7)` for `N = 7`

After `{1, 7}` the only step is `4`; after `{1, 4, 7}` it is `3` or `5`; then `2` (resp.
`6`); then nothing. -/

theorem not_extends_seven_aux {a : List Nat} (hf : IsFoldSeq 7 a) (hs : SemiSymmetric 7 a)
    (h2 : ∀ x, x ∈ a.take 2 ↔ x ∈ [1, 7]) : False := by
  have hla : a.length = 7 := by rw [hf.length_eq]; simp
  have a2 : a[2] = 4 := next_mem (P := fun m => m = 4) hf hs (by omega) h2 fun m hm1 hmN hm hst => by
    revert hm1 hmN hm hst; revert m; decide
  have h3 : ∀ x, x ∈ a.take 3 ↔ x ∈ [1, 7, 4] := fun x => by
    rw [mem_take_succ_iff (by omega), h2, a2]; simp; tauto
  have a3 : a[3] = 3 ∨ a[3] = 5 := next_mem (P := fun m => m = 3 ∨ m = 5) hf hs (by omega) h3 fun m hm1 hmN hm hst => by
    revert hm1 hmN hm hst; revert m; decide
  rcases a3 with a3 | a3
  · have h4 : ∀ x, x ∈ a.take 4 ↔ x ∈ [1, 7, 4, 3] := fun x => by
      rw [mem_take_succ_iff (by omega), h3, a3]; simp; tauto
    have a4 : a[4] = 2 := next_mem (P := fun m => m = 2) hf hs (by omega) h4 fun m hm1 hmN hm hst => by
      revert hm1 hmN hm hst; revert m; decide
    have h5 : ∀ x, x ∈ a.take 5 ↔ x ∈ [1, 7, 4, 3, 2] := fun x => by
      rw [mem_take_succ_iff (by omega), h4, a4]; simp; tauto
    exact next_mem (P := fun _ => False) hf hs (by omega) h5 fun m hm1 hmN hm hst => by
      revert hm1 hmN hm hst; revert m; decide
  · have h4 : ∀ x, x ∈ a.take 4 ↔ x ∈ [1, 7, 4, 5] := fun x => by
      rw [mem_take_succ_iff (by omega), h3, a3]; simp; tauto
    have a4 : a[4] = 6 := next_mem (P := fun m => m = 6) hf hs (by omega) h4 fun m hm1 hmN hm hst => by
      revert hm1 hmN hm hst; revert m; decide
    have h5 : ∀ x, x ∈ a.take 5 ↔ x ∈ [1, 7, 4, 5, 6] := fun x => by
      rw [mem_take_succ_iff (by omega), h4, a4]; simp; tauto
    exact next_mem (P := fun _ => False) hf hs (by omega) h5 fun m hm1 hmN hm hst => by
      revert hm1 hmN hm hst; revert m; decide

/-- **Sporadic dead 2-prefix.**  For `N = 7` (odd!) the valid prefixes `[1, 7]` and
`[7, 1]` cannot be completed. -/
theorem not_extends_seven : ¬ Extends 7 [1, 7] ∧ ¬ Extends 7 [7, 1] := by
  constructor
  all_goals
    rintro ⟨a, hf, hs, hpre⟩
    have e := List.prefix_iff_eq_take.1 hpre
    refine not_extends_seven_aux hf hs fun x => ?_
    rw [show (2 : Nat) = List.length [1, 7] from rfl]
    first
    | rw [← e]
    | rw [show List.length [1, 7] = List.length [7, 1] from rfl, ← e]; simp; tauto

end Folds
