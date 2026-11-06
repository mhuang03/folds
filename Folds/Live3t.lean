import Folds.Live3s

/-!
# Live 3-prefixes, part 5: parametric near copies beyond `{1, 2, c}`

`experiments/live3t/PROOFS.txt`.

* `coReach_image_two`: the image of a closed-form near copy `φ` is co-reachable when its
  complement is the image of a second closed-form near copy `ψ` that is regular except at two
  panels forming a valid, non-dead 2-prefix (Live3r Theorem 2 with the complement given by
  `ψ` directly, Conjecture C of `ThinCover`).
* `coReach_one_three_N`: **`{1, 3, N}` for `N ≡ 1 (mod 4)`**, the family that Live3r settled
  N by N with `nearTrP` hints.
-/

namespace Folds
namespace Live3t

open Live2 Live4 Adjacent Live5 Live6 Live7 Live3p Live3r Live3s

set_option Elab.async false

/-! ## The complement of a near copy through a second near copy -/

/-- The image of `φ` is co-reachable if the rest of `[N]` is the image of a near copy `ψ`
of `[q]`, regular outside `i₁, i₂`, with `[i₁, i₂]` valid and not dead in `[q]` and
`[ψ i₁, ψ i₂]` valid in `[N]`. -/
theorem coReach_image_two {N p q i₁ i₂ : Nat} {φ ψ : Nat → Nat} {R R' : Nat → Prop}
    (hφ : NearEmb N p φ R) (hψ : NearEmb N q ψ R')
    (hcov : ∀ x, 1 ≤ x → x ≤ N → (∃ y, 1 ≤ y ∧ y ≤ p ∧ φ y = x) ∨
      (∃ i, 1 ≤ i ∧ i ≤ q ∧ ψ i = x))
    (hdisj : ∀ y i, 1 ≤ y → y ≤ p → 1 ≤ i → i ≤ q → φ y ≠ ψ i)
    (hreg : ∀ x, 1 ≤ x → x ≤ q → x ≠ i₁ → x ≠ i₂ → R' x)
    (h1 : 1 ≤ i₁ ∧ i₁ ≤ q) (h2 : 1 ≤ i₂ ∧ i₂ ≤ q) (hne : i₁ ≠ i₂)
    (hs1 : SemiStep q [i₁] i₂) (hs2 : SemiStep N [ψ i₁] (ψ i₂))
    (hdd : deadB q (min i₁ i₂) (max i₁ i₂) = false) :
    CoReach N ((Finset.Icc 1 p).image φ) := by
  have hval : SemiSymmetric q [i₁, i₂] := by
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · simp [SemiStep, leftCount, rightCount]
    · simpa using hs1
  have hext : Extends q [i₁, i₂] := (ThinCover.conjectureC h1 h2 hne hval).2 hdd
  have hY := coReach_compl_nearEmb hψ hreg hext hs2
  have e : Finset.Icc 1 N \ (Finset.Icc 1 q).image ψ = (Finset.Icc 1 p).image φ := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨hx, hn⟩
      rcases hcov x hx.1 hx.2 with ⟨y, hy1, hy2, e⟩ | ⟨i, hi1, hi2, e⟩
      · exact ⟨y, ⟨hy1, hy2⟩, e⟩
      · exact absurd ⟨i, ⟨hi1, hi2⟩, e⟩ hn
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hφ.bound y hy.1 hy.2, fun ⟨i, hi, e⟩ => hdisj y i hy.1 hy.2 hi.1 hi.2 e.symm⟩
  rwa [e] at hY

/-! ## `{1, 3, N}` for `N ≡ 1 (mod 4)`

`N = 2p + 1`, `p` even.  `phi13 : [p] → [N]`: `1 ↦ 1`, `2 ↦ 3`, `y ↦ 2y`, `p ↦ N` (the
right-aligned Beatty copy `⌊yN/p⌋` with the panels `1, 2` moved down by one), regular at every
panel outside `{1, 2, p}`; `{1, 3, N}` is the image of `{1, 2, p}`.  The complement
`{2, 4, 5, 7, …, 2p - 1, 2p}` is the image of `psi13 : [p + 1] → [N]` (`1 ↦ 2`, `2 ↦ 4`,
`i ↦ 2i - 1`, `p + 1 ↦ 2p`), regular outside `{2, p + 1}`, and `[2, p + 1]` is a valid
non-dead 2-prefix. -/

/-- The near copy for `{1, 3, N}`. -/
def phi13 (p y : Nat) : Nat := if y = 1 then 1 else if y = 2 then 3 else if y = p then 2 * p + 1
  else 2 * y

/-- The complement of its image. -/
def psi13 (p i : Nat) : Nat := if i = 1 then 2 else if i = 2 then 4 else if i = p + 1 then 2 * p
  else 2 * i - 1

theorem nearEmb_phi13 {p : Nat} (hp : 4 ≤ p) :
    NearEmb (2 * p + 1) p (phi13 p) (fun j => 3 ≤ j ∧ j ≠ p) := by
  refine ⟨fun y h1 h2 => ?_, fun x y hx1 hxp hy1 hyp e => ?_, fun j y hj1 hjp hR hy1 hyp => ?_,
    fun j y hj1 hjp hR hy1 hyp => ?_⟩
  · unfold phi13; split_ifs <;> omega
  · unfold phi13 at e; split_ifs at e <;> omega
  · unfold phi13 reach; split_ifs <;> omega
  · unfold phi13 reach; split_ifs <;> omega

theorem nearEmb_psi13 {p : Nat} (hp : 4 ≤ p) :
    NearEmb (2 * p + 1) (p + 1) (psi13 p) (fun i => i ≠ 2 ∧ i ≠ p + 1) := by
  refine ⟨fun y h1 h2 => ?_, fun x y hx1 hxp hy1 hyp e => ?_, fun j y hj1 hjp hR hy1 hyp => ?_,
    fun j y hj1 hjp hR hy1 hyp => ?_⟩
  · unfold psi13; split_ifs <;> omega
  · unfold psi13 at e; split_ifs at e <;> omega
  · unfold psi13 reach; split_ifs <;> omega
  · unfold psi13 reach; split_ifs <;> omega

/-- **`{1, 3, N}` is co-reachable for `N ≡ 1 (mod 4)`, `N ≥ 17`**, given the smaller strips. -/
theorem coReach_one_three_N {N : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q) (hN : N % 4 = 1)
    (h17 : 17 ≤ N) : CoReach N {1, 3, N} := by
  obtain ⟨p, hp⟩ : ∃ p, p = N / 2 := ⟨_, rfl⟩
  have hNp : N = 2 * p + 1 := by omega
  have hφ := nearEmb_phi13 (p := p) (by omega)
  have hψ := nearEmb_psi13 (p := p) (by omega)
  have hY : CoReach (2 * p + 1) ((Finset.Icc 1 p).image (phi13 p)) := by
    refine coReach_image_two (i₁ := 2) (i₂ := p + 1) hφ hψ (fun x hx1 hxN => ?_)
      (fun y i hy1 hyp hi1 hiq => ?_) (fun x _ _ h1 h2 => ⟨h1, h2⟩) ⟨by omega, by omega⟩
      ⟨by omega, le_rfl⟩ (by omega) ?_ ?_ ?_
    · by_cases h : x = 1 ∨ x = 3 ∨ x = 2 * p + 1 ∨ (x % 2 = 0 ∧ 6 ≤ x ∧ x ≤ 2 * p - 2)
      · left
        rcases h with rfl | rfl | rfl | h
        · exact ⟨1, le_rfl, by omega, by simp [phi13]⟩
        · exact ⟨2, by omega, by omega, by simp [phi13]⟩
        · exact ⟨p, by omega, le_rfl, by unfold phi13; split_ifs <;> omega⟩
        · exact ⟨x / 2, by omega, by omega, by unfold phi13; split_ifs <;> omega⟩
      · right
        by_cases h2 : x = 2
        · exact ⟨1, le_rfl, by omega, by simp [psi13, h2]⟩
        by_cases h4 : x = 4
        · exact ⟨2, by omega, by omega, by simp [psi13, h4]⟩
        by_cases h2p : x = 2 * p
        · exact ⟨p + 1, by omega, le_rfl, by unfold psi13; split_ifs <;> omega⟩
        · exact ⟨(x + 1) / 2, by omega, by omega, by unfold psi13; split_ifs <;> omega⟩
    · unfold phi13 psi13; split_ifs <;> omega
    · unfold SemiStep
      simp [leftCount, rightCount, reach]
    · have e2 : psi13 p 2 = 4 := by simp [psi13]
      have eq : psi13 p (p + 1) = 2 * p := by unfold psi13; split_ifs <;> omega
      have er : reach (2 * p + 1) (2 * p) = 1 := by unfold reach; omega
      rw [e2, eq]
      unfold SemiStep
      rw [leftCount_eq (by simp), rightCount_eq (by simp), er]
      simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq]
      split_ifs <;> omega
    · simp [deadB]; omega
  have hD := coReach_one_two_pre (p := p) (g := p) IH (by omega) (by omega) (by omega) le_rfl
    (Or.inl (by omega))
  have := coReach_nearEmb hφ hY (D := {1, 2, p}) (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]; omega)
    (fun j _ _ hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj; exact ⟨by omega, hj.2.2⟩)
    hD
  rw [hNp]
  have e1 : phi13 p 1 = 1 := by simp [phi13]
  have e2 : phi13 p 2 = 3 := by simp [phi13]
  have e3 : phi13 p p = 2 * p + 1 := by unfold phi13; split_ifs <;> omega
  simpa [Finset.image_insert, e1, e2, e3] using this

/-! ## `{1, b, N}` for `N ≡ 2 (mod 4)`

`N = 4s + 2`, `p = 2s + 2`.  The centred Beatty copy `Z(N, p)` is `zA s`: `k ↦ 2k - 1` for
`k ≤ s + 1`, `k ↦ 2k - 2` above (odd numbers up to `2s + 1`, even numbers from `2s + 2`).
With the panel `j ≤ s + 1` sent to `2j - 1 - e` (`e ∈ {0, 1}`) it is regular outside `j`,
its image satisfies Theorem G with the centre `1/2`, and `{1, j, p}` is valid and not dead in
the even strip `[p]`.  This gives `{1, b, N}` for `2 ≤ b ≤ 2s + 1`, and the rest by the
mirror image. -/

/-- The centred Beatty copy `Z(4s + 2, 2s + 2)` in closed form. -/
def zA (s k : Nat) : Nat := if k ≤ s + 1 then 2 * k - 1 else 2 * k - 2

/-- `zA` with the panel `j` sent to `2j - 1 - e`. -/
def zAm (s j e k : Nat) : Nat := if k = j then 2 * j - 1 - e else zA s k

theorem nearEmb_zAm {s j e : Nat} (hj2 : 2 ≤ j) (hjs : j ≤ s + 1) (he : e ≤ 1) :
    NearEmb (4 * s + 2) (2 * s + 2) (zAm s j e) (fun k => k ≠ j) := by
  refine ⟨fun y h1 h2 => ?_, fun x y hx1 hxp hy1 hyp e' => ?_, fun k y hk1 hkp hR hy1 hyp => ?_,
    fun k y hk1 hkp hR hy1 hyp => ?_⟩
  · unfold zAm zA; split_ifs <;> omega
  · unfold zAm zA at e'; split_ifs at e' <;> omega
  · unfold zAm zA reach; split_ifs <;> omega
  · unfold zAm zA reach; split_ifs <;> omega

/-- The counting function of the image of `zAm s j e`. -/
def FA (s j e t : Nat) : Nat :=
  (if t ≤ 2 * s + 2 then t / 2 else if t ≤ 4 * s + 3 then (t - 1) / 2 + 1 else 2 * s + 2) +
    if e = 1 ∧ t = 2 * j - 1 then 1 else 0

theorem FA_lo {s j e t : Nat} (ht : t ≤ 2 * s + 2) :
    FA s j e t = t / 2 + if e = 1 ∧ t = 2 * j - 1 then 1 else 0 := by
  unfold FA; simp only [ht, ite_true]

theorem FA_hi {s j e t : Nat} (ht : 2 * s + 2 ≤ t) (ht' : t ≤ 4 * s + 3) :
    FA s j e t = (t - 1) / 2 + 1 + if e = 1 ∧ t = 2 * j - 1 then 1 else 0 := by
  unfold FA; split_ifs <;> omega

theorem FA_succ {s j e : Nat} (hj2 : 2 ≤ j) (hjs : j ≤ s + 1) (he : e ≤ 1) (t : Nat) :
    FA s j e (t + 1) = FA s j e t + if (t = 2 * j - 1 - e ∨ (t ≠ 2 * j - 1 ∧
      ((t % 2 = 1 ∧ t ≤ 2 * s + 1) ∨ (t % 2 = 0 ∧ 2 * s + 2 ≤ t ∧ t ≤ 4 * s + 2))))
      then 1 else 0 := by
  unfold FA; split_ifs <;> omega

theorem mem_image_zAm {s j e x : Nat} (hj2 : 2 ≤ j) (hjs : j ≤ s + 1) (he : e ≤ 1) :
    x ∈ (Finset.Icc 1 (2 * s + 2)).image (zAm s j e) ↔ (x = 2 * j - 1 - e ∨ (x ≠ 2 * j - 1 ∧
      ((x % 2 = 1 ∧ x ≤ 2 * s + 1) ∨ (x % 2 = 0 ∧ 2 * s + 2 ≤ x ∧ x ≤ 4 * s + 2)))) := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rw [Finset.mem_Icc] at hy; unfold zAm zA; split_ifs <;> omega
  · intro h
    by_cases hx : x = 2 * j - 1 - e
    · exact ⟨j, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by simp [zAm]; omega⟩
    · by_cases ho : x % 2 = 1
      · exact ⟨(x + 1) / 2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by
          unfold zAm zA; split_ifs <;> omega⟩
      · exact ⟨x / 2 + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by
          unfold zAm zA; split_ifs <;> omega⟩

/-- The image of `zAm s j e` satisfies Theorem G (centre `1/2`). -/
theorem coReach_image_zAm {s j e : Nat} (hj2 : 2 ≤ j) (hjs : j ≤ s + 1) (he : e ≤ 1) :
    CoReach (4 * s + 2) ((Finset.Icc 1 (2 * s + 2)).image (zAm s j e)) := by
  have hmem := fun x => mem_image_zAm (s := s) (x := x) hj2 hjs he
  refine coReach_of_inward (c2 := 1) (fun x hx => ?_) ?_
  · rw [hmem] at hx; rw [Finset.mem_Icc]; omega
  refine inward_of_cnt (F := FA s j e) (fun x hx1 hxN => hmem x) (FA_succ hj2 hjs he) ?_
  intro m hm1 hmN _
  refine cnt_ineq_split hm1 hmN (fun _ => ?_) (fun _ => ?_)
  · rw [FA_lo (t := 1) (by omega), FA_lo (t := m) (by omega), FA_lo (t := m + 1) (by omega)]
    rcases le_or_gt (2 * m) (2 * s + 2) with h | h
    · rw [FA_lo h]; split_ifs <;> omega
    · rw [FA_hi (by omega) (by omega)]; split_ifs <;> omega
  · rw [FA_hi (t := 4 * s + 2 + 1) (by omega) (by omega), FA_hi (t := m) (by omega) (by omega),
      FA_hi (t := m + 1) (by omega) (by omega)]
    rcases le_or_gt (2 * m - (4 * s + 2)) (2 * s + 2) with h | h
    · rw [FA_lo h]; split_ifs <;> omega
    · rw [FA_hi (by omega) (by omega)]; split_ifs <;> omega

/-- `{1, j, p}` is co-reachable in the even strip `[p]` (`p < N`), by the induction
hypothesis. -/
theorem coReach_one_j_top {N p j : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q) (hpN : p < N)
    (hp : p % 2 = 0) (h8 : 8 ≤ p) (hj2 : 2 ≤ j) (hjp : 2 * j ≤ p) :
    CoReach p {1, j, p} := by
  have hv : valid3B p 1 j p = true := by
    unfold valid3B
    have h1 : step2B p j j p = true := by
      unfold step2B reach; simp only [beq_iff_eq]; split_ifs <;> omega
    have h2 : step2B p j p 1 = true := by
      unfold step2B reach; simp only [beq_iff_eq]; split_ifs <;> omega
    simp [h1, h2]
  have hdd : dead3B p 1 j p = false := by
    simp only [dead3B, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      decide_eq_false_iff_not, ne_eq]
    omega
  exact IH p hpN (by omega) 1 j p le_rfl (by omega) (by omega) le_rfl hv hdd

/-- **`{1, b, N}` is co-reachable for `N ≡ 2 (mod 4)`, `N ≥ 30`, `2 ≤ b ≤ N - 1`**, given the
smaller strips. -/
theorem coReach_one_b_N {N b : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q) (hN : N % 4 = 2)
    (h30 : 30 ≤ N) (hb2 : 2 ≤ b) (hbN : b + 1 ≤ N) : CoReach N {1, b, N} := by
  obtain ⟨s, hs⟩ : ∃ s, s = N / 4 := ⟨_, rfl⟩
  have hNs : N = 4 * s + 2 := by omega
  -- the case `b ≤ 2s + 1`
  have key : ∀ b, 2 ≤ b → b ≤ 2 * s + 1 → CoReach N {1, b, N} := by
    intro b hb2 hbs
    obtain ⟨j, hj⟩ : ∃ j, j = b / 2 + 1 := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e, e = (b + 1) % 2 := ⟨_, rfl⟩
    have hφ := nearEmb_zAm (s := s) (j := j) (e := e) (by omega) (by omega) (by omega)
    have hY := coReach_image_zAm (s := s) (j := j) (e := e) (by omega) (by omega) (by omega)
    have hD := coReach_one_j_top (p := 2 * s + 2) (j := j) IH (by omega) (by omega) (by omega)
      (by omega) (by omega)
    have := coReach_nearEmb hφ hY (D := {1, j, 2 * s + 2}) (fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_Icc]; omega)
      (fun k _ _ hk => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk; exact hk.2.1) hD
    have e1 : zAm s j e 1 = 1 := by unfold zAm zA; split_ifs <;> omega
    have e2 : zAm s j e j = b := by unfold zAm; split_ifs <;> omega
    have e3 : zAm s j e (2 * s + 2) = N := by unfold zAm zA; split_ifs <;> omega
    rw [hNs] at e3 ⊢
    simpa [Finset.image_insert, e1, e2, e3] using this
  by_cases hb : b ≤ 2 * s + 1
  · exact key b hb2 hb
  · have := key (N + 1 - b) (by omega) (by omega)
    refine coReach3_of_mirror (by omega) (by omega) le_rfl ?_
    rwa [show N + 1 - N = 1 by omega, show N + 1 - 1 = N by omega]

/-! ## The enlarged rules and the reduction -/

/-- The parametric families of this file: `{1, b, N}` for `N ≡ 2 (mod 4)`, and `{1, 3, N}`,
`{1, N - 2, N}` for `N ≡ 1 (mod 4)`. -/
def OneN (N a b c : Nat) : Prop :=
  a = 1 ∧ c = N ∧ ((N % 4 = 2 ∧ 30 ≤ N) ∨ (N % 4 = 1 ∧ 17 ≤ N ∧ (b = 3 ∨ b + 2 = N)))

/-- `Covered3T` (Live3s) or one of the families `OneN`. -/
def Covered3U (N a b c : Nat) : Prop := Covered3T N a b c ∨ OneN N a b c

theorem coReach_of_covered3U {N a b c : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hcN : c ≤ N) (h : Covered3U N a b c) :
    CoReach N {a, b, c} := by
  rcases h with h | ⟨rfl, rfl, ⟨h2, h30⟩ | ⟨h1, h17, rfl | hb⟩⟩
  · exact coReach_of_covered3T IH ha hab hbc hcN h
  · exact coReach_one_b_N IH h2 h30 (by omega) (by omega)
  · exact coReach_one_three_N IH h1 h17
  · refine coReach3_of_mirror (by omega) (by omega) le_rfl ?_
    rw [show c + 1 - c = 1 by omega, show c + 1 - b = 3 by omega, show c + 1 - 1 = c by omega]
    exact coReach_one_three_N IH h1 h17

/-- **The residual statement with the families `OneN` removed.** -/
def Residual3U (N : Nat) : Prop :=
  ∀ a b c, 1 ≤ a → a < b → b < c → c ≤ N → valid3B N a b c = true → dead3B N a b c = false →
    ¬ Covered3U N a b c → CoReach N {a, b, c}

/-- Given the smaller strips, `Residual3U N` implies `Residual3T N`. -/
theorem residual3T_of_residual3U {N : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (h : Residual3U N) : Residual3T N := by
  intro a b c ha hab hbc hcN hv hd _
  by_cases hc : Covered3U N a b c
  · exact coReach_of_covered3U IH ha hab hbc hcN hc
  · exact h a b c ha hab hbc hcN hv hd hc

/-- **Reduction**: the 3-prefix property for all `N ≠ 7` from the base strips and
`Residual3U` above them. -/
theorem good3_of_residual3U {M : Nat} (hbase : ∀ N, N ≤ M → N ≠ 7 → Good3 N)
    (hres : ∀ N, M < N → Residual3U N) : ∀ N, N ≠ 7 → Good3 N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro h7
    by_cases hN : N ≤ M
    · exact hbase N hN h7
    intro a b c ha hab hbc hcN hv hd
    by_cases hc : Covered3U N a b c
    · exact coReach_of_covered3U ih ha hab hbc hcN hc
    · exact hres N (by omega) a b c ha hab hbc hcN hv hd hc

/-- `Residual3T N` for all `N > M` (the hypothesis of `Live3s.residual3R_all_of_residual3T` and
of `Live3Final.extends3_iff_of_residual3T`) from the base strips and `Residual3U N` for all
`N > M`. -/
theorem residual3T_all_of_residual3U {M : Nat} (hbase : ∀ N, N ≤ M → N ≠ 7 → Good3 N)
    (hres : ∀ N, M < N → Residual3U N) : ∀ N, M < N → Residual3T N := fun N hN =>
  residual3T_of_residual3U (fun q _ hq7 => good3_of_residual3U hbase hres q hq7) (hres N hN)

end Live3t
end Folds
