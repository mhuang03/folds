import Folds.Live3r

/-!
# Live 3-prefixes, part 4: more closed-form near copies for `{1, 2, c}`

`experiments/live3s/PROOFS.txt`.

* `inward_of_cnt`, `semiStep_of_cnt`: Theorem G and valid steps for a set given by a predicate
  with an explicit counting function (`F (t + 1) = F t + [P t]`), so that the arm counts are
  differences of `F` and the conditions are `omega` goals.
* `coReach_one_two_pre`: `{1, 2, g}` is co-reachable in a smaller strip `[p]` (induction
  hypothesis), for `4 ≤ g ≤ p`, `g ≤ p - 2` when `p` is odd.
* Two new closed-form near copies fixing `1` and `2`:
  - `phi12 : [p] → [2p]` (`1 ↦ 1`, `2 ↦ 2`, `y ↦ 2y - 1`), regular at every panel `≠ 2` for
    every `p`; its image `{1, 2, 5, 7, …, 2p - 1}` satisfies Theorem G with the centre `1/2`.
    Hence **`{1, 2, c}` for even `N`, odd `c`** (`coReach_one_two_evenN`).
  - `phiE : [p] → [2p + 1]` (`1 ↦ 1`, `2 ↦ 2`, `y ↦ 2y`), `p` odd, regular at every panel
    `≥ 3`; `5` is a valid step for its image `{1, 2, 6, 8, …, 2p}`, after which Theorem G
    holds with the centre `1/2`.  Hence **`{1, 2, c}` for `N ≡ 3 (mod 4)`, even `c`**
    (`coReach_one_two_even3`).
* `OneTwoB`, `Covered3T`, `Residual3T`, `good3_of_residual3T`, `residual3R_all_of_residual3T`:
  the reduction of Live3r with these families (and `Live3r.coReach_one_two_odd`) added, for the
  triple or its mirror image.
-/

namespace Folds
namespace Live3s

open Live2 Live4 Adjacent Live5 Live6 Live7 Live3p Live3r

-- the `split_ifs <;> omega` arm-count proofs are checked one at a time to keep the memory low
set_option Elab.async false

/-! ## Arm counts through a counting function -/

theorem countP_cnt {P : Nat → Prop} [DecidablePred P] {F : Nat → Nat}
    (hF : ∀ t, F (t + 1) = F t + if P t then 1 else 0) :
    ∀ n lo, (List.range' lo n).countP (fun x => decide (P x)) = F (lo + n) - F lo ∧
      F lo ≤ F (lo + n)
  | 0, lo => by simp
  | n + 1, lo => by
    obtain ⟨ih1, ih2⟩ := countP_cnt hF n (lo + 1)
    rw [List.range'_succ, List.countP_cons, ih1, show lo + (n + 1) = lo + 1 + n by omega]
    have := hF lo
    by_cases hP : P lo
    · simp [hP] at this ⊢; omega
    · simp [hP] at this ⊢; omega

theorem leftCount_cnt {N : Nat} {S : Finset Nat} {P : Nat → Prop} [DecidablePred P]
    {F : Nat → Nat} (hS : ∀ x, 1 ≤ x → x ≤ N → (x ∈ S ↔ P x))
    (hF : ∀ t, F (t + 1) = F t + if P t then 1 else 0) {m : Nat} (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    leftCount N S.toList m = F m - F (m - reach N m) := by
  rw [leftCount_finset]
  obtain ⟨r, hr⟩ : ∃ r, r = reach N m := ⟨_, rfl⟩
  rw [← hr]
  have hr1 : r ≤ m - 1 := by rw [hr]; unfold reach; omega
  have e1 := countP_sub_range' (fun x => x ∈ S) m r (by omega)
  have e2 : (List.range' (m - r) r).countP (fun x => decide (x ∈ S)) =
      (List.range' (m - r) r).countP (fun x => decide (P x)) := by
    apply List.countP_congr; intro x hx; rw [List.mem_range'_1] at hx
    simp only [decide_eq_true_eq]; exact hS x (by omega) (by omega)
  rw [e1, e2, (countP_cnt hF r (m - r)).1, show m - r + r = m by omega]

theorem rightCount_cnt {N : Nat} {S : Finset Nat} {P : Nat → Prop} [DecidablePred P]
    {F : Nat → Nat} (hS : ∀ x, 1 ≤ x → x ≤ N → (x ∈ S ↔ P x))
    (hF : ∀ t, F (t + 1) = F t + if P t then 1 else 0) {m : Nat} (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    rightCount N S.toList m = F (m + 1 + reach N m) - F (m + 1) := by
  rw [rightCount_finset]
  obtain ⟨r, hr⟩ : ∃ r, r = reach N m := ⟨_, rfl⟩
  rw [← hr]
  have hr2 : r ≤ N - m := by rw [hr]; unfold reach; omega
  have e1 := countP_add_range' (fun x => x ∈ S) m r
  have e2 : (List.range' (m + 1) r).countP (fun x => decide (x ∈ S)) =
      (List.range' (m + 1) r).countP (fun x => decide (P x)) := by
    apply List.countP_congr; intro x hx; rw [List.mem_range'_1] at hx
    simp only [decide_eq_true_eq]; exact hS x (by omega) (by omega)
  rw [e1, e2, (countP_cnt hF r (m + 1)).1]

/-- **Theorem G with the centre `1/2` through a counting function**: every outside panel has
at most as many elements in its right arm as in its left arm. -/
theorem inward_of_cnt {N : Nat} {S : Finset Nat} {P : Nat → Prop} [DecidablePred P]
    {F : Nat → Nat} (hS : ∀ x, 1 ≤ x → x ≤ N → (x ∈ S ↔ P x))
    (hF : ∀ t, F (t + 1) = F t + if P t then 1 else 0)
    (h : ∀ m, 1 ≤ m → m ≤ N → ¬ P m →
      F (m + 1 + reach N m) - F (m + 1) ≤ F m - F (m - reach N m)) :
    Inward N 1 S := by
  intro m hm1 hmN hmS
  refine ⟨by omega, fun h => by omega, fun _ => ?_⟩
  rw [leftCount_cnt hS hF hm1 hmN, rightCount_cnt hS hF hm1 hmN]
  exact h m hm1 hmN ((hS m hm1 hmN).not.1 hmS)

/-- A valid step through a counting function. -/
theorem semiStep_of_cnt {N : Nat} {S : Finset Nat} {P : Nat → Prop} [DecidablePred P]
    {F : Nat → Nat} (hS : ∀ x, 1 ≤ x → x ≤ N → (x ∈ S ↔ P x))
    (hF : ∀ t, F (t + 1) = F t + if P t then 1 else 0) {m : Nat} (hm1 : 1 ≤ m) (hmN : m ≤ N)
    (h : F m - F (m - reach N m) = F (m + 1 + reach N m) - F (m + 1)) :
    SemiStep N S.toList m := by
  unfold SemiStep
  rw [leftCount_cnt hS hF hm1 hmN, rightCount_cnt hS hF hm1 hmN]
  exact h

/-- The arm-count inequality of `inward_of_cnt`, split along the two cases of the reach
(`m ≤ (N + 1)/2`: the arms are `[1, m)`, `(m, 2m)`; otherwise `[2m - N, m)`, `(m, N]`). -/
theorem cnt_ineq_split {N : Nat} {F : Nat → Nat} {m : Nat} (hm1 : 1 ≤ m) (hmN : m ≤ N)
    (hA : m - 1 ≤ N - m → F (2 * m) - F (m + 1) ≤ F m - F 1)
    (hB : N - m ≤ m - 1 → F (N + 1) - F (m + 1) ≤ F m - F (2 * m - N)) :
    F (m + 1 + reach N m) - F (m + 1) ≤ F m - F (m - reach N m) := by
  unfold reach
  rcases Nat.le_total (m - 1) (N - m) with h | h
  · rw [min_eq_left h, show m - (m - 1) = 1 by omega, show m + 1 + (m - 1) = 2 * m by omega]
    exact hA h
  · rw [min_eq_right h, show m + 1 + (N - m) = N + 1 by omega,
      show m - (N - m) = 2 * m - N by omega]
    exact hB h

/-! ## The preimage `{1, 2, g}` in the smaller strip -/

/-- `{1, 2, g}` is co-reachable in `[p]` (`p < N`, `p ≠ 7`) by the induction hypothesis, for
`4 ≤ g ≤ p` and `g ≤ p - 2` when `p` is odd (`{1, 2, p - 1}`, `{1, 2, p}` are dead there). -/
theorem coReach_one_two_pre {N p g : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q) (hpN : p < N)
    (hp7 : p ≠ 7) (hg4 : 4 ≤ g) (hgp : g ≤ p) (hd : p % 2 = 0 ∨ g + 2 ≤ p) :
    CoReach p {1, 2, g} := by
  have hv : valid3B p 1 2 g = true := by
    unfold valid3B
    have h1 : step2B p g g 2 = true := by
      unfold step2B reach; simp only [beq_iff_eq]; split_ifs <;> omega
    have h2 : step2B p g 2 1 = true := by
      unfold step2B reach; simp only [beq_iff_eq]; split_ifs <;> omega
    simp [h1, h2]
  have hdd : dead3B p 1 2 g = false := by
    simp only [dead3B, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      decide_eq_false_iff_not, ne_eq]
    omega
  exact IH p hpN hp7 1 2 g le_rfl (by omega) (by omega) hgp hv hdd

/-- The transfer of `{1, 2, g}` through a near copy fixing `1` and `2`. -/
theorem coReach_one_two_near {N p g : Nat} {φ : Nat → Nat} {R : Nat → Prop}
    (hφ : NearEmb N p φ R) (hY : CoReach N ((Finset.Icc 1 p).image φ))
    (h1 : φ 1 = 1) (h2 : φ 2 = 2) (hg3 : 3 ≤ g) (hgp : g ≤ p) (hD : CoReach p {1, 2, g})
    (hR : ∀ j, 1 ≤ j → j ≤ p → j ∉ ({1, 2, g} : Finset Nat) → R j) :
    CoReach N {1, 2, φ g} := by
  have := coReach_nearEmb hφ hY (D := {1, 2, g}) (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]; omega) hR hD
  simpa [Finset.image_insert, h1, h2] using this

/-! ## `phi12 : [p] → [2p]`: `{1, 2, c}` for even `N` and odd `c` -/

theorem nearEmb_phi12_even {p : Nat} (hp : 3 ≤ p) :
    NearEmb (2 * p) p phi12 (fun j => j ≠ 2) := by
  refine ⟨fun y h1 h2 => ?_, fun x y hx1 hxp hy1 hyp e => ?_, fun j y hj1 hjp hR hy1 hyp => ?_,
    fun j y hj1 hjp hR hy1 hyp => ?_⟩
  · unfold phi12; split_ifs <;> omega
  · unfold phi12 at e; split_ifs at e <;> omega
  · unfold phi12 reach; split_ifs <;> omega
  · unfold phi12 reach; split_ifs <;> omega

/-- `#({1, 2} ∪ {odd ≥ 5}) ∩ [0, t)`. -/
def G12 (t : Nat) : Nat := if 5 ≤ t then t / 2 else if 3 ≤ t then 2 else t - 1

theorem G12_succ (t : Nat) :
    G12 (t + 1) = G12 t + if (t = 1 ∨ t = 2 ∨ (t % 2 = 1 ∧ 5 ≤ t)) then 1 else 0 := by
  unfold G12; split_ifs <;> omega

/-- The image of `phi12` in `[2p]` satisfies Theorem G (centre `1/2`). -/
theorem coReach_image_phi12_even {p : Nat} (hp : 3 ≤ p) :
    CoReach (2 * p) ((Finset.Icc 1 p).image phi12) := by
  have hmem := fun x => mem_image_phi12 (p := p) (x := x) hp
  refine coReach_of_inward (c2 := 1) (fun x hx => ?_) ?_
  · rw [hmem] at hx; rw [Finset.mem_Icc]; omega
  refine inward_of_cnt (P := fun x => x = 1 ∨ x = 2 ∨ (x % 2 = 1 ∧ 5 ≤ x)) (F := G12)
    (fun x hx1 hxN => by rw [hmem]; omega) G12_succ ?_
  intro m hm1 hmN hm
  unfold reach G12
  split_ifs <;> omega

/-- **`{1, 2, c}` for even `N` and odd `c`** (`7 ≤ c < N`, and `c + 5 ≤ N` when
`N ≡ 2 (mod 4)`), given the smaller strips: the image under `phi12 : [N/2] → [N]` of
`{1, 2, (c + 1)/2}`. -/
theorem coReach_one_two_evenN {N c : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (hN : N % 2 = 0) (h16 : 16 ≤ N) (hc : c % 2 = 1) (hc7 : 7 ≤ c) (hcN : c < N)
    (hd : N % 4 = 0 ∨ c + 5 ≤ N) : CoReach N {1, 2, c} := by
  obtain ⟨p, hp⟩ : ∃ p, p = N / 2 := ⟨_, rfl⟩
  have hNp : N = 2 * p := by omega
  have hD := coReach_one_two_pre (p := p) (g := (c + 1) / 2) IH (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have e3 : phi12 ((c + 1) / 2) = c := by unfold phi12; split_ifs <;> omega
  rw [← e3, hNp]
  exact coReach_one_two_near (nearEmb_phi12_even (by omega)) (coReach_image_phi12_even
    (by omega)) (by simp [phi12]) (by simp [phi12]) (by omega) (by omega) hD (fun j _ _ hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj; exact hj.2.1)

/-! ## `phiE : [p] → [2p + 1]`, `p` odd: `{1, 2, c}` for `N ≡ 3 (mod 4)` and even `c` -/

/-- The even class with `2 ↦ 1`, `4 ↦ 2`: `1 ↦ 1`, `2 ↦ 2`, `y ↦ 2y`. -/
def phiE (y : Nat) : Nat := if y ≤ 2 then y else 2 * y

theorem nearEmb_phiE {p : Nat} (ho : p % 2 = 1) :
    NearEmb (2 * p + 1) p phiE (fun j => 3 ≤ j) := by
  refine ⟨fun y h1 h2 => ?_, fun x y hx1 hxp hy1 hyp e => ?_, fun j y hj1 hjp hR hy1 hyp => ?_,
    fun j y hj1 hjp hR hy1 hyp => ?_⟩
  · unfold phiE; split_ifs <;> omega
  · unfold phiE at e; split_ifs at e <;> omega
  · unfold phiE reach; split_ifs <;> omega
  · unfold phiE reach; split_ifs <;> omega

theorem mem_image_phiE {p x : Nat} (hp : 3 ≤ p) :
    x ∈ (Finset.Icc 1 p).image phiE ↔
      x = 1 ∨ x = 2 ∨ (x % 2 = 0 ∧ 6 ≤ x ∧ x ≤ 2 * p) := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rw [Finset.mem_Icc] at hy; unfold phiE; split_ifs <;> omega
  · intro h
    rcases h with rfl | rfl | h
    · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, by simp [phiE]⟩
    · exact ⟨2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by simp [phiE]⟩
    · exact ⟨x / 2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by
        unfold phiE; split_ifs <;> omega⟩

/-- `#({1, 2} ∪ {even ≥ 6}) ∩ [0, t)`. -/
def GE (t : Nat) : Nat := if 7 ≤ t then 2 + (t - 5) / 2 else if 3 ≤ t then 2 else t - 1

theorem GE_succ (t : Nat) :
    GE (t + 1) = GE t + if (t = 1 ∨ t = 2 ∨ (t % 2 = 0 ∧ 6 ≤ t)) then 1 else 0 := by
  unfold GE; split_ifs <;> omega

/-- `#({1, 2, 5} ∪ {even ≥ 6}) ∩ [0, t)`. -/
def GE5 (t : Nat) : Nat := if 6 ≤ t then 3 + (t - 5) / 2 else if 3 ≤ t then 2 else t - 1

theorem GE5_succ (t : Nat) :
    GE5 (t + 1) = GE5 t +
      if (t = 1 ∨ t = 2 ∨ t = 5 ∨ (t % 2 = 0 ∧ 6 ≤ t)) then 1 else 0 := by
  unfold GE5; split_ifs <;> omega

/-- The image of `phiE` in `[2p + 1]`: `5` is a valid step, then Theorem G (centre `1/2`). -/
theorem coReach_image_phiE {p : Nat} (hp : 5 ≤ p) :
    CoReach (2 * p + 1) ((Finset.Icc 1 p).image phiE) := by
  have hmem := fun x => mem_image_phiE (p := p) (x := x) (by omega)
  set B := (Finset.Icc 1 p).image phiE with hB
  have hBs : B ⊆ Finset.Icc 1 (2 * p + 1) := by
    intro x hx; rw [hmem] at hx; rw [Finset.mem_Icc]; omega
  have h5 : (5 : Nat) ∉ B := by rw [hmem]; omega
  have hY5 : CoReach (2 * p + 1) (insert 5 B) := by
    refine coReach_of_inward (c2 := 1) (fun x hx => ?_) ?_
    · rw [Finset.mem_insert] at hx; rcases hx with rfl | hx
      · rw [Finset.mem_Icc]; omega
      · exact hBs hx
    refine inward_of_cnt (P := fun x => x = 1 ∨ x = 2 ∨ x = 5 ∨ (x % 2 = 0 ∧ 6 ≤ x))
      (F := GE5) (fun x hx1 hxN => by rw [Finset.mem_insert, hmem]; omega) GE5_succ ?_
    intro m hm1 hmN hm
    unfold reach GE5
    split_ifs <;> omega
  have hstep : SemiStep (2 * p + 1) B.toList 5 := by
    refine semiStep_of_cnt (P := fun x => x = 1 ∨ x = 2 ∨ (x % 2 = 0 ∧ 6 ≤ x)) (F := GE)
      (fun x hx1 hxN => by rw [hmem]; omega) GE_succ (by omega) (by omega) ?_
    unfold reach GE
    split_ifs <;> omega
  exact coReach_of_step hBs (by omega) (by omega) h5 hstep hY5

/-- **`{1, 2, c}` for `N ≡ 3 (mod 4)` and even `c`** (`8 ≤ c ≤ N - 5`), given the smaller
strips: the image under `phiE : [(N - 1)/2] → [N]` of `{1, 2, c/2}`. -/
theorem coReach_one_two_even3 {N c : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (hN : N % 4 = 3) (h19 : 19 ≤ N) (hc : c % 2 = 0) (hc8 : 8 ≤ c) (hcN : c + 5 ≤ N) :
    CoReach N {1, 2, c} := by
  obtain ⟨p, hp⟩ : ∃ p, p = N / 2 := ⟨_, rfl⟩
  have hNp : N = 2 * p + 1 := by omega
  have hD := coReach_one_two_pre (p := p) (g := c / 2) IH (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have e3 : phiE (c / 2) = c := by unfold phiE; split_ifs <;> omega
  rw [← e3, hNp]
  exact coReach_one_two_near (nearEmb_phiE (by omega)) (coReach_image_phiE
    (by omega)) (by simp [phiE]) (by simp [phiE]) (by omega) (by omega) hD (fun j hj1 _ hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj; show 3 ≤ j; omega)

/-! ## Moving the third panel: `{1, 2, c}` for even `N`, even `c`, and `N ≡ 3`, `c ≡ 1 (mod 4)`

A panel of the transferred set `D` may be moved freely as long as every panel outside `D`
keeps its window relation to it.  `phi12` with `g ↦ 2g - 2` (into `[2p]`) and `phiE` with `g ↦
2g - 1` for odd `g` (into `[2p + 1]`, `p` odd) do: the arm ends of `phi12 j` in `[2p]` and of
`phiE j` in `[2p + 1]` never separate the old and the new position of `g`. -/

/-- `phi12` with the panel `g` moved to `2g - 2`. -/
def phi12m (g y : Nat) : Nat := if y = g then 2 * g - 2 else phi12 y

theorem nearEmb_phi12m {p g : Nat} (hg4 : 4 ≤ g) (hgp : g ≤ p) :
    NearEmb (2 * p) p (phi12m g) (fun j => j ≠ 2 ∧ j ≠ g) := by
  refine ⟨fun y h1 h2 => ?_, fun x y hx1 hxp hy1 hyp e => ?_, fun j y hj1 hjp hR hy1 hyp => ?_,
    fun j y hj1 hjp hR hy1 hyp => ?_⟩
  · unfold phi12m phi12; split_ifs <;> omega
  · unfold phi12m phi12 at e; split_ifs at e <;> omega
  · unfold phi12m phi12 reach; split_ifs <;> omega
  · unfold phi12m phi12 reach; split_ifs <;> omega

theorem mem_image_phi12m {p g x : Nat} (hg4 : 4 ≤ g) (hgp : g ≤ p) :
    x ∈ (Finset.Icc 1 p).image (phi12m g) ↔ x = 1 ∨ x = 2 ∨
      (x % 2 = 1 ∧ 5 ≤ x ∧ x ≤ 2 * p - 1 ∧ x ≠ 2 * g - 1) ∨ x = 2 * g - 2 := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rw [Finset.mem_Icc] at hy; unfold phi12m phi12; split_ifs <;> omega
  · intro h
    rcases h with rfl | rfl | h | rfl
    · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, by simp [phi12m, phi12]; omega⟩
    · exact ⟨2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by simp [phi12m, phi12]; omega⟩
    · exact ⟨(x + 1) / 2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by
        unfold phi12m phi12; split_ifs <;> omega⟩
    · exact ⟨g, Finset.mem_Icc.2 ⟨by omega, hgp⟩, by simp [phi12m]⟩

/-- The counting function of the image of `phi12m g`. -/
def G12m (g t : Nat) : Nat := t / 2 + (if t = 3 then 1 else 0) + if t = 2 * g - 1 then 1 else 0

theorem G12m_succ {g : Nat} (hg4 : 4 ≤ g) (t : Nat) :
    G12m g (t + 1) = G12m g t + if (t = 1 ∨ t = 2 ∨ (t % 2 = 1 ∧ 5 ≤ t ∧ t ≠ 2 * g - 1) ∨
      t = 2 * g - 2) then 1 else 0 := by
  unfold G12m; split_ifs <;> omega

/-- The image of `phi12m g` in `[2p]` satisfies Theorem G (centre `1/2`). -/
theorem coReach_image_phi12m {p g : Nat} (hg4 : 4 ≤ g) (hgp : g ≤ p) :
    CoReach (2 * p) ((Finset.Icc 1 p).image (phi12m g)) := by
  have hmem := fun x => mem_image_phi12m (p := p) (x := x) hg4 hgp
  refine coReach_of_inward (c2 := 1) (fun x hx => ?_) ?_
  · rw [hmem] at hx; rw [Finset.mem_Icc]; omega
  refine inward_of_cnt (P := fun x => x = 1 ∨ x = 2 ∨ (x % 2 = 1 ∧ 5 ≤ x ∧ x ≠ 2 * g - 1) ∨
      x = 2 * g - 2) (F := G12m g) (fun x hx1 hxN => by rw [hmem]; omega) (G12m_succ hg4) ?_
  intro m hm1 hmN _
  have e1 : G12m g 1 = 0 := by unfold G12m; split_ifs <;> omega
  have e2 : G12m g (2 * p + 1) = p := by unfold G12m; split_ifs <;> omega
  refine cnt_ineq_split hm1 hmN (fun _ => ?_) (fun _ => ?_)
  · have e3 : G12m g (2 * m) = m := by unfold G12m; split_ifs <;> omega
    rw [e1, e3]; unfold G12m; split_ifs <;> omega
  · rw [e2]; unfold G12m; split_ifs <;> omega

/-- **`{1, 2, c}` for even `N` and even `c`** (`8 ≤ c ≤ N - 2`, and `c + 6 ≤ N` when
`N ≡ 2 (mod 4)`), given the smaller strips: the image under `phi12m ((c + 2)/2) : [N/2] → [N]`
of `{1, 2, (c + 2)/2}`. -/
theorem coReach_one_two_evenN_even {N c : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (hN : N % 2 = 0) (h16 : 16 ≤ N) (hc : c % 2 = 0) (hc8 : 8 ≤ c) (hcN : c + 2 ≤ N)
    (hd : N % 4 = 0 ∨ c + 6 ≤ N) : CoReach N {1, 2, c} := by
  obtain ⟨p, hp⟩ : ∃ p, p = N / 2 := ⟨_, rfl⟩
  have hNp : N = 2 * p := by omega
  obtain ⟨g, hg⟩ : ∃ g, g = (c + 2) / 2 := ⟨_, rfl⟩
  have hD := coReach_one_two_pre (p := p) (g := g) IH (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have e3 : phi12m g g = c := by unfold phi12m; simp only [if_true]; omega
  rw [← e3, hNp]
  exact coReach_one_two_near (nearEmb_phi12m (by omega) (by omega)) (coReach_image_phi12m
    (by omega) (by omega)) (by simp [phi12m, phi12]; omega) (by simp [phi12m, phi12]; omega)
    (by omega) (by omega) hD (fun j _ _ hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj; exact ⟨hj.2.1, hj.2.2⟩)

/-- `phiE` with the (odd) panel `g` moved to `2g - 1`. -/
def phiEm (g y : Nat) : Nat := if y = g then 2 * g - 1 else phiE y

theorem nearEmb_phiEm {p g : Nat} (ho : p % 2 = 1) (hg : g % 2 = 1) (hg3 : 3 ≤ g)
    (hgp : g ≤ p) : NearEmb (2 * p + 1) p (phiEm g) (fun j => 3 ≤ j ∧ j ≠ g) := by
  refine ⟨fun y h1 h2 => ?_, fun x y hx1 hxp hy1 hyp e => ?_, fun j y hj1 hjp hR hy1 hyp => ?_,
    fun j y hj1 hjp hR hy1 hyp => ?_⟩
  · unfold phiEm phiE; split_ifs <;> omega
  · unfold phiEm phiE at e; split_ifs at e <;> omega
  · unfold phiEm phiE reach; split_ifs <;> omega
  · unfold phiEm phiE reach; split_ifs <;> omega

theorem mem_image_phiEm {p g x : Nat} (hg3 : 3 ≤ g) (hgp : g ≤ p) :
    x ∈ (Finset.Icc 1 p).image (phiEm g) ↔ x = 1 ∨ x = 2 ∨
      (x % 2 = 0 ∧ 6 ≤ x ∧ x ≤ 2 * p ∧ x ≠ 2 * g) ∨ x = 2 * g - 1 := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rw [Finset.mem_Icc] at hy; unfold phiEm phiE; split_ifs <;> omega
  · intro h
    rcases h with rfl | rfl | h | rfl
    · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, by simp [phiEm, phiE]; omega⟩
    · exact ⟨2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by simp [phiEm, phiE]; omega⟩
    · exact ⟨x / 2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by
        unfold phiEm phiE; split_ifs <;> omega⟩
    · exact ⟨g, Finset.mem_Icc.2 ⟨by omega, hgp⟩, by simp [phiEm]⟩

/-- The counting function of the image of `phiEm g`. -/
def GEm (g t : Nat) : Nat := GE t + if t = 2 * g then 1 else 0

theorem GEm_succ {g : Nat} (hg : 7 ≤ g) (t : Nat) :
    GEm g (t + 1) = GEm g t + if (t = 1 ∨ t = 2 ∨ (t % 2 = 0 ∧ 6 ≤ t ∧ t ≠ 2 * g) ∨
      t = 2 * g - 1) then 1 else 0 := by
  unfold GEm GE; split_ifs <;> omega

/-- The counting function of the image of `phiEm g` with `5` added. -/
def GE5m (g t : Nat) : Nat := (t + 1) / 2 + (if t = 2 * g then 1 else 0) -
  if t = 1 ∨ t = 5 then 1 else 0

theorem GE5m_succ {g : Nat} (hg : 7 ≤ g) (t : Nat) :
    GE5m g (t + 1) = GE5m g t + if (t = 1 ∨ t = 2 ∨ t = 5 ∨ (t % 2 = 0 ∧ 6 ≤ t ∧ t ≠ 2 * g) ∨
      t = 2 * g - 1) then 1 else 0 := by
  unfold GE5m; split_ifs <;> omega

theorem GE5m_big {g t : Nat} (ht : 6 ≤ t) :
    GE5m g t = (t + 1) / 2 + if t = 2 * g then 1 else 0 := by
  unfold GE5m; split_ifs <;> omega

theorem GE5m_small {g t : Nat} (hg : 7 ≤ g) (ht : t ≤ 5) : GE5m g t = min (t - 1) 2 := by
  unfold GE5m; split_ifs <;> omega

/-- The arm-count inequality for `GE5m` (by regions, to keep the case splits small). -/
theorem GE5m_ineq {p g m : Nat} (hg : 7 ≤ g) (hgp : g + 2 ≤ p) (hm1 : 1 ≤ m)
    (hmN : m ≤ 2 * p + 1) :
    GE5m g (m + 1 + reach (2 * p + 1) m) - GE5m g (m + 1) ≤
      GE5m g m - GE5m g (m - reach (2 * p + 1) m) := by
  have e1 : GE5m g 1 = 0 := GE5m_small hg (by omega)
  have e2 : GE5m g (2 * p + 1 + 1) = p + 1 := by rw [GE5m_big (by omega)]; split_ifs <;> omega
  refine cnt_ineq_split hm1 hmN (fun _ => ?_) (fun _ => ?_)
  · rw [e1]
    rcases Nat.lt_or_ge m 6 with hm | hm
    · interval_cases m <;> simp only [GE5m] <;> split_ifs <;> omega
    · rw [GE5m_big (t := 2 * m) (by omega), GE5m_big (t := m + 1) (by omega),
        GE5m_big (t := m) (by omega)]
      split_ifs <;> omega
  · rw [e2, GE5m_big (t := m + 1) (by omega), GE5m_big (t := m) (by omega)]
    rcases Nat.lt_or_ge (2 * m - (2 * p + 1)) 6 with hd | hd
    · rw [GE5m_small hg (by omega)]; split_ifs <;> omega
    · rw [GE5m_big hd]; split_ifs <;> omega

/-- The image of `phiEm g` in `[2p + 1]`: `5` is a valid step, then Theorem G (centre `1/2`). -/
theorem coReach_image_phiEm {p g : Nat} (hg : 7 ≤ g) (hgp : g + 2 ≤ p) :
    CoReach (2 * p + 1) ((Finset.Icc 1 p).image (phiEm g)) := by
  have hmem := fun x => mem_image_phiEm (p := p) (g := g) (x := x) (by omega) (by omega)
  set B := (Finset.Icc 1 p).image (phiEm g) with hB
  have hBs : B ⊆ Finset.Icc 1 (2 * p + 1) := by
    intro x hx; rw [hmem] at hx; rw [Finset.mem_Icc]; omega
  have h5 : (5 : Nat) ∉ B := by rw [hmem]; omega
  have hY5 : CoReach (2 * p + 1) (insert 5 B) := by
    refine coReach_of_inward (c2 := 1) (fun x hx => ?_) ?_
    · rw [Finset.mem_insert] at hx; rcases hx with rfl | hx
      · rw [Finset.mem_Icc]; omega
      · exact hBs hx
    refine inward_of_cnt (P := fun x => x = 1 ∨ x = 2 ∨ x = 5 ∨
        (x % 2 = 0 ∧ 6 ≤ x ∧ x ≠ 2 * g) ∨ x = 2 * g - 1)
      (F := GE5m g) (fun x hx1 hxN => by
        rw [Finset.mem_insert, hmem]
        constructor
        · rintro (h | h | h | h | h) <;> omega
        · rintro (h | h | h | h | h) <;> omega) (GE5m_succ hg) ?_
    intro m hm1 hmN _
    exact GE5m_ineq hg hgp hm1 hmN
  have hstep : SemiStep (2 * p + 1) B.toList 5 := by
    refine semiStep_of_cnt (P := fun x => x = 1 ∨ x = 2 ∨ (x % 2 = 0 ∧ 6 ≤ x ∧ x ≠ 2 * g) ∨
        x = 2 * g - 1) (F := GEm g)
      (fun x hx1 hxN => by
        rw [hmem]
        constructor
        · rintro (h | h | h | h) <;> omega
        · rintro (h | h | h | h) <;> omega) (GEm_succ hg) (by omega) (by omega) ?_
    rw [show reach (2 * p + 1) 5 = 4 by unfold reach; omega]
    have e1 : GEm g 5 = 2 := by unfold GEm GE; split_ifs <;> omega
    have e2 : GEm g 1 = 0 := by unfold GEm GE; split_ifs <;> omega
    have e3 : GEm g 10 = 4 := by unfold GEm GE; split_ifs <;> omega
    have e4 : GEm g 6 = 2 := by unfold GEm GE; split_ifs <;> omega
    rw [show 5 - 4 = 1 by rfl, show 5 + 1 + 4 = 10 by rfl, e1, e4, e3, e2]
  exact coReach_of_step hBs (by omega) (by omega) h5 hstep hY5

/-- **`{1, 2, c}` for `N ≡ 3 (mod 4)` and `c ≡ 1 (mod 4)`** (`13 ≤ c ≤ N - 6`), given the
smaller strips: the image under `phiEm ((c + 1)/2) : [(N - 1)/2] → [N]` of
`{1, 2, (c + 1)/2}`. -/
theorem coReach_one_two_odd3 {N c : Nat} (IH : ∀ q, q < N → q ≠ 7 → Good3 q)
    (hN : N % 4 = 3) (hc : c % 4 = 1) (hc13 : 13 ≤ c) (hcN : c + 6 ≤ N) :
    CoReach N {1, 2, c} := by
  obtain ⟨p, hp⟩ : ∃ p, p = N / 2 := ⟨_, rfl⟩
  have hNp : N = 2 * p + 1 := by omega
  obtain ⟨g, hg⟩ : ∃ g, g = (c + 1) / 2 := ⟨_, rfl⟩
  have hD := coReach_one_two_pre (p := p) (g := g) IH (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have e3 : phiEm g g = c := by unfold phiEm; simp only [if_true]; omega
  rw [← e3, hNp]
  exact coReach_one_two_near (nearEmb_phiEm (by omega) (by omega) (by omega) (by omega))
    (coReach_image_phiEm (by omega) (by omega)) (by simp [phiEm, phiE]; omega)
    (by simp [phiEm, phiE]; omega) (by omega) (by omega) hD (fun j _ _ hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj; exact ⟨by omega, hj.2.2⟩)

end Live3s
end Folds
