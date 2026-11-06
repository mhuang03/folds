import Folds.Live6

/-!
# Live pairs, part 7

`experiments/live7/PROOFS.txt`.

* `witB`, `coReach_of_witB`: a memory-light Boolean checker for witness orderings (the set
  of placed panels is a bitmask `Nat`, so membership is one `Nat.testBit`); one small
  `decide` per pair.
-/

namespace Folds
namespace Live7

open Live2 Live4 Adjacent Live5 Live6

/-! ## A bitmask checker for witness orderings -/

/-- The bitmask `M ||| 2^x₁ ||| 2^x₂ ||| …` of a list. -/
def maskL (M : Nat) : List Nat → Nat
  | [] => M
  | x :: t => maskL (M ||| 2 ^ x) t

theorem testBit_or_pow (M x y : Nat) :
    (M ||| 2 ^ x).testBit y = true ↔ M.testBit y = true ∨ y = x := by
  rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
  exact or_congr Iff.rfl eq_comm

theorem testBit_maskL (l : List Nat) : ∀ M y,
    (maskL M l).testBit y = true ↔ M.testBit y = true ∨ y ∈ l := by
  induction l with
  | nil => intro M y; simp [maskL]
  | cons x t ih =>
    intro M y
    rw [maskL, ih, testBit_or_pow, List.mem_cons]
    tauto

/-- Panels of the bitmask in the left arm of `m` (reach `r`). -/
def cntL (M m r : Nat) : Nat := (List.range' 1 r).countP fun d => M.testBit (m - d)

/-- Panels of the bitmask in the right arm of `m` (reach `r`). -/
def cntR (M m r : Nat) : Nat := (List.range' 1 r).countP fun d => M.testBit (m + d)

/-- Every step valid and new, the placed panels kept as a bitmask. -/
def semiB (N : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | M, m :: t => (!M.testBit m && cntL M m (reach N m) == cntR M m (reach N m)) &&
      semiB N (M ||| 2 ^ m) t

theorem cntL_eq {N M m : Nat} {S : List Nat} (hM : ∀ x, M.testBit x = true ↔ x ∈ S) :
    cntL M m (reach N m) = leftCount N S m := by
  unfold cntL leftCount
  refine List.countP_congr fun d _ => ?_
  rw [hM, decide_eq_true_eq]

theorem cntR_eq {N M m : Nat} {S : List Nat} (hM : ∀ x, M.testBit x = true ↔ x ∈ S) :
    cntR M m (reach N m) = rightCount N S m := by
  unfold cntR rightCount
  refine List.countP_congr fun d _ => ?_
  rw [hM, decide_eq_true_eq]

theorem semiB_sound {N : Nat} : ∀ (l : List Nat) (M : Nat) (S : List Nat),
    semiB N M l = true → (∀ x, M.testBit x = true ↔ x ∈ S) → S.Nodup →
    (S ++ l).Nodup ∧ ∀ k (h : k < l.length), SemiStep N (S ++ l.take k) l[k] := by
  intro l
  induction l with
  | nil => intro M S _ _ hS; simpa using hS
  | cons m t ih =>
    intro M S h hM hS
    simp only [semiB, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    obtain ⟨⟨hm, hc⟩, ht⟩ := h
    have hmS : m ∉ S := fun e => by rw [← hM] at e; rw [e] at hm; exact absurd hm (by simp)
    have hM' : ∀ x, (M ||| 2 ^ m).testBit x = true ↔ x ∈ S ++ [m] := fun x => by
      rw [testBit_or_pow, hM, List.mem_append, List.mem_singleton]
    have hS' : (S ++ [m]).Nodup := by
      rw [List.nodup_append]
      exact ⟨hS, List.nodup_singleton m, fun a ha b hb e => by
        rw [List.mem_singleton] at hb; subst e; subst hb; exact hmS ha⟩
    obtain ⟨hnd, hst⟩ := ih _ _ ht hM' hS'
    refine ⟨by simpa using hnd, fun k hk => ?_⟩
    cases k with
    | zero =>
      simp only [List.take_zero, List.append_nil, List.getElem_cons_zero]
      unfold SemiStep
      rw [← cntL_eq hM, ← cntR_eq hM]; exact hc
    | succ k =>
      have := hst k (by simp at hk; omega)
      simpa using this

/-- The panels of `[N]` other than `u, v`. -/
def compl2 (N u v : Nat) : List Nat := (List.range' 1 N).filter fun x => x != u && x != v

theorem mem_compl2 {N u v x : Nat} :
    x ∈ compl2 N u v ↔ (1 ≤ x ∧ x ≤ N) ∧ x ≠ u ∧ x ≠ v := by
  unfold compl2
  rw [List.mem_filter, List.mem_range'_1]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  omega

/-- The witness check: `l` is an ordering of `[N] \ {u, v}` from scratch. -/
def witB (N u v : Nat) (l : List Nat) : Bool :=
  semiB N 0 l && maskL 0 l == maskL 0 (compl2 N u v)

theorem coReach_of_witB {N u v : Nat} {l : List Nat} (h : witB N u v l = true) :
    CoReach N {u, v} := by
  unfold witB at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hs, hm⟩ := h
  obtain ⟨hnd, hst⟩ := semiB_sound l 0 [] hs (fun x => by simp) List.nodup_nil
  rw [List.nil_append] at hnd
  have hmem : ∀ x, x ∈ l ↔ x ∈ compl2 N u v := fun x => by
    have a := testBit_maskL l 0 x
    have b := testBit_maskL (compl2 N u v) 0 x
    rw [hm] at a
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or] at a b
    rw [← a, b]
  unfold CoReach g
  rw [Finset.card_pos]
  refine ⟨l, mem_semiOrders.2 ⟨⟨hnd, ?_⟩, fun k hk => by simpa using hst k hk⟩⟩
  ext x
  rw [List.mem_toFinset, hmem, mem_compl2, Finset.mem_sdiff, Finset.mem_Icc]
  simp

/-! ## Centred Beatty copies `Z(N, p)`

`Z(N, p) = {⌊k (N + 2)/(p + 1)⌋ : 1 ≤ k ≤ p}` for `2p ≤ N`: the interior division points of
`[0, N + 2]` into `p + 1` equal parts.  (It is the two-sided Beatty copy of
`experiments/live6/PROOFS.txt` section 5: its left elements follow `⌊k M/q⌋` and, read from the
right end, its right elements follow `⌊(k M - 1)/q⌋`, `M = N + 2`, `q = p + 1`.)  Its counting
function is `beattyCnt (N + 2) (p + 1) 0`. -/

/-- The `k`-th element of `Z(N, p)`. -/
def zF (N p k : Nat) : Nat := beatty (N + 2) (p + 1) 0 k

/-- The counting function of `Z(N, p)`. -/
def zC (N p t : Nat) : Nat := beattyCnt (N + 2) (p + 1) 0 t

theorem zC_top {N p : Nat} (hpN : 2 * p ≤ N) : zC N p N = p := by
  unfold zC beattyCnt
  have e1 : (p + 1) * N + (p + 1) + 0 - 1 = p * N + N + p := by rw [Nat.succ_mul]; omega
  have e2 : p * (N + 2) = p * N + 2 * p := by ring
  have e3 : (p + 1) * (N + 2) = p * N + N + 2 * p + 2 := by ring
  rw [e1]
  exact Nat.div_eq_of_lt_le (by rw [e2]; omega) (by rw [e3]; omega)

theorem countEmb_z {N p : Nat} (hp : 1 ≤ p) (hpN : 2 * p ≤ N) :
    CountEmb N p (zF N p) (zC N p) := by
  have hb := countEmb_beatty (N := N + 2) (p := p + 1) (h := 0) (by omega) (by omega)
  exact ⟨hb.gal, hb.mono, hb.zero, zC_top hpN⟩

/-- Division with remainder for the elements: `k M = q ⌊k M/q⌋ + s`, `s < q`. -/
theorem zF_spec (N p k : Nat) :
    k * (N + 2) = (p + 1) * zF N p k + k * (N + 2) % (p + 1) ∧
      k * (N + 2) % (p + 1) < p + 1 := by
  unfold zF beatty
  rw [Nat.sub_zero]
  exact ⟨(Nat.div_add_mod _ _).symm, Nat.mod_lt _ (by omega)⟩

theorem zC_eq {N p t x : Nat} (lo : x * (N + 2) ≤ (p + 1) * t + p)
    (hi : (p + 1) * t + p < (x + 1) * (N + 2)) : zC N p t = x := by
  unfold zC beattyCnt
  rw [show (p + 1) * t + (p + 1) + 0 - 1 = (p + 1) * t + p by omega]
  exact Nat.div_eq_of_lt_le lo hi

/-- The copy condition of `Z(N, p)` at every element (left half: doubling; right half: the
mirrored doubling). -/
theorem copyAt_z {N p : Nat} (_hp : 1 ≤ p) (hpN : 2 * p ≤ N) {j : Nat} (hj : 1 ≤ j) :
    CopyAt N p (zF N p) (zC N p) j := by
  obtain ⟨e, hs⟩ := zF_spec N p j
  unfold CopyAt
  generalize zF N p j = z at e ⊢
  generalize j * (N + 2) % (p + 1) = s at e hs
  generalize hA : j * (N + 2) = A at e
  generalize hP : (p + 1) * z = P at e
  generalize hQ : (p + 1) * (N + 2) = Q
  have hjM : N + 2 ≤ A := by rw [← hA]; exact Nat.le_mul_of_pos_left _ hj
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  · -- `c(2z - 1) = 2j - 1`
    have hz : 1 ≤ z := by
      by_contra h0; push Not at h0
      have : z = 0 := by omega
      subst this; rw [Nat.mul_zero] at hP; omega
    have f1 : (p + 1) * (2 * z - 1) + (p + 1) = 2 * P := by
      rw [← hP, ← Nat.mul_succ, show (2 * z - 1).succ = 2 * z by omega, Nat.mul_left_comm]
    have f2 : (2 * j - 1) * (N + 2) + (N + 2) = 2 * A := by
      rw [← hA, ← Nat.succ_mul, show (2 * j - 1).succ = 2 * j by omega, Nat.mul_assoc]
    apply zC_eq
    · omega
    · rw [show 2 * j - 1 + 1 = 2 * j by omega, Nat.mul_assoc, hA]; omega
  · -- `c(2z - N - 1) + p = 2j - 1`
    have f0 : (p + 1) * (N + 1) ≤ 2 * P := by
      rw [← hP, Nat.mul_left_comm]; exact Nat.mul_le_mul_left _ (by omega)
    have f0' : (p + 1) * (N + 1) + (p + 1) = Q := by rw [← hQ, ← Nat.mul_succ]
    have hle : p + 1 ≤ 2 * j := by
      by_contra hc; push Not at hc
      have : (2 * j + 1) * (N + 2) ≤ Q := by rw [← hQ]; exact Nat.mul_le_mul_right _ hc
      rw [Nat.add_mul, one_mul, Nat.mul_assoc, hA] at this
      omega
    have f1 : (p + 1) * (2 * z - N - 1) + Q = 2 * P + (p + 1) := by
      rw [← hQ, ← hP, ← Nat.mul_add, show 2 * z - N - 1 + (N + 2) = 2 * z + 1 by omega,
        Nat.mul_add, mul_one, Nat.mul_left_comm]
    have f2 : (2 * j - (p + 1)) * (N + 2) + Q = 2 * A := by
      rw [← hQ, ← hA, ← Nat.add_mul, Nat.sub_add_cancel hle, Nat.mul_assoc]
    have f3 : (2 * j - (p + 1) + 1) * (N + 2) = (2 * j - (p + 1)) * (N + 2) + (N + 2) := by
      rw [Nat.add_mul, one_mul]
    have key : zC N p (2 * z - N - 1) = 2 * j - (p + 1) := by
      apply zC_eq
      · omega
      · rw [f3]; omega
    omega

theorem winEmb_z {N p : Nat} (hp : 1 ≤ p) (hpN : 2 * p ≤ N) : WinEmb N p (zF N p) :=
  (countEmb_z hp hpN).winEmb fun _ hj _ => copyAt_z hp hpN hj

/-- **`Z(N, p)` satisfies Theorem G** with the centre in the middle of the strip. -/
theorem inward_z {N p : Nat} (hp : 1 ≤ p) (hpN : 2 * p ≤ N) :
    Inward N (2 * ((N + 1) / 2) + 1) ((Finset.Icc 1 p).image (zF N p)) := by
  have hc := countEmb_z hp hpN
  have hφ := winEmb_z hp hpN
  have hperm := image_toList_perm hφ
  have hnd := Finset.nodup_toList ((Finset.Icc 1 p).image (zF N p))
  intro m hm1 hmN hmB
  have hnot : ∀ y, 1 ≤ y → y ≤ p → zF N p y ≠ m := fun y hy1 hyp e =>
    hmB (Finset.mem_image.2 ⟨y, Finset.mem_Icc.2 ⟨hy1, hyp⟩, e⟩)
  have hcm := hc.c_pred_of_not_mem hm1 hmN hnot
  rw [leftCount_eq hnd, rightCount_eq hnd, hperm.countP_eq, hperm.countP_eq,
    hc.countP_left hm1 hmN, hc.countP_right hm1 hmN, hcm]
  refine ⟨by omega, fun hlt => ?_, fun hgt => ?_⟩
  · -- left half: `2 c(m - 1) ≤ c(2m - 1)`
    have hr : reach N m = m - 1 := by unfold reach; omega
    rw [hr, show m - (m - 1) - 1 = 0 by omega, hc.zero, show m + (m - 1) = 2 * m - 1 by omega]
    have key := beatty_key (N := N + 2) (p := p + 1) (h := 0) (by omega) (by omega) hm1 (by omega)
    have e : zC N p (2 * m - 1) = (2 * ((p + 1) * m) + 0 - 1) / (N + 2) := by
      unfold zC beattyCnt
      congr 1
      rw [Nat.mul_sub_one, Nat.mul_left_comm]
      have : p + 1 ≤ 2 * ((p + 1) * m) := by
        have := Nat.le_mul_of_pos_right (p + 1) hm1; omega
      omega
    have : zC N p (m - 1) = beattyCnt (N + 2) (p + 1) 0 (m - 1) := rfl
    omega
  · -- right half: `c(2m - N - 1) + p ≤ 2 c(m - 1)`, using `m ∉ Z`
    have hr : reach N m = N - m := by unfold reach; omega
    rw [hr, show m + (N - m) = N by omega, hc.top, show m - (N - m) - 1 = 2 * m - N - 1 by omega]
    -- `x = c(m - 1)`, `q m - 1 = x M + r`, and `r + q < M` since `m ∉ Z`
    have e1 : zC N p (m - 1) = ((p + 1) * m - 1) / (N + 2) := by
      unfold zC beattyCnt; congr 1
      rw [Nat.mul_sub_one]
      have := Nat.le_mul_of_pos_right (p + 1) hm1; omega
    have e2 : zC N p m = ((p + 1) * m - 1 + (p + 1)) / (N + 2) := by
      unfold zC beattyCnt; congr 1
      have := Nat.le_mul_of_pos_right (p + 1) hm1; omega
    have hcm' := hcm
    rw [e1, e2] at hcm'
    have hd := Nat.div_add_mod ((p + 1) * m - 1) (N + 2)
    have hmod := Nat.mod_lt ((p + 1) * m - 1) (show 0 < N + 2 by omega)
    generalize ((p + 1) * m - 1) / (N + 2) = x at hd hcm' e1
    generalize ((p + 1) * m - 1) % (N + 2) = r at hd hmod
    -- `r + q < M`
    have hrq : r + (p + 1) < N + 2 := by
      by_contra hcon; push Not at hcon
      have : x + 1 ≤ ((p + 1) * m - 1 + (p + 1)) / (N + 2) := by
        rw [Nat.le_div_iff_mul_le (by omega)]; rw [← hd]; nlinarith
      omega
    have e3 : zC N p (2 * m - N - 1) + (p + 1) = 2 * x + 1 ∨
        zC N p (2 * m - N - 1) + (p + 1) ≤ 2 * x + 1 := by
      right
      have hpm := Nat.le_mul_of_pos_right (p + 1) hm1
      have : zC N p (2 * m - N - 1) + (p + 1) = zC N p (2 * m - N - 1 + (N + 2)) := by
        unfold zC; rw [beattyCnt_add (by omega) (by omega)]
      rw [this, show 2 * m - N - 1 + (N + 2) = 2 * m + 1 by omega]
      unfold zC beattyCnt
      rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
      have : (p + 1) * (2 * m + 1) + (p + 1) + 0 - 1 = 2 * ((p + 1) * m - 1) + 2 * (p + 1) + 1 := by
        rw [Nat.mul_add, mul_one, Nat.mul_left_comm]; omega
      rw [this, ← hd]
      have : (N + 2) * (2 * x + 1) = 2 * ((N + 2) * x) + (N + 2) := by ring
      omega
    rw [e1]; omega

theorem coReach_z {N p : Nat} (hp : 1 ≤ p) (hpN : 2 * p ≤ N) :
    CoReach N ((Finset.Icc 1 p).image (zF N p)) := by
  refine coReach_of_inward (fun x hx => ?_) (inward_z hp hpN)
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
  rw [Finset.mem_Icc] at hy ⊢
  exact (winEmb_z hp hpN).bound y hy.1 hy.2

/-- **Transfer through a centred Beatty copy.** -/
theorem coReach_z_transfer {N p : Nat} (hp : 1 ≤ p) (hpN : 2 * p ≤ N) {D : Finset Nat}
    (hDs : D ⊆ Finset.Icc 1 p) (hD : CoReach p D) : CoReach N (D.image (zF N p)) :=
  coReach_winEmb (winEmb_z hp hpN) (coReach_z hp hpN) hDs hD

/-! ## (R2) Corner pairs through `Z(N, p)`; the pairs `(3, N - 2)` and `(5, N - 4)` -/

theorem zF_one (N p : Nat) : zF N p 1 = (N + 2) / (p + 1) := by
  unfold zF beatty; rw [Nat.one_mul, Nat.sub_zero]

/-- **Corner pairs of `Z(N, p)`**: for `p` odd, `p ≠ 7`, `2p ≤ N`, the pair formed by the first
and the last element of `Z(N, p)` is co-reachable (image of `{1, p}`). -/
theorem coReach_z_corner {N p : Nat} (hp3 : 3 ≤ p) (hpN : 2 * p ≤ N) (hodd : p % 2 = 1)
    (h7 : p ≠ 7) : CoReach N {zF N p 1, zF N p p} := by
  have := coReach_z_transfer (by omega) hpN (D := {1, p}) (pair_sub le_rfl (by omega) le_rfl)
    (coReach_one_N p hodd h7)
  rwa [Finset.image_insert, Finset.image_singleton] at this

/-- The first element is `c` and the last `N + 1 - c` when `c (p + 1) < N + 2 < (c + 1)(p + 1)`. -/
theorem zF_corner {N p c : Nat} (h1 : c * (p + 1) < N + 2) (h2 : N + 2 < (c + 1) * (p + 1)) :
    zF N p 1 = c ∧ zF N p p = N + 1 - c := by
  rw [zF_one]
  refine ⟨Nat.div_eq_of_lt_le (by omega) (by omega), ?_⟩
  unfold zF beatty
  rw [Nat.sub_zero]
  have e1 : (N + 1 - c) * (p + 1) + c * (p + 1) = (N + 1) * (p + 1) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by nlinarith)]
  have e2 : p * (N + 2) + (N + 2) = (N + 2) * (p + 1) := by ring
  have e3 : (N + 1) * (p + 1) + (p + 1) = (N + 2) * (p + 1) := by ring
  have e4 : (c + 1) * (p + 1) = c * (p + 1) + (p + 1) := by ring
  apply Nat.div_eq_of_lt_le
  · omega
  · have e5 : (N + 1 - c + 1) * (p + 1) = (N + 1 - c) * (p + 1) + (p + 1) := by ring
    omega

/-- **`{3, N - 2}` is co-reachable for every `N ≥ 30`** (in particular for `N = 2^k`, `k ≥ 5`):
the corner pair of `Z(N, p)`, `p + 1 = 2⌊(N + 10)/8⌋`. -/
theorem coReach_three_two {N : Nat} (hN : 30 ≤ N) : CoReach N {3, N - 2} := by
  obtain ⟨p, hp⟩ : ∃ p, p = 2 * ((N + 10) / 8) - 1 := ⟨_, rfl⟩
  have h1 : 3 * (p + 1) < N + 2 := by omega
  have h2 : N + 2 < (3 + 1) * (p + 1) := by omega
  have := coReach_z_corner (N := N) (p := p) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨e1, e2⟩ := zF_corner h1 h2
  rwa [e1, e2, show N + 1 - 3 = N - 2 by omega] at this

/-- **`{5, N - 4}` is co-reachable for every `N ≥ 59`** (in particular for `N = 2^k`, `k ≥ 6`):
the corner pair of `Z(N, p)`, `p + 1 = 2⌊(N + 14)/12⌋`. -/
theorem coReach_five_four {N : Nat} (hN : 59 ≤ N) : CoReach N {5, N - 4} := by
  obtain ⟨p, hp⟩ : ∃ p, p = 2 * ((N + 14) / 12) - 1 := ⟨_, rfl⟩
  have h1 : 5 * (p + 1) < N + 2 := by omega
  have h2 : N + 2 < (5 + 1) * (p + 1) := by omega
  have := coReach_z_corner (N := N) (p := p) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨e1, e2⟩ := zF_corner h1 h2
  rwa [e1, e2, show N + 1 - 5 = N - 4 by omega] at this

/-! ## Conjecture C modulo a covering statement, with the copies `Z(N, p)` -/

/-- The pair `u < v` is the image of a non-dead pair of `[p]` under `Z(N, p)`. -/
def SettledZ (N u v : Nat) : Prop :=
  ∃ p a b, 1 ≤ p ∧ 2 * p ≤ N ∧ 1 ≤ a ∧ a < b ∧ b ≤ p ∧ deadB p a b = false ∧
    zF N p a = u ∧ zF N p b = v

/-- Directly settled: `Live6.Settled` (Theorem G, `{1, N}`, Beatty, swapped Beatty, `chiY`,
doubling splits) or a centred Beatty copy `Z(N, p)`. -/
def Settled7 (N u v : Nat) : Prop := Settled N u v ∨ SettledZ N u v

/-- The covering statement with the centred Beatty copies and an exceptional set `E`. -/
def CoverLemma7 (E : Nat → Nat → Nat → Prop) : Prop :=
  ∀ N u v, 13 ≤ N → 1 ≤ u → u < v → v ≤ N → deadB N u v = false →
    Settled7 N u v ∨ Settled7 N (N + 1 - v) (N + 1 - u) ∨ E N u v

theorem settled_imp {N : Nat}
    (ih : ∀ m < N, ∀ u v, 1 ≤ u → u < v → v ≤ m → deadB m u v = false → CoReach m {u, v})
    (h12 : 13 ≤ N) {u v : Nat} (hu : 1 ≤ u) (huv : u < v) (hv : v ≤ N) (hS : Settled7 N u v) :
    CoReach N {u, v} := by
  rcases hS with hS | ⟨p, a, b, hp, hpN, ha, hab, hb, hdp, e1, e2⟩
  · rcases hS with hS | hS | ⟨p, h, a, b, hp, hh, h1, ha, hab, hb, hdp, e1, e2⟩ |
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
  · exact coReach_image_pair (coReach_z_transfer hp hpN (pair_sub ha hab hb)
      (ih p (by omega) a b ha hab hb hdp)) e1 e2

/-- **Conjecture C modulo `CoverLemma7`**: every non-dead pair is co-reachable. -/
theorem coReach_of_cover7 {E : Nat → Nat → Nat → Prop}
    (hX : ∀ N u v, E N u v → CoReach N {u, v}) (hcov : CoverLemma7 E) :
    ∀ N u v, 1 ≤ u → u < v → v ≤ N → deadB N u v = false → CoReach N {u, v} := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro u v hu huv hv hd
    by_cases h12 : N ≤ 12
    · exact coReach_base h12 hu huv hv hd
    rcases hcov N u v (by omega) hu huv hv hd with hS | hS | hS
    · exact settled_imp ih (by omega) hu huv hv hS
    · have := coReach_mirror (settled_imp ih (by omega) (u := N + 1 - v) (v := N + 1 - u)
        (by omega) (by omega) (by omega) hS)
      rw [Finset.image_insert, Finset.image_singleton,
        show N + 1 - (N + 1 - v) = v by omega, show N + 1 - (N + 1 - u) = u by omega,
        Finset.pair_comm] at this
      exact this
    · exact hX N u v hS

/-- **Conjecture C for valid 2-prefixes, modulo `CoverLemma7 E`** (with the pairs of `E`
co-reachable). -/
theorem extends_iff_not_dead7 {E : Nat → Nat → Nat → Prop}
    (hX : ∀ N u v, E N u v → CoReach N {u, v}) (hcov : CoverLemma7 E) {N m₁ m₂ : Nat}
    (h1 : 1 ≤ m₁ ∧ m₁ ≤ N) (h2 : 1 ≤ m₂ ∧ m₂ ≤ N) (h12 : m₁ ≠ m₂)
    (hval : SemiSymmetric N [m₁, m₂]) :
    Extends N [m₁, m₂] ↔ deadB N (min m₁ m₂) (max m₁ m₂) = false :=
  extends_iff_not_dead (E := fun N u v => 1 ≤ u ∧ u < v ∧ v ≤ N ∧ deadB N u v = false)
    (fun N u v h => coReach_of_cover7 hX hcov N u v h.1 h.2.1 h.2.2.1 h.2.2.2)
    (fun _ _ _ _ hu huv hv hd => Or.inr (Or.inr ⟨hu, huv, hv, hd⟩)) h1 h2 h12 hval

/-! ## (R3) The small hard core: explicit witness orderings -/

-- BEGIN WITNESSES (generated by experiments/live7/gen_wit.py)

/-- The hard core for `13 ≤ N ≤ 128` (`experiments/live6/core520.txt`), `u ≤ N + 1 - v`. -/
def coreList : List (Nat × Nat × Nat) :=
  [(13, 2, 11), (15, 1, 14), (15, 2, 13), (16, 1, 15), (16, 2, 15), (16, 3, 14), (16, 5, 12), (17, 1, 16), (17, 2, 16), (17, 3, 12), (17, 3, 14), (18, 2, 17), (19, 3, 16), (21, 2, 19), (23, 2, 21), (23, 3, 18), (23, 5, 16), (23, 6, 17), (25, 2, 23), (27, 2, 25), (28, 5, 18), (29, 3, 20), (29, 3, 24), (29, 3, 26), (29, 5, 22), (31, 3, 28), (31, 5, 24), (32, 3, 26), (32, 3, 30), (32, 5, 22), (32, 5, 28), (35, 3, 32), (37, 3, 32), (37, 5, 30), (41, 3, 32), (41, 3, 36), (43, 3, 34), (43, 3, 38), (47, 3, 42), (47, 5, 40), (49, 3, 44), (53, 3, 48), (53, 5, 46), (59, 5, 52), (61, 3, 52), (61, 5, 54), (64, 3, 62), (64, 5, 60), (67, 5, 60), (71, 5, 64), (73, 3, 64), (83, 3, 74), (83, 5, 76), (101, 5, 94), (103, 5, 96), (128, 3, 126), (128, 5, 124)]

theorem wit_13_2_11 : witB 13 2 11
    [10, 3, 8, 5, 7, 1, 4, 12, 13, 9, 6] = true := by
  decide +kernel

theorem wit_15_1_14 : witB 15 1 14
    [5, 2, 3, 12, 10, 9, 15, 7, 4, 13, 11, 6, 8] = true := by
  decide +kernel

theorem wit_15_2_13 : witB 15 2 13
    [6, 1, 12, 10, 11, 5, 3, 4, 14, 15, 8, 9, 7] = true := by
  decide +kernel

theorem wit_16_1_15 : witB 16 1 15
    [11, 5, 9, 14, 13, 2, 3, 7, 4, 12, 10, 6, 8, 16] = true := by
  decide +kernel

theorem wit_16_2_15 : witB 16 2 15
    [6, 3, 4, 12, 11, 16, 14, 13, 7, 5, 1, 9, 10, 8] = true := by
  decide +kernel

theorem wit_16_3_14 : witB 16 3 14
    [7, 2, 4, 12, 11, 6, 15, 16, 5, 13, 1, 9, 10, 8] = true := by
  decide +kernel

theorem wit_16_5_12 : witB 16 5 12
    [6, 13, 7, 16, 11, 8, 3, 10, 9, 1, 4, 14, 15, 2] = true := by
  decide +kernel

theorem wit_17_1_16 : witB 17 1 16
    [2, 12, 7, 10, 5, 3, 4, 17, 14, 11, 15, 8, 6, 13, 9] = true := by
  decide +kernel

theorem wit_17_2_16 : witB 17 2 16
    [6, 15, 1, 4, 11, 14, 8, 12, 7, 13, 3, 17, 5, 10, 9] = true := by
  decide +kernel

theorem wit_17_3_12 : witB 17 3 12
    [6, 16, 11, 8, 9, 14, 10, 15, 2, 13, 17, 4, 1, 5, 7] = true := by
  decide +kernel

theorem wit_17_3_14 : witB 17 3 14
    [4, 11, 6, 5, 16, 13, 15, 8, 7, 12, 9, 2, 1, 17, 10] = true := by
  decide +kernel

theorem wit_18_2_17 : witB 18 2 17
    [6, 16, 3, 12, 10, 4, 15, 13, 18, 14, 7, 5, 8, 1, 11, 9] = true := by
  decide +kernel

theorem wit_19_3_16 : witB 19 3 16
    [10, 4, 6, 15, 8, 14, 13, 2, 9, 1, 19, 12, 17, 18, 5, 7, 11] = true := by
  decide +kernel

theorem wit_21_2_19 : witB 21 2 19
    [3, 17, 11, 16, 12, 13, 20, 6, 5, 14, 1, 21, 8, 4, 9, 7, 18, 15, 10] = true := by
  decide +kernel

theorem wit_23_2_21 : witB 23 2 21
    [15, 20, 4, 19, 8, 6, 13, 10, 1, 18, 16, 17, 3, 9, 12, 14, 22, 23, 5, 7, 11] = true := by
  decide +kernel

theorem wit_23_3_18 : witB 23 3 18
    [16, 8, 14, 4, 5, 21, 11, 19, 6, 23, 17, 20, 9, 7, 13, 2, 12, 22, 15, 1, 10] = true := by
  decide +kernel

theorem wit_23_5_16 : witB 23 5 16
    [20, 7, 3, 15, 11, 19, 4, 6, 14, 10, 18, 17, 8, 9, 22, 1, 23, 2, 13, 21, 12] = true := by
  decide +kernel

theorem wit_23_6_17 : witB 23 6 17
    [18, 5, 10, 16, 8, 15, 14, 21, 20, 2, 7, 9, 12, 13, 23, 1, 19, 22, 4, 3, 11] = true := by
  decide +kernel

theorem wit_25_2_23 : witB 25 2 23
    [22, 7, 16, 10, 19, 11, 14, 21, 20, 1, 17, 5, 3, 4, 9, 18, 13, 15, 24, 25, 6, 8, 12] = true := by
  decide +kernel

theorem wit_27_2_25 : witB 27 2 25
    [12, 20, 3, 17, 7, 16, 24, 26, 5, 9, 11, 27, 8, 1, 21, 4, 6, 22, 23, 15, 14, 18, 19, 10, 13] = true := by
  decide +kernel

theorem wit_28_5_18 : witB 28 5 18
    [12, 22, 20, 3, 7, 17, 9, 19, 14, 16, 15, 4, 6, 8, 10, 11, 27, 25, 24, 13, 1, 23, 28, 21, 26, 2] = true := by
  decide +kernel

theorem wit_29_3_20 : witB 29 3 20
    [10, 4, 22, 19, 7, 18, 16, 5, 14, 6, 12, 11, 8, 26, 29, 24, 21, 27, 2, 28, 17, 23, 25, 1, 13, 9, 15] = true := by
  decide +kernel

theorem wit_29_3_24 : witB 29 3 24
    [10, 4, 21, 19, 12, 17, 16, 6, 14, 5, 26, 8, 7, 25, 11, 28, 2, 9, 1, 23, 29, 20, 22, 27, 15, 18, 13] = true := by
  decide +kernel

theorem wit_29_3_26 : witB 29 3 26
    [12, 5, 25, 20, 17, 8, 9, 24, 15, 10, 14, 23, 28, 21, 2, 27, 4, 18, 19, 6, 7, 11, 13, 29, 22, 1, 16] = true := by
  decide +kernel

theorem wit_29_5_22 : witB 29 5 22
    [8, 24, 13, 19, 23, 21, 3, 6, 11, 27, 29, 4, 26, 7, 25, 14, 16, 10, 9, 18, 15, 1, 20, 2, 17, 12, 28] = true := by
  decide +kernel

theorem wit_31_3_28 : witB 31 3 28
    [11, 23, 21, 5, 7, 19, 29, 12, 18, 9, 16, 13, 15, 27, 26, 25, 2, 1, 4, 8, 24, 14, 31, 30, 6, 20, 22, 10, 17] = true := by
  decide +kernel

theorem wit_31_5_24 : witB 31 5 24
    [6, 22, 18, 11, 17, 3, 9, 27, 15, 12, 4, 25, 7, 8, 30, 29, 28, 20, 23, 19, 21, 10, 13, 14, 16, 1, 26, 31, 2] = true := by
  decide +kernel

theorem wit_32_3_26 : witB 32 3 26
    [10, 25, 5, 21, 18, 7, 29, 22, 12, 11, 16, 13, 15, 28, 27, 24, 17, 31, 23, 2, 1, 19, 20, 4, 32, 8, 6, 30, 9, 14] = true := by
  decide +kernel

theorem wit_32_3_30 : witB 32 3 30
    [20, 8, 13, 29, 15, 14, 4, 26, 5, 28, 23, 7, 31, 6, 12, 11, 10, 22, 2, 32, 21, 19, 24, 9, 27, 25, 17, 18, 1, 16] = true := by
  decide +kernel

theorem wit_32_5_22 : witB 32 5 22
    [14, 6, 26, 21, 9, 11, 10, 24, 23, 20, 3, 19, 16, 18, 17, 4, 7, 8, 12, 13, 31, 29, 28, 15, 1, 27, 32, 25, 30, 2] = true := by
  decide +kernel

theorem wit_32_5_28 : witB 32 5 28
    [13, 29, 6, 22, 19, 27, 23, 7, 11, 26, 8, 12, 25, 9, 20, 24, 10, 14, 15, 32, 21, 16, 3, 18, 17, 1, 4, 30, 31, 2] = true := by
  decide +kernel

theorem wit_35_3_32 : witB 35 3 32
    [23, 7, 12, 31, 21, 29, 25, 8, 13, 9, 24, 15, 2, 22, 16, 20, 17, 35, 4, 30, 33, 28, 34, 10, 1, 26, 5, 27, 6, 14, 18, 11, 19] = true := by
  decide +kernel

theorem wit_37_3_32 : witB 37 3 32
    [29, 34, 8, 30, 15, 36, 31, 14, 4, 11, 20, 37, 5, 21, 12, 6, 7, 24, 19, 25, 13, 26, 18, 28, 9, 16, 27, 23, 2, 33, 1, 10, 35, 22, 17] = true := by
  decide +kernel

theorem wit_37_5_30 : witB 37 5 30
    [15, 29, 22, 7, 8, 12, 27, 9, 25, 24, 34, 13, 23, 11, 21, 37, 17, 1, 16, 20, 35, 31, 32, 33, 4, 3, 2, 28, 36, 14, 18, 6, 10, 26, 19] = true := by
  decide +kernel

theorem wit_41_3_32 : witB 41 3 32
    [4, 27, 14, 13, 7, 37, 34, 24, 29, 12, 19, 36, 20, 5, 18, 31, 28, 26, 22, 25, 9, 23, 6, 8, 11, 10, 15, 17, 41, 35, 39, 33, 2, 16, 40, 38, 1, 30, 21] = true := by
  decide +kernel

theorem wit_41_3_36 : witB 41 3 36
    [11, 31, 25, 14, 24, 4, 6, 37, 34, 27, 13, 28, 5, 26, 9, 7, 22, 23, 17, 8, 21, 15, 40, 16, 10, 12, 35, 2, 41, 1, 33, 38, 32, 39, 20, 29, 30, 18, 19] = true := by
  decide +kernel

theorem wit_43_3_34 : witB 43 3 34
    [39, 13, 25, 14, 4, 7, 30, 11, 36, 32, 21, 19, 17, 29, 20, 38, 37, 33, 35, 5, 15, 27, 28, 6, 23, 24, 26, 8, 9, 10, 12, 16, 42, 41, 43, 18, 40, 2, 1, 31, 22] = true := by
  decide +kernel

theorem wit_43_3_38 : witB 43 3 38
    [24, 8, 23, 12, 21, 34, 39, 37, 32, 4, 5, 26, 35, 15, 42, 36, 17, 16, 7, 9, 11, 29, 14, 41, 22, 28, 30, 18, 33, 2, 27, 25, 40, 1, 31, 6, 43, 13, 10, 19, 20] = true := by
  decide +kernel

theorem wit_47_3_42 : witB 47 3 42
    [33, 8, 21, 43, 23, 11, 16, 39, 17, 32, 18, 20, 41, 19, 35, 38, 31, 37, 25, 28, 26, 46, 4, 2, 30, 29, 9, 1, 47, 44, 7, 45, 34, 5, 6, 14, 13, 15, 40, 10, 24, 12, 36, 27, 22] = true := by
  decide +kernel

theorem wit_47_5_40 : witB 47 5 40
    [28, 14, 41, 6, 10, 37, 29, 32, 18, 11, 22, 12, 17, 46, 36, 27, 3, 4, 7, 35, 26, 44, 42, 21, 19, 8, 34, 15, 47, 39, 25, 16, 38, 20, 43, 31, 30, 1, 2, 45, 23, 9, 13, 33, 24] = true := by
  decide +kernel

theorem wit_49_3_44 : witB 49 3 44
    [16, 33, 30, 7, 13, 29, 20, 46, 27, 8, 41, 43, 39, 38, 34, 9, 15, 10, 31, 32, 17, 19, 21, 2, 48, 24, 42, 47, 40, 35, 4, 1, 14, 5, 36, 6, 25, 22, 12, 45, 11, 37, 26, 28, 18, 49, 23] = true := by
  decide +kernel

theorem wit_53_3_48 : witB 53 3 48
    [12, 39, 29, 38, 19, 36, 37, 5, 9, 49, 46, 11, 20, 24, 47, 45, 44, 22, 14, 16, 41, 31, 43, 42, 17, 21, 18, 23, 33, 30, 35, 34, 52, 51, 2, 1, 7, 8, 4, 40, 15, 6, 50, 26, 27, 53, 10, 13, 28, 32, 25] = true := by
  decide +kernel

theorem wit_53_5_46 : witB 53 5 46
    [8, 35, 23, 15, 48, 19, 43, 17, 47, 33, 28, 4, 32, 44, 6, 45, 37, 40, 42, 16, 9, 7, 14, 10, 30, 12, 41, 11, 31, 38, 22, 39, 21, 13, 34, 36, 20, 29, 18, 24, 25, 51, 53, 26, 27, 52, 1, 3, 2, 49, 50] = true := by
  decide +kernel

theorem wit_59_5_52 : witB 59 5 52
    [19, 49, 29, 41, 55, 20, 35, 54, 37, 50, 9, 42, 10, 11, 23, 51, 13, 43, 17, 46, 14, 15, 26, 16, 28, 48, 47, 36, 22, 18, 25, 39, 24, 40, 27, 4, 45, 44, 38, 34, 30, 33, 58, 2, 3, 1, 31, 59, 7, 56, 6, 8, 12, 53, 21, 57, 32] = true := by
  decide +kernel

theorem wit_61_3_52 : witB 61 3 52
    [29, 49, 41, 9, 30, 46, 33, 38, 34, 15, 11, 17, 32, 13, 19, 14, 21, 20, 28, 24, 57, 25, 54, 48, 56, 55, 4, 45, 53, 51, 22, 5, 42, 26, 50, 43, 6, 40, 39, 37, 7, 36, 35, 2, 8, 60, 16, 10, 12, 27, 18, 23, 59, 61, 58, 1, 47, 44, 31] = true := by
  decide +kernel

theorem wit_61_5_54 : witB 61 5 54
    [25, 10, 49, 14, 41, 23, 17, 48, 39, 45, 35, 18, 24, 44, 38, 36, 3, 19, 27, 34, 28, 33, 31, 6, 4, 9, 8, 7, 26, 58, 55, 13, 15, 16, 60, 53, 52, 57, 50, 21, 1, 51, 11, 46, 47, 40, 61, 56, 30, 29, 59, 22, 2, 42, 12, 37, 43, 20, 32] = true := by
  decide +kernel

theorem wit_64_3_62 : witB 64 3 62
    [45, 10, 27, 40, 57, 53, 50, 19, 13, 16, 30, 41, 18, 48, 23, 46, 31, 4, 21, 43, 24, 39, 38, 35, 34, 61, 6, 60, 37, 58, 5, 9, 7, 59, 15, 8, 29, 25, 54, 26, 52, 28, 12, 11, 14, 20, 17, 2, 56, 55, 49, 51, 44, 42, 63, 36, 22, 47, 33, 1, 64, 32] = true := by
  decide +kernel

theorem wit_64_5_60 : witB 64 5 60
    [13, 40, 29, 54, 35, 17, 20, 23, 50, 26, 61, 24, 59, 6, 7, 10, 8, 55, 58, 39, 57, 9, 43, 41, 45, 15, 51, 30, 28, 56, 14, 11, 37, 12, 38, 47, 52, 44, 53, 46, 21, 25, 48, 16, 22, 27, 64, 49, 18, 19, 36, 31, 42, 32, 3, 34, 33, 1, 4, 62, 63, 2] = true := by
  decide +kernel

theorem wit_67_5_60 : witB 67 5 60
    [34, 56, 48, 14, 18, 27, 24, 26, 47, 63, 61, 7, 9, 12, 41, 22, 19, 54, 21, 62, 44, 49, 32, 51, 33, 43, 39, 38, 36, 3, 59, 4, 37, 6, 15, 28, 16, 30, 58, 1, 66, 57, 65, 52, 10, 45, 46, 17, 8, 11, 40, 29, 23, 13, 67, 25, 55, 20, 2, 53, 50, 64, 35, 42, 31] = true := by
  decide +kernel

theorem wit_71_5_64 : witB 71 5 64
    [39, 17, 33, 67, 18, 25, 53, 29, 56, 31, 63, 6, 49, 65, 34, 46, 35, 45, 38, 9, 60, 62, 58, 8, 61, 13, 15, 14, 48, 52, 59, 22, 50, 16, 40, 55, 51, 3, 24, 4, 7, 10, 27, 41, 21, 28, 70, 71, 11, 57, 30, 12, 32, 43, 23, 26, 68, 19, 1, 20, 47, 54, 2, 44, 66, 42, 37, 69, 36] = true := by
  decide +kernel

theorem wit_73_3_64 : witB 73 3 64
    [53, 10, 34, 47, 22, 44, 14, 21, 29, 24, 65, 27, 70, 52, 28, 51, 68, 43, 36, 61, 39, 67, 62, 50, 46, 59, 63, 57, 4, 60, 6, 12, 11, 15, 25, 16, 18, 19, 58, 20, 37, 54, 31, 55, 38, 23, 30, 26, 32, 35, 56, 49, 73, 48, 45, 42, 41, 5, 7, 40, 2, 8, 9, 1, 71, 69, 66, 13, 17, 33, 72] = true := by
  decide +kernel

theorem wit_83_3_74 : witB 83 3 74
    [23, 64, 39, 58, 51, 4, 40, 13, 7, 50, 29, 12, 77, 72, 22, 37, 76, 73, 66, 67, 69, 71, 26, 11, 19, 35, 47, 53, 27, 45, 70, 28, 59, 33, 30, 34, 36, 57, 68, 60, 61, 65, 14, 52, 5, 15, 41, 48, 16, 63, 43, 6, 82, 44, 80, 62, 55, 54, 2, 18, 56, 20, 1, 24, 79, 25, 9, 8, 78, 21, 32, 46, 49, 10, 42, 17, 83, 31, 75, 81, 38] = true := by
  decide +kernel

theorem wit_83_5_76 : witB 83 5 76
    [60, 28, 47, 10, 56, 17, 54, 75, 70, 58, 14, 16, 74, 35, 36, 26, 71, 68, 69, 19, 37, 20, 24, 59, 61, 67, 21, 33, 62, 66, 23, 31, 38, 65, 39, 50, 63, 4, 25, 45, 40, 29, 6, 53, 52, 55, 51, 8, 41, 7, 9, 49, 48, 1, 44, 43, 12, 11, 13, 15, 83, 79, 27, 78, 22, 18, 32, 77, 81, 82, 73, 34, 30, 80, 3, 2, 72, 57, 64, 46, 42] = true := by
  decide +kernel

theorem wit_101_5_94 : witB 101 5 94
    [36, 76, 63, 11, 72, 19, 49, 71, 30, 32, 67, 14, 42, 93, 20, 22, 87, 92, 27, 23, 26, 24, 86, 75, 61, 73, 25, 91, 47, 85, 59, 62, 39, 44, 46, 45, 29, 43, 31, 34, 41, 35, 37, 38, 90, 82, 89, 70, 84, 81, 80, 68, 40, 79, 66, 78, 48, 69, 65, 64, 60, 4, 51, 56, 52, 53, 100, 54, 97, 55, 99, 58, 57, 6, 8, 7, 96, 98, 12, 10, 95, 13, 88, 1, 9, 83, 16, 101, 17, 3, 18, 15, 21, 77, 74, 28, 2, 33, 50] = true := by
  decide +kernel

theorem wit_103_5_96 : witB 103 5 96
    [67, 33, 10, 87, 73, 68, 21, 12, 54, 20, 60, 39, 45, 14, 44, 86, 18, 100, 15, 95, 98, 61, 52, 17, 31, 88, 94, 37, 77, 36, 19, 32, 89, 66, 62, 81, 82, 34, 48, 65, 72, 76, 56, 23, 85, 40, 75, 57, 71, 22, 25, 24, 70, 59, 58, 28, 27, 26, 55, 29, 35, 38, 53, 42, 43, 50, 51, 97, 4, 102, 47, 6, 101, 46, 92, 90, 7, 99, 2, 80, 91, 79, 93, 103, 74, 3, 9, 78, 64, 8, 11, 69, 1, 84, 83, 13, 16, 41, 30, 63, 49] = true := by
  decide +kernel

theorem wit_128_3_126 : witB 128 3 126
    [71, 108, 119, 35, 50, 89, 75, 101, 76, 83, 116, 10, 88, 18, 30, 106, 39, 38, 13, 34, 17, 33, 65, 103, 99, 93, 15, 16, 79, 80, 23, 27, 24, 72, 69, 78, 52, 70, 45, 54, 57, 25, 62, 28, 4, 48, 29, 47, 44, 6, 125, 123, 114, 111, 124, 43, 102, 121, 32, 92, 87, 100, 63, 97, 122, 85, 59, 40, 113, 82, 36, 60, 51, 58, 112, 98, 95, 120, 66, 115, 5, 84, 8, 73, 118, 91, 7, 9, 14, 12, 96, 42, 11, 56, 90, 2, 31, 77, 61, 117, 21, 20, 74, 49, 109, 55, 53, 37, 107, 110, 127, 68, 94, 105, 19, 104, 22, 67, 26, 46, 86, 81, 1, 41, 64, 128] = true := by
  decide +kernel

theorem wit_128_5_124 : witB 128 5 124
    [31, 105, 57, 83, 103, 13, 46, 17, 90, 84, 49, 15, 55, 25, 42, 23, 80, 41, 119, 79, 76, 47, 116, 78, 114, 48, 107, 110, 68, 108, 95, 102, 82, 101, 18, 21, 91, 24, 37, 26, 28, 125, 87, 58, 29, 86, 43, 53, 67, 123, 89, 122, 85, 120, 113, 109, 92, 93, 94, 112, 100, 98, 32, 39, 33, 34, 36, 99, 50, 44, 51, 38, 52, 56, 54, 6, 71, 61, 97, 7, 70, 59, 60, 62, 81, 8, 63, 77, 75, 69, 9, 10, 66, 11, 64, 12, 14, 16, 3, 127, 121, 126, 128, 73, 1, 74, 72, 20, 115, 4, 111, 118, 27, 117, 22, 19, 35, 30, 40, 45, 104, 96, 106, 88, 2, 65] = true := by
  decide +kernel

theorem coReach_coreList {N u v : Nat} (h : (N, u, v) ∈ coreList) : CoReach N {u, v} := by
  simp only [coreList, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact coReach_of_witB wit_13_2_11
  · exact coReach_of_witB wit_15_1_14
  · exact coReach_of_witB wit_15_2_13
  · exact coReach_of_witB wit_16_1_15
  · exact coReach_of_witB wit_16_2_15
  · exact coReach_of_witB wit_16_3_14
  · exact coReach_of_witB wit_16_5_12
  · exact coReach_of_witB wit_17_1_16
  · exact coReach_of_witB wit_17_2_16
  · exact coReach_of_witB wit_17_3_12
  · exact coReach_of_witB wit_17_3_14
  · exact coReach_of_witB wit_18_2_17
  · exact coReach_of_witB wit_19_3_16
  · exact coReach_of_witB wit_21_2_19
  · exact coReach_of_witB wit_23_2_21
  · exact coReach_of_witB wit_23_3_18
  · exact coReach_of_witB wit_23_5_16
  · exact coReach_of_witB wit_23_6_17
  · exact coReach_of_witB wit_25_2_23
  · exact coReach_of_witB wit_27_2_25
  · exact coReach_of_witB wit_28_5_18
  · exact coReach_of_witB wit_29_3_20
  · exact coReach_of_witB wit_29_3_24
  · exact coReach_of_witB wit_29_3_26
  · exact coReach_of_witB wit_29_5_22
  · exact coReach_of_witB wit_31_3_28
  · exact coReach_of_witB wit_31_5_24
  · exact coReach_of_witB wit_32_3_26
  · exact coReach_of_witB wit_32_3_30
  · exact coReach_of_witB wit_32_5_22
  · exact coReach_of_witB wit_32_5_28
  · exact coReach_of_witB wit_35_3_32
  · exact coReach_of_witB wit_37_3_32
  · exact coReach_of_witB wit_37_5_30
  · exact coReach_of_witB wit_41_3_32
  · exact coReach_of_witB wit_41_3_36
  · exact coReach_of_witB wit_43_3_34
  · exact coReach_of_witB wit_43_3_38
  · exact coReach_of_witB wit_47_3_42
  · exact coReach_of_witB wit_47_5_40
  · exact coReach_of_witB wit_49_3_44
  · exact coReach_of_witB wit_53_3_48
  · exact coReach_of_witB wit_53_5_46
  · exact coReach_of_witB wit_59_5_52
  · exact coReach_of_witB wit_61_3_52
  · exact coReach_of_witB wit_61_5_54
  · exact coReach_of_witB wit_64_3_62
  · exact coReach_of_witB wit_64_5_60
  · exact coReach_of_witB wit_67_5_60
  · exact coReach_of_witB wit_71_5_64
  · exact coReach_of_witB wit_73_3_64
  · exact coReach_of_witB wit_83_3_74
  · exact coReach_of_witB wit_83_5_76
  · exact coReach_of_witB wit_101_5_94
  · exact coReach_of_witB wit_103_5_96
  · exact coReach_of_witB wit_128_3_126
  · exact coReach_of_witB wit_128_5_124

-- END WITNESSES

end Live7
end Folds
