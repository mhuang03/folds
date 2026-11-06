import Folds.SuperExp2

/-!
# Upper slip positions with averaging: exponent `1/17` for all `N`

Notation of `Folds/SuperExp2.lean`.  For odd `n = 2h + 1` the restricted chain
(`mSum_chain`) only uses the slip positions `k ≤ h` of the slip sum `B(n)`.  For the upper odd
positions `k = 2i - 1` (`(h+3)/2 ≤ i ≤ h`) and odds-first inputs `τ = PB(α, β)`,
`σ = PB(α', β')`:

* `τ` places `2i - 1` before `qq n (2i-1) = 2·qq_{h+1}(i) - 1` iff `α` places `i` before
  `qq (h+1) i` (`qq_up`);
* `σ` places `pp n (2i-1) = 2·pp_h(i-1)` before `2i` iff `β'` places `pp h (i-1)` before `i`
  (`pp_up`).

`α` and `β'` are exactly the halves that the restricted chain leaves free, so
(`slipSum_odd_up`)

    B(2h+1) ≥ 2^{⌈h/2⌉} · W(h) · M(h, h+1, ⌊h/2⌋),
    W(h) = ∑_{U ⊆ I_h} #{α ∈ V_{h+1} : U-conditions} · #{β' ∈ V_h : U-conditions},

and reversal flips each of these order conditions, which gives by averaging over the four
reversals (`avg4`, `wSum_ge`)

    4 W(h) ≥ a(h+1) a(h) 2^{⌈⌊h/2⌋/4⌉}.

A new potential induction (`alln17_aux`) with the surplus of the even child used at the top
of the odd slip sums gives (`self_pow_le_semiCount_pow_17`)

    N^N ≤ 2^{11N} a(N)^{17}   for all N ≥ 1,   i.e.  a(N) ≥ (N/2048)^{N/17},

improving the exponent `1/22` of `self_pow_le_semiCount_pow_22`.
Paper proofs and checks: `experiments/superexp4/PROOFS.txt`.
-/

namespace Folds
namespace Slip
namespace Up

/-! ## Order conditions and reversal -/

/-- `b` does not come before `a` in `l`. -/
def NotBefore (l : List Nat) (a b : Nat) : Prop :=
  ∀ k (hk : k < l.length), l[k] = a → b ∉ l.take k

theorem notBefore_getElem {l : List Nat} (hnd : l.Nodup) {p q : Nat} (hp : p < l.length)
    (hq : q < l.length) : NotBefore l l[p] l[q] ↔ ¬ q < p := by
  constructor
  · intro h hqp
    exact h p hp rfl ((getElem_mem_take_iff hnd hq).2 hqp)
  · intro h k hk e hm
    have : k = p := (List.Nodup.getElem_inj_iff hnd).1 e
    subst this
    exact h ((getElem_mem_take_iff hnd hq).1 hm)

/-- Reversal flips the order of two distinct members. -/
theorem notBefore_reverse {l : List Nat} (hnd : l.Nodup) {a b : Nat} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : NotBefore l.reverse a b ↔ ¬ NotBefore l a b := by
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 ha
  obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.1 hb
  have hpq : p ≠ q := fun e => hab (by subst e; rfl)
  have hnd' : l.reverse.Nodup := List.nodup_reverse.2 hnd
  have hp' : l.length - 1 - p < l.reverse.length := by simp; omega
  have hq' : l.length - 1 - q < l.reverse.length := by simp; omega
  have ep : l.reverse[l.length - 1 - p] = l[p] := by
    rw [List.getElem_reverse]; congr 1; omega
  have eq : l.reverse[l.length - 1 - q] = l[q] := by
    rw [List.getElem_reverse]; congr 1; omega
  rw [← ep, ← eq, notBefore_getElem hnd' hp' hq', ep, eq, notBefore_getElem hnd hp hq]
  omega

/-! ## Averaging over four reversals -/

theorem sum_pow_ge {t a b c d : Nat} (h : a + b + c + d = t) :
    2 ^ ((t + 3) / 4) ≤ 2 ^ a + 2 ^ b + 2 ^ c + 2 ^ d := by
  have z := fun x : Nat => Nat.zero_le (2 ^ x)
  by_cases h1 : (t + 3) / 4 ≤ a
  · exact le_trans (Nat.pow_le_pow_right (by norm_num) h1) (by linarith [z b, z c, z d])
  by_cases h2 : (t + 3) / 4 ≤ b
  · exact le_trans (Nat.pow_le_pow_right (by norm_num) h2) (by linarith [z a, z c, z d])
  by_cases h3 : (t + 3) / 4 ≤ c
  · exact le_trans (Nat.pow_le_pow_right (by norm_num) h3) (by linarith [z a, z b, z d])
  by_cases h4 : (t + 3) / 4 ≤ d
  · exact le_trans (Nat.pow_le_pow_right (by norm_num) h4) (by linarith [z a, z b, z c])
  omega

/-- **Averaging.**  If `r` and `r'` are involutions of `S` and `T` that flip the conditions
`P · i`, `Q · i` for `i ∈ I`, then
`|S| |T| 2^{⌈|I|/4⌉} ≤ 4 ∑_{U ⊆ I} #{x ∈ S : P x on U} · #{y ∈ T : Q y on U}`. -/
theorem avg4 {α β : Type*} (S : Finset α) (T : Finset β) (I : Finset Nat)
    (P : α → Nat → Prop) (Q : β → Nat → Prop) [∀ x i, Decidable (P x i)]
    [∀ y i, Decidable (Q y i)] (r : α → α) (r' : β → β)
    (hr : ∀ x ∈ S, r x ∈ S) (hrr : ∀ x ∈ S, r (r x) = x)
    (hr' : ∀ y ∈ T, r' y ∈ T) (hrr' : ∀ y ∈ T, r' (r' y) = y)
    (hP : ∀ x ∈ S, ∀ i ∈ I, P (r x) i ↔ ¬ P x i)
    (hQ : ∀ y ∈ T, ∀ i ∈ I, Q (r' y) i ↔ ¬ Q y i) :
    S.card * T.card * 2 ^ ((I.card + 3) / 4) ≤
      4 * ∑ U ∈ I.powerset, (S.filter fun x => ∀ i ∈ U, P x i).card *
        (T.filter fun y => ∀ i ∈ U, Q y i).card := by
  classical
  -- the sum as a sum over pairs
  set c : α → β → Nat := fun x y => (I.filter fun i => P x i ∧ Q y i).card with hc
  have key : ∑ U ∈ I.powerset, (S.filter fun x => ∀ i ∈ U, P x i).card *
      (T.filter fun y => ∀ i ∈ U, Q y i).card = ∑ x ∈ S, ∑ y ∈ T, 2 ^ c x y := by
    simp only [Finset.card_filter, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e : ∀ U ∈ I.powerset, ((if ∀ i ∈ U, P x i then 1 else 0) *
        (if ∀ i ∈ U, Q y i then 1 else 0) : Nat) =
        if U ⊆ I.filter (fun i => P x i ∧ Q y i) then 1 else 0 := by
      intro U hU
      rw [Finset.mem_powerset] at hU
      rw [ite_zero_mul_ite_zero, Nat.one_mul]
      refine if_congr ⟨fun h i hi => Finset.mem_filter.2 ⟨hU hi, h.1 i hi, h.2 i hi⟩,
        fun h => ⟨fun i hi => (Finset.mem_filter.1 (h hi)).2.1,
          fun i hi => (Finset.mem_filter.1 (h hi)).2.2⟩⟩ rfl rfl
    rw [Finset.sum_congr rfl e, ← Finset.card_filter]
    rw [show I.powerset.filter (· ⊆ I.filter fun i => P x i ∧ Q y i) =
        (I.filter fun i => P x i ∧ Q y i).powerset by
      ext U; simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun h => h.2, fun h => ⟨h.trans (Finset.filter_subset _ _), h⟩⟩,
      Finset.card_powerset]
  rw [key]
  -- the four reversals
  have s1 : ∑ x ∈ S, ∑ y ∈ T, 2 ^ c (r x) y = ∑ x ∈ S, ∑ y ∈ T, 2 ^ c x y :=
    Finset.sum_nbij' r r hr hr hrr hrr (fun _ _ => rfl)
  have s2 : ∑ x ∈ S, ∑ y ∈ T, 2 ^ c x (r' y) = ∑ x ∈ S, ∑ y ∈ T, 2 ^ c x y :=
    Finset.sum_congr rfl fun x _ =>
      Finset.sum_nbij' r' r' hr' hr' hrr' hrr' (fun _ _ => rfl)
  have s3 : ∑ x ∈ S, ∑ y ∈ T, 2 ^ c (r x) (r' y) = ∑ x ∈ S, ∑ y ∈ T, 2 ^ c x y := by
    rw [← s1]
    exact Finset.sum_congr rfl fun x _ =>
      Finset.sum_nbij' r' r' hr' hr' hrr' hrr' (fun _ _ => rfl)
  have pt : ∀ x ∈ S, ∀ y ∈ T, 2 ^ ((I.card + 3) / 4) ≤
      2 ^ c x y + 2 ^ c (r x) y + 2 ^ c x (r' y) + 2 ^ c (r x) (r' y) := by
    intro x hx y hy
    apply sum_pow_ge
    have f0 : c x y = (I.filter fun i => P x i ∧ Q y i).card := rfl
    have f1 : c (r x) y = (I.filter fun i => ¬ P x i ∧ Q y i).card := by
      show (I.filter fun i => P (r x) i ∧ Q y i).card = _; congr 1; exact Finset.filter_congr fun i hi => by rw [hP x hx i hi]
    have f2 : c x (r' y) = (I.filter fun i => P x i ∧ ¬ Q y i).card := by
      show (I.filter fun i => P x i ∧ Q (r' y) i).card = _; congr 1; exact Finset.filter_congr fun i hi => by rw [hQ y hy i hi]
    have f3 : c (r x) (r' y) = (I.filter fun i => ¬ P x i ∧ ¬ Q y i).card := by
      show (I.filter fun i => P (r x) i ∧ Q (r' y) i).card = _; congr 1; exact Finset.filter_congr fun i hi => by rw [hP x hx i hi, hQ y hy i hi]
    rw [f0, f1, f2, f3]
    have a1 := Finset.card_filter_add_card_filter_not (s := I) (fun i => P x i)
    have a2 := Finset.card_filter_add_card_filter_not (s := I.filter fun i => P x i)
      (fun i => Q y i)
    have a3 := Finset.card_filter_add_card_filter_not
      (s := I.filter fun i => ¬ P x i) (fun i => Q y i)
    simp only [Finset.filter_filter] at a2 a3
    omega
  have := Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => pt x hx y hy
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Finset.sum_add_distrib] at this
  rw [s1, s2, s3] at this
  calc S.card * T.card * 2 ^ ((I.card + 3) / 4) = S.card * (T.card * 2 ^ ((I.card + 3) / 4)) :=
        by ring
    _ ≤ _ := this
    _ = _ := by ring


/-! ## The upper slip positions of `B(2h+1)` -/

/-- The upper indices `I_h = [(h+3)/2, h]`, i.e. `h + 2 ≤ 2i ≤ 2h`. -/
def iset (h : Nat) : Finset Nat := Finset.Icc ((h + 3) / 2) h

theorem card_iset (h : Nat) : (iset h).card = h / 2 := by
  unfold iset; rw [Nat.card_Icc]; omega

theorem mem_iset {h i : Nat} (hi : i ∈ iset h) : h + 2 ≤ 2 * i ∧ i ≤ h := by
  unfold iset at hi; rw [Finset.mem_Icc] at hi; omega

theorem qq_up' {h i : Nat} (h1 : h + 2 ≤ 2 * i) (h2 : i ≤ h) : qq (h + 1) i = 2 * i - h - 1 := by
  unfold qq
  rw [show 2 * i - 1 = (2 * i - h - 2) + (h + 1) by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem pp_up' {h i : Nat} (h1 : h + 2 ≤ 2 * i) (h2 : i ≤ h) : pp h (i - 1) = 2 * i - 1 - h := by
  unfold pp
  rw [show 2 * (i - 1) = (2 * i - 2 - h) + h by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- `qq (2h+1) (2i-1) = 2 qq(h+1, i) - 1` for upper `i`. -/
theorem qq_up {h i : Nat} (h1 : h + 2 ≤ 2 * i) (h2 : i ≤ h) :
    qq (2 * h + 1) (2 * i - 1) = 2 * qq (h + 1) i - 1 := by
  rw [qq_up' h1 h2]
  unfold qq
  rw [show 2 * (2 * i - 1) - 1 = (4 * i - 2 * h - 4) + (2 * h + 1) by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- `pp (2h+1) (2i-1) = 2 pp(h, i-1)` for upper `i`. -/
theorem pp_up {h i : Nat} (h1 : h + 2 ≤ 2 * i) (h2 : i ≤ h) :
    pp (2 * h + 1) (2 * i - 1) = 2 * pp h (i - 1) := by
  rw [pp_up' h1 h2]
  unfold pp
  rw [show 2 * (2 * i - 1) = (4 * i - 2 * h - 3) + (2 * h + 1) by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- The first-block condition at an upper index: `α` places `i` before `qq (h+1) i`. -/
def upF (h : Nat) (α : List Nat) (i : Nat) : Prop := NotBefore α i (qq (h + 1) i)

/-- The second-block condition at an upper index: `β` places `pp h (i-1)` before `i`. -/
def upS (h : Nat) (β : List Nat) (i : Nat) : Prop := ¬ NotBefore β i (pp h (i - 1))

open Classical in
/-- `W(h) = ∑_{U ⊆ I_h} #{α ∈ V_{h+1} : upF on U} · #{β ∈ V_h : upS on U}`. -/
noncomputable def wSum (h : Nat) : Nat :=
  ∑ U ∈ (iset h).powerset, ((semiSeqs (h + 1)).filter fun α => ∀ i ∈ U, upF h α i).card *
    ((semiSeqs h).filter fun β => ∀ i ∈ U, upS h β i).card

theorem reverse_mem_semiSeqs {n : Nat} {x : List Nat} (hx : x ∈ semiSeqs n) :
    x.reverse ∈ semiSeqs n := by
  rw [mem_semiSeqs] at hx ⊢
  exact ⟨(List.reverse_perm _).trans hx.1, hx.2.reverse hx.1⟩

/-- **Averaging** for the upper positions: `4 W(h) ≥ a(h+1) a(h) 2^{⌈⌊h/2⌋/4⌉}`. -/
theorem wSum_ge (h : Nat) :
    semiCount (h + 1) * semiCount h * 2 ^ ((h / 2 + 3) / 4) ≤ 4 * wSum h := by
  classical
  have := avg4 (semiSeqs (h + 1)) (semiSeqs h) (iset h) (upF h) (upS h) List.reverse List.reverse
    (fun x hx => reverse_mem_semiSeqs hx) (fun x _ => List.reverse_reverse x)
    (fun x hx => reverse_mem_semiSeqs hx) (fun x _ => List.reverse_reverse x) ?_ ?_
  · rw [card_iset] at this
    unfold semiCount wSum
    convert this using 4
  · intro x hx i hi
    have hb := mem_iset hi
    have hf := (mem_semiSeqs.1 hx).1
    unfold upF
    rw [qq_up' hb.1 hb.2]
    exact notBefore_reverse (nodup_of_foldSeq hf) ((mem_range'_of_perm hf).2 (by omega))
      ((mem_range'_of_perm hf).2 (by omega)) (by omega)
  · intro x hx i hi
    have hb := mem_iset hi
    have hf := (mem_semiSeqs.1 hx).1
    unfold upS
    rw [pp_up' hb.1 hb.2, notBefore_reverse (nodup_of_foldSeq hf)
      ((mem_range'_of_perm hf).2 (by omega)) ((mem_range'_of_perm hf).2 (by omega)) (by omega)]

/-- First block with upper slips: `PB(α, β) ∈ condF(2h+1, E ∪ 2D' ∪ (2U - 1))`. -/
theorem blockMap_mem_condF_up {h : Nat} {E D' U : Finset Nat} (hE : E ⊆ oddR h)
    (hD' : D' ⊆ Finset.Icc 1 (h / 2)) (hU : U ⊆ iset h) {α β : List Nat}
    (hα : α ∈ semiSeqs (h + 1)) (hαU : ∀ i ∈ U, upF h α i) (hβ : β ∈ condF h D') :
    blockMap 1 (α, β) ∈ condF (2 * h + 1) (dbl (E, D') ∪ U.image fun i => 2 * i - 1) := by
  have hβs : β ∈ semiSeqs h := (Finset.mem_filter.1 hβ).1
  have hβc := (Finset.mem_filter.1 hβ).2
  have hαf := (mem_semiSeqs.1 hα).1
  have hβf := (mem_semiSeqs.1 hβs).1
  have hE1 : ∀ z ∈ E, z % 2 = 1 := fun z hz => (mem_oddR (hE hz)).1
  unfold condF
  rw [Finset.mem_filter]
  refine ⟨blockMap_mem_gen (x := 2 * h + 1) (by rwa [show (2 * h + 1 + 1) / 2 = h + 1 by omega])
    (by rwa [show (2 * h + 1) / 2 = h by omega]), ?_⟩
  rw [blockMap_eq]
  intro k hk hd
  have hxD : (α.map (scale 1) ++ β.map (scale 0))[k] ∈
      dbl (E, D') ∪ U.image fun i => 2 * i - 1 := by
    unfold ind at hd; split at hd
    · assumption
    · omega
  rcases Nat.lt_or_ge k α.length with hkA | hkA
  · have hkA' : k < (α.map (scale 1)).length := by simpa using hkA
    have hi1 : 1 ≤ α[k] := ((mem_range'_of_perm hαf).1 (List.getElem_mem _)).1
    have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * α[k] - 1 := by
      rw [List.getElem_append_left hkA']; simp [scale]
    rw [e] at hxD ⊢
    rcases Finset.mem_union.1 hxD with hx | hx
    · have hsub := dbl_sub' (r := h) hE hD' hx
      rw [Finset.mem_Icc] at hsub
      rw [qq_small (by omega) (by omega)]
      intro hmem
      rw [List.take_append_of_le_length hkA'.le] at hmem
      have := mem_map_scale_one_odd hαf (List.mem_of_mem_take hmem)
      omega
    · obtain ⟨i, hiU, hi⟩ := Finset.mem_image.1 hx
      have hb := mem_iset (hU hiU)
      have hik : α[k] = i := by omega
      rw [show 2 * α[k] - 1 = 2 * i - 1 by omega, qq_up hb.1 hb.2]
      intro hmem
      rw [List.take_append_of_le_length hkA'.le, ← List.map_take] at hmem
      obtain ⟨z, hz, hz2⟩ := List.mem_map.1 hmem
      have hz1 : 1 ≤ z := ((mem_range'_of_perm hαf).1 (List.mem_of_mem_take hz)).1
      have hq1 : 1 ≤ qq (h + 1) i := by unfold qq; omega
      unfold scale at hz2
      have hzq : z = qq (h + 1) i := by omega
      exact hαU i hiU k hkA hik (hzq ▸ hz)
  · have hkA' : (α.map (scale 1)).length ≤ k := by simpa using hkA
    have hβl : k - α.length < β.length := by simp at hk; omega
    have hi1 : 1 ≤ β[k - α.length] := ((mem_range'_of_perm hβf).1 (List.getElem_mem _)).1
    have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * β[k - α.length] := by
      rw [List.getElem_append_right hkA']; simp [scale]
    rw [e] at hxD ⊢
    have hiD : β[k - α.length] ∈ D' := by
      rcases Finset.mem_union.1 hxD with hx | hx
      · rcases (mem_dbl' (p := (E, D')) hE1).1 hx with ⟨h1, -⟩ | ⟨-, h2⟩
        · omega
        · simpa using h2
      · obtain ⟨i, hiU, hi⟩ := Finset.mem_image.1 hx
        have hb := mem_iset (hU hiU)
        omega
    have hir := Finset.mem_Icc.1 (hD' hiD)
    have hcond := hβc (k - α.length) hβl
      (by unfold ind; rw [ite_eq_left_iff.2 (fun hh => absurd hiD hh)])
    rw [qq_small (by omega) (by omega),
      show 2 * (2 * β[k - α.length]) = 2 * qq h β[k - α.length] by
        rw [qq_small hi1 (by omega)]]
    intro hmem
    rw [List.take_append, List.take_of_length_le hkA'] at hmem
    rcases List.mem_append.1 hmem with hm | hm
    · have := mem_map_scale_one_odd hαf hm; omega
    · rw [List.length_map, ← List.map_take] at hm
      obtain ⟨z, hz, hz2⟩ := List.mem_map.1 hm
      unfold scale at hz2
      have : z = qq h β[k - α.length] := by omega
      exact hcond (this ▸ hz)

/-- Second block with upper slips: `PB(α', β') ∈ condS(2h+1, E ∪ 2D' ∪ (2U - 1))`. -/
theorem blockMap_mem_condS_up {h : Nat} {E D' U : Finset Nat} (hE : E ⊆ oddR h)
    (hD' : D' ⊆ Finset.Icc 1 (h / 2)) (hU : U ⊆ iset h) {α β : List Nat}
    (hα : α ∈ condS (h + 1) D') (hβ : β ∈ semiSeqs h) (hβU : ∀ i ∈ U, upS h β i) :
    blockMap 1 (α, β) ∈ condS (2 * h + 1) (dbl (E, D') ∪ U.image fun i => 2 * i - 1) := by
  have hαs : α ∈ semiSeqs (h + 1) := (Finset.mem_filter.1 hα).1
  have hαc := (Finset.mem_filter.1 hα).2
  have hαf := (mem_semiSeqs.1 hαs).1
  have hβf := (mem_semiSeqs.1 hβ).1
  have hE1 : ∀ z ∈ E, z % 2 = 1 := fun z hz => (mem_oddR (hE hz)).1
  unfold condS
  rw [Finset.mem_filter]
  refine ⟨blockMap_mem_gen (x := 2 * h + 1) (by rwa [show (2 * h + 1 + 1) / 2 = h + 1 by omega])
    (by rwa [show (2 * h + 1) / 2 = h by omega]), ?_⟩
  rw [blockMap_eq]
  intro k hk hd
  have hxD : (α.map (scale 1) ++ β.map (scale 0))[k] - 1 ∈
      dbl (E, D') ∪ U.image fun i => 2 * i - 1 := by
    unfold ind at hd; split at hd
    · assumption
    · omega
  rcases Nat.lt_or_ge k α.length with hkA | hkA
  · have hkA' : k < (α.map (scale 1)).length := by simpa using hkA
    have hi1 : 1 ≤ α[k] := ((mem_range'_of_perm hαf).1 (List.getElem_mem _)).1
    have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * α[k] - 1 := by
      rw [List.getElem_append_left hkA']; simp [scale]
    rw [e] at hxD ⊢
    have hiD : α[k] - 1 ∈ D' := by
      rcases Finset.mem_union.1 hxD with hx | hx
      · rcases (mem_dbl' (p := (E, D')) hE1).1 hx with ⟨h1, -⟩ | ⟨-, h2⟩
        · omega
        · rwa [show (2 * α[k] - 1 - 1) / 2 = α[k] - 1 by omega] at h2
      · obtain ⟨i, hiU, hi⟩ := Finset.mem_image.1 hx
        have hb := mem_iset (hU hiU)
        omega
    have hir := Finset.mem_Icc.1 (hD' hiD)
    have hcond := hαc k hkA (by unfold ind; rw [ite_eq_left_iff.2 (fun hh => absurd hiD hh)])
    rw [show 2 * α[k] - 1 - 1 = 2 * (α[k] - 1) by omega, pp_small (by omega),
      show 2 * (2 * (α[k] - 1)) + 1 = scale 1 (pp (h + 1) (α[k] - 1)) by
        rw [pp_small (by omega)]; unfold scale; omega,
      List.take_append_of_le_length hkA'.le, ← List.map_take]
    exact List.mem_map.2 ⟨_, hcond, rfl⟩
  · have hkA' : (α.map (scale 1)).length ≤ k := by simpa using hkA
    have hβl : k - α.length < β.length := by simp at hk; omega
    have hi1 : 1 ≤ β[k - α.length] := ((mem_range'_of_perm hβf).1 (List.getElem_mem _)).1
    have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * β[k - α.length] := by
      rw [List.getElem_append_right hkA']; simp [scale]
    rw [e] at hxD ⊢
    rcases Finset.mem_union.1 hxD with hx | hx
    · have hsub := dbl_sub' (r := h) hE hD' hx
      rw [Finset.mem_Icc] at hsub
      rw [pp_small (by omega)]
      have hmemA : 2 * (2 * β[k - α.length] - 1) + 1 ∈ α.map (scale 1) := by
        refine List.mem_map.2 ⟨2 * β[k - α.length],
          (mem_range'_of_perm hαf).2 ⟨by omega, by omega⟩, ?_⟩
        unfold scale; omega
      rw [List.take_append, List.take_of_length_le hkA']
      exact List.mem_append_left _ hmemA
    · obtain ⟨i, hiU, hi⟩ := Finset.mem_image.1 hx
      have hb := mem_iset (hU hiU)
      have hik : β[k - α.length] = i := by omega
      rw [show 2 * β[k - α.length] - 1 = 2 * i - 1 by omega, pp_up hb.1 hb.2]
      have hmem : pp h (i - 1) ∈ β.take (k - α.length) := by
        by_contra hn
        apply hβU i hiU
        intro k2 hk2 e2 hm2
        have : k2 = k - α.length :=
          (List.Nodup.getElem_inj_iff (nodup_of_foldSeq hβf)).1 (e2.trans hik.symm)
        subst this
        exact hn hm2
      rw [List.take_append, List.take_of_length_le hkA', List.length_map, ← List.map_take]
      refine List.mem_append_right _ (List.mem_map.2 ⟨_, hmem, ?_⟩)
      unfold scale; omega

open Classical in
/-- **Upper slips.**  `2^{⌈h/2⌉} · W(h) · M(h, h+1, ⌊h/2⌋) ≤ B(2h+1)`. -/
theorem slipSum_odd_up (h : Nat) :
    2 ^ ((h + 1) / 2) * (wSum h * mSum h (h + 1) (h / 2)) ≤ slipSum (2 * h + 1) := by
  set P := (oddR h).powerset ×ˢ ((Finset.Icc 1 (h / 2)).powerset ×ˢ (iset h).powerset) with hP
  set g : Finset Nat × (Finset Nat × Finset Nat) → Finset Nat :=
    fun p => dbl (p.1, p.2.1) ∪ p.2.2.image fun i => 2 * i - 1 with hg
  set f : Finset Nat → Nat :=
    fun D => (condF (2 * h + 1) D).card * (condS (2 * h + 1) D).card with hf
  have memP : ∀ p ∈ P, p.1 ⊆ oddR h ∧ p.2.1 ⊆ Finset.Icc 1 (h / 2) ∧ p.2.2 ⊆ iset h := by
    intro p hp
    rw [hP, Finset.mem_product, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset,
      Finset.mem_powerset] at hp
    exact ⟨hp.1, hp.2.1, hp.2.2⟩
  -- the two parts of `g p` are separated by `h`
  have split : ∀ p ∈ P, ∀ x, x ∈ g p ↔
      (x ≤ h ∧ x ∈ dbl (p.1, p.2.1)) ∨ (h < x ∧ ∃ i ∈ p.2.2, 2 * i - 1 = x) := by
    intro p hp x
    obtain ⟨h1, h2, h3⟩ := memP p hp
    rw [hg]
    simp only [Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (hx | ⟨i, hi, rfl⟩)
      · have := Finset.mem_Icc.1 (dbl_sub' h1 h2 hx); exact Or.inl ⟨this.2, hx⟩
      · have := mem_iset (h3 hi); exact Or.inr ⟨by omega, i, hi, rfl⟩
    · rintro (⟨-, hx⟩ | ⟨-, hx⟩)
      · exact Or.inl hx
      · exact Or.inr hx
  have hsub : P.image g ⊆ (Finset.Icc 1 (2 * h + 1 - 1)).powerset := by
    intro D hD
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hD
    obtain ⟨h1, h2, h3⟩ := memP p hp
    rw [Finset.mem_powerset]
    intro x hx
    rw [Finset.mem_Icc]
    rcases (split p hp x).1 hx with ⟨hxh, hx⟩ | ⟨-, i, hi, rfl⟩
    · have := Finset.mem_Icc.1 (dbl_sub' h1 h2 hx); omega
    · have := mem_iset (h3 hi); omega
  have hinj : Set.InjOn g P := by
    intro p hp p' hp' e
    have hp1 := memP p hp
    have hp1' := memP p' hp'
    have he : ∀ x, x ∈ g p ↔ x ∈ g p' := fun x => by rw [e]
    have hd : dbl (p.1, p.2.1) = dbl (p'.1, p'.2.1) := by
      ext x
      constructor
      · intro hx
        have hxh := (Finset.mem_Icc.1 (dbl_sub' hp1.1 hp1.2.1 hx)).2
        rcases (split p' hp' x).1 ((he x).1 ((split p hp x).2 (Or.inl ⟨hxh, hx⟩))) with
          ⟨-, h'⟩ | ⟨hh, -⟩
        · exact h'
        · omega
      · intro hx
        have hxh := (Finset.mem_Icc.1 (dbl_sub' hp1'.1 hp1'.2.1 hx)).2
        rcases (split p hp x).1 ((he x).2 ((split p' hp' x).2 (Or.inl ⟨hxh, hx⟩))) with
          ⟨-, h'⟩ | ⟨hh, -⟩
        · exact h'
        · omega
    have hd' := dbl_injOn' (r := h)
      (show (p.1, p.2.1) ∈ ((((oddR h).powerset ×ˢ
            (Finset.Icc 1 (h / 2)).powerset : Finset _)) : Set _) by
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powerset]
        exact ⟨hp1.1, hp1.2.1⟩)
      (show (p'.1, p'.2.1) ∈ ((((oddR h).powerset ×ˢ
            (Finset.Icc 1 (h / 2)).powerset : Finset _)) : Set _) by
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powerset]
        exact ⟨hp1'.1, hp1'.2.1⟩) hd
    have hU : p.2.2 = p'.2.2 := by
      ext i
      constructor
      · intro hi
        have hb := mem_iset (hp1.2.2 hi)
        rcases (split p' hp' (2 * i - 1)).1 ((he _).1 ((split p hp _).2
          (Or.inr ⟨by omega, i, hi, rfl⟩))) with ⟨hh, -⟩ | ⟨-, j, hj, ej⟩
        · omega
        · have := mem_iset (hp1'.2.2 hj)
          rwa [show i = j by omega]
      · intro hi
        have hb := mem_iset (hp1'.2.2 hi)
        rcases (split p hp (2 * i - 1)).1 ((he _).2 ((split p' hp' _).2
          (Or.inr ⟨by omega, i, hi, rfl⟩))) with ⟨hh, -⟩ | ⟨-, j, hj, ej⟩
        · omega
        · have := mem_iset (hp1.2.2 hj)
          rwa [show i = j by omega]
    obtain ⟨a, b, c⟩ := p
    obtain ⟨a', b', c'⟩ := p'
    simp only [Prod.mk.injEq] at hd' hU ⊢
    exact ⟨hd'.1, hd'.2, hU⟩
  have step1 : ∑ p ∈ P, f (g p) ≤ slipSum (2 * h + 1) := by
    rw [← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset hsub
  set A : Finset Nat → Finset (List Nat) :=
    fun U => (semiSeqs (h + 1)).filter fun α => ∀ i ∈ U, upF h α i with hA
  set Bs : Finset Nat → Finset (List Nat) :=
    fun U => (semiSeqs h).filter fun β => ∀ i ∈ U, upS h β i with hBs
  have step2 : ∀ p ∈ P, ((condF h p.2.1).card * (condS (h + 1) p.2.1).card) *
      ((A p.2.2).card * (Bs p.2.2).card) ≤ f (g p) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := memP p hp
    have hF : (A p.2.2 ×ˢ condF h p.2.1).image (blockMap 1) ⊆ condF (2 * h + 1) (g p) := by
      intro z hz
      obtain ⟨⟨α, β⟩, hab, rfl⟩ := Finset.mem_image.1 hz
      rw [Finset.mem_product] at hab
      have ha := Finset.mem_filter.1 hab.1
      exact blockMap_mem_condF_up h1 h2 h3 ha.1 ha.2 hab.2
    have hS : (condS (h + 1) p.2.1 ×ˢ Bs p.2.2).image (blockMap 1) ⊆
        condS (2 * h + 1) (g p) := by
      intro z hz
      obtain ⟨⟨α, β⟩, hab, rfl⟩ := Finset.mem_image.1 hz
      rw [Finset.mem_product] at hab
      have hb := Finset.mem_filter.1 hab.2
      exact blockMap_mem_condS_up h1 h2 h3 hab.1 hb.1 hb.2
    have e1 : (2 * h + 1 + 1) / 2 = h + 1 := by omega
    have e2 : (2 * h + 1) / 2 = h := by omega
    have c1 := Finset.card_le_card hF
    have c2 := Finset.card_le_card hS
    rw [card_image_blockMap_gen (x := 2 * h + 1)
      (by rw [e1]; exact Finset.filter_subset _ _)
      (by rw [e2]; exact Finset.filter_subset _ _)] at c1
    rw [card_image_blockMap_gen (x := 2 * h + 1)
      (by rw [e1]; exact Finset.filter_subset _ _)
      (by rw [e2]; exact Finset.filter_subset _ _)] at c2
    calc (condF h p.2.1).card * (condS (h + 1) p.2.1).card * ((A p.2.2).card * (Bs p.2.2).card)
        = ((A p.2.2).card * (condF h p.2.1).card) * ((condS (h + 1) p.2.1).card *
            (Bs p.2.2).card) := by ring
      _ ≤ f (g p) := Nat.mul_le_mul c1 c2
  have step3 := Finset.sum_le_sum step2
  have lhs : ∑ p ∈ P, ((condF h p.2.1).card * (condS (h + 1) p.2.1).card) *
      ((A p.2.2).card * (Bs p.2.2).card) =
      2 ^ ((h + 1) / 2) * (wSum h * mSum h (h + 1) (h / 2)) := by
    simp only [hP, Finset.sum_product, Finset.sum_const, Finset.card_powerset, card_oddR,
      nsmul_eq_mul, Nat.cast_id]
    unfold wSum mSum
    rw [Finset.sum_mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun D _ => Finset.sum_congr rfl fun U _ => ?_
    simp only [hA, hBs]
    ring
  rw [lhs] at step3
  exact le_trans step3 step1

end Up
end Slip
end Folds
