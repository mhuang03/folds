import Folds.SuperExp
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Chained slips: `a(N) ≥ (N/2)^{N/6}` for `N = 2^L`

Notation of `Folds/SuperExp.lean`.  The **slip sum**
`B(n) = ∑_{D ⊆ [1, n-1]} #condF(n, D) · #condS(n, D)` is at most `a(2n)` (the slip lemma,
`semiCount_slip`).  The parity-slip recursion bounded it below using odds-first parity-block
inputs `τ = PB(α, β)`, `σ = PB(α', β')` and odd slip positions only.  Here the even slip
positions are used too: for `n = 2m` and an odds-first `τ = PB(α, β)`,

* `τ` places an odd `k` before `2k mod* 2m` (an even panel), always;
* `τ` places `2i` before `2·(2i) mod* 2m = 2·(2i mod* m)` iff `β` places `i` before
  `2i mod* m` (`qq_double`);

and for an odds-first `σ = PB(α', β')`,

* `σ` places `(2k+1) mod* 2m` (odd) before `k+1` (even) for odd `k`, always;
* `σ` places `(4i+1) mod* 2m = 2·((2i+1) mod* m) - 1` before `2i+1` iff `α'` places
  `(2i+1) mod* m` before `i+1` (`pp_double`).

So for `D = E ∪ 2D'` (`E` any set of odd positions, `D'` a slip set of `[m]`),
`condF(2m, D) ⊇ PB(V_m × condF(m, D'))` and `condS(2m, D) ⊇ PB(condS(m, D') × V_m)`, whence
(`slipSum_chain`)

        B(2m) ≥ 2^m · a(m)² · B(m).

Together with `a(2n) ≥ B(n)` this gives, for `N = 2^L` (`pow_le_semiCount_pow_six`),

        N^N ≤ 2^N · a(N)^6,     i.e.   a(N) ≥ (N/2)^{N/6},

improving `a(N) ≥ N^{N/8}` (`N = 4^j`, `pow_le_semiCount_pow_four`).
Paper proofs: `experiments/superexp2/PROOFS.txt`.
-/

namespace Folds
namespace Slip

/-! ## The slip sum -/

/-- The slip sum `B(n) = ∑_{D ⊆ [1, n-1]} #condF(n, D) · #condS(n, D)`. -/
noncomputable def slipSum (n : Nat) : Nat :=
  ∑ D ∈ (Finset.Icc 1 (n - 1)).powerset, (condF n D).card * (condS n D).card

/-- `B(n) ≤ a(2n)` (the slip lemma). -/
theorem slipSum_le {n : Nat} (hn : 1 ≤ n) : slipSum n ≤ semiCount (2 * n) :=
  semiCount_slip hn

theorem condF_empty (n : Nat) : condF n ∅ = semiSeqs n := by
  unfold condF
  refine Finset.filter_true_of_mem fun τ _ k _ h => ?_
  simp [ind] at h

theorem condS_empty (n : Nat) : condS n ∅ = semiSeqs n := by
  unfold condS
  refine Finset.filter_true_of_mem fun τ _ k _ h => ?_
  simp [ind] at h

/-- `a(n)² ≤ B(n)` (the term `D = ∅`). -/
theorem sq_le_slipSum (n : Nat) : semiCount n ^ 2 ≤ slipSum n := by
  unfold slipSum
  have h : (∅ : Finset Nat) ∈ (Finset.Icc 1 (n - 1)).powerset := Finset.empty_mem_powerset _
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h)
  rw [condF_empty, condS_empty, Nat.pow_two]; rfl

theorem slipSum_pos (n : Nat) : 1 ≤ slipSum n :=
  le_trans (Nat.one_le_pow _ _ (semiCount_pos n)) (sq_le_slipSum n)

/-! ## Doubling the slip positions -/

theorem two_mul_add_one_mod {y m : Nat} (hm : 1 ≤ m) :
    (2 * y + 1) % (2 * m) = 2 * (y % m) + 1 := by
  have h := Nat.div_add_mod y m
  have hlt := Nat.mod_lt y (show 0 < m by omega)
  have e : 2 * y + 1 = (2 * (y % m) + 1) + (2 * m) * (y / m) := by
    rw [Nat.mul_comm (2 * m) (y / m)]
    have : y = y % m + m * (y / m) := by omega
    calc 2 * y + 1 = 2 * (y % m + m * (y / m)) + 1 := by rw [← this]
      _ = 2 * (y % m) + 1 + y / m * (2 * m) := by ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- `2·(2i) mod* 2m = 2·(2i mod* m)`. -/
theorem qq_double {m i : Nat} (hm : 1 ≤ m) (hi : 1 ≤ i) : qq (2 * m) (2 * i) = 2 * qq m i := by
  unfold qq
  rw [show 2 * (2 * i) - 1 = 2 * (2 * i - 1) + 1 by omega, two_mul_add_one_mod hm]
  ring

/-- `(2·(2i)+1) mod* 2m = 2·((2i+1) mod* m) - 1`. -/
theorem pp_double {m i : Nat} : pp (2 * m) (2 * i) = 2 * pp m i - 1 := by
  unfold pp
  rw [show 2 * (2 * i) = 2 * (2 * i) by rfl, Nat.mul_mod_mul_left]
  omega

/-- The doubled slip set `E ∪ 2D'`. -/
def dbl (p : Finset Nat × Finset Nat) : Finset Nat := p.1 ∪ p.2.image (2 * ·)

theorem mem_dbl {p : Finset Nat × Finset Nat} (hE : p.1 ⊆ cset (2 * m)) {x : Nat} :
    x ∈ dbl p ↔ (x % 2 = 1 ∧ x ∈ p.1) ∨ (x % 2 = 0 ∧ x / 2 ∈ p.2) := by
  unfold dbl
  rw [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨i, hi, rfl⟩)
    · exact Or.inl ⟨(mem_cset (hE h)).1, h⟩
    · right; refine ⟨by omega, ?_⟩; rwa [show 2 * i / 2 = i by omega]
  · rintro (⟨-, h⟩ | ⟨h0, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨x / 2, h, by omega⟩

theorem dbl_sub {m : Nat} {p : Finset Nat × Finset Nat} (hE : p.1 ⊆ cset (2 * m))
    (hD : p.2 ⊆ Finset.Icc 1 (m - 1)) : dbl p ⊆ Finset.Icc 1 (2 * m - 1) := by
  intro x hx
  unfold dbl at hx
  rcases Finset.mem_union.1 hx with h | h
  · exact cset_sub _ (hE h)
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 h
    have := Finset.mem_Icc.1 (hD hi); rw [Finset.mem_Icc]; omega

theorem dbl_injOn {m : Nat} :
    Set.InjOn dbl
      (((cset (2 * m)).powerset ×ˢ (Finset.Icc 1 (m - 1)).powerset : Finset _) : Set _) := by
  rintro ⟨E, D⟩ hp ⟨E', D'⟩ hp' e
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powerset] at hp hp'
  have h := fun x => (mem_dbl (m := m) (p := (E, D)) hp.1 (x := x)).symm.trans
    ((congrArg (x ∈ ·) e).to_iff.trans (mem_dbl (m := m) (p := (E', D')) hp'.1))
  simp only at h
  have hE : E = E' := by
    ext x
    constructor
    · intro hx
      have := (mem_cset (hp.1 hx)).1
      rcases (h x).1 (Or.inl ⟨this, hx⟩) with ⟨-, h'⟩ | ⟨h0, -⟩
      · exact h'
      · omega
    · intro hx
      have := (mem_cset (hp'.1 hx)).1
      rcases (h x).2 (Or.inl ⟨this, hx⟩) with ⟨-, h'⟩ | ⟨h0, -⟩
      · exact h'
      · omega
  have hD : D = D' := by
    ext i
    have e2 : 2 * i / 2 = i := by omega
    constructor
    · intro hi
      rcases (h (2 * i)).1 (Or.inr ⟨by omega, by rwa [e2]⟩) with ⟨h1, -⟩ | ⟨-, h'⟩
      · omega
      · rwa [e2] at h'
    · intro hi
      rcases (h (2 * i)).2 (Or.inr ⟨by omega, by rwa [e2]⟩) with ⟨h1, -⟩ | ⟨-, h'⟩
      · omega
      · rwa [e2] at h'
  rw [hE, hD]

/-! ## Odds-first parity blocks with constrained halves -/

theorem blockMap_mem_two_mul {m : Nat} {α β : List Nat} (hα : α ∈ semiSeqs m)
    (hβ : β ∈ semiSeqs m) : blockMap 1 (α, β) ∈ semiSeqs (2 * m) := by
  apply blockMap_mem (N := 2 * m) (c := 1) le_rfl
  rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + (1 - 1)) / 2 = m by omega]
  exact Finset.mem_product.2 ⟨hα, hβ⟩

theorem card_image_blockMap {m : Nat} {X Y : Finset (List Nat)} (hX : X ⊆ semiSeqs m)
    (hY : Y ⊆ semiSeqs m) : ((X ×ˢ Y).image (blockMap 1)).card = X.card * Y.card := by
  rw [Finset.card_image_of_injOn, Finset.card_product]
  have := blockMap_injOn (N := 2 * m) (c := 1) le_rfl
  rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + (1 - 1)) / 2 = m by omega] at this
  exact this.mono (Finset.coe_subset.2 (Finset.product_subset_product hX hY))

theorem mem_map_scale_one_odd {α : List Nat} {m : Nat} (hα : IsFoldSeq m α) {x : Nat}
    (hx : x ∈ α.map (scale 1)) : x % 2 = 1 := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  have := (mem_range'_of_perm hα).1 hy; unfold scale; omega

theorem mem_map_scale_zero_even {β : List Nat} {x : Nat} (hx : x ∈ β.map (scale 0)) :
    x % 2 = 0 := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; unfold scale; omega

theorem blockMap_eq (α β : List Nat) :
    blockMap 1 (α, β) = α.map (scale 1) ++ β.map (scale 0) := rfl

theorem odd_mem_cset {m x : Nat} (h1 : 1 ≤ x) (h2 : x ≤ 2 * m - 1) (ho : x % 2 = 1) :
    x ∈ cset (2 * m) := by
  unfold cset cnt
  rw [Finset.mem_image]
  refine ⟨x / 2, ?_, by omega⟩
  rw [Finset.mem_range]; split <;> omega

/-- First block: `PB(α, β)` with `β ∈ condF(m, D')` is in `condF(2m, E ∪ 2D')`. -/
theorem blockMap_mem_condF {m : Nat} (hm : 1 ≤ m) {E D' : Finset Nat}
    (hE : E ⊆ cset (2 * m)) (hD' : D' ⊆ Finset.Icc 1 (m - 1)) {α β : List Nat}
    (hα : α ∈ semiSeqs m) (hβ : β ∈ condF m D') :
    blockMap 1 (α, β) ∈ condF (2 * m) (dbl (E, D')) := by
  have hβs : β ∈ semiSeqs m := (Finset.mem_filter.1 hβ).1
  have hβc := (Finset.mem_filter.1 hβ).2
  have hαf := (mem_semiSeqs.1 hα).1
  have hβf := (mem_semiSeqs.1 hβs).1
  unfold condF
  rw [Finset.mem_filter]
  refine ⟨blockMap_mem_two_mul hα hβs, ?_⟩
  rw [blockMap_eq]
  intro k hk hd
  have hxD : (α.map (scale 1) ++ β.map (scale 0))[k] ∈ dbl (E, D') := by
    unfold ind at hd; split at hd
    · assumption
    · omega
  rcases Nat.lt_or_ge k α.length with hkA | hkA
  · -- an odd panel: its image `2k mod* 2m` is even and the prefix is all odd
    have hkA' : k < (α.map (scale 1)).length := by simpa using hkA
    have hi1 : 1 ≤ α[k] := ((mem_range'_of_perm hαf).1 (List.getElem_mem _)).1
    have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * α[k] - 1 := by
      rw [List.getElem_append_left hkA']; simp [scale]
    rw [e] at hxD ⊢
    have hsub := dbl_sub (m := m) hE hD' hxD
    rw [Finset.mem_Icc] at hsub
    have hq := qq_even (odd_mem_cset (m := m) hsub.1 hsub.2 (by omega))
    intro hmem
    rw [List.take_append_of_le_length hkA'.le] at hmem
    have := mem_map_scale_one_odd hαf (List.mem_of_mem_take hmem)
    omega
  · -- an even panel `2i`, `i ∈ D'`
    have hkA' : (α.map (scale 1)).length ≤ k := by simpa using hkA
    have hβl : k - α.length < β.length := by simp at hk; omega
    have hi1 : 1 ≤ β[k - α.length] := ((mem_range'_of_perm hβf).1 (List.getElem_mem _)).1
    have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * β[k - α.length] := by
      rw [List.getElem_append_right hkA']; simp [scale]
    rw [e] at hxD ⊢
    have hiD : β[k - α.length] ∈ D' := by
      rcases (mem_dbl (m := m) (p := (E, D')) hE).1 hxD with ⟨h1, -⟩ | ⟨-, h2⟩
      · omega
      · simpa using h2
    have hcond := hβc (k - α.length) hβl (by unfold ind; rw [ite_eq_left_iff.2 (fun h => absurd hiD h)])
    rw [qq_double hm hi1]
    intro hmem
    rw [List.take_append, List.take_of_length_le hkA'] at hmem
    rcases List.mem_append.1 hmem with h | h
    · have := mem_map_scale_one_odd hαf h; omega
    · rw [List.length_map, ← List.map_take] at h
      obtain ⟨y, hy, hy2⟩ := List.mem_map.1 h
      unfold scale at hy2
      have : y = qq m β[k - α.length] := by omega
      exact hcond (this ▸ hy)

/-- Second block: `PB(α', β')` with `α' ∈ condS(m, D')` is in `condS(2m, E ∪ 2D')`. -/
theorem blockMap_mem_condS {m : Nat} {E D' : Finset Nat}
    (hE : E ⊆ cset (2 * m)) (hD' : D' ⊆ Finset.Icc 1 (m - 1)) {α β : List Nat}
    (hα : α ∈ condS m D') (hβ : β ∈ semiSeqs m) :
    blockMap 1 (α, β) ∈ condS (2 * m) (dbl (E, D')) := by
  have hαs : α ∈ semiSeqs m := (Finset.mem_filter.1 hα).1
  have hαc := (Finset.mem_filter.1 hα).2
  have hαf := (mem_semiSeqs.1 hαs).1
  have hβf := (mem_semiSeqs.1 hβ).1
  unfold condS
  rw [Finset.mem_filter]
  refine ⟨blockMap_mem_two_mul hαs hβ, ?_⟩
  rw [blockMap_eq]
  intro k hk hd
  have hxD : (α.map (scale 1) ++ β.map (scale 0))[k] - 1 ∈ dbl (E, D') := by
    unfold ind at hd; split at hd
    · assumption
    · omega
  rcases Nat.lt_or_ge k α.length with hkA | hkA
  · -- an odd panel `2i+1`, `i ∈ D'`: handled inside `α`
    have hkA' : k < (α.map (scale 1)).length := by simpa using hkA
    have hi1 : 1 ≤ α[k] := ((mem_range'_of_perm hαf).1 (List.getElem_mem _)).1
    have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * α[k] - 1 := by
      rw [List.getElem_append_left hkA']; simp [scale]
    rw [e] at hxD ⊢
    have hiD : α[k] - 1 ∈ D' := by
      rcases (mem_dbl (m := m) (p := (E, D')) hE).1 hxD with ⟨h1, -⟩ | ⟨-, h2⟩
      · omega
      · rwa [show (2 * α[k] - 1 - 1) / 2 = α[k] - 1 by omega] at h2
    have hcond := hαc k hkA (by unfold ind; rw [ite_eq_left_iff.2 (fun h => absurd hiD h)])
    rw [show 2 * α[k] - 1 - 1 = 2 * (α[k] - 1) by omega, pp_double,
      List.take_append_of_le_length hkA'.le, ← List.map_take]
    exact List.mem_map.2 ⟨_, hcond, rfl⟩
  · -- an even panel: `(2k+1) mod* 2m` is odd, hence in the complete first block
    have hkA' : (α.map (scale 1)).length ≤ k := by simpa using hkA
    have hβl : k - α.length < β.length := by simp at hk; omega
    have e : (α.map (scale 1) ++ β.map (scale 0))[k] = 2 * β[k - α.length] := by
      rw [List.getElem_append_right hkA']; simp [scale]
    rw [e] at hxD ⊢
    have hsub := dbl_sub (m := m) hE hD' hxD
    rw [Finset.mem_Icc] at hsub
    have hpp := pp_odd (odd_mem_cset (m := m) hsub.1 hsub.2 (by omega))
    have hmemA : pp (2 * m) (2 * β[k - α.length] - 1) ∈ α.map (scale 1) := by
      refine List.mem_map.2 ⟨(pp (2 * m) (2 * β[k - α.length] - 1) + 1) / 2,
        (mem_range'_of_perm hαf).2 ⟨by omega, by omega⟩, ?_⟩
      unfold scale; omega
    rw [List.take_append, List.take_of_length_le hkA']
    exact List.mem_append_left _ hmemA

/-! ## The chain recursion -/

/-- **Chain recursion.**  `2^m · a(m)² · B(m) ≤ B(2m)`. -/
theorem slipSum_chain {m : Nat} (hm : 1 ≤ m) :
    2 ^ m * (semiCount m ^ 2 * slipSum m) ≤ slipSum (2 * m) := by
  set P := (cset (2 * m)).powerset ×ˢ (Finset.Icc 1 (m - 1)).powerset with hP
  set f : Finset Nat → Nat := fun D => (condF (2 * m) D).card * (condS (2 * m) D).card
  have hsub : P.image dbl ⊆ (Finset.Icc 1 (2 * m - 1)).powerset := by
    intro D hD
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hD
    rw [hP, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    exact Finset.mem_powerset.2 (dbl_sub hp.1 hp.2)
  have step1 : ∑ D ∈ P.image dbl, f D ≤ slipSum (2 * m) :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_image (fun x hx y hy e => dbl_injOn (m := m) hx hy e)] at step1
  have step2 : ∀ p ∈ P, semiCount m ^ 2 *
      ((condF m p.2).card * (condS m p.2).card) ≤ f (dbl p) := by
    rintro ⟨E, D'⟩ hp
    rw [hP, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    have hF : (semiSeqs m ×ˢ condF m D').image (blockMap 1) ⊆ condF (2 * m) (dbl (E, D')) := by
      intro x hx
      obtain ⟨⟨α, β⟩, hab, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_product] at hab
      exact blockMap_mem_condF hm hp.1 hp.2 hab.1 hab.2
    have hS : (condS m D' ×ˢ semiSeqs m).image (blockMap 1) ⊆ condS (2 * m) (dbl (E, D')) := by
      intro x hx
      obtain ⟨⟨α, β⟩, hab, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_product] at hab
      exact blockMap_mem_condS hp.1 hp.2 hab.1 hab.2
    have c1 := Finset.card_le_card hF
    have c2 := Finset.card_le_card hS
    have sF : condF m D' ⊆ semiSeqs m := by unfold condF; exact Finset.filter_subset _ _
    have sS : condS m D' ⊆ semiSeqs m := by unfold condS; exact Finset.filter_subset _ _
    rw [card_image_blockMap le_rfl sF] at c1
    rw [card_image_blockMap sS le_rfl] at c2
    calc semiCount m ^ 2 * ((condF m D').card * (condS m D').card)
        = (semiCount m * (condF m D').card) * ((condS m D').card * semiCount m) := by
          unfold semiCount; ring
      _ ≤ f (dbl (E, D')) := Nat.mul_le_mul c1 c2
  have step3 := Finset.sum_le_sum step2
  rw [hP, Finset.sum_product] at step3
  simp only at step3
  rw [Finset.sum_const, Finset.card_powerset, card_cset,
    show cnt (2 * m) = m by unfold cnt; split <;> omega, nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum] at step3
  exact le_trans step3 (by rw [← hP]; exact step1)

/-! ## Powers of two -/

/-- The joint induction: for `N = 2^L`, `N^N ≤ 2^N a(N)^6` and `N^N ≤ B(N)^3`. -/
theorem pow_two_aux (L : Nat) :
    (2 ^ L) ^ (2 ^ L) ≤ 2 ^ (2 ^ L) * semiCount (2 ^ L) ^ 6 ∧
      (2 ^ L) ^ (2 ^ L) ≤ slipSum (2 ^ L) ^ 3 := by
  induction L with
  | zero =>
    simp only [Nat.pow_zero, Nat.pow_one]
    exact ⟨le_trans (Nat.one_le_pow _ _ (semiCount_pos 1)) (Nat.le_mul_of_pos_left _ (by omega)),
      Nat.one_le_pow _ _ (slipSum_pos 1)⟩
  | succ L ih =>
    obtain ⟨hQ, hR⟩ := ih
    set x := 2 ^ L with hx
    have hx1 : 1 ≤ x := Nat.one_le_two_pow
    have e : 2 ^ (L + 1) = 2 * x := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [e]
    have hsq : (2 * x) ^ (2 * x) = 2 ^ (2 * x) * (x ^ x * x ^ x) := by
      rw [Nat.mul_pow, ← Nat.pow_add, ← Nat.two_mul]
    have hchain := slipSum_chain hx1
    have hle := slipSum_le hx1
    constructor
    · -- (2x)^{2x} = 2^{2x} (x^x)² ≤ 2^{2x} B(x)^6 ≤ 2^{2x} a(2x)^6
      rw [hsq]
      refine Nat.mul_le_mul_left _ ?_
      calc x ^ x * x ^ x ≤ slipSum x ^ 3 * slipSum x ^ 3 := Nat.mul_le_mul hR hR
        _ = slipSum x ^ 6 := by ring
        _ ≤ semiCount (2 * x) ^ 6 := Nat.pow_le_pow_left hle 6
    · -- (2x)^{2x} ≤ 2^{2x} (2^x a(x)^6)(B(x)^3) ≤ (2^x a(x)² B(x))^3 ≤ B(2x)^3
      rw [hsq]
      calc 2 ^ (2 * x) * (x ^ x * x ^ x)
          ≤ 2 ^ (2 * x) * ((2 ^ x * semiCount x ^ 6) * slipSum x ^ 3) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul hQ hR)
        _ = (2 ^ x * (semiCount x ^ 2 * slipSum x)) ^ 3 := by
            rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul, Nat.pow_mul, ← Nat.pow_mul]
            ring
        _ ≤ slipSum (2 * x) ^ 3 := Nat.pow_le_pow_left hchain 3

/-- **Super-exponential lower bound with exponent 1/6** along `N = 2^L`:
`N^N ≤ 2^N · a(N)^6`, i.e. `a(N) ≥ (N/2)^{N/6}`. -/
theorem pow_le_semiCount_pow_six (L : Nat) :
    (2 ^ L) ^ (2 ^ L) ≤ 2 ^ (2 ^ L) * semiCount (2 ^ L) ^ 6 :=
  (pow_two_aux L).1

end Slip
end Folds
