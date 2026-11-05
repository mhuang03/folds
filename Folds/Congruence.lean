import Folds.Recursion
import Folds.RevMirror

/-!
# Congruences for `a(N)` from the reversal/mirror symmetry

Reversal `R a = a.reverse` and mirror `M a = a.map (N + 1 - ·)` are commuting involutions
of the set `semiSeqs N` of semi-symmetric fold sequences, so they generate a Klein
four-group acting on it.  For `N ≥ 2`:

* `reverse_ne_self`, `mirror_ne_self`: neither `R` nor `M` has a fixed point.
* Hence an orbit has size 4, unless it passes through a fixed point of `R ∘ M`
  (`revMirror`), in which case it is `{a, R a}` of size 2 and both elements are fixed.
* `semiCount_mod_four`: `a(N) ≡ c(N) (mod 4)` where `c(N)` is the number of
  semi-symmetric fold sequences fixed by `revMirror`.
* `revMirrorFixed_even`: `c(N)` is even (`M` acts freely on the fixed set), so
  `a(N) ≡ 2 · (c(N) / 2) (mod 4)`.
* `semiCount_even'`: `a(N)` is even (reversal pairs).
* `semiCount_mod_four_of_three`: `a(N) ≡ 0 (mod 4)` when `N ≡ 3 (mod 4)`
  (then `c(N) = 0` by `revMirror_no_fixed`).

Note: the claim `a(N) ≡ 2 · c(N) (mod 4)` that appeared in the experimental notes is
false (`N = 2`: `a = 2`, `c = 2`); the correct statement is `a(N) ≡ c(N) (mod 4)`.

The orbit counting is done abstractly (`card_even_of_involution`, `card_mod_four`) by
strong induction on the size of the set, removing one orbit at a time.
-/

namespace Folds

section Abstract

variable {α : Type*} [DecidableEq α]

/-- A finite set with a fixed-point-free involution has even size. -/
theorem card_even_of_involution (R : α → α) : ∀ (n : Nat) (X : Finset α), X.card = n →
    (∀ x ∈ X, R x ∈ X) → (∀ x ∈ X, R (R x) = x) → (∀ x ∈ X, R x ≠ x) →
    X.card % 2 = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn hR hRR hRf
  rcases X.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  set O : Finset α := {a, R a} with hOdef
  have hO : O ⊆ X := by
    intro y hy; simp only [hOdef, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact ha
    · exact hR _ ha
  have hOR : ∀ y ∈ O, R y ∈ O := by
    intro y hy; simp only [hOdef, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl
    · simp
    · simp [hRR a ha]
  have hcO : O.card = 2 := Finset.card_pair_eq_two_iff.2 (hRf a ha).symm
  have hcard := Finset.card_sdiff_add_card_eq_card hO
  have := ih (X \ O).card (by omega) (X \ O) rfl
    (fun x hx => by
      rw [Finset.mem_sdiff] at hx ⊢
      refine ⟨hR x hx.1, fun h => hx.2 ?_⟩
      have := hOR _ h; rwa [hRR x hx.1] at this)
    (fun x hx => hRR x (Finset.mem_sdiff.1 hx).1)
    (fun x hx => hRf x (Finset.mem_sdiff.1 hx).1)
  omega

theorem card_filter_eq_sdiff_add {X O : Finset α} (hO : O ⊆ X) (p : α → Prop)
    [DecidablePred p] :
    (X.filter p).card = ((X \ O).filter p).card + (O.filter p).card := by
  rw [← Finset.card_sdiff_add_card_eq_card (Finset.filter_subset_filter p hO)]
  congr 2
  ext x; simp only [Finset.mem_sdiff, Finset.mem_filter]; tauto

/-- **Orbit counting for a Klein four-group.**  Let `R`, `M` be commuting involutions of a
finite set `X`, neither with a fixed point.  Then `|X| ≡ |Fix(R ∘ M)| (mod 4)`. -/
theorem card_mod_four (R M : α → α) : ∀ (n : Nat) (X : Finset α), X.card = n →
    (∀ x ∈ X, R x ∈ X) → (∀ x ∈ X, M x ∈ X) →
    (∀ x ∈ X, R (R x) = x) → (∀ x ∈ X, M (M x) = x) → (∀ x ∈ X, R (M x) = M (R x)) →
    (∀ x ∈ X, R x ≠ x) → (∀ x ∈ X, M x ≠ x) →
    X.card % 4 = (X.filter fun x => R (M x) = x).card % 4 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn hR hM hRR hMM hc hRf hMf
  rcases X.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  have hRa := hR a ha
  have hMa := hM a ha
  have hRMa := hR _ hMa
  have e1 : R (R a) = a := hRR a ha
  have e2 : M (M a) = a := hMM a ha
  have e3 : R (R (M a)) = M a := hRR _ hMa
  have e4 : R (M a) = M (R a) := hc a ha
  have e5 : M (M (R a)) = R a := hMM _ hRa
  set O : Finset α := {a, R a, M a, R (M a)} with hOdef
  have hO : O ⊆ X := by
    intro y hy; simp only [hOdef, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> assumption
  have hOR : ∀ y ∈ O, R y ∈ O := by
    intro y hy; simp only [hOdef, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl | rfl <;> simp [e1, e3]
  have hOM : ∀ y ∈ O, M y ∈ O := by
    intro y hy; simp only [hOdef, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl | rfl <;> simp [e2, e4, e5]
  have hcard := Finset.card_sdiff_add_card_eq_card hO
  have hF := card_filter_eq_sdiff_add hO (fun x => R (M x) = x)
  have hmem : a ∈ O := by simp [hOdef]
  have hpos : 0 < O.card := Finset.card_pos.2 ⟨a, hmem⟩
  have hX' := ih (X \ O).card (by omega) (X \ O) rfl
    (fun x hx => by
      rw [Finset.mem_sdiff] at hx ⊢
      refine ⟨hR x hx.1, fun h => hx.2 ?_⟩
      have := hOR _ h; rwa [hRR x hx.1] at this)
    (fun x hx => by
      rw [Finset.mem_sdiff] at hx ⊢
      refine ⟨hM x hx.1, fun h => hx.2 ?_⟩
      have := hOM _ h; rwa [hMM x hx.1] at this)
    (fun x hx => hRR x (Finset.mem_sdiff.1 hx).1)
    (fun x hx => hMM x (Finset.mem_sdiff.1 hx).1)
    (fun x hx => hc x (Finset.mem_sdiff.1 hx).1)
    (fun x hx => hRf x (Finset.mem_sdiff.1 hx).1)
    (fun x hx => hMf x (Finset.mem_sdiff.1 hx).1)
  by_cases hfix : R (M a) = a
  · -- orbit `{a, R a}` of size 2, both fixed by `R ∘ M`
    have hMR : M a = R a := by rw [← e3, hfix]
    have hO2 : O = {a, R a} := by
      rw [hOdef, hfix, hMR]; ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    have hc2 : O.card = 2 := by
      rw [hO2]; exact Finset.card_pair_eq_two_iff.2 (hRf a ha).symm
    have hf2 : (O.filter fun x => R (M x) = x) = O := by
      apply Finset.filter_true_of_mem
      intro y hy; rw [hO2] at hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hfix
      · rw [← e4, e3, hMR]
    rw [hf2] at hF
    omega
  · -- orbit of size 4 without fixed points of `R ∘ M`
    have d4 : R a ≠ M a := fun h => hfix (by rw [← h, e1])
    have d5 : R a ≠ R (M a) := fun h => by
      have := congrArg R h; rw [e1, e3] at this; exact hMf a ha this.symm
    have d6 : M a ≠ R (M a) := (hRf _ hMa).symm
    have hc4 : O.card = 4 := by
      rw [hOdef, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair_eq_two_iff.2 d6]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d4, d5⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨(hRf a ha).symm, (hMf a ha).symm, fun h => hfix h.symm⟩
    have hf0 : (O.filter fun x => R (M x) = x) = ∅ := by
      apply Finset.filter_false_of_mem
      intro y hy; simp only [hOdef, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hfix
      · rw [← e4, e3]; exact d4.symm
      · rw [e2]; exact d4
      · rw [e4, e5, e1]; exact fun h => hfix (e4.trans h.symm)
    rw [hf0, Finset.card_empty] at hF
    omega

end Abstract

/-! ## Reversal and mirror on semi-symmetric fold sequences -/

/-- The mirror image `m ↦ N + 1 - m` of a sequence. -/
def mirror (N : Nat) (a : List Nat) : List Nat := a.map (N + 1 - ·)

theorem revMirror_eq (N : Nat) (a : List Nat) : revMirror N a = (mirror N a).reverse := rfl

theorem reverse_mem_semiSeqs {N : Nat} {a : List Nat} (ha : a ∈ semiSeqs N) :
    a.reverse ∈ semiSeqs N := by
  rw [mem_semiSeqs] at ha ⊢
  exact ⟨(List.reverse_perm _).trans ha.1, ha.2.reverse ha.1⟩

theorem mirror_mem_semiSeqs {N : Nat} {a : List Nat} (ha : a ∈ semiSeqs N) :
    mirror N a ∈ semiSeqs N := by
  rw [mem_semiSeqs] at ha ⊢
  exact ⟨ha.1.mirror, ha.2.mirror ha.1⟩

theorem mirror_mirror {N : Nat} {a : List Nat} (hf : IsFoldSeq N a) :
    mirror N (mirror N a) = a := by
  unfold mirror
  rw [List.map_map]
  conv => rhs; rw [← List.map_id a]
  apply List.map_congr_left
  intro x hx; have := (mem_range'_of_perm hf).1 hx; simp; omega

theorem reverse_mirror (N : Nat) (a : List Nat) :
    (mirror N a).reverse = mirror N a.reverse := by
  simp [mirror]

/-- For `N ≥ 2`, no fold sequence is a palindrome. -/
theorem reverse_ne_self {N : Nat} (hN : 2 ≤ N) {a : List Nat} (hf : IsFoldSeq N a) :
    a.reverse ≠ a := by
  intro h
  have hnd := nodup_of_foldSeq hf
  have hlen : a.length = N := by rw [hf.length_eq]; simp
  have e : a.reverse[0]'(by simp; omega) = a[0]'(by omega) := by simp only [h]
  rw [List.getElem_reverse] at e
  have := (List.Nodup.getElem_inj hnd).1 e
  omega

/-- For `N ≥ 2`, no fold sequence equals its mirror image. -/
theorem mirror_ne_self {N : Nat} (hN : 2 ≤ N) {a : List Nat} (hf : IsFoldSeq N a) :
    mirror N a ≠ a := by
  intro h
  have hnd := nodup_of_foldSeq hf
  have hlen : a.length = N := by rw [hf.length_eq]; simp
  have e0 : (mirror N a)[0]'(by simp [mirror]; omega) = a[0]'(by omega) := by simp only [h]
  have e1 : (mirror N a)[1]'(by simp [mirror]; omega) = a[1]'(by omega) := by simp only [h]
  simp only [mirror, List.getElem_map] at e0 e1
  have b0 := (mem_range'_of_perm hf).1 (List.getElem_mem (show 0 < a.length by omega))
  have b1 := (mem_range'_of_perm hf).1 (List.getElem_mem (show 1 < a.length by omega))
  have : a[0]'(by omega) = a[1]'(by omega) := by omega
  have := (List.Nodup.getElem_inj hnd).1 this
  omega

/-- `c(N)`: the semi-symmetric fold sequences fixed by `revMirror N`. -/
def revMirrorFixed (N : Nat) : Finset (List Nat) :=
  (semiSeqs N).filter fun a => revMirror N a = a

/-- **`a(N) ≡ c(N) (mod 4)`** for `N ≥ 2`, where `c(N) = #{a semi-symmetric :
revMirror N a = a}`.  Orbits of the Klein group `⟨reverse, mirror⟩` have size 4, except
those through fixed points of `revMirror`, which have size 2. -/
theorem semiCount_mod_four {N : Nat} (hN : 2 ≤ N) :
    semiCount N % 4 = (revMirrorFixed N).card % 4 := by
  have := card_mod_four List.reverse (mirror N) _ (semiSeqs N) rfl
    (fun _ ha => reverse_mem_semiSeqs ha)
    (fun _ ha => mirror_mem_semiSeqs ha)
    (fun _ _ => List.reverse_reverse _)
    (fun _ ha => mirror_mirror (mem_semiSeqs.1 ha).1)
    (fun x _ => reverse_mirror N x)
    (fun _ ha => reverse_ne_self hN (mem_semiSeqs.1 ha).1)
    (fun _ ha => mirror_ne_self hN (mem_semiSeqs.1 ha).1)
  exact this

/-- **`c(N)` is even** for `N ≥ 2`: the mirror acts on the `revMirror`-fixed sequences
without fixed points. -/
theorem revMirrorFixed_even {N : Nat} (hN : 2 ≤ N) : (revMirrorFixed N).card % 2 = 0 := by
  have hfix : ∀ x ∈ revMirrorFixed N, x ∈ semiSeqs N ∧ (mirror N x).reverse = x :=
    fun x hx => by unfold revMirrorFixed at hx; rw [Finset.mem_filter] at hx; exact hx
  refine card_even_of_involution (mirror N) _ _ rfl ?_ ?_ ?_
  · intro x hx
    obtain ⟨hs, hx⟩ := hfix x hx
    have hf := (mem_semiSeqs.1 hs).1
    refine Finset.mem_filter.2 ⟨mirror_mem_semiSeqs hs, ?_⟩
    rw [revMirror_eq, mirror_mirror hf]
    -- `x.reverse = mirror x`
    conv => lhs; rw [← hx]
    rw [List.reverse_reverse]
  · intro x hx; exact mirror_mirror (mem_semiSeqs.1 (hfix x hx).1).1
  · intro x hx; exact mirror_ne_self hN (mem_semiSeqs.1 (hfix x hx).1).1

/-- `a(N) ≡ 2 · (c(N) / 2) (mod 4)` for `N ≥ 2`. -/
theorem semiCount_mod_four' {N : Nat} (hN : 2 ≤ N) :
    semiCount N % 4 = 2 * ((revMirrorFixed N).card / 2) % 4 := by
  have h1 := semiCount_mod_four hN
  have h2 := revMirrorFixed_even hN
  omega

/-- **`a(N)` is even** for `N ≥ 2` (reversal pairs up semi-symmetric sequences). -/
theorem semiCount_even' {N : Nat} (hN : 2 ≤ N) : semiCount N % 2 = 0 :=
  card_even_of_involution List.reverse _ (semiSeqs N) rfl
    (fun _ ha => reverse_mem_semiSeqs ha) (fun _ _ => List.reverse_reverse _)
    (fun _ ha => reverse_ne_self hN (mem_semiSeqs.1 ha).1)

/-- **`a(N) ≡ 0 (mod 4)` when `N ≡ 3 (mod 4)`.** -/
theorem semiCount_mod_four_of_three {N : Nat} (hN : N % 4 = 3) : semiCount N % 4 = 0 := by
  have h := semiCount_mod_four (N := N) (by omega)
  have : revMirrorFixed N = ∅ := by
    apply Finset.filter_false_of_mem
    intro a ha
    rw [mem_semiSeqs] at ha
    exact revMirror_no_fixed hN ha.1 ha.2
  rw [this, Finset.card_empty] at h
  exact h

end Folds
