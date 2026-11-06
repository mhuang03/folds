import Folds.Recursion
import Folds.Live2

/-!
# Exact counts of recursive constructions, and prefix-set decompositions of `a(N)`

`experiments/reccount/NOTES.txt`.

## The recursive parity-block family

`parFam N` is the family obtained by applying the parity-block construction at every
level: for `N ≥ 2` it consists of the sequences `blockMap c (σ, τ)` (the class `c` first, in
the order `σ`, then the other class in the order `τ`) with `σ`, `τ` again in the family.

* `parFam_subset`: every member is a semi-symmetric fold sequence.
* `card_parFam`: `#parFam N = 2 ^ (N - 1)` for `N ≥ 1` (the recursion
  `R(N) = 2 R(⌊N/2⌋) R(⌈N/2⌉)`, `R(1) = 1`: the two block orders are disjoint and each
  block map is injective).

## Prefix-set fibres

* `card_prefix_eq`: for `S ⊆ [1, N]` with `|S| = k`, the number of semi-symmetric sequences
  whose first `k` panels form the set `S` is `g(S) · g([1, N] \ S)` (the fibres of the split
  identity `semiCount_eq_sum_split`).
* `g_winEmb`: if `φ` window-embeds the `p`-strip, its image `X` has `g(X) = a(p)`: a window
  copy is built in exactly `a(p)` ways.
* `Split.card_prefix`: for a split (`Folds.Split`, i.e. `X` and its complement are both window
  copies, each balanced around the other), exactly `a(p) · a(q)` sequences start with `X`.
  This generalises `card_class_prefix` (parity classes) to every split, e.g. the doubling
  splits `{2, 4, …, 2j} mod 2j+1` (`split_res`).

## Antichain decomposition

* `semiCount_eq_sum_antichain`: for any family `𝓕` of subsets of `[1, N]` that is an antichain
  under `⊆`,
    `a(N) = ∑_{X ∈ 𝓕} g(X) g(Xᶜ) + #{sequences none of whose prefix sets lies in 𝓕}`
  (a sequence has at most one prefix set in an antichain).
* `semiCount_eq_parity_add`: with `𝓕` the two parity classes,
  `a(N) = 2 a(⌊N/2⌋) a(⌈N/2⌉) + #{sequences not starting with a full parity class}`.

The data in `experiments/reccount/` show that the balanced-everywhere ("neutral") sets are
exactly the parity classes and the doubling sets `E_d`, `E_dᶜ` (`d` odd, `d ∣ N`), that they
form an antichain, and hence the exact identity
`a(N) = 2a(⌊N/2⌋)a(⌈N/2⌉) + 2 ∑_{d | N odd, 3 ≤ d < N} a(jN/d) a((j+1)N/d) + I(N)`
(`j = (d-1)/2`), where `I(N)/a(N) → 1` (0.999 at `N = 24`).
-/

namespace Folds

/-! ## The recursive parity-block family -/

/-- The recursive parity-block family: `[]`, `[1]`, and for `N ≥ 2` every
`blockMap c (σ, τ)` with `σ ∈ parFam ((N + c) / 2)`, `τ ∈ parFam ((N + 1 - c) / 2)`. -/
def parFam : Nat → Finset (List Nat)
  | 0 => {[]}
  | 1 => {[1]}
  | N + 2 =>
    (parFam ((N + 2 + 0) / 2) ×ˢ parFam ((N + 2 + (1 - 0)) / 2)).image (blockMap 0) ∪
      (parFam ((N + 2 + 1) / 2) ×ˢ parFam ((N + 2 + (1 - 1)) / 2)).image (blockMap 1)
  decreasing_by all_goals omega

theorem parFam_succ_succ (N : Nat) :
    parFam (N + 2) =
      (parFam ((N + 2 + 0) / 2) ×ˢ parFam ((N + 2 + (1 - 0)) / 2)).image (blockMap 0) ∪
        (parFam ((N + 2 + 1) / 2) ×ˢ parFam ((N + 2 + (1 - 1)) / 2)).image (blockMap 1) := by
  rw [parFam]

/-- Every member of the recursive parity-block family is a semi-symmetric fold sequence. -/
theorem parFam_subset : ∀ N, parFam N ⊆ semiSeqs N
  | 0 => by
    intro a ha
    rw [parFam, Finset.mem_singleton] at ha
    subst ha
    exact mem_semiSeqs.2 ⟨by decide, by decide⟩
  | 1 => by
    intro a ha
    rw [parFam, Finset.mem_singleton] at ha
    subst ha
    exact mem_semiSeqs.2 ⟨by decide, by decide⟩
  | N + 2 => by
    have h1 := parFam_subset ((N + 2 + 0) / 2)
    have h2 := parFam_subset ((N + 2 + (1 - 0)) / 2)
    have h3 := parFam_subset ((N + 2 + 1) / 2)
    have h4 := parFam_subset ((N + 2 + (1 - 1)) / 2)
    rw [parFam_succ_succ]
    apply Finset.union_subset <;> intro x hx <;> rw [Finset.mem_image] at hx <;>
      obtain ⟨p, hp, rfl⟩ := hx
    · exact blockMap_mem (by omega) (Finset.product_subset_product h1 h2 hp)
    · exact blockMap_mem (by omega) (Finset.product_subset_product h3 h4 hp)
  termination_by N => N
  decreasing_by all_goals omega

/-- **Exact count of the recursive parity-block family:** `2 ^ (N - 1)` for `N ≥ 1`. -/
theorem card_parFam : ∀ N, 1 ≤ N → (parFam N).card = 2 ^ (N - 1)
  | 0, h => absurd h (by omega)
  | 1, _ => by rw [parFam]; rfl
  | N + 2, _ => by
    have i1 := card_parFam ((N + 2 + 0) / 2) (by omega)
    have i2 := card_parFam ((N + 2 + (1 - 0)) / 2) (by omega)
    have s0 := Finset.product_subset_product (parFam_subset ((N + 2 + 0) / 2))
      (parFam_subset ((N + 2 + (1 - 0)) / 2))
    have s1 := Finset.product_subset_product (parFam_subset ((N + 2 + 1) / 2))
      (parFam_subset ((N + 2 + (1 - 1)) / 2))
    have hdisj := (blockMap_disjoint (N := N + 2) (by omega)).mono
      (Finset.image_subset_image s0) (Finset.image_subset_image s1)
    have inj0 := (blockMap_injOn (N := N + 2) (c := 0) (by omega)).mono
      (Finset.coe_subset.2 s0)
    have inj1 := (blockMap_injOn (N := N + 2) (c := 1) (by omega)).mono
      (Finset.coe_subset.2 s1)
    rw [parFam_succ_succ, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injOn inj0, Finset.card_image_of_injOn inj1,
      Finset.card_product, Finset.card_product, i1, i2,
      Nat.mul_comm (2 ^ ((N + 2 + (1 - 0)) / 2 - 1)), ← Nat.pow_add]
    have e1 : (N + 2 + 0) / 2 - 1 + ((N + 2 + (1 - 0)) / 2 - 1) = N := by omega
    rw [e1, show N + 2 - 1 = N + 1 by omega, Nat.pow_succ]
    omega
  termination_by N => N
  decreasing_by all_goals omega

/-! ## Prefix-set fibres -/

/-- **Prefix-set fibres.**  For `S ⊆ [1, N]` with `|S| = k`, exactly `g(S) · g([1, N] \ S)`
semi-symmetric sequences have `S` as the set of their first `k` panels. -/
theorem card_prefix_eq {N k : Nat} {S : Finset Nat}
    (hS : S ∈ (Finset.Icc 1 N).powersetCard k) :
    ((semiSeqs N).filter (fun a => (a.take k).toFinset = S)).card =
      g N S * g N (Finset.Icc 1 N \ S) := by
  rw [Finset.mem_powersetCard] at hS
  have hk : k ≤ N := by
    have := Finset.card_le_card hS.1; rw [hS.2] at this; simpa using this
  rw [g, g, ← Finset.card_product]
  apply Finset.card_nbij' (fun a => (a.take k, (a.drop k).reverse))
    (fun p => p.1 ++ p.2.reverse)
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_semiSeqs] at ha
    obtain ⟨⟨hf, hss⟩, hSa⟩ := ha
    have hnd := nodup_of_foldSeq hf
    have hlen : a.length = N := by rw [hf.length_eq]; simp
    rw [semiSymmetric_split_iff hf (k := k) (by omega)] at hss
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_semiOrders]
    refine ⟨⟨⟨take_nodup hnd k, hSa⟩, hss.1⟩, ⟨⟨?_, ?_⟩, hss.2⟩⟩
    · exact List.nodup_reverse.2 (hnd.sublist (List.drop_sublist _ _))
    · ext x
      rw [List.mem_toFinset, List.mem_reverse, mem_drop_iff_of_nodup hnd, Finset.mem_sdiff,
        ← hSa, List.mem_toFinset, ← List.mem_toFinset (l := a), (isFoldSeq_iff.1 hf).2]
  · rintro ⟨u, v⟩ hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_semiOrders] at hp
    obtain ⟨⟨⟨hnu, hu⟩, hsu⟩, ⟨⟨hnv, hv⟩, hsv⟩⟩ := hp
    have hulen : u.length = k := by
      rw [← List.toFinset_card_of_nodup hnu, hu, hS.2]
    have hf : IsFoldSeq N (u ++ v.reverse) := by
      rw [isFoldSeq_iff]
      refine ⟨List.nodup_append.2 ⟨hnu, List.nodup_reverse.2 hnv, ?_⟩, ?_⟩
      · intro x hx y hy e
        subst e
        have h1 : x ∈ u.toFinset := List.mem_toFinset.2 hx
        have h2 : x ∈ v.toFinset := List.mem_toFinset.2 (List.mem_reverse.1 hy)
        rw [hu] at h1; rw [hv, Finset.mem_sdiff] at h2
        exact h2.2 h1
      · rw [List.toFinset_append, List.toFinset_reverse, hu, hv,
          Finset.union_sdiff_of_subset hS.1]
    have ht : (u ++ v.reverse).take k = u := List.take_left' hulen
    have hd : (u ++ v.reverse).drop k = v.reverse := List.drop_left' hulen
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_semiSeqs]
    refine ⟨⟨hf, ?_⟩, by rw [ht, hu]⟩
    rw [semiSymmetric_split_iff hf (k := k) (by simp; omega), ht, hd, List.reverse_reverse]
    exact ⟨hsu, hsv⟩
  · intro a _
    simp
  · rintro ⟨u, v⟩ hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_semiOrders] at hp
    have hulen : u.length = k := by
      rw [← List.toFinset_card_of_nodup hp.1.1.1, hp.1.1.2, hS.2]
    simp [List.take_left' hulen, List.drop_left' hulen]

/-! ## Window copies are built in exactly `a(p)` ways -/

theorem list_lift {φ : Nat → Nat} {P : Nat → Prop} :
    ∀ l : List Nat, (∀ x ∈ l, ∃ y, P y ∧ φ y = x) → ∃ σ : List Nat, σ.map φ = l ∧ ∀ y ∈ σ, P y
  | [], _ => ⟨[], rfl, by simp⟩
  | x :: l, h => by
    obtain ⟨y, hy, rfl⟩ := h x (by simp)
    obtain ⟨σ, e, hσ⟩ := list_lift l (fun z hz => h z (by simp [hz]))
    refine ⟨y :: σ, by simp [e], ?_⟩
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    exacts [hy, hσ z hz]

theorem WinEmb.injOn_Icc {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ) :
    Set.InjOn φ (Finset.Icc 1 p : Set Nat) := fun x hx y hy e => by
  simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
  exact hφ.inj x y hx.1 hx.2 hy.1 hy.2 e

/-- **A window copy is built in exactly `a(p)` ways:** if `φ` window-embeds the `p`-strip
into the `N`-strip, then `g N (φ [1, p]) = a(p)`. -/
theorem g_winEmb {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ) :
    g N ((Finset.Icc 1 p).image φ) = semiCount p := by
  rw [g, semiCount]
  symm
  apply Finset.card_nbij (fun σ => σ.map φ)
  · intro σ hσ
    rw [Finset.mem_coe, mem_semiSeqs] at hσ
    rw [Finset.mem_coe, mem_semiOrders]
    have b : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ p := fun y hy => (mem_range'_of_perm hσ.1).1 hy
    have hnd := nodup_of_foldSeq hσ.1
    refine ⟨⟨hφ.nodup_map hnd b, ?_⟩, (hφ.semiSymmetric_iff hnd b).2 hσ.2⟩
    have hs := (isFoldSeq_iff.1 hσ.1).2
    ext x
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, by rw [← hs, List.mem_toFinset]; exact hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, by rw [← hs, List.mem_toFinset] at hy; exact hy, rfl⟩
  · intro σ hσ σ' hσ' e
    rw [Finset.mem_coe, mem_semiSeqs] at hσ hσ'
    exact hφ.map_inj (fun y hy => (mem_range'_of_perm hσ.1).1 hy)
      (fun y hy => (mem_range'_of_perm hσ'.1).1 hy) e
  · intro l hl
    rw [Finset.mem_coe, mem_semiOrders] at hl
    obtain ⟨⟨hnd, hX⟩, hss⟩ := hl
    obtain ⟨σ, rfl, hσ⟩ := list_lift (P := fun y => 1 ≤ y ∧ y ≤ p) l (fun x hx => by
      have : x ∈ l.toFinset := List.mem_toFinset.2 hx
      rw [hX, Finset.mem_image] at this
      obtain ⟨y, hy, e⟩ := this
      exact ⟨y, Finset.mem_Icc.1 hy, e⟩)
    have hndσ : σ.Nodup := List.Nodup.of_map φ hnd
    have hset : σ.toFinset = Finset.Icc 1 p := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        rw [List.mem_toFinset] at hy
        exact Finset.mem_Icc.2 (hσ y hy)
      · rw [List.toFinset_card_of_nodup hndσ]
        have h1 : (σ.map φ).toFinset.card = (σ.map φ).length := List.toFinset_card_of_nodup hnd
        rw [hX, List.length_map, Finset.card_image_of_injOn hφ.injOn_Icc] at h1
        omega
    have hf : IsFoldSeq p σ := isFoldSeq_iff.2 ⟨hndσ, hset⟩
    refine ⟨σ, ?_, rfl⟩
    rw [Finset.mem_coe, mem_semiSeqs]
    exact ⟨hf, (hφ.semiSymmetric_iff hndσ hσ).1 hss⟩

/-- The complement of the first image of a split is the second image. -/
theorem Split.compl_image {N p q : Nat} {φ ψ : Nat → Nat} (h : Split N p q φ ψ) :
    Finset.Icc 1 N \ (Finset.Icc 1 p).image φ = (Finset.Icc 1 q).image ψ := by
  have hnd := (List.nodup_append.1 (h.cover.nodup_iff.2 (List.nodup_range' ..))).2.2
  have hc : ∀ x, x ∈ (List.range' 1 p).map φ ++ (List.range' 1 q).map ψ ↔
      x ∈ List.range' 1 N := fun x => h.cover.mem_iff
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨hx, hnot⟩
    rcases List.mem_append.1 ((hc x).2 (List.mem_range'_1.2 (by omega))) with h1 | h2
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h1
      rw [List.mem_range'_1] at hy
      exact absurd ⟨y, by omega, rfl⟩ hnot
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h2
      rw [List.mem_range'_1] at hy
      exact ⟨y, by omega, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hm : ψ y ∈ (List.range' 1 p).map φ ++ (List.range' 1 q).map ψ :=
      List.mem_append.2 (Or.inr (List.mem_map.2 ⟨y, List.mem_range'_1.2 (by omega), rfl⟩))
    have := List.mem_range'_1.1 ((hc _).1 hm)
    refine ⟨by omega, ?_⟩
    rintro ⟨z, hz, e⟩
    exact hnd (φ z) (List.mem_map.2 ⟨z, List.mem_range'_1.2 (by omega), rfl⟩) (ψ y)
      (List.mem_map.2 ⟨y, List.mem_range'_1.2 (by omega), rfl⟩) e

theorem WinEmb.image_mem_powersetCard {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ) :
    (Finset.Icc 1 p).image φ ∈ (Finset.Icc 1 N).powersetCard p := by
  rw [Finset.mem_powersetCard, Finset.card_image_of_injOn hφ.injOn_Icc]
  refine ⟨?_, by simp⟩
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [Finset.mem_Icc] at hy ⊢
  exact hφ.bound y hy.1 hy.2

/-- **Split prefix count.**  For a split `[1, N] = φ[1, p] ⊔ ψ[1, q]`, exactly `a(p) · a(q)`
semi-symmetric sequences start with the panels `φ[1, p]` (in some order).  Generalises
`card_class_prefix`. -/
theorem Split.card_prefix {N p q : Nat} {φ ψ : Nat → Nat} (h : Split N p q φ ψ) :
    ((semiSeqs N).filter (fun a => (a.take p).toFinset = (Finset.Icc 1 p).image φ)).card =
      semiCount p * semiCount q := by
  rw [card_prefix_eq h.emb₁.image_mem_powersetCard, g_winEmb h.emb₁, h.compl_image,
    g_winEmb h.emb₂]

/-! ## Antichain decomposition -/

theorem take_toFinset_subset {a : List Nat} {m n : Nat} (h : m ≤ n) :
    (a.take m).toFinset ⊆ (a.take n).toFinset := by
  intro x hx
  rw [List.mem_toFinset] at hx ⊢
  have e : a.take m = (a.take n).take m := by rw [List.take_take, Nat.min_eq_left h]
  rw [e] at hx
  exact List.mem_of_mem_take hx

/-- **Antichain decomposition.**  If `𝓕` is a family of subsets of `[1, N]` no two of which
are comparable under `⊆`, every sequence has at most one prefix set in `𝓕`, so
`a(N) = ∑_{X ∈ 𝓕} g(X) g([1, N] \ X) + #{sequences with no prefix set in 𝓕}`. -/
theorem semiCount_eq_sum_antichain {N : Nat} (𝓕 : Finset (Finset Nat))
    (hsub : ∀ X ∈ 𝓕, X ⊆ Finset.Icc 1 N)
    (hanti : ∀ X ∈ 𝓕, ∀ Y ∈ 𝓕, X ⊆ Y → X = Y) :
    semiCount N = (∑ X ∈ 𝓕, g N X * g N (Finset.Icc 1 N \ X)) +
      ((semiSeqs N).filter (fun a => ∀ X ∈ 𝓕, (a.take X.card).toFinset ≠ X)).card := by
  have hfib : ∀ X ∈ 𝓕, ((semiSeqs N).filter (fun a => (a.take X.card).toFinset = X)).card =
      g N X * g N (Finset.Icc 1 N \ X) :=
    fun X hX => card_prefix_eq (Finset.mem_powersetCard.2 ⟨hsub X hX, rfl⟩)
  rw [← Finset.sum_congr rfl hfib, ← Finset.card_biUnion]
  · have e1 : (semiSeqs N).filter (fun a => ∃ X ∈ 𝓕, (a.take X.card).toFinset = X) =
        𝓕.biUnion (fun X => (semiSeqs N).filter (fun a => (a.take X.card).toFinset = X)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · rintro ⟨ha, X, hX, e⟩; exact ⟨X, hX, ha, e⟩
      · rintro ⟨X, hX, ha, e⟩; exact ⟨ha, X, hX, e⟩
    have e2 : (semiSeqs N).filter (fun a => ¬ ∃ X ∈ 𝓕, (a.take X.card).toFinset = X) =
        (semiSeqs N).filter (fun a => ∀ X ∈ 𝓕, (a.take X.card).toFinset ≠ X) := by
      apply Finset.filter_congr
      intro a _
      simp
    rw [semiCount, ← Finset.card_filter_add_card_filter_not (s := semiSeqs N)
      (fun a => ∃ X ∈ 𝓕, (a.take X.card).toFinset = X), e1, e2]
  · intro X hX Y hY hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_filter] at ha hb
    rcases Nat.le_total X.card Y.card with hle | hle
    · have hXY : X ⊆ Y := by
        rw [← ha.2, ← hb.2]; exact take_toFinset_subset hle
      exact hne (hanti X hX Y hY hXY)
    · have hYX : Y ⊆ X := by
        rw [← ha.2, ← hb.2]; exact take_toFinset_subset hle
      exact hne (hanti Y hY X hX hYX).symm

/-- **Antichain of splits.**  If every member of the antichain `𝓕` is the first image of a
split `[1, N] = φ[1, p] ⊔ ψ[1, N - p]`, then
`a(N) = ∑_{X ∈ 𝓕} a(|X|) a(N - |X|) + #{sequences with no prefix set in 𝓕}`. -/
theorem semiCount_eq_sum_splits {N : Nat} (𝓕 : Finset (Finset Nat))
    (hsplit : ∀ X ∈ 𝓕, ∃ φ ψ, Split N X.card (N - X.card) φ ψ ∧
      X = (Finset.Icc 1 X.card).image φ)
    (hanti : ∀ X ∈ 𝓕, ∀ Y ∈ 𝓕, X ⊆ Y → X = Y) :
    semiCount N = (∑ X ∈ 𝓕, semiCount X.card * semiCount (N - X.card)) +
      ((semiSeqs N).filter (fun a => ∀ X ∈ 𝓕, (a.take X.card).toFinset ≠ X)).card := by
  have hsub : ∀ X ∈ 𝓕, X ⊆ Finset.Icc 1 N := by
    intro X hX
    obtain ⟨φ, ψ, h, e⟩ := hsplit X hX
    have := h.emb₁.image_mem_powersetCard
    rw [← e, Finset.mem_powersetCard] at this
    exact this.1
  rw [semiCount_eq_sum_antichain 𝓕 hsub hanti]
  congr 1
  apply Finset.sum_congr rfl
  intro X hX
  obtain ⟨φ, ψ, h, e⟩ := hsplit X hX
  conv_lhs => rw [e]
  rw [g_winEmb h.emb₁, h.compl_image, g_winEmb h.emb₂]

/-! ## The parity instance -/

/-- The parity class of `s ∈ {1, 2}` (odds for `s = 1`, evens for `s = 2`) as the image of
the class embedding `cls 2 s`. -/
def parCls (N s : Nat) : Finset Nat := (Finset.Icc 1 (ccount 2 s N)).image (cls 2 s)

theorem mem_parCls {N s x : Nat} (hs : 1 ≤ s) (hs2 : s ≤ 2) :
    x ∈ parCls N s ↔ 1 ≤ x ∧ x ≤ N ∧ x % 2 = s % 2 := by
  unfold parCls
  rw [Finset.mem_image]
  unfold cls ccount
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Finset.mem_Icc] at hy
    omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(x + 2 - s) / 2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩

theorem compl_parCls {N : Nat} : Finset.Icc 1 N \ parCls N 1 = parCls N 2 := by
  ext x
  rw [Finset.mem_sdiff, Finset.mem_Icc, mem_parCls (le_refl 1) (by omega),
    mem_parCls (by omega) (le_refl 2)]
  omega

theorem g_parCls {N s : Nat} (hs : 1 ≤ s) (hs2 : s ≤ 2) (hsN : s ≤ N) :
    g N (parCls N s) = semiCount (ccount 2 s N) :=
  g_winEmb (Live2.winEmb_res (by omega) hs hs2 hsN)

/-- **One-level parity decomposition.**  For `N ≥ 2`,
`a(N) = 2 a(⌊N/2⌋) a(⌈N/2⌉) + #{sequences whose prefix sets are never a full parity class}`. -/
theorem semiCount_eq_parity_add {N : Nat} (hN : 2 ≤ N) :
    semiCount N = 2 * (semiCount (N / 2) * semiCount ((N + 1) / 2)) +
      ((semiSeqs N).filter (fun a => ∀ X ∈ ({parCls N 1, parCls N 2} : Finset (Finset Nat)),
        (a.take X.card).toFinset ≠ X)).card := by
  have m1 : 1 ∈ parCls N 1 := (mem_parCls (le_refl 1) (by omega)).2 ⟨le_refl 1, by omega, rfl⟩
  have m1' : 1 ∉ parCls N 2 := fun h => by
    have := (mem_parCls (by omega) (le_refl 2)).1 h; omega
  have m2 : 2 ∈ parCls N 2 := (mem_parCls (by omega) (le_refl 2)).2 ⟨by omega, hN, rfl⟩
  have m2' : 2 ∉ parCls N 1 := fun h => by
    have := (mem_parCls (le_refl 1) (by omega)).1 h; omega
  have hne : parCls N 1 ≠ parCls N 2 := fun e => m1' (e ▸ m1)
  have hsub : ∀ X ∈ ({parCls N 1, parCls N 2} : Finset (Finset Nat)), X ⊆ Finset.Icc 1 N := by
    intro X hX
    rw [Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl <;> intro x hx
    · rw [mem_parCls (le_refl 1) (by omega)] at hx; exact Finset.mem_Icc.2 ⟨hx.1, hx.2.1⟩
    · rw [mem_parCls (by omega) (le_refl 2)] at hx; exact Finset.mem_Icc.2 ⟨hx.1, hx.2.1⟩
  have hanti : ∀ X ∈ ({parCls N 1, parCls N 2} : Finset (Finset Nat)),
      ∀ Y ∈ ({parCls N 1, parCls N 2} : Finset (Finset Nat)), X ⊆ Y → X = Y := by
    intro X hX Y hY hXY
    rw [Finset.mem_insert, Finset.mem_singleton] at hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · rfl
    · exact absurd (hXY m1) m1'
    · exact absurd (hXY m2) m2'
    · rfl
  have c2 : Finset.Icc 1 N \ parCls N 2 = parCls N 1 := by
    rw [← compl_parCls, Finset.sdiff_sdiff_eq_self]
    exact hsub _ (by simp)
  rw [semiCount_eq_sum_antichain _ hsub hanti, Finset.sum_pair hne, compl_parCls, c2,
    g_parCls (le_refl 1) (by omega) (by omega), g_parCls (by omega) (le_refl 2) hN]
  have e1 : ccount 2 1 N = (N + 1) / 2 := by unfold ccount; omega
  have e2 : ccount 2 2 N = N / 2 := by unfold ccount; omega
  rw [e1, e2]
  ring

/-! ## Parity classes and one doubling split together -/

/-- The doubling set `E = {x : x mod (2j+1) ∈ {2, 4, …, 2j}}` of `[1, (2j+1)n]`. -/
def resE (j n : Nat) : Finset Nat := (Finset.Icc 1 (j * n)).image (evenRes j)

theorem evenRes_ne {j y : Nat} (hj : 1 ≤ j) (hy : 1 ≤ y) :
    evenRes j y ≠ 1 ∧ evenRes j y ≠ 2 * j + 2 := by
  obtain ⟨u, v, hv, rfl⟩ : ∃ u v, v < j ∧ y = j * u + v + 1 :=
    ⟨(y - 1) / j, (y - 1) % j, Nat.mod_lt _ (by omega), by
      have := Nat.div_add_mod (y - 1) j; omega⟩
  rw [evenRes_eq hv]
  have hju : (u = 0 ∧ j * u = 0) ∨ (1 ≤ u ∧ j ≤ j * u) := by
    rcases Nat.eq_zero_or_pos u with h | h
    · exact Or.inl ⟨h, by rw [h, Nat.mul_zero]⟩
    · exact Or.inr ⟨h, Nat.le_mul_of_pos_right j h⟩
  omega

/-- The four sets odds, evens, `E`, `Eᶜ` of `[1, (2j+1)n]`. -/
def fam4 (j n : Nat) : Finset (Finset Nat) :=
  {parCls ((2 * j + 1) * n) 1, parCls ((2 * j + 1) * n) 2, resE j n,
    Finset.Icc 1 ((2 * j + 1) * n) \ resE j n}

/-- **Parity classes and the doubling split `{2, 4, …, 2j} mod 2j+1` together.**  For
`N = (2j+1)n` with `j ≥ 1`, `n ≥ 2`, the four sets (odds, evens, `E`, `Eᶜ`) form an antichain
of splits, so
`a(N) = 2 a(⌊N/2⌋) a(⌈N/2⌉) + 2 a(jn) a((j+1)n) + #{no prefix set among the four}`. -/
theorem semiCount_eq_parity_doubling_add {j n : Nat} (hj : 1 ≤ j) (hn : 2 ≤ n) :
    semiCount ((2 * j + 1) * n) =
      2 * (semiCount ((2 * j + 1) * n / 2) * semiCount (((2 * j + 1) * n + 1) / 2)) +
      2 * (semiCount (j * n) * semiCount ((j + 1) * n)) +
      ((semiSeqs ((2 * j + 1) * n)).filter (fun a =>
        ∀ X ∈ fam4 j n, (a.take X.card).toFinset ≠ X)).card := by
  set N := (2 * j + 1) * n with hN
  have hN2 : 2 * (2 * j + 1) ≤ N := by rw [hN, Nat.mul_comm 2]; exact Nat.mul_le_mul_left _ hn
  have hs := split_res hj n
  have hE : (Finset.Icc 1 (j * n)).image (evenRes j) = resE j n := rfl
  have cE : Finset.Icc 1 N \ resE j n = (Finset.Icc 1 ((j + 1) * n)).image (oddRes j) := by
    rw [← hE]; exact hs.compl_image
  have Esub : resE j n ⊆ Finset.Icc 1 N := by
    have := hs.emb₁.image_mem_powersetCard
    rw [Finset.mem_powersetCard] at this
    exact this.1
  -- membership facts
  have jn : j + 1 ≤ j * n := by nlinarith
  have r0 := evenRes_eq (j := j) (u := 0) (v := 0) (by omega)
  have r1 := evenRes_eq (j := j) (u := 1) (v := 0) (by omega)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add] at r0 r1
  have mE2 : 2 ∈ resE j n := Finset.mem_image.2 ⟨1, Finset.mem_Icc.2
    ⟨le_refl 1, by omega⟩, r0⟩
  have mE3 : 2 * j + 3 ∈ resE j n := Finset.mem_image.2 ⟨j + 1, Finset.mem_Icc.2
    ⟨by omega, jn⟩, by rw [r1]⟩
  have nE1 : 1 ∉ resE j n := by
    intro h; obtain ⟨y, hy, e⟩ := Finset.mem_image.1 h
    exact (evenRes_ne hj (Finset.mem_Icc.1 hy).1).1 e
  have nE2' : 2 * j + 2 ∉ resE j n := by
    intro h; obtain ⟨y, hy, e⟩ := Finset.mem_image.1 h
    exact (evenRes_ne hj (Finset.mem_Icc.1 hy).1).2 e
  have mC1 : 1 ∈ Finset.Icc 1 N \ resE j n :=
    Finset.mem_sdiff.2 ⟨Finset.mem_Icc.2 ⟨le_refl 1, by omega⟩, nE1⟩
  have mC2' : 2 * j + 2 ∈ Finset.Icc 1 N \ resE j n :=
    Finset.mem_sdiff.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, nE2'⟩
  have nC2 : 2 ∉ Finset.Icc 1 N \ resE j n := fun h => (Finset.mem_sdiff.1 h).2 mE2
  have nC3 : 2 * j + 3 ∉ Finset.Icc 1 N \ resE j n := fun h => (Finset.mem_sdiff.1 h).2 mE3
  have pO : ∀ x, x ∈ parCls N 1 ↔ 1 ≤ x ∧ x ≤ N ∧ x % 2 = 1 % 2 :=
    fun x => mem_parCls (le_refl 1) (by omega)
  have pE : ∀ x, x ∈ parCls N 2 ↔ 1 ≤ x ∧ x ≤ N ∧ x % 2 = 2 % 2 :=
    fun x => mem_parCls (by omega) (le_refl 2)
  have mO1 : 1 ∈ parCls N 1 := (pO 1).2 ⟨le_refl 1, by omega, rfl⟩
  have mO3 : 2 * j + 3 ∈ parCls N 1 := (pO _).2 ⟨by omega, by omega, by omega⟩
  have nO2 : 2 ∉ parCls N 1 := fun h => by have := (pO 2).1 h; omega
  have nO2' : 2 * j + 2 ∉ parCls N 1 := fun h => by have := (pO _).1 h; omega
  have mV2 : 2 ∈ parCls N 2 := (pE 2).2 ⟨by omega, by omega, rfl⟩
  have mV2' : 2 * j + 2 ∈ parCls N 2 := (pE _).2 ⟨by omega, by omega, by omega⟩
  have nV1 : 1 ∉ parCls N 2 := fun h => by have := (pE 1).1 h; omega
  have nV3 : 2 * j + 3 ∉ parCls N 2 := fun h => by have := (pE _).1 h; omega
  have Osub : parCls N 1 ⊆ Finset.Icc 1 N := fun x hx => by
    rw [pO] at hx; exact Finset.mem_Icc.2 ⟨hx.1, hx.2.1⟩
  have Vsub : parCls N 2 ⊆ Finset.Icc 1 N := fun x hx => by
    rw [pE] at hx; exact Finset.mem_Icc.2 ⟨hx.1, hx.2.1⟩
  -- the family
  have hsub : ∀ X ∈ fam4 j n, X ⊆ Finset.Icc 1 N := by
    intro X hX
    simp only [fam4, Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl | rfl
    exacts [Osub, Vsub, Esub, Finset.sdiff_subset]
  have hanti : ∀ X ∈ fam4 j n, ∀ Y ∈ fam4 j n, X ⊆ Y → X = Y := by
    intro X hX Y hY hXY
    simp only [fam4, Finset.mem_insert, Finset.mem_singleton] at hX hY
    rcases hX with rfl | rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact absurd (hXY mO1) nV1 | exact absurd (hXY mO1) nE1
      | exact absurd (hXY mO3) nC3 | exact absurd (hXY mV2) nO2
      | exact absurd (hXY mV2') nE2' | exact absurd (hXY mV2) nC2
      | exact absurd (hXY mE2) nO2 | exact absurd (hXY mE3) nV3
      | exact absurd (hXY mE2) nC2 | exact absurd (hXY mC2') nO2'
      | exact absurd (hXY mC1) nV1 | exact absurd (hXY mC1) nE1
  have n12 : parCls N 1 ≠ parCls N 2 := fun e => nV1 (e ▸ mO1)
  have n13 : parCls N 1 ≠ resE j n := fun e => nE1 (e ▸ mO1)
  have n14 : parCls N 1 ≠ Finset.Icc 1 N \ resE j n := fun e => nC3 (e ▸ mO3)
  have n23 : parCls N 2 ≠ resE j n := fun e => nE2' (e ▸ mV2')
  have n24 : parCls N 2 ≠ Finset.Icc 1 N \ resE j n := fun e => nC2 (e ▸ mV2)
  have n34 : resE j n ≠ Finset.Icc 1 N \ resE j n := fun e => nC2 (e ▸ mE2)
  have hsum : (∑ X ∈ fam4 j n, g N X * g N (Finset.Icc 1 N \ X)) =
      2 * (semiCount (N / 2) * semiCount ((N + 1) / 2)) +
      2 * (semiCount (j * n) * semiCount ((j + 1) * n)) := by
    unfold fam4
    rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto),
      Finset.sum_pair n34]
    have c2 : Finset.Icc 1 N \ parCls N 2 = parCls N 1 := by
      rw [← compl_parCls, Finset.sdiff_sdiff_eq_self Osub]
    rw [compl_parCls, c2, Finset.sdiff_sdiff_eq_self Esub, cE, ← hE, g_winEmb hs.emb₁,
      g_winEmb hs.emb₂, g_parCls (le_refl 1) (by omega) (by omega),
      g_parCls (by omega) (le_refl 2) (by omega)]
    have e1 : ccount 2 1 N = (N + 1) / 2 := by unfold ccount; omega
    have e2 : ccount 2 2 N = N / 2 := by unfold ccount; omega
    rw [e1, e2]
    ring
  rw [semiCount_eq_sum_antichain (fam4 j n) hsub hanti, hsum]

end Folds
