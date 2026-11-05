import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Folds.Blocks

/-!
# Counting semi-symmetric fold sequences (uses Mathlib)

`semiSeqs N` is the `Finset` of semi-symmetric fold sequences of length `N` and
`semiCount N = a(N)` its cardinality.

* `semiCount_blocks`: `2 · a(⌊N/2⌋) · a(⌈N/2⌉) ≤ a(N)` for `N ≥ 2`
  (the two parity-block orders give disjoint injective families).
* `semiCount_even`: `2 · a(n)² ≤ a(2n)`, `semiCount_odd`: `2 · a(n) · a(n+1) ≤ a(2n+1)`.
* `semiCount_ge_pow`: `2 ^ (N - 1) ≤ a(N)` for `N ≥ 1`.
* `card_class_prefix`: exactly `a((N+c)/2) · a((N+1-c)/2)` semi-symmetric sequences
  start with the whole parity class `c`.
-/

namespace Folds

/-- The semi-symmetric fold sequences of length `N`. -/
def semiSeqs (N : Nat) : Finset (List Nat) :=
  (List.range' 1 N).permutations.toFinset.filter (SemiSymmetric N)

/-- `a(N)`, the number of semi-symmetric fold sequences of length `N`. -/
def semiCount (N : Nat) : Nat := (semiSeqs N).card

theorem mem_semiSeqs {N : Nat} {a : List Nat} :
    a ∈ semiSeqs N ↔ IsFoldSeq N a ∧ SemiSymmetric N a := by
  simp [semiSeqs, List.mem_permutations, IsFoldSeq]

/-- The parity-block map: `(σ, τ) ↦ σ.map (scale c) ++ τ.map (scale (1 - c))`. -/
def blockMap (c : Nat) (p : List Nat × List Nat) : List Nat :=
  p.1.map (scale c) ++ p.2.map (scale (1 - c))

theorem map_scale_injective {c : Nat} (hc : c ≤ 1) :
    Function.Injective (List.map (scale c)) :=
  List.map_injective_iff.2 fun _ _ e => scale_inj hc e

theorem blockMap_mem {N c : Nat} (hc : c ≤ 1) {p : List Nat × List Nat}
    (hp : p ∈ semiSeqs ((N + c) / 2) ×ˢ semiSeqs ((N + (1 - c)) / 2)) :
    blockMap c p ∈ semiSeqs N := by
  rw [Finset.mem_product, mem_semiSeqs, mem_semiSeqs] at hp
  rw [mem_semiSeqs]
  exact ⟨hp.1.1.blocks hc hp.2.1,
    (semiSymmetric_blocks_iff hc hp.1.1 hp.2.1).2 ⟨hp.1.2, hp.2.2⟩⟩

theorem blockMap_injOn {N c : Nat} (hc : c ≤ 1) :
    Set.InjOn (blockMap c)
      (semiSeqs ((N + c) / 2) ×ˢ semiSeqs ((N + (1 - c)) / 2) : Finset _) := by
  rintro ⟨σ, τ⟩ hp ⟨σ', τ'⟩ hp' e
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_semiSeqs] at hp hp'
  have l1 : (σ.map (scale c)).length = (σ'.map (scale c)).length := by
    simp [hp.1.1.length_eq, hp'.1.1.length_eq]
  obtain ⟨e1, e2⟩ := List.append_inj e l1
  simp only at e1 e2
  rw [map_scale_injective hc e1, map_scale_injective (by omega) e2]

theorem blockMap_disjoint {N : Nat} (hN : 2 ≤ N) :
    Disjoint ((semiSeqs ((N + 0) / 2) ×ˢ semiSeqs ((N + (1 - 0)) / 2)).image (blockMap 0))
      ((semiSeqs ((N + 1) / 2) ×ˢ semiSeqs ((N + (1 - 1)) / 2)).image (blockMap 1)) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  simp only [Finset.mem_image, Finset.mem_product, mem_semiSeqs] at hx hx'
  obtain ⟨⟨σ, τ⟩, ⟨⟨hσ, -⟩, -⟩, rfl⟩ := hx
  obtain ⟨⟨σ', τ'⟩, ⟨⟨hσ', -⟩, -⟩, e⟩ := hx'
  have l : σ.length = (N + 0) / 2 := by rw [hσ.length_eq]; simp
  have l' : σ'.length = (N + 1) / 2 := by rw [hσ'.length_eq]; simp
  obtain ⟨y, s, rfl⟩ : ∃ y s, σ = y :: s := by
    cases σ with
    | nil => simp at l; omega
    | cons y s => exact ⟨y, s, rfl⟩
  obtain ⟨y', s', rfl⟩ : ∃ y s, σ' = y :: s := by
    cases σ' with
    | nil => simp at l'; omega
    | cons y s => exact ⟨y, s, rfl⟩
  have hy' : 1 ≤ y' := ((mem_range'_of_perm hσ').1 (by simp)).1
  simp only [blockMap, List.map_cons, List.cons_append, List.cons.injEq] at e
  have := e.1
  unfold scale at this
  omega

/-- **Parity-block lower bound.** `2 · a(⌊N/2⌋) · a(⌈N/2⌉) ≤ a(N)` for `N ≥ 2`. -/
theorem semiCount_blocks {N : Nat} (hN : 2 ≤ N) :
    2 * (semiCount (N / 2) * semiCount ((N + 1) / 2)) ≤ semiCount N := by
  have c0 := Finset.card_image_of_injOn (blockMap_injOn (N := N) (c := 0) (by omega))
  have c1 := Finset.card_image_of_injOn (blockMap_injOn (N := N) (c := 1) (by omega))
  have hsub : (semiSeqs ((N + 0) / 2) ×ˢ semiSeqs ((N + (1 - 0)) / 2)).image (blockMap 0) ∪
      (semiSeqs ((N + 1) / 2) ×ˢ semiSeqs ((N + (1 - 1)) / 2)).image (blockMap 1) ⊆
      semiSeqs N := by
    apply Finset.union_subset <;> intro x hx <;> rw [Finset.mem_image] at hx <;>
      obtain ⟨p, hp, rfl⟩ := hx
    · exact blockMap_mem (by omega) hp
    · exact blockMap_mem (by omega) hp
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (blockMap_disjoint hN), c0, c1,
    Finset.card_product, Finset.card_product] at this
  unfold semiCount
  simp only [Nat.add_zero, Nat.sub_zero, Nat.sub_self] at this
  rw [Nat.mul_comm (semiSeqs ((N + 1) / 2)).card] at this
  omega

theorem semiCount_even {n : Nat} (hn : 1 ≤ n) : 2 * semiCount n ^ 2 ≤ semiCount (2 * n) := by
  have := semiCount_blocks (N := 2 * n) (by omega)
  rw [show 2 * n / 2 = n by omega, show (2 * n + 1) / 2 = n by omega] at this
  rw [Nat.pow_two]; exact this

theorem semiCount_odd {n : Nat} (hn : 1 ≤ n) :
    2 * (semiCount n * semiCount (n + 1)) ≤ semiCount (2 * n + 1) := by
  have := semiCount_blocks (N := 2 * n + 1) (by omega)
  rwa [show (2 * n + 1) / 2 = n by omega, show (2 * n + 1 + 1) / 2 = n + 1 by omega] at this

theorem semiCount_one_pos : 1 ≤ semiCount 1 :=
  Finset.card_pos.2 ⟨[1], mem_semiSeqs.2 ⟨by decide, by decide⟩⟩

/-- **Exponential lower bound.** `2 ^ (N - 1) ≤ a(N)` for `N ≥ 1`. -/
theorem semiCount_ge_pow : ∀ N, 1 ≤ N → 2 ^ (N - 1) ≤ semiCount N
  | 0, h => absurd h (by omega)
  | 1, _ => semiCount_one_pos
  | N + 2, _ => by
    have hb := semiCount_blocks (N := N + 2) (by omega)
    have h1 := semiCount_ge_pow ((N + 2) / 2) (by omega)
    have h2 := semiCount_ge_pow ((N + 2 + 1) / 2) (by omega)
    have e : N + 2 - 1 = 1 + ((N + 2) / 2 - 1) + ((N + 2 + 1) / 2 - 1) := by omega
    rw [e, Nat.pow_add, Nat.pow_add, Nat.pow_one]
    calc 2 * 2 ^ ((N + 2) / 2 - 1) * 2 ^ ((N + 2 + 1) / 2 - 1)
        = 2 * (2 ^ ((N + 2) / 2 - 1) * 2 ^ ((N + 2 + 1) / 2 - 1)) := by rw [Nat.mul_assoc]
      _ ≤ 2 * (semiCount ((N + 2) / 2) * semiCount ((N + 2 + 1) / 2)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2)
      _ ≤ semiCount (N + 2) := hb
  termination_by N => N
  decreasing_by all_goals omega

/-! ## Exact count of sequences that start with a full parity class -/

/-- If a fold sequence starts with `(N + c) / 2` panels of class `c`, it is
`blockMap c (σ, τ)` for the halves `σ`, `τ` of its two blocks, and both are fold
sequences. -/
theorem eq_blockMap_of_class_prefix {N c : Nat} (hc : c ≤ 1) {a : List Nat}
    (hf : IsFoldSeq N a) (h : SemiSymmetric N a)
    (hcls : ∀ x ∈ a.take ((N + c) / 2), (x + c) % 2 = 0) :
    ∃ σ τ, IsFoldSeq ((N + c) / 2) σ ∧ IsFoldSeq ((N + (1 - c)) / 2) τ ∧
      a = blockMap c (σ, τ) := by
  obtain ⟨hσ, -⟩ := prefix_class_semiSymmetric hc hf h hcls
  have hnd := nodup_of_foldSeq hf
  have hlen : a.length = N := by rw [hf.length_eq]; simp
  have bA : ∀ x ∈ a, 1 ≤ x ∧ x ≤ N := fun x hx => (mem_range'_of_perm hf).1 hx
  have eσ : ((a.take ((N + c) / 2)).map (half c)).map (scale c) = a.take ((N + c) / 2) := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id (a.take _)]
    apply List.map_congr_left
    intro x hx; have := bA x (List.mem_of_mem_take hx); have := hcls x hx
    simp only [Function.comp, half, scale, id]; omega
  have hperm := hσ.map_scale (N := N) (c := c) rfl
  rw [eσ] at hperm
  -- every panel after the prefix has the other parity
  have hdrop : ∀ x ∈ a.drop ((N + c) / 2), (x + (1 - c)) % 2 = 0 := by
    intro x hx
    have bx := bA x (List.mem_of_mem_drop hx)
    refine Decidable.byContradiction fun hpar => ?_
    have hxc : x ∈ classList N c := (mem_classList hc).2 ⟨bx.1, bx.2, by omega⟩
    have hxt := hperm.symm.subset hxc
    have hdisj := (List.nodup_append.1 ((List.take_append_drop ((N + c) / 2) a).symm ▸ hnd)).2.2
    exact hdisj x hxt x hx rfl
  have hndτ : ((a.drop ((N + c) / 2)).map (half (1 - c))).Nodup :=
    nodup_map_of_injOn (hnd.sublist (List.drop_sublist _ _)) fun x hx y hy e => by
      have := hdrop x hx; have := hdrop y hy; unfold half at e; omega
  have bτ : ∀ y ∈ (a.drop ((N + c) / 2)).map (half (1 - c)),
      1 ≤ y ∧ y ≤ (N + (1 - c)) / 2 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have := bA x (List.mem_of_mem_drop hx); have := hdrop x hx; unfold half; omega
  have hτ : IsFoldSeq ((N + (1 - c)) / 2) ((a.drop ((N + c) / 2)).map (half (1 - c))) :=
    perm_range'_of_nodup_subset hndτ bτ (by simp; omega)
  have eτ : ((a.drop ((N + c) / 2)).map (half (1 - c))).map (scale (1 - c)) =
      a.drop ((N + c) / 2) := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id (a.drop _)]
    apply List.map_congr_left
    intro x hx; have := bA x (List.mem_of_mem_drop hx); have := hdrop x hx
    simp only [Function.comp, half, scale, id]; omega
  refine ⟨_, _, hσ, hτ, ?_⟩
  simp only [blockMap, eσ, eτ, List.take_append_drop]

/-- **Exact parity-block count.**  The number of semi-symmetric fold sequences of length
`N` whose first `(N + c) / 2` panels all have parity class `c` (evens for `c = 0`, odds
for `c = 1`) is `a((N + c) / 2) · a((N + 1 - c) / 2)`.  In particular the number of ways
to bisect the whole class `c` first is `a((N + c) / 2)`, and then the other class can be
completed in `a((N + 1 - c) / 2)` ways regardless of how the first block was built. -/
theorem card_class_prefix {N c : Nat} (hc : c ≤ 1) :
    ((semiSeqs N).filter (fun a => ∀ x ∈ a.take ((N + c) / 2), (x + c) % 2 = 0)).card =
      semiCount ((N + c) / 2) * semiCount ((N + (1 - c)) / 2) := by
  have e : (semiSeqs N).filter (fun a => ∀ x ∈ a.take ((N + c) / 2), (x + c) % 2 = 0) =
      (semiSeqs ((N + c) / 2) ×ˢ semiSeqs ((N + (1 - c)) / 2)).image (blockMap c) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨ha, hcls⟩
      rw [mem_semiSeqs] at ha
      obtain ⟨σ, τ, hσ, hτ, rfl⟩ := eq_blockMap_of_class_prefix hc ha.1 ha.2 hcls
      have := (semiSymmetric_blocks_iff hc hσ hτ).1 ha.2
      exact ⟨(σ, τ), Finset.mem_product.2 ⟨mem_semiSeqs.2 ⟨hσ, this.1⟩,
        mem_semiSeqs.2 ⟨hτ, this.2⟩⟩, rfl⟩
    · rintro ⟨⟨σ, τ⟩, hp, rfl⟩
      refine ⟨blockMap_mem hc hp, ?_⟩
      have hσ := (mem_semiSeqs.1 (Finset.mem_product.1 hp).1).1
      have hl : (σ.map (scale c)).length = (N + c) / 2 := by
        rw [List.length_map, hσ.length_eq]; simp
      intro x hx
      simp only [blockMap] at hx
      rw [List.take_left' hl] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := ((mem_range'_of_perm hσ).1 hy).1
      unfold scale; omega
  rw [e, Finset.card_image_of_injOn (blockMap_injOn hc), Finset.card_product]
  rfl

end Folds
