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

end Folds
