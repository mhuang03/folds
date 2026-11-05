import Folds.Extremal
import Folds.Counting

/-!
# Shifted parity blocks: an exact-type lower bound for `a(2n)`

For `N = 2n`, `n ≥ 3`, the shifted parity blocks of `Extremal.shifted_blocks`
(`σ` on `n - 1` panels through `shX`, then `τ` on `n + 1` panels through `shY`, with `τ`
placing `1` before its middle panel when `n` is even) are injective in `(σ, τ)` and
disjoint from both parity-block families (their first `n - 1` panels contain both `2` and
`2n - 1`).  Hence

* `semiCount_shifted_odd`:  `2 a(n)² + a(n-1) a(n+1) ≤ a(2n)` for odd `n ≥ 3`;
* `semiCount_shifted_even`: `4 a(n)² + a(n-1) a(n+1) ≤ 2 a(2n)` for even `n ≥ 4`
  (i.e. `a(2n) ≥ 2a(n)² + a(n-1)a(n+1)/2`; reversal maps the `τ` placing `1` after the
  middle onto those placing it before).

See `experiments/extremal/PROOFS.txt` (remarks after Thm 4).
-/

namespace Folds

/-- `τ` places panel `1` before its middle panel `n/2 + 1` (only required for even `n`). -/
def MidFirst (n : Nat) (τ : List Nat) : Prop :=
  n % 2 = 0 → ∀ k (hk : k < τ.length), τ[k] = n / 2 + 1 → 1 ∈ τ.take k

open Classical in
/-- Semi-symmetric sequences of the `(n+1)`-strip satisfying `MidFirst n`. -/
noncomputable def midSeqs (n : Nat) : Finset (List Nat) :=
  (semiSeqs (n + 1)).filter (MidFirst n)

theorem mem_midSeqs {n : Nat} {τ : List Nat} :
    τ ∈ midSeqs n ↔ τ ∈ semiSeqs (n + 1) ∧ MidFirst n τ := by
  classical
  unfold midSeqs; convert Finset.mem_filter

/-- The shifted parity-block map. -/
def shMap (n : Nat) (x : List Nat × List Nat) : List Nat :=
  x.1.map (shX (n / 2)) ++ x.2.map (shY (n / 2))

theorem shMap_mem {n : Nat} (hn : 2 ≤ n) {x : List Nat × List Nat}
    (hx : x ∈ semiSeqs (n - 1) ×ˢ midSeqs n) : shMap n x ∈ semiSeqs (2 * n) := by
  rw [Finset.mem_product, mem_semiSeqs, mem_midSeqs, mem_semiSeqs] at hx
  obtain ⟨⟨hσ, hσs⟩, ⟨hτ, hτs⟩, hmid⟩ := hx
  obtain ⟨hf, hs, -⟩ := shifted_blocks hn hσ hσs hτ hτs hmid
  exact mem_semiSeqs.2 ⟨hf, hs⟩

theorem shMap_injOn {n : Nat} :
    Set.InjOn (shMap n) (semiSeqs (n - 1) ×ˢ midSeqs n : Finset _) := by
  rintro ⟨σ, τ⟩ hp ⟨σ', τ'⟩ hp' e
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_semiSeqs,
    mem_midSeqs] at hp hp'
  have l1 : (σ.map (shX (n / 2))).length = (σ'.map (shX (n / 2))).length := by
    simp [hp.1.1.length_eq, hp'.1.1.length_eq]
  obtain ⟨e1, e2⟩ := List.append_inj e l1
  have i1 : σ = σ' := List.map_injective_iff.2 (fun _ _ h => shX_inj h) e1
  have i2 : τ = τ' := by
    have b : ∀ y ∈ τ, 1 ≤ y := fun y hy => ((mem_range'_of_perm hp.2.1.1).1 hy).1
    have b' : ∀ y ∈ τ', 1 ≤ y := fun y hy => ((mem_range'_of_perm hp'.2.1.1).1 hy).1
    clear e e1 l1 hp hp'
    induction τ generalizing τ' with
    | nil => cases τ' with
      | nil => rfl
      | cons _ _ => simp at e2
    | cons y s ih => cases τ' with
      | nil => simp at e2
      | cons y' s' =>
        simp only [List.map_cons, List.cons.injEq] at e2
        rw [shY_inj (b y (by simp)) (b' y' (by simp)) e2.1,
          ih s' e2.2 (fun z hz => b z (by simp [hz])) (fun z hz => b' z (by simp [hz]))]
  rw [i1, i2]

/-- The first `n - 1` panels of a shifted parity block sequence contain `2` and `2n - 1`,
so it is not a parity-block sequence. -/
theorem shMap_disjoint {n c : Nat} (hn : 3 ≤ n) (hc : c ≤ 1) :
    Disjoint ((semiSeqs ((2 * n + c) / 2) ×ˢ semiSeqs ((2 * n + (1 - c)) / 2)).image
        (blockMap c)) ((semiSeqs (n - 1) ×ˢ midSeqs n).image (shMap n)) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  simp only [Finset.mem_image, Finset.mem_product, mem_semiSeqs, mem_midSeqs] at hx hx'
  obtain ⟨⟨σ', τ'⟩, ⟨⟨hσ', -⟩, -⟩, rfl⟩ := hx
  obtain ⟨⟨σ, τ⟩, ⟨⟨hσ, -⟩, -⟩, e⟩ := hx'
  have l : σ.length = n - 1 := by rw [hσ.length_eq]; simp
  have l' : σ'.length = n := by rw [hσ'.length_eq, List.length_range']; omega
  have key : ∀ z, z ∈ σ.map (shX (n / 2)) → ∃ y, z = scale c y := by
    intro z hz
    have t1 : (shMap n (σ, τ)).take (n - 1) = σ.map (shX (n / 2)) := by
      unfold shMap; exact List.take_left' (by simp [l])
    have t2 : (blockMap c (σ', τ')).take (n - 1) = (σ'.map (scale c)).take (n - 1) := by
      unfold blockMap; exact List.take_append_of_le_length (by simp [l'])
    rw [← t1, e, t2] at hz
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hz)
    exact ⟨y, rfl⟩
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · obtain ⟨y, hy⟩ := key (2 * n - 1) (List.mem_map.2 ⟨n - 1,
      (mem_range'_of_perm hσ).2 (by omega), by unfold shX; split_ifs <;> omega⟩)
    unfold scale at hy; omega
  · obtain ⟨y, hy⟩ := key 2 (List.mem_map.2 ⟨1,
      (mem_range'_of_perm hσ).2 (by omega), by unfold shX; split_ifs <;> omega⟩)
    unfold scale at hy; omega

/-- **Parity blocks plus shifted blocks.**  For `n ≥ 3`:
`2 a(n)² + a(n-1) · #{τ valid on n+1 panels, MidFirst} ≤ a(2n)`. -/
theorem semiCount_shifted {n : Nat} (hn : 3 ≤ n) :
    2 * semiCount n ^ 2 + semiCount (n - 1) * (midSeqs n).card ≤ semiCount (2 * n) := by
  have c0 := Finset.card_image_of_injOn (blockMap_injOn (N := 2 * n) (c := 0) (by omega))
  have c1 := Finset.card_image_of_injOn (blockMap_injOn (N := 2 * n) (c := 1) (by omega))
  have c2 := Finset.card_image_of_injOn (shMap_injOn (n := n))
  have hsub : ((semiSeqs ((2 * n + 0) / 2) ×ˢ semiSeqs ((2 * n + (1 - 0)) / 2)).image
      (blockMap 0) ∪
      (semiSeqs ((2 * n + 1) / 2) ×ˢ semiSeqs ((2 * n + (1 - 1)) / 2)).image (blockMap 1)) ∪
      (semiSeqs (n - 1) ×ˢ midSeqs n).image (shMap n) ⊆ semiSeqs (2 * n) := by
    refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_ <;> intro x hx <;>
      rw [Finset.mem_image] at hx <;> obtain ⟨p, hp, rfl⟩ := hx
    · exact blockMap_mem (by omega) hp
    · exact blockMap_mem (by omega) hp
    · exact shMap_mem (by omega) hp
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2
      ⟨shMap_disjoint hn (by omega), shMap_disjoint hn (by omega)⟩),
    Finset.card_union_of_disjoint (blockMap_disjoint (by omega)), c0, c1, c2,
    Finset.card_product, Finset.card_product, Finset.card_product] at this
  unfold semiCount
  simp only [Nat.add_zero, Nat.sub_zero, Nat.sub_self] at this
  rw [show 2 * n / 2 = n by omega, show (2 * n + 1) / 2 = n by omega] at this
  rw [Nat.pow_two]; omega

/-- **Shifted-block lower bound, odd `n`.**  `2 a(n)² + a(n-1) a(n+1) ≤ a(2n)`. -/
theorem semiCount_shifted_odd {n : Nat} (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    2 * semiCount n ^ 2 + semiCount (n - 1) * semiCount (n + 1) ≤ semiCount (2 * n) := by
  have e : midSeqs n = semiSeqs (n + 1) := by
    ext τ; rw [mem_midSeqs]; exact ⟨fun h => h.1, fun h => ⟨h, fun h0 => by omega⟩⟩
  have := semiCount_shifted hn
  rw [e] at this; exact this

/-- At least half of the sequences of the `(n+1)`-strip place `1` before the middle panel
(reversal maps the others onto them). -/
theorem semiCount_le_two_midSeqs {n : Nat} (hn : 2 ≤ n) :
    semiCount (n + 1) ≤ 2 * (midSeqs n).card := by
  have hsub : semiSeqs (n + 1) ⊆ midSeqs n ∪ (midSeqs n).image List.reverse := by
    intro τ hτ
    have hτ' := mem_semiSeqs.1 hτ
    rcases before_or_reverse_before (nodup_of_foldSeq hτ'.1) (a := 1) (b := n / 2 + 1)
      ((mem_range'_of_perm hτ'.1).2 (by omega)) ((mem_range'_of_perm hτ'.1).2 (by omega))
      (by omega) with h | h
    · exact Finset.mem_union_left _ (mem_midSeqs.2 ⟨hτ, fun _ => h⟩)
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨τ.reverse, ?_, by simp⟩)
      exact mem_midSeqs.2 ⟨mem_semiSeqs.2 ⟨(List.reverse_perm τ).trans hτ'.1,
        SemiSymmetric.reverse hτ'.1 hτ'.2⟩, fun _ => h⟩
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have := Finset.card_image_le (s := midSeqs n) (f := List.reverse)
  unfold semiCount; omega

/-- **Shifted-block lower bound, even `n`.**  `4 a(n)² + a(n-1) a(n+1) ≤ 2 a(2n)`, i.e.
`a(2n) ≥ 2a(n)² + a(n-1)a(n+1)/2`. -/
theorem semiCount_shifted_even {n : Nat} (hn : 4 ≤ n) :
    4 * semiCount n ^ 2 + semiCount (n - 1) * semiCount (n + 1) ≤ 2 * semiCount (2 * n) := by
  have h1 := semiCount_shifted (n := n) (by omega)
  have h2 := Nat.mul_le_mul_left (semiCount (n - 1)) (semiCount_le_two_midSeqs (n := n)
    (by omega))
  have : semiCount (n - 1) * (2 * (midSeqs n).card) =
      2 * (semiCount (n - 1) * (midSeqs n).card) := Nat.mul_left_comm _ _ _
  omega

end Folds
