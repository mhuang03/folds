import Folds.Parity

/-!
# Reversal ∘ mirror

`revMirror N a = (a.map (N + 1 - ·)).reverse`.  It maps semi-symmetric fold sequences to
semi-symmetric fold sequences and is an involution on fold sequences.  A fixed point
satisfies `a[N-1-k] = N + 1 - a[k]`; for `N ≡ 3 (mod 4)` there is none
(`revMirror_no_fixed`), because the middle panel would have to sit at index
`(N-1)/2`, which is odd, contradicting `middle_index_even`.
-/

namespace Folds

def revMirror (N : Nat) (a : List Nat) : List Nat := (a.map (N + 1 - ·)).reverse

theorem IsFoldSeq.mirror {N : Nat} {a : List Nat} (hf : IsFoldSeq N a) :
    IsFoldSeq N (a.map (N + 1 - ·)) := by
  have hnd := nodup_of_foldSeq hf
  unfold IsFoldSeq
  rw [List.perm_ext_iff_of_nodup _ (List.nodup_range' ..)]
  · intro x
    simp only [List.mem_map, List.mem_range'_1, mem_range'_of_perm hf]
    constructor
    · rintro ⟨y, hy, rfl⟩; omega
    · intro hx; exact ⟨N + 1 - x, by omega, by omega⟩
  · exact nodup_map_of_injOn hnd fun x hx y hy e => by
      rw [mem_range'_of_perm hf] at hx hy; omega

theorem IsFoldSeq.revMirror {N : Nat} {a : List Nat} (hf : IsFoldSeq N a) :
    IsFoldSeq N (revMirror N a) :=
  (List.reverse_perm _).trans hf.mirror

theorem SemiSymmetric.revMirror {N : Nat} {a : List Nat} (hf : IsFoldSeq N a)
    (h : SemiSymmetric N a) : SemiSymmetric N (revMirror N a) :=
  (h.mirror hf).reverse hf.mirror

/-- `revMirror N` is an involution on lists with entries `≤ N` (in particular on fold
sequences). -/
theorem revMirror_revMirror {N : Nat} {a : List Nat} (h : ∀ x ∈ a, x ≤ N) :
    revMirror N (revMirror N a) = a := by
  unfold revMirror
  rw [List.map_reverse, List.reverse_reverse, List.map_map]
  conv => rhs; rw [← List.map_id a]
  apply List.map_congr_left
  intro x hx; have := h x hx; simp; omega

/-- A fixed point of `revMirror` satisfies `a[N-1-k] = N + 1 - a[k]`. -/
theorem revMirror_fixed_getElem {N : Nat} {a : List Nat} (hfix : revMirror N a = a)
    (hle : ∀ x ∈ a, x ≤ N) {k : Nat} (hk : k < a.length) :
    a[a.length - 1 - k]'(by omega) = N + 1 - a[k] := by
  have hlen : (revMirror N a).length = a.length := by simp [revMirror]
  have e : (revMirror N a)[k]'(by omega) = a[k] := by simp only [hfix]
  simp only [revMirror, List.getElem_reverse, List.getElem_map, List.length_map] at e
  have := hle _ (List.getElem_mem (show a.length - 1 - k < a.length by omega))
  omega

/-- No semi-symmetric fold sequence is fixed by reversal ∘ mirror when `N ≡ 3 (mod 4)`. -/
theorem revMirror_no_fixed {N : Nat} (hN : N % 4 = 3) {a : List Nat} (hf : IsFoldSeq N a)
    (h : SemiSymmetric N a) : revMirror N a ≠ a := by
  intro hfix
  obtain ⟨n, rfl⟩ : ∃ n, N = 2 * n + 1 := ⟨N / 2, by omega⟩
  have hnd := nodup_of_foldSeq hf
  have hlen : a.length = 2 * n + 1 := by rw [hf.length_eq]; simp
  have hmem : n + 1 ∈ a := (mem_range'_of_perm hf).2 ⟨by omega, by omega⟩
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.1 hmem
  have h1 := revMirror_fixed_getElem hfix (fun x hx => ((mem_range'_of_perm hf).1 hx).2) hk
  rw [hke] at h1
  have h2 : a.length - 1 - k = k := by
    have : a[a.length - 1 - k]'(by omega) = a[k] := by rw [h1, hke]; omega
    exact (List.Nodup.getElem_inj hnd).1 this
  have h3 := middle_index_even hf h hk hke
  omega

end Folds
