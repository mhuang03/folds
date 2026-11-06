import Folds.SymParity

/-!
# Structure of symmetric (3-AP-free) fold sequences: the merge theorem

See `experiments/symstruct/PROOFS.txt`.  Fix a 3-AP-free permutation `a = w :: tl` of
`[1..N]`.  Call the entries of the parity of `w` the `D`-entries and the others the
`C`-entries.  A `D`-value `y` and a `C`-value `u` are **linked** when they lie in a common
3-term progression inside `[1, N]`, i.e. `2y - u ∈ [1, N]` or `2u - y ∈ [1, N]`.

* `merge_iff` (**merge theorem**): `a` is 3-AP-free iff its `D`-subsequence and its
  `C`-subsequence are 3-AP-free and every linked pair has the `D`-entry first.  So a
  3-AP-free permutation is exactly a shuffle of two 3-AP-free permutations of the two
  parity classes in which `D` precedes `C` on every linked pair.
* `not_linked_of_bef`: a `C`-entry placed before a `D`-entry is never linked to it.
* `parity_sort`: sorting a 3-AP-free permutation by parity (`D`-subsequence, then
  `C`-subsequence) keeps it 3-AP-free.  (This is the map onto the Davis–Entringer–
  Graham–Simmons parity-block permutations whose fibres give
  `θ(N) = Σ_{σ,τ} P(σ,τ)`.)
-/

namespace Folds
namespace SymStructure

open SymParity
open scoped List

/-- `y` and `u` (of different parities) lie in a common 3-term progression inside
`[1, N]`: either `y` is the middle (`2y - u ∈ [1, N]`) or `u` is (`2u - y ∈ [1, N]`). -/
def Linked (N y u : ℕ) : Prop := (u < 2 * y ∧ 2 * y ≤ N + u) ∨ (y < 2 * u ∧ 2 * u ≤ N + y)

/-- A 3-element sublist all of whose entries satisfy `p` is a sublist of the filter. -/
theorem sublist3_filter {a : List ℕ} {p : ℕ → Bool} {x y z : ℕ} (h : [x, y, z] <+ a)
    (hx : p x) (hy : p y) (hz : p z) : [x, y, z] <+ a.filter p := by
  have := h.filter p
  simpa [List.filter_cons, hx, hy, hz] using this

/-- **Merge theorem.**  For a permutation `a = w :: tl` of `[1..N]`: `a` is 3-AP-free iff
its two parity subsequences are 3-AP-free and on every linked pair the entry of the
parity of `w` comes first. -/
theorem merge_iff {N : ℕ} {a : List ℕ} {w : ℕ} {tl : List ℕ} (ha : a = w :: tl)
    (hnd : a.Nodup) (hI : ∀ v, v ∈ a ↔ 1 ≤ v ∧ v ≤ N) :
    APF a ↔ APF (a.filter (fun v => decide (v % 2 = w % 2))) ∧
      APF (a.filter (fun v => decide (v % 2 ≠ w % 2))) ∧
      ∀ y u, y ∈ a → u ∈ a → y % 2 = w % 2 → u % 2 ≠ w % 2 → Linked N y u → Bef a y u := by
  constructor
  · intro hap
    refine ⟨hap.sublist List.filter_sublist, hap.sublist List.filter_sublist, ?_⟩
    intro y u hy hu hyw huw hl
    exact bef_of_window ha hnd hI hap ((hI u).1 hu) ((hI y).1 hy) huw (by omega) hl
  · rintro ⟨hD, hC, hor⟩ x y z hs e
    have hx : x ∈ a := hs.subset (by simp)
    have hy : y ∈ a := hs.subset (by simp)
    have hz : z ∈ a := hs.subset (by simp)
    have hxI := (hI x).1 hx
    have hyI := (hI y).1 hy
    have hzI := (hI z).1 hz
    have hxy : Bef a x y := (show [x, y] <+ [x, y, z] by simp).trans hs
    have hyz : Bef a y z := (show [y, z] <+ [x, y, z] by simp).trans hs
    by_cases hpy : x % 2 = y % 2
    · -- all three have the same parity
      by_cases hw : y % 2 = w % 2
      · exact hD x y z (sublist3_filter hs (by simp; omega) (by simp; omega) (by simp; omega)) e
      · exact hC x y z (sublist3_filter hs (by simp; omega) (by simp; omega) (by simp; omega)) e
    · by_cases hw : y % 2 = w % 2
      · -- the middle `y` is a `D`-entry, linked to the `C`-entry `x`
        have h := hor y x hy hx hw (by omega) (Or.inl ⟨by omega, by omega⟩)
        exact bef_asymm hnd hxy h
      · -- the middle `y` is a `C`-entry, linked to the `D`-entry `z`
        have h := hor z y hz hy (by omega) hw (Or.inr ⟨by omega, by omega⟩)
        exact bef_asymm hnd hyz h

/-- In a 3-AP-free permutation, a `C`-entry `u` placed before a `D`-entry `y` is not linked
to it: `2y - u ∉ [1, N]` and `2u - y ∉ [1, N]`. -/
theorem not_linked_of_bef {N : ℕ} {a : List ℕ} {w : ℕ} {tl : List ℕ} (ha : a = w :: tl)
    (hnd : a.Nodup) (hI : ∀ v, v ∈ a ↔ 1 ≤ v ∧ v ≤ N) (hap : APF a) {y u : ℕ}
    (hyw : y % 2 = w % 2) (huw : u % 2 ≠ w % 2) (h : Bef a u y) : ¬ Linked N y u := by
  intro hl
  have := ((merge_iff ha hnd hI).1 hap).2.2 y u (bef_mem h).2 (bef_mem h).1 hyw huw hl
  exact bef_asymm hnd h this

theorem bef_append_left {l₁ l₂ : List ℕ} {x y : ℕ} (h : Bef l₁ x y) : Bef (l₁ ++ l₂) x y :=
  h.trans (List.sublist_append_left _ _)

theorem bef_append_right {l₁ l₂ : List ℕ} {x y : ℕ} (h : Bef l₂ x y) : Bef (l₁ ++ l₂) x y :=
  h.trans (List.sublist_append_right _ _)

theorem bef_append_mid {l₁ l₂ : List ℕ} {x y : ℕ} (hx : x ∈ l₁) (hy : y ∈ l₂) :
    Bef (l₁ ++ l₂) x y := by
  have : [x] ++ [y] <+ l₁ ++ l₂ :=
    List.Sublist.append (List.singleton_sublist.2 hx) (List.singleton_sublist.2 hy)
  simpa using this

/-- **Parity sort.**  Moving all entries of the parity of the first entry to the front
(keeping the order inside each class) maps 3-AP-free permutations of `[1..N]` to
3-AP-free permutations (the parity-block permutations). -/
theorem parity_sort {N : ℕ} {a : List ℕ} {w : ℕ} {tl : List ℕ} (ha : a = w :: tl)
    (hnd : a.Nodup) (hI : ∀ v, v ∈ a ↔ 1 ≤ v ∧ v ≤ N) (hap : APF a) :
    APF (a.filter (fun v => decide (v % 2 = w % 2)) ++
      a.filter (fun v => decide (v % 2 ≠ w % 2))) := by
  set D := a.filter (fun v => decide (v % 2 = w % 2)) with hDdef
  set C := a.filter (fun v => decide (v % 2 ≠ w % 2)) with hCdef
  obtain ⟨hD, hC, -⟩ := (merge_iff ha hnd hI).1 hap
  have hDt : D = w :: tl.filter (fun v => decide (v % 2 = w % 2)) := by
    rw [hDdef, ha]; simp
  have hb : D ++ C = w :: (tl.filter (fun v => decide (v % 2 = w % 2)) ++ C) := by
    rw [hDt]; rfl
  have hperm : (D ++ C).Perm a := by
    rw [hDdef, hCdef]
    have := List.filter_append_perm (fun v => decide (v % 2 = w % 2)) a
    refine List.Perm.trans ?_ this
    apply List.Perm.append_left
    rw [List.filter_congr (q := fun v => !decide (v % 2 = w % 2))]
    intro v _; simp
  have hnd' : (D ++ C).Nodup := hperm.nodup_iff.2 hnd
  have hI' : ∀ v, v ∈ D ++ C ↔ 1 ≤ v ∧ v ≤ N := fun v => by rw [hperm.mem_iff]; exact hI v
  have hfD : (D ++ C).filter (fun v => decide (v % 2 = w % 2)) = D := by
    rw [List.filter_append]
    have h1 : D.filter (fun v => decide (v % 2 = w % 2)) = D :=
      List.filter_eq_self.2 (fun v hv => by rw [hDdef, List.mem_filter] at hv; exact hv.2)
    have h2 : C.filter (fun v => decide (v % 2 = w % 2)) = [] :=
      List.filter_eq_nil_iff.2 (fun v hv => by
        rw [hCdef, List.mem_filter] at hv; simp at hv ⊢; exact hv.2)
    rw [h1, h2, List.append_nil]
  have hfC : (D ++ C).filter (fun v => decide (v % 2 ≠ w % 2)) = C := by
    rw [List.filter_append]
    have h1 : C.filter (fun v => decide (v % 2 ≠ w % 2)) = C :=
      List.filter_eq_self.2 (fun v hv => by rw [hCdef, List.mem_filter] at hv; exact hv.2)
    have h2 : D.filter (fun v => decide (v % 2 ≠ w % 2)) = [] :=
      List.filter_eq_nil_iff.2 (fun v hv => by
        rw [hDdef, List.mem_filter] at hv; simp at hv ⊢; exact hv.2)
    rw [h1, h2, List.nil_append]
  refine (merge_iff hb hnd' hI').2 ⟨by rw [hfD]; exact hD, by rw [hfC]; exact hC, ?_⟩
  intro y u _ _ hyw huw _
  apply bef_append_mid
  · rw [hDdef, List.mem_filter]; exact ⟨(hperm.mem_iff).1 ‹y ∈ D ++ C›, by simpa using hyw⟩
  · rw [hCdef, List.mem_filter]; exact ⟨(hperm.mem_iff).1 ‹u ∈ D ++ C›, by simpa using huw⟩

/-- The fold-sequence form of the merge theorem. -/
theorem merge_iff_apFree {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a) {w : ℕ} {tl : List ℕ}
    (ha : a = w :: tl) :
    APF a ↔ APF (a.filter (fun v => decide (v % 2 = w % 2))) ∧
      APF (a.filter (fun v => decide (v % 2 ≠ w % 2))) ∧
      ∀ y u, y ∈ a → u ∈ a → y % 2 = w % 2 → u % 2 ≠ w % 2 → Linked N y u → Bef a y u := by
  have hnd : a.Nodup := hf.nodup_iff.2 (List.nodup_range' ..)
  have hI : ∀ v, v ∈ a ↔ 1 ≤ v ∧ v ≤ N := fun v => by rw [mem_range'_of_perm hf]
  exact merge_iff ha hnd hI

end SymStructure
end Folds
