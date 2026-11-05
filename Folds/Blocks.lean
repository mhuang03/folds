import Folds.Parity

/-!
# The parity-block construction

Write `scale c y = 2y - c`: `c = 0` gives the evens `2, 4, …, 2⌊N/2⌋`, `c = 1` the odds
`1, 3, …, 2⌈N/2⌉ - 1`.  Class `c` has `(N + c) / 2` elements (`⌊N/2⌋` evens,
`⌈N/2⌉` odds).

Main theorem (`semiSymmetric_blocks_iff`): for fold sequences `σ` of length `(N+c)/2`
and `τ` of length `(N+1-c)/2`, the fold sequence `σ.map (scale c) ++ τ.map (scale (1-c))`
of length `N` is semi-symmetric iff both `σ` and `τ` are.  With `c = 0` this is
"evens then odds", with `c = 1` "odds then evens".

Two key facts:
* (i) `semiStep_scale_iff`: restricted to class `c`, the window of `scale c j` in
  `[1..N]` is the scaled window of `j` in `[1..(N+c)/2]`.
* (ii) `class_balanced`: a complete parity class is balanced in the window of any panel
  of the other parity.

Converse (`prefix_class_semiSymmetric`): if a semi-symmetric fold sequence starts with
`(N+c)/2` panels of class `c`, the halves of that prefix form a semi-symmetric fold
sequence for `(N+c)/2`.
-/

namespace Folds

/-- `scale c y = 2y - c`; `c = 0` gives evens, `c = 1` odds. -/
def scale (c y : Nat) : Nat := 2 * y - c

/-- Inverse of `scale c` on class `c`. -/
def half (c x : Nat) : Nat := (x + c) / 2

/-- The panels of parity class `c` among `1..N`, in increasing order. -/
def classList (N c : Nat) : List Nat := (List.range' 1 ((N + c) / 2)).map (scale c)

/-! ## Splitting a sequence into two blocks -/

theorem semiSymmetric_append_iff {N : Nat} {A B : List Nat} :
    SemiSymmetric N (A ++ B) ↔
      SemiSymmetric N A ∧ ∀ k (hk : k < B.length), SemiStep N (A ++ B.take k) B[k] := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have := h k (by simp; omega)
      rwa [List.take_append_of_le_length (by omega), List.getElem_append_left hk] at this
    · have := h (A.length + k) (by simp; omega)
      rw [List.take_length_add_append, List.getElem_append_right (by omega)] at this
      simpa using this
  · rintro ⟨hA, hB⟩ k hk
    by_cases hkA : k < A.length
    · rw [List.take_append_of_le_length (by omega), List.getElem_append_left hkA]
      exact hA k hkA
    · obtain ⟨i, rfl⟩ : ∃ i, k = A.length + i := ⟨k - A.length, by omega⟩
      simp only [List.length_append] at hk
      have := hB i (by omega)
      rw [List.take_length_add_append]
      rw [List.getElem_append_right (by omega)]
      simpa using this

/-! ## Counting an interval in `[1..n]` -/

theorem countP_range'_interval (A B : Nat) :
    ∀ n, (List.range' 1 n).countP (fun y => decide (A ≤ y ∧ y ≤ B)) =
      min B n + 1 - max A 1
  | 0 => by simp; omega
  | n + 1 => by
    rw [List.range'_concat, List.countP_append, countP_range'_interval A B n]
    simp only [List.countP_cons, List.countP_nil]
    by_cases h : A ≤ 1 + n ∧ 1 + n ≤ B
    · simp [h]; omega
    · simp [h]; omega

/-! ## (i) Scaled windows -/

theorem scale_inj {c : Nat} (hc : c ≤ 1) {x y : Nat} (h : scale c x = scale c y) : x = y := by
  unfold scale at h; omega

/-- Key fact (i).  `U` is a set of already-bisected panels that is balanced around
`scale c j` (e.g. empty, or a complete class of the other parity). -/
theorem semiStep_scale_iff {N c : Nat} (hc : c ≤ 1) {U T : List Nat} {j : Nat}
    (hnd : (U ++ T.map (scale c)).Nodup) (hT : ∀ y ∈ T, 1 ≤ y)
    (hj1 : 1 ≤ j) (hjn : j ≤ (N + c) / 2)
    (hU : U.countP (fun x => decide (scale c j - reach N (scale c j) ≤ x ∧ x < scale c j)) =
      U.countP (fun x => decide (scale c j < x ∧ x ≤ scale c j + reach N (scale c j)))) :
    SemiStep N (U ++ T.map (scale c)) (scale c j) ↔ SemiStep ((N + c) / 2) T j := by
  have hndT : T.Nodup :=
    List.Pairwise.of_map (scale c) (fun a b h e => h (by rw [e]))
      (List.nodup_append.1 hnd).2.1
  unfold SemiStep
  rw [leftCount_eq hnd, rightCount_eq hnd, leftCount_eq hndT, rightCount_eq hndT,
    List.countP_append, List.countP_append, List.countP_map, List.countP_map]
  have L : T.countP ((fun x => decide (scale c j - reach N (scale c j) ≤ x ∧ x < scale c j))
        ∘ scale c) =
      T.countP (fun y => decide (j - reach ((N + c) / 2) j ≤ y ∧ y < j)) := by
    apply List.countP_congr; intro y hy; have := hT y hy
    simp only [Function.comp_apply, decide_eq_true_eq]; unfold scale reach; omega
  have R : T.countP ((fun x => decide (scale c j < x ∧ x ≤ scale c j + reach N (scale c j)))
        ∘ scale c) =
      T.countP (fun y => decide (j < y ∧ y ≤ j + reach ((N + c) / 2) j)) := by
    apply List.countP_congr; intro y hy; have := hT y hy
    simp only [Function.comp_apply, decide_eq_true_eq]; unfold scale reach; omega
  rw [L, R]; omega

/-! ## (ii) A complete class is balanced around a panel of the other parity -/

theorem class_balanced {N c : Nat} (hc : c ≤ 1) {U : List Nat} (hU : U.Perm (classList N c))
    {m : Nat} (hm1 : 1 ≤ m) (hmN : m ≤ N) (hpar : (m + c) % 2 = 1) :
    U.countP (fun x => decide (m - reach N m ≤ x ∧ x < m)) =
      U.countP (fun x => decide (m < x ∧ x ≤ m + reach N m)) := by
  rw [hU.countP_eq, hU.countP_eq]
  unfold classList
  rw [List.countP_map, List.countP_map]
  have L : (List.range' 1 ((N + c) / 2)).countP
        ((fun x => decide (m - reach N m ≤ x ∧ x < m)) ∘ scale c) =
      (List.range' 1 ((N + c) / 2)).countP
        (fun y => decide ((m - reach N m + c + 1) / 2 ≤ y ∧ y ≤ (m + c - 1) / 2)) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]; unfold scale reach; omega
  have R : (List.range' 1 ((N + c) / 2)).countP
        ((fun x => decide (m < x ∧ x ≤ m + reach N m)) ∘ scale c) =
      (List.range' 1 ((N + c) / 2)).countP
        (fun y => decide ((m + c + 2) / 2 ≤ y ∧ y ≤ (m + reach N m + c) / 2)) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]; unfold scale reach; omega
  rw [L, R, countP_range'_interval, countP_range'_interval]
  unfold reach; omega

/-! ## Fold-sequence bookkeeping -/

theorem nodup_classList {N c : Nat} (hc : c ≤ 1) : (classList N c).Nodup :=
  nodup_map_of_injOn (List.nodup_range' ..) fun _ _ _ _ e => scale_inj hc e

theorem mem_classList {N c x : Nat} (hc : c ≤ 1) :
    x ∈ classList N c ↔ 1 ≤ x ∧ x ≤ N ∧ (x + c) % 2 = 0 := by
  unfold classList scale
  simp only [List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨y, hy, rfl⟩; omega
  · intro h; exact ⟨(x + c) / 2, by omega, by omega⟩

theorem classList_append_perm {N c : Nat} (hc : c ≤ 1) :
    (classList N c ++ classList N (1 - c)).Perm (List.range' 1 N) := by
  rw [List.perm_ext_iff_of_nodup _ (List.nodup_range' ..)]
  · intro x
    simp only [List.mem_append, mem_classList hc, mem_classList (show 1 - c ≤ 1 by omega),
      List.mem_range'_1]
    omega
  · refine List.nodup_append.2 ⟨nodup_classList hc, nodup_classList (by omega), ?_⟩
    intro x hx y hy
    rw [mem_classList hc] at hx; rw [mem_classList (by omega)] at hy; omega

theorem IsFoldSeq.map_scale {n N c : Nat} {σ : List Nat} (hσ : IsFoldSeq n σ)
    (hn : n = (N + c) / 2) : (σ.map (scale c)).Perm (classList N c) := by
  subst hn; exact hσ.map _

/-- The block sequence is a fold sequence. -/
theorem IsFoldSeq.blocks {N c : Nat} (hc : c ≤ 1) {σ τ : List Nat}
    (hσ : IsFoldSeq ((N + c) / 2) σ) (hτ : IsFoldSeq ((N + (1 - c)) / 2) τ) :
    IsFoldSeq N (σ.map (scale c) ++ τ.map (scale (1 - c))) :=
  ((hσ.map_scale rfl).append (hτ.map_scale rfl)).trans (classList_append_perm hc)

/-- A single block: `σ.map (scale c)` (placed on an empty strip) is semi-symmetric for
`N` iff `σ` is semi-symmetric for `(N + c) / 2`. -/
theorem semiSymmetric_scale_iff {N c : Nat} (hc : c ≤ 1) {σ : List Nat}
    (hnd : σ.Nodup) (hσ : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ (N + c) / 2) :
    SemiSymmetric N (σ.map (scale c)) ↔ SemiSymmetric ((N + c) / 2) σ := by
  have hndm : (σ.map (scale c)).Nodup :=
    nodup_map_of_injOn hnd fun _ _ _ _ e => scale_inj hc e
  constructor
  · intro h k hk
    have := h k (by simpa using hk)
    rw [List.getElem_map, ← List.map_take, ← List.nil_append (List.map _ _)] at this
    have hm := hσ _ (List.getElem_mem hk)
    refine (semiStep_scale_iff hc ?_ (fun y hy => (hσ y (List.mem_of_mem_take hy)).1)
      hm.1 hm.2 (by simp)).1 this
    simpa [List.map_take] using take_nodup hndm k
  · intro h k hk
    simp only [List.length_map] at hk
    rw [List.getElem_map, ← List.map_take, ← List.nil_append (List.map _ _)]
    have hm := hσ _ (List.getElem_mem hk)
    refine (semiStep_scale_iff hc ?_ (fun y hy => (hσ y (List.mem_of_mem_take hy)).1)
      hm.1 hm.2 (by simp)).2 (h k hk)
    simpa [List.map_take] using take_nodup hndm k

/-! ## Main theorem -/

/-- **Parity blocks.**  `σ.map (scale c) ++ τ.map (scale (1 - c))` is semi-symmetric iff
`σ` and `τ` are.  `c = 0`: `σ.map (2·) ++ τ.map (2·-1)` with `σ` for `⌊N/2⌋` and `τ`
for `⌈N/2⌉`; `c = 1`: `σ.map (2·-1) ++ τ.map (2·)` with `σ` for `⌈N/2⌉`, `τ` for
`⌊N/2⌋`. -/
theorem semiSymmetric_blocks_iff {N c : Nat} (hc : c ≤ 1) {σ τ : List Nat}
    (hσ : IsFoldSeq ((N + c) / 2) σ) (hτ : IsFoldSeq ((N + (1 - c)) / 2) τ) :
    SemiSymmetric N (σ.map (scale c) ++ τ.map (scale (1 - c))) ↔
      SemiSymmetric ((N + c) / 2) σ ∧ SemiSymmetric ((N + (1 - c)) / 2) τ := by
  have hc' : 1 - c ≤ 1 := by omega
  have hall := nodup_of_foldSeq (hσ.blocks hc hτ)
  have bσ : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ (N + c) / 2 := fun y hy => (mem_range'_of_perm hσ).1 hy
  have bτ : ∀ y ∈ τ, 1 ≤ y ∧ y ≤ (N + (1 - c)) / 2 := fun y hy => (mem_range'_of_perm hτ).1 hy
  rw [semiSymmetric_append_iff, semiSymmetric_scale_iff hc (nodup_of_foldSeq hσ) bσ]
  apply and_congr Iff.rfl
  have step : ∀ k (hk : k < τ.length),
      SemiStep N (σ.map (scale c) ++ (τ.map (scale (1 - c))).take k)
          ((τ.map (scale (1 - c)))[k]'(by simpa using hk)) ↔
        SemiStep ((N + (1 - c)) / 2) (τ.take k) τ[k] := by
    intro k hk
    rw [List.getElem_map, ← List.map_take]
    have hm := bτ _ (List.getElem_mem hk)
    refine semiStep_scale_iff hc' ?_ (fun y hy => (bτ y (List.mem_of_mem_take hy)).1)
      hm.1 hm.2 ?_
    · have := take_nodup hall ((σ.map (scale c)).length + k)
      rw [List.take_length_add_append] at this; rwa [List.map_take]
    · apply class_balanced hc (hσ.map_scale rfl) <;> unfold scale <;> omega
  constructor
  · intro h k hk; exact (step k hk).1 (h k (by simpa using hk))
  · intro h k hk
    simp only [List.length_map] at hk
    exact (step k hk).2 (h k hk)

/-! ## Converse: a class-`c` prefix -/

theorem perm_range'_of_nodup_subset {n : Nat} {σ : List Nat} (hnd : σ.Nodup)
    (hsub : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ n) (hlen : σ.length = n) : IsFoldSeq n σ := by
  unfold IsFoldSeq
  rw [List.perm_ext_iff_of_nodup hnd (List.nodup_range' ..)]
  intro y
  rw [List.mem_range'_1]
  constructor
  · intro hy; have := hsub y hy; omega
  · intro hy
    refine Decidable.byContradiction fun hn => ?_
    have := List.Nodup.length_le_of_subset (l₁ := y :: σ) (l₂ := List.range' 1 n)
      (List.nodup_cons.2 ⟨hn, hnd⟩) (by
        intro x hx
        rw [List.mem_cons] at hx
        rw [List.mem_range'_1]
        rcases hx with rfl | hx
        · omega
        · have := hsub x hx; omega)
    simp at this; omega

/-- **Converse.**  If a semi-symmetric fold sequence for `N` starts with `(N + c) / 2`
panels of parity class `c`, then the halves of that prefix form a semi-symmetric fold
sequence for `(N + c) / 2`.  (So the prefix is exactly the class, and the number of ways
to build class `c` first is `a((N + c) / 2)`.) -/
theorem prefix_class_semiSymmetric {N c : Nat} (hc : c ≤ 1) {a : List Nat}
    (hf : IsFoldSeq N a) (h : SemiSymmetric N a)
    (hcls : ∀ x ∈ a.take ((N + c) / 2), (x + c) % 2 = 0) :
    IsFoldSeq ((N + c) / 2) ((a.take ((N + c) / 2)).map (half c)) ∧
      SemiSymmetric ((N + c) / 2) ((a.take ((N + c) / 2)).map (half c)) := by
  have hnd := nodup_of_foldSeq hf
  have hlen : a.length = N := by rw [hf.length_eq]; simp
  have bA : ∀ x ∈ a.take ((N + c) / 2), 1 ≤ x ∧ x ≤ N := fun x hx =>
    (mem_range'_of_perm hf).1 (List.mem_of_mem_take hx)
  have hndσ : ((a.take ((N + c) / 2)).map (half c)).Nodup :=
    nodup_map_of_injOn (take_nodup hnd _) fun x hx y hy e => by
      have := hcls x hx; have := hcls y hy; unfold half at e; omega
  have bσ : ∀ y ∈ (a.take ((N + c) / 2)).map (half c), 1 ≤ y ∧ y ≤ (N + c) / 2 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have := bA x hx; have := hcls x hx; unfold half; omega
  have hfold : IsFoldSeq ((N + c) / 2) ((a.take ((N + c) / 2)).map (half c)) :=
    perm_range'_of_nodup_subset hndσ bσ (by simp; omega)
  refine ⟨hfold, ?_⟩
  have e : ((a.take ((N + c) / 2)).map (half c)).map (scale c) = a.take ((N + c) / 2) := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id (a.take _)]
    apply List.map_congr_left
    intro x hx; have := bA x hx; have := hcls x hx
    simp only [Function.comp, half, scale, id]; omega
  rw [← semiSymmetric_scale_iff hc hndσ bσ, e]
  have := h
  rw [← List.take_append_drop ((N + c) / 2) a, semiSymmetric_append_iff] at this
  exact this.1

end Folds
