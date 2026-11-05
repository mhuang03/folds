import Folds.Blocks

/-!
# Generating valid fold sequences of every length

See `experiments/generate/NOTES.txt` for the paper version.

* `gen ch N` is the **recursive parity-block family**: at every node of the recursion
  (a residue class of `[1..N]` mod `2^d`, addressed by the list of its residue bits
  `p`, least significant first) the choice `ch p` decides whether the even or the odd
  half of the class comes first.  `gen_valid`: every member is a fold sequence that is
  **symmetric** (hence semi-symmetric) — for every `N` and every choice function.
* `gen_filter` (**truncation**): deleting the panels `> N` from `gen ch M` (`N ≤ M`)
  gives exactly `gen ch N`.  With `bitRev` the `k`-bit reversal and
  `gen_canon_pow : gen (fun _ => false) (2^k) = [bitRev k i + 1 | i < 2^k]`
  this gives `truncation`: the bit-reversal order of `[1..2^k]`, truncated to `≤ N`, is a
  symmetric and semi-symmetric fold sequence for every `N ≤ 2^k`.
* `genAt` computes the `i`-th entry of `gen ch N` in `O(log N)` steps (`genAt_eq`).
* `ladder` is the "exponentiation by squaring" (Montgomery ladder) construction: it
  carries the pair `(R(n), R(n+1))` of canonical sequences along the binary digits of
  `n`, with one parity-block step per digit (`ladder_eq`, `ladder_valid`).
-/

namespace Folds
namespace Gen

/-! ## The family -/

/-- The recursive parity-block sequence for the choice function `ch`.  `ch [] = true`:
evens first, `false`: odds first.  The odd panels `2y-1` form the subproblem with
choices `fun p => ch (false :: p)`, the even panels `2y` the one with
`fun p => ch (true :: p)`. -/
def gen (ch : List Bool → Bool) (N : Nat) : List Nat :=
  if N ≤ 1 then List.range' 1 N
  else if ch [] then
    (gen (fun p => ch (true :: p)) (N / 2)).map (scale 0) ++
      (gen (fun p => ch (false :: p)) ((N + 1) / 2)).map (scale 1)
  else
    (gen (fun p => ch (false :: p)) ((N + 1) / 2)).map (scale 1) ++
      (gen (fun p => ch (true :: p)) (N / 2)).map (scale 0)
termination_by N
decreasing_by all_goals omega

theorem gen_small {ch : List Bool → Bool} {N : Nat} (h : N ≤ 1) : gen ch N = List.range' 1 N := by
  rw [gen]; simp only [h, ↓reduceIte]

/-- The canonical (all odds-first) member. -/
abbrev canon : List Bool → Bool := fun _ => false

/-- The defining equation, valid for every `N` (also `N ≤ 1`). -/
theorem gen_unfold (ch : List Bool → Bool) (N : Nat) :
    gen ch N = if ch [] then
      (gen (fun p => ch (true :: p)) (N / 2)).map (scale 0) ++
        (gen (fun p => ch (false :: p)) ((N + 1) / 2)).map (scale 1)
    else
      (gen (fun p => ch (false :: p)) ((N + 1) / 2)).map (scale 1) ++
        (gen (fun p => ch (true :: p)) (N / 2)).map (scale 0) := by
  rcases Nat.lt_or_ge N 2 with h | h
  · have h01 : N = 0 ∨ N = 1 := by omega
    rcases h01 with rfl | rfl
    · rw [gen]; simp [gen]
    · rw [gen]; simp [gen, scale]
  · rw [gen]; simp only [show ¬N ≤ 1 by omega, ↓reduceIte]

theorem gen_canon_unfold (N : Nat) :
    gen canon N = (gen canon ((N + 1) / 2)).map (scale 1) ++ (gen canon (N / 2)).map (scale 0) := by
  rw [gen_unfold]; rfl

/-! ## Symmetric blocks -/

theorem symmetric_append_iff {N : Nat} {A B : List Nat} :
    Symmetric N (A ++ B) ↔
      Symmetric N A ∧ ∀ k (hk : k < B.length), SymStep N (A ++ B.take k) B[k] := by
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

theorem mem_map_scale {c : Nat} (hc : c ≤ 1) {T : List Nat} (hT : ∀ y ∈ T, 1 ≤ y) {z : Nat}
    (hz : 1 ≤ z) : scale c z ∈ T.map (scale c) ↔ z ∈ T := by
  constructor
  · intro h
    obtain ⟨y, hy, e⟩ := List.mem_map.1 h
    have := hT y hy
    have : y = z := by unfold scale at e; omega
    exact this ▸ hy
  · intro h; exact List.mem_map.2 ⟨z, h, rfl⟩

/-- Key step: on a background `U` that consists of panels of the *other* parity and either
contains all of them in `[1..N]` (`b = true`) or none (`b = false`), a step of the class-`c`
block is symmetric iff the corresponding step of the half-size strip is. -/
theorem symStep_scale {N c : Nat} (hc : c ≤ 1) {U T : List Nat} {j : Nat} (b : Prop)
    (hUpar : ∀ x ∈ U, (x + c) % 2 = 1)
    (hU : ∀ x, 1 ≤ x → x ≤ N → (x + c) % 2 = 1 → (x ∈ U ↔ b))
    (hT : ∀ y ∈ T, 1 ≤ y) (hj1 : 1 ≤ j) (hjn : j ≤ (N + c) / 2)
    (h : SymStep ((N + c) / 2) T j) :
    SymStep N (U ++ T.map (scale c)) (scale c j) := by
  intro d hd1 hd2
  have hr : d ≤ scale c j - 1 ∧ d ≤ N - scale c j := by
    unfold reach at hd2; omega
  simp only [List.mem_append]
  obtain ⟨e, he⟩ : ∃ e, d = 2 * e ∨ d = 2 * e + 1 := ⟨d / 2, by omega⟩
  rcases he with rfl | rfl
  · -- even distance: same class
    have he1 : 1 ≤ e := by omega
    have hl : scale c j - 2 * e = scale c (j - e) := by unfold scale at *; omega
    have hr' : scale c j + 2 * e = scale c (j + e) := by unfold scale at *; omega
    have nl : scale c (j - e) ∉ U := fun hx => by
      have := hUpar _ hx; unfold scale at this hr; omega
    have nr : scale c (j + e) ∉ U := fun hx => by
      have := hUpar _ hx; unfold scale at this hr; omega
    rw [hl, hr', mem_map_scale hc hT (by unfold scale at hr; omega),
      mem_map_scale hc hT (by omega)]
    have := h e he1 (by unfold reach scale at *; omega)
    simp only [nl, nr, false_or]; exact this
  · -- odd distance: both in the other class, both in `U` or both not
    have nl : scale c j - (2 * e + 1) ∉ T.map (scale c) := fun hx => by
      obtain ⟨y, _, ey⟩ := List.mem_map.1 hx; unfold scale at ey hr; omega
    have nr : scale c j + (2 * e + 1) ∉ T.map (scale c) := fun hx => by
      obtain ⟨y, _, ey⟩ := List.mem_map.1 hx; unfold scale at ey hr; omega
    simp only [nl, nr, or_false]
    rw [hU _ (by omega) (by omega) (by unfold scale at *; omega),
      hU _ (by omega) (by omega) (by unfold scale at *; omega)]

/-- **Symmetric parity blocks.**  If `σ` and `τ` are symmetric, so is the block sequence. -/
theorem symmetric_blocks {N c : Nat} (hc : c ≤ 1) {σ τ : List Nat}
    (hσ : IsFoldSeq ((N + c) / 2) σ) (hτ : IsFoldSeq ((N + (1 - c)) / 2) τ)
    (sσ : Symmetric ((N + c) / 2) σ) (sτ : Symmetric ((N + (1 - c)) / 2) τ) :
    Symmetric N (σ.map (scale c) ++ τ.map (scale (1 - c))) := by
  have bσ : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ (N + c) / 2 := fun y hy => (mem_range'_of_perm hσ).1 hy
  have bτ : ∀ y ∈ τ, 1 ≤ y ∧ y ≤ (N + (1 - c)) / 2 := fun y hy =>
    (mem_range'_of_perm hτ).1 hy
  rw [symmetric_append_iff]
  constructor
  · intro k hk
    simp only [List.length_map] at hk
    rw [List.getElem_map, ← List.map_take, ← List.nil_append (List.map _ (σ.take k))]
    have hm := bσ _ (List.getElem_mem hk)
    exact symStep_scale hc False (by simp) (by simp)
      (fun y hy => (bσ y (List.mem_of_mem_take hy)).1) hm.1 hm.2 (sσ k hk)
  · intro k hk
    simp only [List.length_map] at hk
    rw [List.getElem_map, ← List.map_take]
    have hm := bτ _ (List.getElem_mem hk)
    refine symStep_scale (by omega) True ?_ ?_
      (fun y hy => (bτ y (List.mem_of_mem_take hy)).1) hm.1 hm.2 (sτ k hk)
    · intro x hx
      have := (hσ.map_scale rfl).mem_iff.1 hx
      rw [mem_classList hc] at this; omega
    · intro x h1 h2 hpar
      simp only [iff_true]
      refine (hσ.map_scale rfl).mem_iff.2 ?_
      rw [mem_classList hc]; omega

/-! ## Validity of the whole family -/

theorem gen_valid_aux : ∀ (N : Nat) (ch : List Bool → Bool),
    IsFoldSeq N (gen ch N) ∧ Symmetric N (gen ch N)
  | N, ch => by
    rcases Nat.lt_or_ge N 2 with h | h
    · rw [gen_small (by omega)]
      refine ⟨List.Perm.refl _, ?_⟩
      have h01 : N = 0 ∨ N = 1 := by omega
      rcases h01 with rfl | rfl
      · intro k hk; simp at hk
      · intro k hk d hd1 hd2; simp [reach] at hd2; omega
    · have hE := gen_valid_aux (N / 2) (fun p => ch (true :: p))
      have hO := gen_valid_aux ((N + 1) / 2) (fun p => ch (false :: p))
      rw [gen_unfold]
      split
      · have e1 : N / 2 = (N + 0) / 2 := by simp
        have e2 : (N + 1) / 2 = (N + (1 - 0)) / 2 := by simp
        rw [e1] at hE; rw [e2] at hO
        exact ⟨IsFoldSeq.blocks (by omega) hE.1 hO.1,
          symmetric_blocks (by omega) hE.1 hO.1 hE.2 hO.2⟩
      · have e2 : N / 2 = (N + (1 - 1)) / 2 := by simp
        rw [e2] at hE
        exact ⟨IsFoldSeq.blocks (by omega) hO.1 hE.1,
          symmetric_blocks (by omega) hO.1 hE.1 hO.2 hE.2⟩
termination_by N => N
decreasing_by all_goals omega

/-- **Every member of the parity-block family is a symmetric and semi-symmetric fold
sequence**, for every `N` and every choice function `ch`. -/
theorem gen_valid (ch : List Bool → Bool) (N : Nat) :
    IsFoldSeq N (gen ch N) ∧ Symmetric N (gen ch N) ∧ SemiSymmetric N (gen ch N) :=
  ⟨(gen_valid_aux N ch).1, (gen_valid_aux N ch).2, (gen_valid_aux N ch).2.semiSymmetric⟩

theorem gen_bound {ch : List Bool → Bool} {N y : Nat} (h : y ∈ gen ch N) : 1 ≤ y ∧ y ≤ N :=
  (mem_range'_of_perm (gen_valid ch N).1).1 h

/-! ## Truncation -/

theorem filter_map_scale {c : Nat} (hc : c ≤ 1) (N : Nat) :
    ∀ L : List Nat, (∀ y ∈ L, 1 ≤ y) →
      (L.map (scale c)).filter (fun x => decide (x ≤ N)) =
        (L.filter (fun y => decide (y ≤ (N + c) / 2))).map (scale c)
  | [], _ => rfl
  | y :: L, h => by
    have hy := h y (by simp)
    have ih := filter_map_scale hc N L (fun z hz => h z (by simp [hz]))
    have e : decide (scale c y ≤ N) = decide (y ≤ (N + c) / 2) := by
      unfold scale; apply decide_eq_decide.2; omega
    simp only [List.map_cons, List.filter_cons, e]
    split <;> simp [ih]

/-- **Truncation, for the whole family.**  Deleting the panels `> N` from `gen ch M`
(`N ≤ M`) leaves exactly `gen ch N`. -/
theorem gen_filter : ∀ (M N : Nat) (ch : List Bool → Bool), N ≤ M →
    (gen ch M).filter (fun x => decide (x ≤ N)) = gen ch N
  | M, N, ch, hNM => by
    rcases Nat.lt_or_ge M 2 with h | h
    · have hM : gen ch M = List.range' 1 M := gen_small (by omega)
      have h01 : M = 0 ∨ M = 1 := by omega
      rcases h01 with rfl | rfl
      · have : N = 0 := by omega
        subst this; simp [hM]
      · rcases Nat.eq_zero_or_pos N with rfl | hN
        · simp [hM, gen]
        · have : N = 1 := by omega
          subst this; simp [hM]
    · have iE := gen_filter (M / 2) (N / 2) (fun p => ch (true :: p)) (by omega)
      have iO := gen_filter ((M + 1) / 2) ((N + 1) / 2) (fun p => ch (false :: p)) (by omega)
      have bE : ∀ y ∈ gen (fun p => ch (true :: p)) (M / 2), 1 ≤ y := fun y hy =>
        (gen_bound hy).1
      have bO : ∀ y ∈ gen (fun p => ch (false :: p)) ((M + 1) / 2), 1 ≤ y := fun y hy =>
        (gen_bound hy).1
      rw [gen_unfold ch M, gen_unfold ch N]
      split
      · rw [List.filter_append, filter_map_scale (by omega) N _ bE,
          filter_map_scale (by omega) N _ bO]
        simp only [Nat.add_zero, iE, iO]
      · rw [List.filter_append, filter_map_scale (by omega) N _ bE,
          filter_map_scale (by omega) N _ bO]
        simp only [Nat.add_zero, iE, iO]
termination_by M => M
decreasing_by all_goals omega

/-! ## Bit reversal -/

/-- `bitRev k i`: the `k`-bit reversal of `i < 2^k`.  The top bit of `i` (`i / 2^k`)
becomes bit 0, and the lower `k` bits (`i % 2^k`), reversed, move up by one place. -/
def bitRev : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, i => 2 * bitRev k (i % 2 ^ k) + i / 2 ^ k

example : (List.range 8).map (fun i => bitRev 3 i + 1) = [1, 5, 3, 7, 2, 6, 4, 8] := by
  decide

/-- The canonical family member at `2^k` is the bit-reversal order. -/
theorem gen_canon_pow : ∀ k : Nat,
    gen canon (2 ^ k) = (List.range (2 ^ k)).map (fun i => bitRev k i + 1)
  | 0 => by simp [gen, bitRev]
  | k + 1 => by
    rw [gen_canon_unfold]
    have e1 : (2 ^ (k + 1) + 1) / 2 = 2 ^ k := by rw [Nat.pow_succ]; omega
    have e2 : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [Nat.pow_succ]; omega
    have e3 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    rw [e1, e2, gen_canon_pow k, e3, List.range_add, List.map_append, List.map_map,
      List.map_map, List.map_map]
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    congr 1
    · apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      simp only [Function.comp, scale, bitRev, Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi]
      omega
    · apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      have m1 : (2 ^ k + i) % 2 ^ k = i := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt hi]
      have d1 : (2 ^ k + i) / 2 ^ k = 1 := by
        rw [Nat.add_comm, Nat.add_div_right _ hp, Nat.div_eq_of_lt hi]
      simp only [Function.comp, scale, bitRev, m1, d1]
      omega

/-- **Truncation theorem.**  The bit-reversal order of `[1..2^k]`, with the panels `> N`
deleted, is the canonical family member for `N`. -/
theorem truncation_eq {k N : Nat} (h : N ≤ 2 ^ k) :
    ((List.range (2 ^ k)).map (fun i => bitRev k i + 1)).filter (fun x => decide (x ≤ N)) =
      gen canon N := by
  rw [← gen_canon_pow, gen_filter _ _ _ h]

/-- **Truncation theorem** (validity): for every `N ≤ 2^k`, the truncated bit-reversal
order is a fold sequence that is symmetric and semi-symmetric. -/
theorem truncation {k N : Nat} (h : N ≤ 2 ^ k) :
    let a := ((List.range (2 ^ k)).map (fun i => bitRev k i + 1)).filter
      (fun x => decide (x ≤ N))
    IsFoldSeq N a ∧ Symmetric N a ∧ SemiSymmetric N a := by
  simp only [truncation_eq h]; exact gen_valid canon N

/-! ## Random access in `O(log N)` -/

/-- The `i`-th entry (0-based) of `gen ch N`, computed by descending one level per
recursion step (depth `⌈log₂ N⌉`). -/
def genAt (ch : List Bool → Bool) (N i : Nat) : Nat :=
  if N ≤ 1 then i + 1
  else if ch [] then
    if i < N / 2 then scale 0 (genAt (fun p => ch (true :: p)) (N / 2) i)
    else scale 1 (genAt (fun p => ch (false :: p)) ((N + 1) / 2) (i - N / 2))
  else
    if i < (N + 1) / 2 then scale 1 (genAt (fun p => ch (false :: p)) ((N + 1) / 2) i)
    else scale 0 (genAt (fun p => ch (true :: p)) (N / 2) (i - (N + 1) / 2))
termination_by N
decreasing_by all_goals omega

theorem length_gen (ch : List Bool → Bool) (N : Nat) : (gen ch N).length = N := by
  rw [(gen_valid ch N).1.length_eq]; simp

theorem genAt_eq : ∀ (N : Nat) (ch : List Bool → Bool) (i : Nat) (hi : i < N),
    (gen ch N)[i]'(by rw [length_gen]; exact hi) = genAt ch N i
  | N, ch, i, hi => by
    rcases Nat.lt_or_ge N 2 with h | h
    · have e1 : genAt ch N i = i + 1 := by
        rw [genAt]; simp only [show N ≤ 1 by omega, ↓reduceIte]
      simp only [gen_small (show N ≤ 1 by omega), List.getElem_range', e1]; omega
    · have hE := fun j hj => genAt_eq (N / 2) (fun p => ch (true :: p)) j hj
      have hO := fun j hj => genAt_eq ((N + 1) / 2) (fun p => ch (false :: p)) j hj
      have l1 := length_gen (fun p => ch (true :: p)) (N / 2)
      have l2 := length_gen (fun p => ch (false :: p)) ((N + 1) / 2)
      rw [genAt]
      simp only [gen_unfold ch N, show ¬N ≤ 1 by omega, ↓reduceIte]
      by_cases hc : ch [] = true
      · simp only [hc, ↓reduceIte]
        split
        · rw [List.getElem_append_left (by simp [l1]; omega), List.getElem_map, hE i (by omega)]
        · rw [List.getElem_append_right (by simp [l1]; omega), List.getElem_map]
          simp only [List.length_map, l1]
          rw [hO (i - N / 2) (by omega)]
      · simp only [hc, ↓reduceIte, Bool.false_eq_true]
        split
        · rw [List.getElem_append_left (by simp [l2]; omega), List.getElem_map, hO i (by omega)]
        · rw [List.getElem_append_right (by simp [l2]; omega), List.getElem_map]
          simp only [List.length_map, l2]
          rw [hE (i - (N + 1) / 2) (by omega)]
termination_by N => N
decreasing_by all_goals omega

/-! ## The ladder: exponentiation by squaring -/

/-- Odds-first parity blocks: `D A B = (2A - 1) ++ 2B`. -/
def D (A B : List Nat) : List Nat := A.map (scale 1) ++ B.map (scale 0)

/-- **Montgomery ladder.**  `ladder n = (R(n), R(n+1))`, computed from `ladder (n / 2)`
with one parity-block step, exactly as `x^n` is computed by repeated squaring:
`R(2m) = D(R m, R m)`, `R(2m+1) = D(R(m+1), R m)`, `R(2m+2) = D(R(m+1), R(m+1))`. -/
def ladder (n : Nat) : List Nat × List Nat :=
  if n = 0 then ([], [1])
  else
    let p := ladder (n / 2)
    if n % 2 = 0 then (D p.1 p.1, D p.2 p.1) else (D p.2 p.1, D p.2 p.2)
termination_by n
decreasing_by omega

theorem ladder_eq (n : Nat) : ladder n = (gen canon n, gen canon (n + 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ladder]; simp [gen]
  · have ih := ladder_eq (n / 2)
    rw [ladder]
    simp only [show n ≠ 0 by omega, ↓reduceIte, ih]
    rw [gen_canon_unfold n, gen_canon_unfold (n + 1)]
    unfold D
    rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
    · have e1 : (n + 1) / 2 = n / 2 := by omega
      have e2 : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
      simp only [h2, ↓reduceIte, e1, e2]
    · have e1 : (n + 1) / 2 = n / 2 + 1 := by omega
      have e2 : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
      simp only [h2, ↓reduceIte, e1, e2, Nat.one_ne_zero]
termination_by n
decreasing_by omega

/-- The ladder (`O(log N)` parity-block steps) produces a symmetric and semi-symmetric
fold sequence for every `N`. -/
theorem ladder_valid (N : Nat) :
    IsFoldSeq N (ladder N).1 ∧ Symmetric N (ladder N).1 ∧ SemiSymmetric N (ladder N).1 := by
  rw [ladder_eq]; exact gen_valid canon N

end Gen
end Folds
