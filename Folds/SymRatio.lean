import Folds.SymStructure2
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The ratio `θ(n) / (2 θ(⌊n/2⌋) θ(⌈n/2⌉))`: the window (locality) theorem

See `experiments/symratio/PROOFS.txt`.  The merge count `P(σ, τ) = (shuffles N p σ τ).card`
of `SymStructure2.card_symSeqs_eq_sum` depends only on a window of `12` entries: the last
`6` entries of `σ` and the first `6` entries of `τ`.

* `run_prefix`: in a 3-AP-free permutation of `[1, N]` whose first entry has parity `q`, the
  first `⌊(N+q)/2⌋ - 6` entries have parity `q` (the sharp form of Sharma's ends theorem,
  with the size of the class instead of `⌊N/2⌋`).
* `shuffle_decomp`: every allowed shuffle `a` of `σ` and `τ` is
  `lift(σ.take k) ++ w ++ lift(τ.drop 6)` with `k = |σ| - 6`, where `w` (`12` entries) is an
  allowed shuffle of the windows `σ.drop k` and `τ.take 6`.
* `card_shuffles_eq_win` (**Theorem W**): `P(σ, τ) = Π_N(σ.drop k, τ.take 6)`, where
  `Π = (winShuffles N p S T).card` counts the interleavings of the two lifted windows in which
  every linked pair has its `D`-entry first.
* `card_shuffles_congr`: hence `P(σ, τ) = P(σ', τ')` whenever the windows agree.
* `card_symSeqs_eq_win_sum`: the exact identity `θ(N) = Σ_p Σ_σ Σ_τ Π_N(window)` (`N ≥ 14`).
* `card_symSeqs_eq_stat_sum`: `θ(N) = Σ_p Σ_S Σ_T α_p(S) β_p(T) Π_N(S, T)`, where `α_p(S)`
  counts the `σ` with tail window `S` and `β_p(T)` the `τ` with head window `T`: `θ(N)` (and
  `r(N)`) is a bilinear form in the window statistics of the two halves.
* `shuffle_head`, `shuffle_tail`: the head window of a shuffle is the lifted head window of
  `σ`, and its tail window is the lifted tail window of `τ` (`|σ|, |τ| ≥ 12`): the window
  statistics propagate exactly under the merge (the joint recursion `J` of PROOFS.txt).
* `card_window_eq_sum` (**Theorem J**): the number of 3-AP-free permutations of `[1, N]`
  with a given head window `H` and tail window `T` is
  `Σ_p Σ_{σ : lift(head σ) = H} Σ_{τ : lift(tail τ) = T} Π_N(tail σ, head τ)` (`N ≥ 24`).
-/

set_option linter.unusedSectionVars false

namespace Folds
namespace SymRatio

open SymParity SymStructure SymStructure2
open scoped List

/-- The allowed interleavings of the lifted windows `S` (parity `p`) and `T` (parity `1-p`):
every linked pair `(y, u)` (`y` of parity `p`) has `y` first. -/
def winShuffles (N p : ℕ) (S T : List ℕ) : Finset (List ℕ) :=
  (S.map (lift p) ++ T.map (lift (1 - p))).permutations.toFinset.filter fun w =>
    w.filter (fun v => decide (v % 2 = p)) = S.map (lift p) ∧
      w.filter (fun v => decide (v % 2 ≠ p)) = T.map (lift (1 - p)) ∧
      ∀ y ∈ w, ∀ u ∈ w, y % 2 = p → u % 2 ≠ p → Linked N y u → Bef w y u

/-! ## Opening runs -/

/-- In a 3-AP-free permutation of `[1, N]` with first entry `w`, every entry at index
`k < ⌊(N + w mod 2)/2⌋ - 6` has the parity of `w`. -/
theorem run_prefix {N w : ℕ} {tl : List ℕ} (hP : IsPermOf N (w :: tl)) (hap : APF (w :: tl))
    {k : ℕ} (hk : k < (w :: tl).length) (hkK : k + 6 < (N + w % 2) / 2) :
    (w :: tl)[k] % 2 = w % 2 := by
  by_contra hu
  have h6 := D_after_le_six rfl hP hap hk hu
  have hσ := (cls_isPermOf (p := w % 2) (by omega) hP).length
  have hsplit : w :: tl = ((w :: tl).take k ++ [(w :: tl)[k]]) ++ (w :: tl).drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hk,
      List.take_append_drop]
  rw [hsplit, cls_append, cls_append, List.length_append, List.length_append] at hσ
  have h1 : (cls (w % 2) ((w :: tl).take k)).length ≤ k := by
    rw [cls, List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)
  have h2 : (cls (w % 2) [(w :: tl)[k]]).length = 0 := by
    simp [cls, hu]
  have h3 : (cls (w % 2) ((w :: tl).drop (k + 1))).length =
      (((w :: tl).drop (k + 1)).filter (fun v => decide (v % 2 = w % 2))).length := by
    simp [cls]
  omega

/-- The first `⌊(N + w mod 2)/2⌋ - 6` entries all have the parity of the first entry `w`. -/
theorem run_take {N w : ℕ} {tl : List ℕ} (hP : IsPermOf N (w :: tl)) (hap : APF (w :: tl)) :
    ∀ v ∈ (w :: tl).take ((N + w % 2) / 2 - 6), v % 2 = w % 2 := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  rw [List.getElem_take]
  rw [List.length_take] at hi
  exact run_prefix hP hap (by omega) (by omega)

/-- If the first `k` entries of `l` satisfy `P`, they are also the first `k` entries of the
`P`-subsequence. -/
theorem filter_take_of_forall {l : List ℕ} {P : ℕ → Bool} {k : ℕ}
    (h : ∀ v ∈ l.take k, P v = true) : (l.filter P).take k = l.take k := by
  conv_lhs => rw [← List.take_append_drop k l]
  rw [List.filter_append, List.filter_eq_self.2 h]
  rcases le_or_gt k l.length with h1 | h1
  · rw [List.take_append_of_le_length (by simp; omega), List.take_take, min_self]
  · rw [List.drop_eq_nil_of_le h1.le, List.filter_nil, List.append_nil, List.take_take,
      min_self]

/-! ## Lifted classes -/

theorem mem_map_lift {M p : ℕ} (hp : p ≤ 1) {σ : List ℕ} (hσ : IsPermOf M σ) {v : ℕ} :
    v ∈ σ.map (lift p) ↔ 1 ≤ v ∧ v ≤ 2 * M - p ∧ v % 2 = p := by
  constructor
  · intro hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv
    have := (hσ.2 r).1 hr
    simp only [lift]; omega
  · rintro ⟨h1, h2, h3⟩
    refine List.mem_map.2 ⟨half v, (hσ.2 _).2 ?_, lift_half h3⟩
    simp only [half]; omega

theorem lift_union_isPermOf {N p : ℕ} (hp : p ≤ 1) {σ τ : List ℕ}
    (hσ : IsPermOf ((N + p) / 2) σ) (hτ : IsPermOf ((N + 1 - p) / 2) τ) :
    IsPermOf N (σ.map (lift p) ++ τ.map (lift (1 - p))) := by
  refine ⟨List.nodup_append.2 ⟨hσ.1.map (lift_inj hp), hτ.1.map (lift_inj (by omega)), ?_⟩, ?_⟩
  · intro x hx y hy hxy
    subst hxy
    have := ((mem_map_lift hp hσ).1 hx).2.2
    have := ((mem_map_lift (by omega) hτ).1 hy).2.2
    omega
  · intro v
    rw [List.mem_append, mem_map_lift hp hσ, mem_map_lift (by omega) hτ]
    omega

theorem map_lift_mod {M p : ℕ} (hp : p ≤ 1) {σ : List ℕ} (hσ : IsPermOf M σ) {l : List ℕ}
    (hl : l <+ σ) : ∀ v ∈ l.map (lift p), v % 2 = p := by
  intro v hv
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv
  exact lift_mod hp ((hσ.2 r).1 (hl.subset hr)).1

theorem filter_all_eq {l : List ℕ} {p : ℕ} (h : ∀ v ∈ l, v % 2 = p) :
    l.filter (fun v => decide (v % 2 = p)) = l ∧ l.filter (fun v => decide (v % 2 ≠ p)) = [] :=
  ⟨List.filter_eq_self.2 fun v hv => by simpa using h v hv,
    List.filter_eq_nil_iff.2 fun v hv => by simpa using h v hv⟩

theorem filter_none_eq {l : List ℕ} {p : ℕ} (h : ∀ v ∈ l, v % 2 ≠ p) :
    l.filter (fun v => decide (v % 2 = p)) = [] ∧ l.filter (fun v => decide (v % 2 ≠ p)) = l :=
  ⟨List.filter_eq_nil_iff.2 fun v hv => by simpa using h v hv,
    List.filter_eq_self.2 fun v hv => by simpa using h v hv⟩

/-- Order inside a contiguous block. -/
theorem bef_of_infix {X w Y : List ℕ} (hnd : (X ++ w ++ Y).Nodup) {y u : ℕ} (hy : y ∈ w)
    (hu : u ∈ w) (h : Bef (X ++ w ++ Y) y u) : Bef w y u := by
  have hsub : w <+ X ++ w ++ Y := (List.infix_append X w Y).sublist
  have hwnd : w.Nodup := hnd.sublist hsub
  rcases bef_total hwnd hy hu (bef_ne hnd h) with h' | h'
  · exact h'
  · exact absurd (h'.trans hsub) (bef_asymm hnd h)

/-! ## The decomposition of a shuffle -/

section decomp
variable {N p : ℕ} {σ τ : List ℕ}

/-- The prefix `lift(σ.take k)`, `k = |σ| - 6`. -/
abbrev pre (p : ℕ) (σ : List ℕ) : List ℕ := (σ.take (σ.length - 6)).map (lift p)
/-- The suffix `lift(τ.drop 6)`. -/
abbrev suf (p : ℕ) (τ : List ℕ) : List ℕ := (τ.drop 6).map (lift (1 - p))

theorem mem_shuffles {N p : ℕ} {σ τ a : List ℕ} :
    a ∈ shuffles N p σ τ ↔ a.Perm (List.range' 1 N) ∧ a.headD 0 % 2 = p ∧
      a.filter (fun v => decide (v % 2 = p)) = σ.map (lift p) ∧
      a.filter (fun v => decide (v % 2 ≠ p)) = τ.map (lift (1 - p)) ∧
      ∀ y ∈ a, ∀ u ∈ a, y % 2 = p → u % 2 ≠ p → Linked N y u → Bef a y u := by
  simp only [shuffles, Finset.mem_filter, List.mem_toFinset, List.mem_permutations]

theorem mem_winShuffles {N p : ℕ} {S T w : List ℕ} :
    w ∈ winShuffles N p S T ↔ w.Perm (S.map (lift p) ++ T.map (lift (1 - p))) ∧
      w.filter (fun v => decide (v % 2 = p)) = S.map (lift p) ∧
      w.filter (fun v => decide (v % 2 ≠ p)) = T.map (lift (1 - p)) ∧
      ∀ y ∈ w, ∀ u ∈ w, y % 2 = p → u % 2 ≠ p → Linked N y u → Bef w y u := by
  simp only [winShuffles, Finset.mem_filter, List.mem_toFinset, List.mem_permutations]

variable (hp : p ≤ 1) (hσ : σ ∈ symSeqs ((N + p) / 2)) (hτ : τ ∈ symSeqs ((N + 1 - p) / 2))
  (hD : 7 ≤ (N + p) / 2) (hC : 6 ≤ (N + 1 - p) / 2)
include hp hσ hτ hD hC

theorem lens : σ.length = (N + p) / 2 ∧ τ.length = (N + 1 - p) / 2 :=
  ⟨(mem_symSeqs_iff.1 hσ).1.length, (mem_symSeqs_iff.1 hτ).1.length⟩

theorem pre_mod : ∀ v ∈ pre p σ, v % 2 = p :=
  map_lift_mod hp (mem_symSeqs_iff.1 hσ).1 (List.take_sublist _ _)

theorem suf_mod : ∀ v ∈ suf p τ, v % 2 ≠ p := by
  intro v hv
  have := map_lift_mod (p := 1 - p) (by omega) (mem_symSeqs_iff.1 hτ).1 (List.drop_sublist _ _)
    v hv
  omega

theorem sigma_split : σ.map (lift p) = pre p σ ++ (σ.drop (σ.length - 6)).map (lift p) := by
  rw [← List.map_append, List.take_append_drop]

theorem tau_split : τ.map (lift (1 - p)) = (τ.take 6).map (lift (1 - p)) ++ suf p τ := by
  rw [← List.map_append, List.take_append_drop]

/-- **Decomposition of a shuffle**: `a = lift(σ.take k) ++ w ++ lift(τ.drop 6)`, with `w`
the `12` middle entries. -/
theorem shuffle_decomp {a : List ℕ} (ha : a ∈ shuffles N p σ τ) :
    a = pre p σ ++ ((a.drop (σ.length - 6)).take 12 ++ suf p τ) := by
  obtain ⟨hl1, hl2⟩ := lens hp hσ hτ hD hC
  obtain ⟨hperm, hh, hfD, hfC, hlk⟩ := mem_shuffles.1 ha
  obtain ⟨hσP, hσA⟩ := mem_symSeqs_iff.1 hσ
  obtain ⟨hτP, hτA⟩ := mem_symSeqs_iff.1 hτ
  have hP : IsPermOf N a := isPermOf_iff_isFoldSeq.2 hperm
  have hN : 1 ≤ N := by omega
  have hap : APF a := ((shuffle_key hp hσA (fun r hr => ((hσP.2 r).1 hr).1) hτA
    (fun r hr => ((hτP.2 r).1 hr).1) hP hN hh).2 ⟨hfD, hfC, hlk⟩).1
  have hlen : a.length = N := hP.length
  -- the prefix
  have htake : a.take (σ.length - 6) = pre p σ := by
    obtain ⟨w, tl, rfl⟩ : ∃ w tl, a = w :: tl := by
      cases a with
      | nil => simp at hlen; omega
      | cons w tl => exact ⟨w, tl, rfl⟩
    have hw : w % 2 = p := by simpa using hh
    have hrun := run_take hP hap
    rw [hw, ← hl1] at hrun
    rw [← filter_take_of_forall (P := fun v => decide (v % 2 = p))
      (fun v hv => by simpa using hrun v hv), hfD]
    exact List.map_take.symm
  -- the suffix, through the reversal
  have hdrop : a.drop (σ.length + 6) = suf p τ := by
    have hne : a ≠ [] := by rintro rfl; simp at hlen; omega
    obtain ⟨w', tl', hb⟩ : ∃ w' tl', a.reverse = w' :: tl' := by
      cases h : a.reverse with
      | nil => simp at h; exact absurd h hne
      | cons w' tl' => exact ⟨w', tl', rfl⟩
    have hbP : IsPermOf N (w' :: tl') := by
      rw [← hb]; exact ⟨List.nodup_reverse.2 hP.1, fun v => by rw [List.mem_reverse]; exact hP.2 v⟩
    have hbA : APF (w' :: tl') := by rw [← hb]; exact hap.reverse
    have hlp := head_last_parity (isPermOf_iff_isFoldSeq.1 hP) (apFree_of_apf hap) (by omega)
      (by omega)
    have hw' : w' % 2 = 1 - p := by
      have e1 : w' = a[a.length - 1]'(by omega) := by
        have : (a.reverse)[0]'(by simp; omega) = w' := by simp [hb]
        rw [← this, List.getElem_reverse]; congr 1
      have e0 : a[0]'(by omega) % 2 = p := by
        obtain ⟨x, t, rfl⟩ : ∃ x t, a = x :: t := by
          cases a with
          | nil => exact absurd rfl hne
          | cons x t => exact ⟨x, t, rfl⟩
        simpa using hh
      rw [e1]; omega
    have hrun := run_take hbP hbA
    rw [hw', show N + (1 - p) = N + 1 - p by omega, ← hl2, ← hb] at hrun
    have key := filter_take_of_forall (P := fun v => decide (v % 2 ≠ p))
      (fun v hv => by have := hrun v hv; simp; omega)
    rw [List.filter_reverse, hfC, List.take_reverse, List.take_reverse] at key
    have key2 := List.reverse_injective key
    rw [List.length_map, hl2, hlen] at key2
    rw [show N - ((N + 1 - p) / 2 - 6) = σ.length + 6 by omega,
      show (N + 1 - p) / 2 - ((N + 1 - p) / 2 - 6) = 6 by omega, ← List.map_drop] at key2
    exact key2.symm
  have hdd : (a.drop (σ.length - 6)).drop 12 = a.drop (σ.length + 6) := by
    rw [List.drop_drop]; congr 1; omega
  calc a = a.take (σ.length - 6) ++ a.drop (σ.length - 6) := (List.take_append_drop _ _).symm
    _ = pre p σ ++ ((a.drop (σ.length - 6)).take 12 ++ (a.drop (σ.length - 6)).drop 12) := by
        rw [htake, List.take_append_drop]
    _ = _ := by rw [hdd, hdrop]

/-- The middle of a shuffle is an allowed window shuffle. -/
theorem mid_mem {a : List ℕ} (ha : a ∈ shuffles N p σ τ) :
    (a.drop (σ.length - 6)).take 12 ∈ winShuffles N p (σ.drop (σ.length - 6)) (τ.take 6) := by
  have hdec := shuffle_decomp hp hσ hτ hD hC ha
  set w := (a.drop (σ.length - 6)).take 12
  obtain ⟨hperm, hh, hfD, hfC, hlk⟩ := mem_shuffles.1 ha
  have hP : IsPermOf N a := isPermOf_iff_isFoldSeq.2 hperm
  obtain ⟨fX1, fX2⟩ := filter_all_eq (pre_mod hp hσ hτ hD hC)
  obtain ⟨fY1, fY2⟩ := filter_none_eq (suf_mod hp hσ hτ hD hC)
  have hD' : w.filter (fun v => decide (v % 2 = p)) =
      (σ.drop (σ.length - 6)).map (lift p) := by
    have := hfD
    rw [hdec, List.filter_append, List.filter_append, fX1, fY1, List.append_nil,
      sigma_split hp hσ hτ hD hC] at this
    exact List.append_cancel_left this
  have hC' : w.filter (fun v => decide (v % 2 ≠ p)) = (τ.take 6).map (lift (1 - p)) := by
    have := hfC
    rw [hdec, List.filter_append, List.filter_append, fX2, fY2, List.nil_append,
      tau_split hp hσ hτ hD hC] at this
    exact List.append_cancel_right this
  refine mem_winShuffles.2 ⟨?_, hD', hC', ?_⟩
  · rw [← hD', ← hC']
    refine List.Perm.symm ((List.Perm.of_eq ?_).trans (List.filter_append_perm
      (fun v => decide (v % 2 = p)) w))
    congr 1
  · intro y hy u hu hyp hup hl
    have hnd : (pre p σ ++ w ++ suf p τ).Nodup := by
      rw [List.append_assoc, ← hdec]; exact hP.1
    refine bef_of_infix hnd hy hu ?_
    rw [List.append_assoc, ← hdec]
    have hmem : ∀ x ∈ w, x ∈ a := fun x hx => by
      rw [hdec]; exact List.mem_append_right _ (List.mem_append_left _ hx)
    exact hlk y (hmem y hy) u (hmem u hu) hyp hup hl

/-- The assembled list of a window shuffle is an allowed shuffle. -/
theorem assemble_mem {w : List ℕ}
    (hw : w ∈ winShuffles N p (σ.drop (σ.length - 6)) (τ.take 6)) :
    pre p σ ++ (w ++ suf p τ) ∈ shuffles N p σ τ := by
  obtain ⟨hl1, hl2⟩ := lens hp hσ hτ hD hC
  obtain ⟨hwperm, hwD, hwC, hwl⟩ := mem_winShuffles.1 hw
  obtain ⟨hσP, -⟩ := mem_symSeqs_iff.1 hσ
  obtain ⟨hτP, -⟩ := mem_symSeqs_iff.1 hτ
  obtain ⟨fX1, fX2⟩ := filter_all_eq (pre_mod hp hσ hτ hD hC)
  obtain ⟨fY1, fY2⟩ := filter_none_eq (suf_mod hp hσ hτ hD hC)
  set a := pre p σ ++ (w ++ suf p τ) with hadef
  have hfD : a.filter (fun v => decide (v % 2 = p)) = σ.map (lift p) := by
    rw [hadef, List.filter_append, List.filter_append, fX1, fY1, hwD, List.append_nil,
      sigma_split hp hσ hτ hD hC]
  have hfC : a.filter (fun v => decide (v % 2 ≠ p)) = τ.map (lift (1 - p)) := by
    rw [hadef, List.filter_append, List.filter_append, fX2, fY2, hwC, List.nil_append,
      tau_split hp hσ hτ hD hC]
  have hU := lift_union_isPermOf hp hσP hτP
  have hperm : a.Perm (σ.map (lift p) ++ τ.map (lift (1 - p))) := by
    rw [← hfD, ← hfC]
    refine List.Perm.symm ((List.Perm.of_eq ?_).trans (List.filter_append_perm
      (fun v => decide (v % 2 = p)) a))
    congr 1
  have hP : IsPermOf N a := ⟨hperm.nodup_iff.2 hU.1, fun v => by rw [hperm.mem_iff]; exact hU.2 v⟩
  have hmodY := suf_mod hp hσ hτ hD hC
  have hmodX := pre_mod hp hσ hτ hD hC
  refine mem_shuffles.2 ⟨isPermOf_iff_isFoldSeq.1 hP, ?_, hfD, hfC, ?_⟩
  · obtain ⟨s0, σ', rfl⟩ : ∃ s0 σ', σ = s0 :: σ' := by
      cases σ with
      | nil => simp at hl1; omega
      | cons s0 σ' => exact ⟨s0, σ', rfl⟩
    have hk : (s0 :: σ').length - 6 = (σ'.length - 6) + 1 := by simp at hl1 ⊢; omega
    have hpre : pre p (s0 :: σ') = lift p s0 :: (σ'.take (σ'.length - 6)).map (lift p) := by
      simp only [pre]; rw [hk]; simp
    have hs0 : 1 ≤ s0 := ((hσP.2 s0).1 (by simp)).1
    rw [hadef, hpre]
    simpa using lift_mod hp hs0
  · intro y hy u hu hyp hup hl
    rw [hadef] at hy hu ⊢
    rcases List.mem_append.1 hy with hyX | hyR
    · rcases List.mem_append.1 hu with huX | huR
      · exact absurd (hmodX u huX) hup
      · exact bef_append_mid hyX huR
    rcases List.mem_append.1 hyR with hyw | hyY
    · rcases List.mem_append.1 hu with huX | huR
      · exact absurd (hmodX u huX) hup
      rcases List.mem_append.1 huR with huw | huY
      · exact bef_append_right (bef_append_left (hwl y hyw u huw hyp hup hl))
      · exact bef_append_right (bef_append_mid hyw huY)
    · exact absurd hyp (hmodY y hyY)

/-- **Theorem W (locality).**  The merge count `P(σ, τ)` equals the window count
`Π_N(σ.drop (|σ| - 6), τ.take 6)`. -/
theorem card_shuffles_eq_win :
    (shuffles N p σ τ).card = (winShuffles N p (σ.drop (σ.length - 6)) (τ.take 6)).card := by
  obtain ⟨hl1, hl2⟩ := lens hp hσ hτ hD hC
  refine Finset.card_nbij' (fun a => (a.drop (σ.length - 6)).take 12)
    (fun w => pre p σ ++ (w ++ suf p τ)) (fun a ha => mid_mem hp hσ hτ hD hC ha)
    (fun w hw => assemble_mem hp hσ hτ hD hC hw) (fun a ha => ?_) (fun w hw => ?_)
  · exact (shuffle_decomp hp hσ hτ hD hC ha).symm
  · have hwl : w.length = 12 := by
      rw [(mem_winShuffles.1 hw).1.length_eq]
      simp [List.length_drop, List.length_take]; omega
    have hX : (pre p σ).length = σ.length - 6 := by simp
    simp only
    rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
      List.nil_append, List.take_append_of_le_length (by omega), List.take_of_length_le
      (by omega)]

/-- The head window of a shuffle is the lifted head window of `σ` (`|σ| ≥ 12`). -/
theorem shuffle_head (h12 : 12 ≤ (N + p) / 2) {a : List ℕ} (ha : a ∈ shuffles N p σ τ) :
    a.take 6 = (σ.take 6).map (lift p) := by
  obtain ⟨hl1, -⟩ := lens hp hσ hτ hD hC
  rw [shuffle_decomp hp hσ hτ hD hC ha, List.take_append_of_le_length (by simp; omega), pre,
    ← List.map_take, List.take_take]
  congr 2; omega

/-- The tail window of a shuffle is the lifted tail window of `τ` (`|τ| ≥ 12`). -/
theorem shuffle_tail (h12 : 12 ≤ (N + 1 - p) / 2) {a : List ℕ} (ha : a ∈ shuffles N p σ τ) :
    a.drop (N - 6) = (τ.drop ((N + 1 - p) / 2 - 6)).map (lift (1 - p)) := by
  obtain ⟨hl1, hl2⟩ := lens hp hσ hτ hD hC
  have hdec := shuffle_decomp hp hσ hτ hD hC ha
  have hlen : (pre p σ ++ (a.drop (σ.length - 6)).take 12).length = σ.length + 6 := by
    have : ((a.drop (σ.length - 6)).take 12).length = 12 := by
      have hN : a.length = N := (isPermOf_iff_isFoldSeq.2 (mem_shuffles.1 ha).1).length
      simp [List.length_take, List.length_drop]; omega
    simp only [List.length_append, this]; simp; omega
  rw [hdec, ← List.append_assoc, show N - 6 = (σ.length + 6) + ((N + 1 - p) / 2 - 12) by
    omega, ← List.drop_drop, List.drop_append_of_le_length (le_of_eq hlen.symm),
    List.drop_of_length_le (le_of_eq hlen), List.nil_append, suf, ← List.map_drop,
    List.drop_drop]
  congr 2; omega

end decomp

/-- `P(σ, τ)` depends only on the last `6` entries of `σ` and the first `6` of `τ`. -/
theorem card_shuffles_congr {N p : ℕ} (hp : p ≤ 1) (hD : 7 ≤ (N + p) / 2)
    (hC : 6 ≤ (N + 1 - p) / 2) {σ σ' τ τ' : List ℕ} (hσ : σ ∈ symSeqs ((N + p) / 2))
    (hσ' : σ' ∈ symSeqs ((N + p) / 2)) (hτ : τ ∈ symSeqs ((N + 1 - p) / 2))
    (hτ' : τ' ∈ symSeqs ((N + 1 - p) / 2))
    (hS : σ.drop (σ.length - 6) = σ'.drop (σ'.length - 6)) (hT : τ.take 6 = τ'.take 6) :
    (shuffles N p σ τ).card = (shuffles N p σ' τ').card := by
  rw [card_shuffles_eq_win hp hσ hτ hD hC, card_shuffles_eq_win hp hσ' hτ' hD hC, hS, hT]

/-- **The window identity**: for `N ≥ 14`,
`θ(N) = Σ_p Σ_σ Σ_τ Π_N(σ.drop (|σ| - 6), τ.take 6)`. -/
theorem card_symSeqs_eq_win_sum {N : ℕ} (hN : 14 ≤ N) :
    (symSeqs N).card = ∑ p ∈ Finset.range 2, ∑ σ ∈ symSeqs ((N + p) / 2),
      ∑ τ ∈ symSeqs ((N + 1 - p) / 2),
        (winShuffles N p (σ.drop ((N + p) / 2 - 6)) (τ.take 6)).card := by
  rw [card_symSeqs_eq_sum (by omega)]
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun σ hσ =>
    Finset.sum_congr rfl fun τ hτ => ?_
  have hp1 : p ≤ 1 := by simp at hp; omega
  rw [card_shuffles_eq_win hp1 hσ hτ (by omega) (by omega),
    (mem_symSeqs_iff.1 hσ).1.length]

theorem sum_comp_mul {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (g : ι → κ) (f : κ → ℕ) :
    ∑ a ∈ s, f (g a) = ∑ b ∈ s.image g, (s.filter (fun a => g a = b)).card * f b := by
  rw [Finset.sum_comp]; simp only [nsmul_eq_mul, Nat.cast_id]

/-- **`θ(N)` is a bilinear form in the window statistics of the halves**: with
`α_p(S) = #{σ ∈ Θ(⌊(N+p)/2⌋) : tail window S}` and `β_p(T) = #{τ ∈ Θ(⌊(N+1-p)/2⌋) : head
window T}`, `θ(N) = Σ_p Σ_S Σ_T α_p(S) β_p(T) Π_N(S, T)`. -/
theorem card_symSeqs_eq_stat_sum {N : ℕ} (hN : 14 ≤ N) :
    (symSeqs N).card = ∑ p ∈ Finset.range 2,
      ∑ S ∈ (symSeqs ((N + p) / 2)).image (fun σ => σ.drop ((N + p) / 2 - 6)),
      ∑ T ∈ (symSeqs ((N + 1 - p) / 2)).image (fun τ => τ.take 6),
        ((symSeqs ((N + p) / 2)).filter (fun σ => σ.drop ((N + p) / 2 - 6) = S)).card *
        ((symSeqs ((N + 1 - p) / 2)).filter (fun τ => τ.take 6 = T)).card *
        (winShuffles N p S T).card := by
  rw [card_symSeqs_eq_win_sum hN]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_comp_mul (symSeqs ((N + p) / 2)) (fun σ => σ.drop ((N + p) / 2 - 6))
    (fun S => ∑ τ ∈ symSeqs ((N + 1 - p) / 2), (winShuffles N p S (τ.take 6)).card)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [sum_comp_mul (symSeqs ((N + 1 - p) / 2)) (fun τ => τ.take 6)
    (fun T => (winShuffles N p S T).card), Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [mul_assoc]

/-! ## Theorem J: the window statistics propagate exactly -/

/-- `card_symSeqs_eq_sum` refined by any predicate `Q`. -/
theorem card_filter_symSeqs_eq_sum {N : ℕ} (hN : 1 ≤ N) (Q : List ℕ → Prop) [DecidablePred Q] :
    ((symSeqs N).filter Q).card = ∑ p ∈ Finset.range 2, ∑ σ ∈ symSeqs ((N + p) / 2),
      ∑ τ ∈ symSeqs ((N + 1 - p) / 2), ((shuffles N p σ τ).filter Q).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun a => a.headD 0 % 2) (t := Finset.range 2)
    (fun a _ => Finset.mem_range.2 (Nat.mod_lt _ (by omega)))]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp1 : p ≤ 1 := by simp at hp; omega
  rw [Finset.card_eq_sum_card_fiberwise (f := cls p) (t := symSeqs ((N + p) / 2))
    (s := ((symSeqs N).filter Q).filter (fun a => a.headD 0 % 2 = p)) (by
    intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, mem_symSeqs_iff] at ha
    exact mem_symSeqs_iff.2 ⟨cls_isPermOf hp1 ha.1.1.1, cls_apf ha.1.1.2⟩)]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [Finset.card_eq_sum_card_fiberwise (f := cls (1 - p)) (t := symSeqs ((N + 1 - p) / 2))
    (s := (((symSeqs N).filter Q).filter (fun a => a.headD 0 % 2 = p)).filter
      (fun a => cls p a = σ)) (by
    intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, mem_symSeqs_iff] at ha
    have := cls_isPermOf (p := 1 - p) (by omega) ha.1.1.1.1
    rw [show (N + (1 - p)) / 2 = (N + 1 - p) / 2 by omega] at this
    exact mem_symSeqs_iff.2 ⟨this, cls_apf ha.1.1.1.2⟩)]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  congr 1
  ext a
  obtain ⟨hσP, hσA⟩ := mem_symSeqs_iff.1 hσ
  obtain ⟨hτP, hτA⟩ := mem_symSeqs_iff.1 hτ
  have hσ1 : ∀ r ∈ σ, 1 ≤ r := fun r hr => ((hσP.2 r).1 hr).1
  have hτ1 : ∀ r ∈ τ, 1 ≤ r := fun r hr => ((hτP.2 r).1 hr).1
  simp only [shuffles, Finset.mem_filter, mem_symSeqs_iff, List.mem_toFinset,
    List.mem_permutations]
  rw [← IsFoldSeq, ← isPermOf_iff_isFoldSeq]
  constructor
  · rintro ⟨⟨⟨⟨⟨hP, hap⟩, hQ⟩, hh⟩, h1⟩, h2⟩
    exact ⟨⟨hP, hh, (shuffle_key hp1 hσA hσ1 hτA hτ1 hP hN hh).1 ⟨hap, h1, h2⟩⟩, hQ⟩
  · rintro ⟨⟨hP, hh, h⟩, hQ⟩
    obtain ⟨hap, h1, h2⟩ := (shuffle_key hp1 hσA hσ1 hτA hτ1 hP hN hh).2 h
    exact ⟨⟨⟨⟨⟨hP, hap⟩, hQ⟩, hh⟩, h1⟩, h2⟩

/-- **Theorem J.**  For `N ≥ 24`, the number of 3-AP-free permutations of `[1, N]` with head
window `H` (first `6` entries) and tail window `T` (last `6` entries) is
`Σ_p Σ_{σ : lift(σ.take 6) = H} Σ_{τ : lift(τ.drop (|τ|-6)) = T} Π_N(σ.drop (|σ|-6), τ.take 6)`.
So the joint head/tail statistics at size `N` are an exact bilinear image of those at sizes
`⌊N/2⌋` and `⌈N/2⌉`. -/
theorem card_window_eq_sum {N : ℕ} (hN : 24 ≤ N) (H T : List ℕ) :
    ((symSeqs N).filter (fun a => a.take 6 = H ∧ a.drop (N - 6) = T)).card =
      ∑ p ∈ Finset.range 2,
        ∑ σ ∈ (symSeqs ((N + p) / 2)).filter (fun σ => (σ.take 6).map (lift p) = H),
        ∑ τ ∈ (symSeqs ((N + 1 - p) / 2)).filter
            (fun τ => (τ.drop ((N + 1 - p) / 2 - 6)).map (lift (1 - p)) = T),
          (winShuffles N p (σ.drop ((N + p) / 2 - 6)) (τ.take 6)).card := by
  rw [card_filter_symSeqs_eq_sum (by omega)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp1 : p ≤ 1 := by simp at hp; omega
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [Finset.sum_filter]
  have hfun : ∀ τ ∈ symSeqs ((N + 1 - p) / 2),
      ((shuffles N p σ τ).filter (fun a => a.take 6 = H ∧ a.drop (N - 6) = T)).card =
      if (σ.take 6).map (lift p) = H ∧
          (τ.drop ((N + 1 - p) / 2 - 6)).map (lift (1 - p)) = T then
        (winShuffles N p (σ.drop ((N + p) / 2 - 6)) (τ.take 6)).card else 0 := by
    intro τ hτ
    have hw := card_shuffles_eq_win hp1 hσ hτ (by omega) (by omega)
    rw [(mem_symSeqs_iff.1 hσ).1.length] at hw
    have hiff : ∀ a ∈ shuffles N p σ τ, (a.take 6 = H ∧ a.drop (N - 6) = T) ↔
        ((σ.take 6).map (lift p) = H ∧
          (τ.drop ((N + 1 - p) / 2 - 6)).map (lift (1 - p)) = T) := by
      intro a ha
      rw [shuffle_head hp1 hσ hτ (by omega) (by omega) (by omega) ha,
        shuffle_tail hp1 hσ hτ (by omega) (by omega) (by omega) ha]
    split_ifs with hc
    · rw [← hw]; congr 1
      exact Finset.filter_true_of_mem fun a ha => (hiff a ha).2 hc
    · rw [Finset.card_eq_zero]
      exact Finset.filter_false_of_mem fun a ha h => hc ((hiff a ha).1 h)
  rw [Finset.sum_congr rfl hfun]
  split_ifs with hc
  · refine Finset.sum_congr rfl fun τ _ => ?_
    simp [hc]
  · refine Finset.sum_eq_zero fun τ _ => ?_
    exact ite_eq_right_iff.2 fun h => absurd h.1 hc

end SymRatio
end Folds
