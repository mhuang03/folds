import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Folds.Basic

/-!
# Descents and decreasing subsequences of semi-symmetric fold sequences

Proofs on paper: `experiments/descents/PROOFS.txt`.

Conjecture (checked by computer far beyond the range of this file): a semi-symmetric fold
sequence of length `N` has at least `⌊log₂(N+1)⌋ - 1` descents.  Here we prove the weaker,
but unconditional, logarithmic bound

    `N + 1 ≤ (⌊log₂(N+1)⌋ + 2) ^ (des a + 1)`      (`descents_bound`),

i.e. `des a + 1 ≥ log(N+1) / log(⌊log₂(N+1)⌋ + 2)`.

The bound is proved for any *level labelling* `c` of the panels: a function that increases
strictly along every inversion (`x` placed before `y` and `y < x` imply `c x < c y`).  The
run index (number of descents before a position) is one such labelling, with `des a + 1`
values; the patience level (length of the longest decreasing subsequence ending at a panel)
is another, with `LDS(a)` values.  So the same bound holds for the longest decreasing
subsequence (`labelling_bound`).

## Proof
* `window_lemma`: if `c` is a level labelling, then for every panel `m`,
  `#{d ≤ r : c (m-d) ≤ c m} ≤ #{d ≤ r : c (m+d) < c m}` (`r = reach N m`): a panel on the
  left with level `≤ c m` must have been placed before `m`, and an earlier panel on the right
  has level `< c m`; the step at `m` balances the earlier panels.
* `left_part`: at most `s_v + 1` panels of level `v` lie in the left half, where `s_v` is the
  number of panels of level `< v` (apply the window lemma to the largest one).
* `right_part`: in the right half, write `g = N + 1 - m`.  Inside a dyadic block
  `g ∈ [2^j, 2^(j+1))` all other panels of level `v` lie in the left part of the window of
  the one with the smallest `g`, so each block holds at most `s_v + 1` of them
  (`block_count`), and there are at most `⌊log₂(N+1)⌋` blocks.
* Hence `s_{v+1} + 1 ≤ (s_v + 1)(⌊log₂(N+1)⌋ + 2)`, and `s_t = N`.
-/

namespace Folds

open Finset

/-! ## Counting over `List.range'` as `Finset` cardinalities -/

theorem countP_range'_eq_card (p : Nat → Bool) (r : Nat) :
    (List.range' 1 r).countP p = ((Finset.Icc 1 r).filter (fun d => p d = true)).card := by
  rw [List.countP_eq_length_filter]
  have h : (Finset.Icc 1 r).filter (fun d => p d = true)
      = ((List.range' 1 r).filter p).toFinset := by
    ext x; simp [List.mem_range'_1]; omega
  rw [h, List.toFinset_card_of_nodup ((List.nodup_range' (s := 1)).filter _)]

/-! ## Dyadic blocks -/

/-- If every `g ∈ G ⊆ [1, H]` has at most `s` elements of `G` in `(g, 2g)`, then
`|G| ≤ (s + 1)(⌊log₂ H⌋ + 1)`. -/
theorem block_count (s : Nat) : ∀ (H : Nat) (G : Finset Nat),
    (∀ g ∈ G, 1 ≤ g ∧ g ≤ H) →
    (∀ g ∈ G, (G.filter (fun g' => g < g' ∧ g' < 2 * g)).card ≤ s) →
    G.card ≤ (s + 1) * (Nat.log 2 H + 1) := by
  intro H
  induction H using Nat.strong_induction_on with
  | _ H ih =>
  intro G hG hcnt
  rcases Nat.eq_zero_or_pos H with hH | hH
  · subst hH
    have : G = ∅ := by
      ext g; simp only [Finset.notMem_empty, iff_false]; intro hg; have := hG g hg; omega
    simp [this]
  -- split into the lower part `g ≤ H/2` and the upper part `g > H/2`
  have hsplit := Finset.card_filter_add_card_filter_not (s := G) (fun g => g ≤ H / 2)
  set lo := G.filter (fun g => g ≤ H / 2)
  set up := G.filter (fun g => ¬ g ≤ H / 2)
  have hup : up.card ≤ s + 1 := by
    rcases up.eq_empty_or_nonempty with he | hne
    · rw [he]; simp
    · set g0 := up.min' hne
      have hg0 : g0 ∈ up := Finset.min'_mem _ _
      have hg0G : g0 ∈ G := (Finset.mem_filter.1 hg0).1
      have hg0big : ¬ g0 ≤ H / 2 := (Finset.mem_filter.1 hg0).2
      have hsub : up.erase g0 ⊆ G.filter (fun g' => g0 < g' ∧ g' < 2 * g0) := by
        intro g hg
        rw [Finset.mem_erase] at hg
        have hgu := hg.2
        have hgG : g ∈ G := (Finset.mem_filter.1 hgu).1
        have hle : g0 ≤ g := Finset.min'_le _ _ hgu
        have hgH := (hG g hgG).2
        rw [Finset.mem_filter]
        refine ⟨hgG, ?_, ?_⟩
        · exact lt_of_le_of_ne hle (Ne.symm hg.1)
        · omega
      have h1 := Finset.card_le_card hsub
      have h2 := hcnt g0 hg0G
      have h3 := Finset.card_erase_of_mem hg0
      omega
  have hlo : lo.card ≤ (s + 1) * (Nat.log 2 (H / 2) + 1) := by
    apply ih (H / 2) (by omega)
    · intro g hg
      have := Finset.mem_filter.1 hg
      exact ⟨(hG g this.1).1, this.2⟩
    · intro g hg
      refine le_trans (Finset.card_le_card ?_) (hcnt g (Finset.mem_filter.1 hg).1)
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨(Finset.mem_filter.1 hx.1).1, hx.2⟩
  rcases Nat.lt_or_ge H 2 with hH2 | hH2
  · -- H = 1: the lower part is empty
    have hlo0 : lo.card = 0 := by
      rw [Finset.card_eq_zero]
      ext g; simp only [Finset.notMem_empty, iff_false]
      intro hg
      have := Finset.mem_filter.1 hg
      have := (hG g this.1).1
      omega
    have : H = 1 := by omega
    subst this
    simp
    omega
  · have hlog : Nat.log 2 (H / 2) + 1 = Nat.log 2 H := by
      rw [Nat.log_div_base]
      have : 1 ≤ Nat.log 2 H := Nat.le_log_of_pow_le (by norm_num) (by simpa using hH2)
      omega
    rw [hlog] at hlo
    calc G.card = lo.card + up.card := hsplit.symm
      _ ≤ (s + 1) * Nat.log 2 H + (s + 1) := by omega
      _ = (s + 1) * (Nat.log 2 H + 1) := by ring

/-! ## The abstract counting theorem -/

/-- Balance of the panels placed before `m`, phrased with a time function `τ`. -/
def TimeBalanced (N : Nat) (τ : Nat → Nat) : Prop :=
  ∀ m, 1 ≤ m → m ≤ N →
    (List.range' 1 (reach N m)).countP (fun d => τ (m - d) < τ m) =
    (List.range' 1 (reach N m)).countP (fun d => τ (m + d) < τ m)

/-- `c` increases strictly along inversions of the time order `τ`. -/
def LevelLabelling (N : Nat) (τ c : Nat → Nat) : Prop :=
  ∀ x y, 1 ≤ x → x ≤ N → 1 ≤ y → y ≤ N → τ x < τ y → y < x → c x < c y

section abstract

variable {N : Nat} {τ c : Nat → Nat}

theorem window_lemma (hinj : ∀ x y, 1 ≤ x → x ≤ N → 1 ≤ y → y ≤ N → τ x = τ y → x = y)
    (hbal : TimeBalanced N τ) (hc : LevelLabelling N τ c) {m : Nat} (hm1 : 1 ≤ m)
    (hmN : m ≤ N) :
    ((Finset.Icc 1 (reach N m)).filter (fun d => c (m - d) ≤ c m)).card ≤
      ((Finset.Icc 1 (reach N m)).filter (fun d => c (m + d) < c m)).card := by
  have hb := hbal m hm1 hmN
  rw [countP_range'_eq_card, countP_range'_eq_card] at hb
  simp only [decide_eq_true_eq] at hb
  calc ((Finset.Icc 1 (reach N m)).filter (fun d => c (m - d) ≤ c m)).card
      ≤ ((Finset.Icc 1 (reach N m)).filter (fun d => τ (m - d) < τ m)).card := by
        apply Finset.card_le_card
        intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
        refine ⟨hd.1, ?_⟩
        have hr : d ≤ reach N m := hd.1.2
        unfold reach at hr
        rcases Nat.lt_trichotomy (τ (m - d)) (τ m) with h | h | h
        · exact h
        · have := hinj _ _ (by omega) (by omega) hm1 hmN h; omega
        · have := hc m (m - d) hm1 hmN (by omega) (by omega) h (by omega); omega
    _ = ((Finset.Icc 1 (reach N m)).filter (fun d => τ (m + d) < τ m)).card := hb
    _ ≤ ((Finset.Icc 1 (reach N m)).filter (fun d => c (m + d) < c m)).card := by
        apply Finset.card_le_card
        intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
        refine ⟨hd.1, ?_⟩
        have hr : d ≤ reach N m := hd.1.2
        unfold reach at hr
        exact hc (m + d) m (by omega) (by omega) hm1 hmN hd.2 (by omega)

/-- Panels of level `< v`. -/
def lowCount (N : Nat) (c : Nat → Nat) (v : Nat) : Nat :=
  ((Finset.Icc 1 N).filter (fun x => c x < v)).card

/-- The right side of the window lemma is at most the number of panels of lower level. -/
theorem right_le_low {m : Nat} (hm1 : 1 ≤ m) :
    ((Finset.Icc 1 (reach N m)).filter (fun d => c (m + d) < c m)).card ≤
      lowCount N c (c m) := by
  unfold lowCount
  apply Finset.card_le_card_of_injOn (fun d => m + d)
  · intro d hd
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hd
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
    have hr := hd.1.2; unfold reach at hr
    exact ⟨⟨by omega, by omega⟩, hd.2⟩
  · intro d₁ _ d₂ _ h; simp only at h; omega

variable (hinj : ∀ x y, 1 ≤ x → x ≤ N → 1 ≤ y → y ≤ N → τ x = τ y → x = y)
    (hbal : TimeBalanced N τ) (hc : LevelLabelling N τ c)
include hinj hbal hc

theorem left_part (v : Nat) :
    ((Finset.Icc 1 N).filter (fun m => c m = v ∧ 2 * m ≤ N + 1)).card ≤ lowCount N c v + 1 := by
  set X := (Finset.Icc 1 N).filter (fun m => c m = v ∧ 2 * m ≤ N + 1)
  rcases X.eq_empty_or_nonempty with he | hne
  · rw [he]; simp
  set m := X.max' hne
  have hmX : m ∈ X := Finset.max'_mem _ _
  obtain ⟨hmP, hcm, hm2⟩ := Finset.mem_filter.1 hmX
  rw [Finset.mem_Icc] at hmP
  have hreach : reach N m = m - 1 := by unfold reach; omega
  have hW := window_lemma hinj hbal hc hmP.1 hmP.2
  have hR := right_le_low (N := N) (c := c) hmP.1
  have hlow : lowCount N c (c m) = lowCount N c v := by rw [hcm]
  have hinj' : (X.erase m).card ≤
      ((Finset.Icc 1 (reach N m)).filter (fun d => c (m - d) ≤ c m)).card := by
    apply Finset.card_le_card_of_injOn (fun x => m - x)
    · intro x hx
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hx
      obtain ⟨hxX, hxm⟩ := hx
      have hxle : x ≤ m := Finset.le_max' _ _ hxX
      obtain ⟨hxP, hcx, _⟩ := Finset.mem_filter.1 hxX
      rw [Finset.mem_Icc] at hxP
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [show m - (m - x) = x by omega, hcx, hcm]
    · intro x₁ hx₁ x₂ hx₂ h
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe] at hx₁ hx₂
      have h1 : x₁ ≤ m := Finset.le_max' _ _ hx₁.1
      have h2 : x₂ ≤ m := Finset.le_max' _ _ hx₂.1
      simp only at h; omega
  have := Finset.card_erase_of_mem hmX
  have hpos : 0 < X.card := Finset.card_pos.2 hne
  omega

theorem right_part (v : Nat) :
    ((Finset.Icc 1 N).filter (fun m => c m = v ∧ ¬ 2 * m ≤ N + 1)).card ≤
      (lowCount N c v + 1) * Nat.log 2 (N + 1) := by
  set Y := (Finset.Icc 1 N).filter (fun m => c m = v ∧ ¬ 2 * m ≤ N + 1)
  set G := Y.image (fun m => N + 1 - m)
  have hYG : G.card = Y.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy h
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq, Y] at hx hy
    simp only at h; omega
  have hGrange : ∀ g ∈ G, 1 ≤ g ∧ g ≤ N / 2 := by
    intro g hg
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨hmP, _, hm2⟩ := Finset.mem_filter.1 hm
    rw [Finset.mem_Icc] at hmP
    omega
  have hGcnt : ∀ g ∈ G, (G.filter (fun g' => g < g' ∧ g' < 2 * g)).card ≤ lowCount N c v := by
    intro g hg
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨hmP, hcm, hm2⟩ := Finset.mem_filter.1 hm
    rw [Finset.mem_Icc] at hmP
    have hW := window_lemma hinj hbal hc hmP.1 hmP.2
    have hR := right_le_low (N := N) (c := c) hmP.1
    have hlow : lowCount N c (c m) = lowCount N c v := by rw [hcm]
    have hreach : reach N m = N - m := by unfold reach; omega
    refine le_trans ?_ (le_trans hW (hlow ▸ hR))
    apply Finset.card_le_card_of_injOn (fun g' => g' - (N + 1 - m))
    · intro g' hg'
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hg'
      obtain ⟨hg'G, hlt1, hlt2⟩ := hg'
      obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hg'G
      obtain ⟨hm'P, hcm', _⟩ := Finset.mem_filter.1 hm'
      rw [Finset.mem_Icc] at hm'P
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [show m - (N + 1 - m' - (N + 1 - m)) = m' by omega, hcm', hcm]
    · intro x₁ hx₁ x₂ hx₂ h
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx₁ hx₂
      simp only at h; omega
  have hb := block_count (lowCount N c v) (N / 2) G hGrange hGcnt
  rw [← hYG]
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have : G = ∅ := by
      ext g; simp only [Finset.notMem_empty, iff_false]; intro hg
      have := hGrange g hg; omega
    rw [this]; simp
  · have hlog : Nat.log 2 (N / 2) + 1 ≤ Nat.log 2 (N + 1) := by
      have h2 : Nat.log 2 (2 * (N / 2)) = Nat.log 2 (N / 2) + 1 := by
        rw [Nat.mul_comm]; exact Nat.log_mul_base (by norm_num) (by omega)
      rw [← h2]; exact Nat.log_mono_right (by omega)
    calc G.card ≤ (lowCount N c v + 1) * (Nat.log 2 (N / 2) + 1) := hb
      _ ≤ (lowCount N c v + 1) * Nat.log 2 (N + 1) := Nat.mul_le_mul_left _ hlog

theorem lowCount_succ (v : Nat) :
    lowCount N c (v + 1) + 1 ≤ (lowCount N c v + 1) * (Nat.log 2 (N + 1) + 2) := by
  have hL := left_part hinj hbal hc v
  have hR := right_part hinj hbal hc v
  have h1 : lowCount N c (v + 1) = lowCount N c v +
      ((Finset.Icc 1 N).filter (fun m => c m = v)).card := by
    unfold lowCount
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.Icc 1 N).filter (fun x => c x < v + 1)) (fun x => c x < v)
    rw [Finset.filter_filter, Finset.filter_filter] at this
    rw [← this]
    congr 2
    · ext x; simp only [Finset.mem_filter]; constructor
      · rintro ⟨h, _, h2⟩; exact ⟨h, h2⟩
      · rintro ⟨h, h2⟩; exact ⟨h, by omega, h2⟩
    · ext x; simp only [Finset.mem_filter]; constructor
      · rintro ⟨h, h1, h2⟩; exact ⟨h, by omega⟩
      · rintro ⟨h, h1⟩; exact ⟨h, by omega, by omega⟩
  have h2 : ((Finset.Icc 1 N).filter (fun m => c m = v)).card =
      ((Finset.Icc 1 N).filter (fun m => c m = v ∧ 2 * m ≤ N + 1)).card +
      ((Finset.Icc 1 N).filter (fun m => c m = v ∧ ¬ 2 * m ≤ N + 1)).card := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.Icc 1 N).filter (fun x => c x = v)) (fun x => 2 * x ≤ N + 1)
    rw [Finset.filter_filter, Finset.filter_filter] at this
    exact this.symm
  rw [h1, h2]
  nlinarith [hL, hR]

theorem lowCount_le_pow (v : Nat) :
    lowCount N c v + 1 ≤ (Nat.log 2 (N + 1) + 2) ^ v := by
  induction v with
  | zero => simp [lowCount]
  | succ v ih =>
    calc lowCount N c (v + 1) + 1 ≤ (lowCount N c v + 1) * (Nat.log 2 (N + 1) + 2) :=
          lowCount_succ hinj hbal hc v
      _ ≤ (Nat.log 2 (N + 1) + 2) ^ v * (Nat.log 2 (N + 1) + 2) :=
          Nat.mul_le_mul_right _ ih
      _ = (Nat.log 2 (N + 1) + 2) ^ (v + 1) := by ring

/-- **Abstract counting bound.**  If the panels `1..N` are placed in a balanced order
(time `τ`) and `c` is a level labelling with values `< t`, then
`N + 1 ≤ (⌊log₂(N+1)⌋ + 2)^t`. -/
theorem card_le_pow_of_labelling {t : Nat} (ht : ∀ x, 1 ≤ x → x ≤ N → c x < t) :
    N + 1 ≤ (Nat.log 2 (N + 1) + 2) ^ t := by
  have h := lowCount_le_pow hinj hbal hc t
  have : lowCount N c t = N := by
    unfold lowCount
    rw [Finset.filter_true_of_mem (fun x hx => by rw [Finset.mem_Icc] at hx; exact ht x hx.1 hx.2)]
    simp
  omega

end abstract

/-! ## Fold sequences -/

section sequences

variable {N : Nat} {a : List Nat}

theorem timeBalanced_of_semiSymmetric (hf : IsFoldSeq N a) (h : SemiSymmetric N a) :
    TimeBalanced N (fun x => a.idxOf x) := by
  intro m hm1 hmN
  have hma : m ∈ a := (mem_range'_of_perm hf).2 ⟨hm1, hmN⟩
  have hk : a.idxOf m < a.length := List.idxOf_lt_length_of_mem hma
  have hstep := h (a.idxOf m) hk
  rw [List.getElem_idxOf hk] at hstep
  unfold SemiStep leftCount rightCount at hstep
  have hl : (List.range' 1 (reach N m)).countP (fun d => m - d ∈ a.take (a.idxOf m)) =
      (List.range' 1 (reach N m)).countP (fun d => a.idxOf (m - d) < a.idxOf m) := by
    apply List.countP_congr
    intro d hd
    rw [List.mem_range'_1] at hd
    have hr := hd.2; unfold reach at hr
    have hx : m - d ∈ a := (mem_range'_of_perm hf).2 ⟨by omega, by omega⟩
    simp only [decide_eq_true_eq]
    exact List.mem_take_iff_idxOf_lt hx
  have hr : (List.range' 1 (reach N m)).countP (fun d => m + d ∈ a.take (a.idxOf m)) =
      (List.range' 1 (reach N m)).countP (fun d => a.idxOf (m + d) < a.idxOf m) := by
    apply List.countP_congr
    intro d hd
    rw [List.mem_range'_1] at hd
    have hr := hd.2; unfold reach at hr
    have hx : m + d ∈ a := (mem_range'_of_perm hf).2 ⟨by omega, by omega⟩
    simp only [decide_eq_true_eq]
    exact List.mem_take_iff_idxOf_lt hx
  rw [← hl, ← hr]
  exact hstep

theorem idxOf_injOn (hf : IsFoldSeq N a) :
    ∀ x y, 1 ≤ x → x ≤ N → 1 ≤ y → y ≤ N → a.idxOf x = a.idxOf y → x = y := by
  intro x y hx1 hxN _ _ h
  exact (List.idxOf_inj ((mem_range'_of_perm hf).2 ⟨hx1, hxN⟩)).1 h

/-- **Level labellings.**  If `c` increases strictly along every inversion of a
semi-symmetric fold sequence `a` (an earlier, larger panel has a smaller label) and takes
values `< t` on the panels, then `N + 1 ≤ (⌊log₂(N+1)⌋ + 2)^t`.  With `c` = patience level
(the length of the longest decreasing subsequence ending at a panel) this bounds the longest
decreasing subsequence: `N + 1 ≤ (⌊log₂(N+1)⌋ + 2)^LDS(a)`. -/
theorem labelling_bound (hf : IsFoldSeq N a) (h : SemiSymmetric N a) (c : Nat → Nat)
    {t : Nat} (hc : ∀ i j (hij : i < j) (hj : j < a.length),
      a[j] < a[i]'(Nat.lt_trans hij hj) → c a[i] < c a[j])
    (ht : ∀ x ∈ a, c x < t) :
    N + 1 ≤ (Nat.log 2 (N + 1) + 2) ^ t := by
  refine card_le_pow_of_labelling (τ := fun x => a.idxOf x) (c := c) (idxOf_injOn hf)
    (timeBalanced_of_semiSymmetric hf h) ?_ (fun x hx1 hxN => ht x ((mem_range'_of_perm hf).2 ⟨hx1, hxN⟩))
  intro x y hx1 hxN hy1 hyN hτ hyx
  have hxa : x ∈ a := (mem_range'_of_perm hf).2 ⟨hx1, hxN⟩
  have hya : y ∈ a := (mem_range'_of_perm hf).2 ⟨hy1, hyN⟩
  have hiy : a.idxOf y < a.length := List.idxOf_lt_length_of_mem hya
  have := hc (a.idxOf x) (a.idxOf y) hτ hiy
  simp only [List.getElem_idxOf] at this
  exact this hyx

/-! ### Descents -/

/-- The descent indicator at position `i`: `a[i+1] < a[i]`. -/
def descentAt (a : List Nat) (i : Nat) : Bool := decide (a.getD (i + 1) 0 < a.getD i 0)

/-- Number of descents of `a` at positions `< k`. -/
def desBefore (a : List Nat) (k : Nat) : Nat := (List.range k).countP (descentAt a)

/-- Number of descents of `a`. -/
def des (a : List Nat) : Nat := desBefore a (a.length - 1)

theorem desBefore_mono (a : List Nat) {i j : Nat} (h : i ≤ j) : desBefore a i ≤ desBefore a j := by
  unfold desBefore
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.countP_append]
  omega

theorem desBefore_lt (a : List Nat) {i l : Nat} (hl : i ≤ l) (hd : descentAt a l = true) :
    desBefore a i < desBefore a (l + 1) := by
  unfold desBefore
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hl
  rw [show i + k + 1 = i + (k + 1) by omega, List.range_add, List.countP_append]
  have : 0 < (List.map (fun x => i + x) (List.range (k + 1))).countP (descentAt a) := by
    rw [List.countP_pos_iff]
    exact ⟨i + k, List.mem_map.2 ⟨k, List.mem_range.2 (by omega), rfl⟩, hd⟩
  omega

/-- Between two positions `i < j` with `a[j] < a[i]` there is a descent. -/
theorem exists_descent (a : List Nat) : ∀ (n i : Nat) (j : Nat) (hji : j = i + n + 1)
    (hj : j < a.length), a[j] < a[i]'(by omega) →
    ∃ l, i ≤ l ∧ l < j ∧ descentAt a l = true := by
  intro n
  induction n with
  | zero =>
    intro i j hji hj hlt
    refine ⟨i, le_refl _, by omega, ?_⟩
    unfold descentAt
    subst hji
    simp only [List.getD_eq_getElem?_getD, decide_eq_true_eq]
    rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (by omega)]
    simpa using hlt
  | succ n ih =>
    intro i j hji hj hlt
    by_cases hd : descentAt a i = true
    · exact ⟨i, le_refl _, by omega, hd⟩
    · have hle : a[i]'(by omega) ≤ a[i + 1]'(by omega) := by
        unfold descentAt at hd
        simp only [List.getD_eq_getElem?_getD, decide_eq_true_eq] at hd
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hd
        simp only [Option.getD_some] at hd
        omega
      obtain ⟨l, hl1, hl2, hl3⟩ := ih (i + 1) j (by omega) hj (by omega)
      exact ⟨l, by omega, hl2, hl3⟩

/-- **Descents.**  A semi-symmetric fold sequence of length `N` satisfies
`N + 1 ≤ (⌊log₂(N+1)⌋ + 2) ^ (des a + 1)`; in particular the number of descents tends to
infinity, at least like `log N / log log N`. -/
theorem descents_bound (hf : IsFoldSeq N a) (h : SemiSymmetric N a) :
    N + 1 ≤ (Nat.log 2 (N + 1) + 2) ^ (des a + 1) := by
  refine labelling_bound hf h (fun x => desBefore a (a.idxOf x)) ?_ ?_
  · intro i j hij hj hlt
    have hnd : a.Nodup := hf.nodup_iff.2 (List.nodup_range' (s := 1))
    have hi : a.idxOf a[i] = i := List.Nodup.idxOf_getElem hnd i _
    have hj' : a.idxOf a[j] = j := List.Nodup.idxOf_getElem hnd j hj
    simp only [hi, hj']
    obtain ⟨l, hl1, hl2, hl3⟩ := exists_descent a (j - i - 1) i j (by omega) hj hlt
    exact lt_of_lt_of_le (desBefore_lt a hl1 hl3) (desBefore_mono a (by omega))
  · intro x hx
    have := List.idxOf_lt_length_of_mem hx
    have := desBefore_mono a (show a.idxOf x ≤ a.length - 1 by omega)
    unfold des; omega

end sequences

end Folds
