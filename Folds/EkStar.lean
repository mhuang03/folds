import Folds.Ek

/-!
# Conjecture E*_k: the two-sided family `S_a`

`experiments/ekstar/PROOFS.txt`.
-/

namespace Folds
namespace EkStar

open Live2 Live4 Adjacent LiveK Ek

/-! ## Plays on a background -/

/-- Left arm count of `m` in a finite set. -/
def lc (N m : Nat) (X : Finset Nat) : Nat := (X.filter (fun x => m - reach N m ≤ x ∧ x < m)).card

/-- Right arm count of `m` in a finite set. -/
def rc (N m : Nat) (X : Finset Nat) : Nat := (X.filter (fun x => m < x ∧ x ≤ m + reach N m)).card

/-- A complete play on the background `Y 0`: the placed sets `Y i`, the panel `e i` placed at
step `i`, every step valid, `n` steps, ending with every panel placed. -/
structure Play (N : Nat) (Y : Nat → Finset Nat) (e : Nat → Nat) (n : Nat) : Prop where
  sub : ∀ i, i ≤ n → Y i ⊆ Finset.Icc 1 N
  succ : ∀ i, i < n → Y (i + 1) = insert (e i) (Y i)
  fresh : ∀ i, i < n → e i ∉ Y i
  valid : ∀ i, i < n → lc N (e i) (Y i) = rc N (e i) (Y i)
  full : Y n = Finset.Icc 1 N

theorem play_of_coReach {N : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 N)
    (h : CoReach N D) : ∃ n Y e, Play N Y e n ∧ Y 0 = D := by
  classical
  obtain ⟨l, hnd, hmem, hstep⟩ := bg_of_coReach hD h
  refine ⟨l.length, fun i => D ∪ (l.take i).toFinset, fun i => if h : i < l.length then l[i] else 0,
    ⟨?_, ?_, ?_, ?_, ?_⟩, by simp⟩
  · intro i _ x hx
    rw [Finset.mem_union, List.mem_toFinset] at hx
    rcases hx with hx | hx
    · exact hD hx
    · exact Finset.mem_Icc.2 ((hmem x).1 (List.mem_of_mem_take hx)).1
  · intro i hi
    simp only [List.take_succ_eq_append_getElem hi, hi, ↓reduceDIte]
    ext x; simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_singleton,
      Finset.mem_insert]; tauto
  · intro i hi
    simp only [hi, ↓reduceDIte]
    rw [Finset.mem_union, List.mem_toFinset, getElem_mem_take_iff hnd hi]
    have := ((hmem _).1 (List.getElem_mem hi)).2
    rintro (h' | h')
    · exact this h'
    · omega
  · intro i hi
    have hS := bg_nodup hnd (fun x hx => ((hmem x).1 hx).2) i
    have hv := hstep i hi
    unfold SemiStep at hv
    rw [leftCount_eq hS, rightCount_eq hS, countP_eq_card_filter hS,
      countP_eq_card_filter hS] at hv
    simp only [hi, ↓reduceDIte]
    unfold lc rc
    have e1 : (D.toList ++ List.take i l).toFinset = D ∪ (l.take i).toFinset := by
      ext x; simp
    rw [e1] at hv
    exact hv
  · ext x
    simp only [List.take_length, Finset.mem_union, List.mem_toFinset, Finset.mem_Icc]
    constructor
    · rintro (hx | hx)
      · exact Finset.mem_Icc.1 (hD hx)
      · exact ((hmem x).1 hx).1
    · intro hx
      by_cases hxD : x ∈ D
      · exact Or.inl hxD
      · exact Or.inr ((hmem x).2 ⟨hx, hxD⟩)

namespace Play

variable {N n : Nat} {Y : Nat → Finset Nat} {e : Nat → Nat}

theorem mono (hP : Play N Y e n) {i j : Nat} (hij : i ≤ j) (hj : j ≤ n) : Y i ⊆ Y j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    rw [hP.succ j (by omega)]
    exact (ih (by omega)).trans (Finset.subset_insert _ _)

theorem mem_succ (hP : Play N Y e n) {i : Nat} (hi : i < n) : e i ∈ Y (i + 1) := by
  rw [hP.succ i hi]; exact Finset.mem_insert_self _ _

/-- A panel absent at step `i` and present at step `j` is placed at some step in between. -/
theorem exists_step (hP : Play N Y e n) {x i j : Nat} (hij : i ≤ j) (hj : j ≤ n)
    (hxi : x ∉ Y i) (hxj : x ∈ Y j) : ∃ k, i ≤ k ∧ k < j ∧ e k = x ∧ x ∉ Y k := by
  induction j, hij using Nat.le_induction with
  | base => exact absurd hxj hxi
  | succ j hij ih =>
    by_cases hx : x ∈ Y j
    · obtain ⟨k, h1, h2, h3, h4⟩ := ih (by omega) hx
      exact ⟨k, h1, by omega, h3, h4⟩
    · rw [hP.succ j (by omega), Finset.mem_insert] at hxj
      rcases hxj with h' | h'
      · exact ⟨j, hij, by omega, h'.symm, hx⟩
      · exact absurd h' hx

/-- Every panel outside the background is placed at some step. -/
theorem exists_step_of_free (hP : Play N Y e n) {x : Nat} (hx1 : 1 ≤ x) (hxN : x ≤ N)
    (hx : x ∉ Y 0) : ∃ k, k < n ∧ e k = x ∧ x ∉ Y k := by
  obtain ⟨k, -, h2, h3, h4⟩ := hP.exists_step (Nat.zero_le n) le_rfl hx
    (by rw [hP.full]; exact Finset.mem_Icc.2 ⟨hx1, hxN⟩)
  exact ⟨k, h2, h3, h4⟩

/-- A panel placed at step `k` was not placed at any earlier step. -/
theorem ne_of_lt (hP : Play N Y e n) {i k : Nat} (hik : i < k) (hk : k < n) : e i ≠ e k := by
  intro h
  exact hP.fresh k hk (h ▸ hP.mono (by omega) (by omega) (hP.mem_succ (by omega)))

end Play

/-! ## Mirror image of a play -/

theorem card_filter_image_mirror {N : Nat} (X : Finset Nat) (hX : X ⊆ Finset.Icc 1 N)
    (P : Nat → Prop) [DecidablePred P] :
    ((X.image (N + 1 - ·)).filter P).card = (X.filter (fun x => P (N + 1 - x))).card := by
  classical
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  intro x hx y hy hxy
  have := Finset.mem_Icc.1 (hX (Finset.mem_filter.1 hx).1)
  have := Finset.mem_Icc.1 (hX (Finset.mem_filter.1 hy).1)
  simp only at hxy
  omega

theorem mem_image_mirror {N : Nat} {X : Finset Nat} (hX : X ⊆ Finset.Icc 1 N) {y : Nat} :
    y ∈ X.image (N + 1 - ·) ↔ 1 ≤ y ∧ y ≤ N ∧ N + 1 - y ∈ X := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := Finset.mem_Icc.1 (hX hx)
    refine ⟨by omega, by omega, ?_⟩
    rwa [show N + 1 - (N + 1 - x) = x by omega]
  · rintro ⟨h1, h2, h3⟩
    exact ⟨_, h3, by omega⟩

theorem Play.mirror {N n : Nat} {Y : Nat → Finset Nat} {e : Nat → Nat} (hP : Play N Y e n) :
    Play N (fun i => (Y i).image (N + 1 - ·)) (fun i => N + 1 - e i) n := by
  classical
  have he : ∀ i, i < n → 1 ≤ e i ∧ e i ≤ N := fun i hi =>
    Finset.mem_Icc.1 (hP.sub (i + 1) (by omega) (hP.mem_succ hi))
  refine ⟨fun i hi x hx => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [mem_image_mirror (hP.sub i hi)] at hx
    exact Finset.mem_Icc.2 ⟨hx.1, hx.2.1⟩
  · simp only [hP.succ i hi, Finset.image_insert]
  · have := he i hi
    rw [mem_image_mirror (hP.sub i (by omega)), show N + 1 - (N + 1 - e i) = e i by omega]
    exact fun h' => hP.fresh i hi h'.2.2
  · have hm := he i hi
    have hv := hP.valid i hi
    have hX := hP.sub i (by omega)
    have hXN : ∀ x ∈ Y i, 1 ≤ x ∧ x ≤ N := fun x hx => Finset.mem_Icc.1 (hX hx)
    have hr : reach N (N + 1 - e i) = reach N (e i) := by unfold reach; omega
    unfold lc rc at hv ⊢
    rw [card_filter_image_mirror _ hX, card_filter_image_mirror _ hX, hr]
    rw [Finset.filter_congr (fun x hx => show (N + 1 - e i - reach N (e i) ≤ N + 1 - x ∧
        N + 1 - x < N + 1 - e i) ↔ (e i < x ∧ x ≤ e i + reach N (e i)) by
          have := hXN x hx; have : reach N (e i) ≤ e i - 1 := Nat.min_le_left _ _
          have : reach N (e i) ≤ N - e i := Nat.min_le_right _ _
          omega)]
    rw [Finset.filter_congr (fun x hx => show (N + 1 - e i < N + 1 - x ∧
        N + 1 - x ≤ N + 1 - e i + reach N (e i)) ↔ (e i - reach N (e i) ≤ x ∧ x < e i) by
          have := hXN x hx; have : reach N (e i) ≤ e i - 1 := Nat.min_le_left _ _
          have : reach N (e i) ≤ N - e i := Nat.min_le_right _ _
          omega)]
    exact hv.symm
  · ext y
    simp only [hP.full]
    rw [mem_image_mirror le_rfl, Finset.mem_Icc, Finset.mem_Icc]
    omega

/-! ## The one-sided lemma: a truncated anchored block

`Y 0` contains the anchor `a` and the truncated block `[2a+2, 4a-1]`, and nothing of
`G = [a+1, 2a+1]`.  Let `T = 2a+1` be the top panel of `G`, placed at step `τ`.  Up to `τ`,
the set `Y i ∪ {4a, 4a+1}` satisfies the invariant of the anchored block `B_a` with `j = a+1`
(the panels of `G` below `T` never see `4a`, `4a+1`). -/

theorem filter_union_far {X : Finset Nat} {c : Nat} (P : Nat → Prop) [DecidablePred P]
    (hP : ∀ x, P x → x < c) :
    (X ∪ {c, c + 1}).filter P = X.filter P := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1 | h1 | h1, h2⟩
    · exact ⟨h1, h2⟩
    · have := hP x h2; omega
    · have := hP x h2; omega
  · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩

theorem left_inv {N n a τ : Nat} {Y : Nat → Finset Nat} {e : Nat → Nat} (hP : Play N Y e n)
    (ha1 : 1 ≤ a) (hN : 4 * a + 1 ≤ N) (ha : a ∈ Y 0)
    (hgap : ∀ x ∈ Y 0, ¬ (a < x ∧ x < 2 * a + 2))
    (hb : ∀ x, 2 * a + 2 ≤ x → x < 4 * a → x ∈ Y 0)
    (hτ : τ < n) (heτ : e τ = 2 * a + 1) :
    ∀ i, i ≤ τ →
      (∀ x ∈ Y i ∪ {4 * a, 4 * a + 1}, a < x → x < 2 * (a + 1) →
        (a + 1) + 1 ≤ x ∧ x ≤ (a + 1) + ((Y i ∪ {4 * a, 4 * a + 1}).filter (· < a)).card) ∧
      ((Y i ∪ {4 * a, 4 * a + 1}).filter (fun x => a < x ∧ x < 2 * (a + 1))).card ≤
        ((Y i ∪ {4 * a, 4 * a + 1}).filter (· < a)).card := by
  classical
  intro i
  induction i with
  | zero =>
    intro _
    have h0 : (Y 0 ∪ {4 * a, 4 * a + 1}).filter (fun x => a < x ∧ x < 2 * (a + 1)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | rfl | rfl
      · have := hgap x hx; omega
      · omega
      · omega
    refine ⟨fun x hx h1 h2 => ?_, by rw [h0, Finset.card_empty]; exact Nat.zero_le _⟩
    have : x ∉ (Y 0 ∪ {4 * a, 4 * a + 1}).filter (fun x => a < x ∧ x < 2 * (a + 1)) := by
      rw [h0]; exact Finset.notMem_empty x
    exact absurd (Finset.mem_filter.2 ⟨hx, h1, h2⟩) this
  | succ i ih =>
    intro hi
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hin : i < n := by omega
    set Z := Y i ∪ {4 * a, 4 * a + 1} with hZ
    have hZs : Y (i + 1) ∪ {4 * a, 4 * a + 1} = insert (e i) Z := by
      rw [hP.succ i hin, Finset.insert_union]
    rw [hZs]
    by_cases hmZ : e i ∈ Z
    · rw [Finset.insert_eq_of_mem hmZ]; exact ⟨ih1, ih2⟩
    have hYi := hP.sub i (by omega)
    have hZsub : Z ⊆ Finset.Icc 1 N := by
      intro x hx
      rw [hZ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | rfl | rfl
      · exact hYi hx
      · rw [Finset.mem_Icc]; omega
      · rw [Finset.mem_Icc]; omega
    have hmN := Finset.mem_Icc.1 (hP.sub (i + 1) hin (hP.mem_succ hin))
    have hne : e i ≠ 2 * a + 1 := heτ ▸ hP.ne_of_lt (by omega) hτ
    have haZ : a ∈ Z := Finset.mem_union_left _ (hP.mono (Nat.zero_le i) (by omega) ha)
    generalize hmdef : e i = m at hmZ hmN hne
    by_cases hma : m < a
    · have ep : ((insert m Z).filter (· < a)).card = (Z.filter (· < a)).card + 1 := by
        rw [Finset.filter_insert, ite_eq_left hma, Finset.card_insert_of_notMem (by simp [hmZ])]
      have es : (insert m Z).filter (fun x => a < x ∧ x < 2 * (a + 1)) =
          Z.filter (fun x => a < x ∧ x < 2 * (a + 1)) := by
        rw [Finset.filter_insert, ite_eq_right (by omega)]
      rw [ep, es]
      refine ⟨fun x hx h1 h2 => ?_, by omega⟩
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · omega
      · have := ih1 x hx h1 h2; omega
    · have hma' : a < m := by
        rcases Nat.lt_or_ge a m with h' | h'
        · exact h'
        · exfalso; exact hmZ (show m = a by omega ▸ haZ)
      have ep : (insert m Z).filter (· < a) = Z.filter (· < a) := by
        rw [Finset.filter_insert, ite_eq_right hma]
      rw [ep]
      by_cases hm2 : m < 2 * (a + 1)
      · have hv := hP.valid i hin
        rw [hmdef] at hv
        have hr : reach N m = m - 1 := by unfold reach; omega
        have hv' : (Z.filter (fun x => m - reach N m ≤ x ∧ x < m)).card =
            (Z.filter (fun x => m < x ∧ x ≤ m + reach N m)).card := by
          rw [hZ, filter_union_far _ (fun x hx => by omega),
            filter_union_far _ (fun x hx => by rw [hr] at hx; omega)]
          exact hv
        have hbZ : ∀ t, t < 2 * a → 2 * (a + 1) + t ∈ Z := by
          intro t ht
          rw [hZ, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          by_cases h4 : 2 * (a + 1) + t < 4 * a
          · exact Or.inl (hP.mono (Nat.zero_le i) (by omega) (hb _ (by omega) h4))
          · right; omega
        obtain ⟨k1, k2, k3⟩ := anchor_step hZsub ha1 le_rfl (by omega) haZ hbZ ih1 ih2
          hma' hm2 hmZ hv'
        have es : ((insert m Z).filter (fun x => a < x ∧ x < 2 * (a + 1))).card =
            (Z.filter (fun x => a < x ∧ x < 2 * (a + 1))).card + 1 := by
          rw [Finset.filter_insert, ite_eq_left ⟨hma', hm2⟩,
            Finset.card_insert_of_notMem (by simp [hmZ])]
        rw [es]
        refine ⟨fun x hx h1 h2 => ?_, k3⟩
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact ⟨k1, k2⟩
        · exact ih1 x hx h1 h2
      · have es : (insert m Z).filter (fun x => a < x ∧ x < 2 * (a + 1)) =
            Z.filter (fun x => a < x ∧ x < 2 * (a + 1)) := by
          rw [Finset.filter_insert, ite_eq_right (by omega)]
        rw [es]
        refine ⟨fun x hx h1 h2 => ?_, ih2⟩
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · omega
        · exact ih1 x hx h1 h2

/-- **The one-sided lemma.**  With the anchor `a ≥ 2`, the truncated block `[2a+2, 4a-1]` and
nothing of `[a+1, 2a+1]` in the background, at the step `τ` where the top panel `2a+1` is
placed, at most `2a - 1` panels of `(2a+1, 4a+1]` are placed, and `2a` is already placed.
(Before `τ` the `B_a` invariant holds; validity of `2a+1` forces all of `[1, a-1]` placed;
afterwards `a+1` needs `2a` placed and `2a` needs `a+1` placed.) -/
theorem left_side {N n a : Nat} {Y : Nat → Finset Nat} {e : Nat → Nat} (hP : Play N Y e n)
    (ha2 : 2 ≤ a) (hN : 4 * a + 1 ≤ N) (ha : a ∈ Y 0)
    (hgap : ∀ x ∈ Y 0, ¬ (a < x ∧ x < 2 * a + 2))
    (hb : ∀ x, 2 * a + 2 ≤ x → x < 4 * a → x ∈ Y 0) :
    ∃ τ, τ < n ∧ e τ = 2 * a + 1 ∧
      ((Y τ).filter (fun x => 2 * a + 1 < x ∧ x ≤ 4 * a + 1)).card ≤ 2 * a - 1 ∧
      2 * a ∈ Y τ := by
  classical
  obtain ⟨τ, hτ, heτ, hTY⟩ := hP.exists_step_of_free (x := 2 * a + 1) (by omega) (by omega)
    (fun h' => hgap _ h' ⟨by omega, by omega⟩)
  obtain ⟨I1, I2⟩ := left_inv hP (by omega) hN ha hgap hb hτ heτ τ le_rfl
  set Z := Y τ ∪ {4 * a, 4 * a + 1} with hZ
  have hYτ := hP.sub τ (by omega)
  have hYN : ∀ x ∈ Y τ, 1 ≤ x ∧ x ≤ N := fun x hx => Finset.mem_Icc.1 (hYτ hx)
  have hbτ : ∀ x, 2 * a + 2 ≤ x → x < 4 * a → x ∈ Y τ :=
    fun x h1 h2 => hP.mono (Nat.zero_le τ) (by omega) (hb x h1 h2)
  set p := (Z.filter (· < a)).card with hp
  set s := (Z.filter (fun x => a < x ∧ x < 2 * (a + 1))).card with hs
  have hpa : p ≤ a - 1 := by
    calc p ≤ (Finset.Icc 1 (a - 1)).card := Finset.card_le_card (fun x hx => by
            rw [Finset.mem_filter, hZ, Finset.mem_union, Finset.mem_insert,
              Finset.mem_singleton] at hx
            rw [Finset.mem_Icc]
            rcases hx.1 with h' | h' | h'
            · have := hYN x h'; omega
            · omega
            · omega)
      _ = a - 1 := by rw [Nat.card_Icc]; omega
  -- validity of the top panel
  have hv := hP.valid τ hτ
  rw [heτ] at hv
  unfold lc rc at hv
  have hr : reach N (2 * a + 1) = 2 * a := by unfold reach; omega
  rw [hr] at hv
  have hlc : ((Y τ).filter (fun x => 2 * a + 1 - 2 * a ≤ x ∧ x < 2 * a + 1)).card ≤
      p + 1 + s := by
    calc _ ≤ (insert a (Z.filter (· < a) ∪ Z.filter (fun x => a < x ∧ x < 2 * (a + 1)))).card :=
          Finset.card_le_card (fun x hx => by
            rw [Finset.mem_filter] at hx
            rw [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
            have hxZ : x ∈ Z := Finset.mem_union_left _ hx.1
            rcases Nat.lt_trichotomy x a with h' | h' | h'
            · exact Or.inr (Or.inl ⟨hxZ, h'⟩)
            · exact Or.inl h'
            · exact Or.inr (Or.inr ⟨hxZ, h', by omega⟩))
      _ ≤ (Z.filter (· < a) ∪ Z.filter (fun x => a < x ∧ x < 2 * (a + 1))).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ p + s + 1 := by gcongr; exact Finset.card_union_le _ _
      _ = p + 1 + s := by omega
  have hrc : 2 * a - 2 ≤
      ((Y τ).filter (fun x => 2 * a + 1 < x ∧ x ≤ 2 * a + 1 + 2 * a)).card := by
    calc 2 * a - 2 = (Finset.Ico (2 * a + 2) (4 * a)).card := by rw [Nat.card_Ico]; omega
      _ ≤ _ := Finset.card_le_card (fun x hx => by
          rw [Finset.mem_Ico] at hx
          rw [Finset.mem_filter]
          exact ⟨hbτ x hx.1 hx.2, by omega, by omega⟩)
  have hp1 : a - 1 ≤ p := by omega
  refine ⟨τ, hτ, heτ, ?_, ?_⟩
  · have e1 : (Y τ).filter (fun x => 2 * a + 1 < x ∧ x ≤ 4 * a + 1) =
        (Y τ).filter (fun x => 2 * a + 1 < x ∧ x ≤ 2 * a + 1 + 2 * a) :=
      Finset.filter_congr (fun x _ => by omega)
    rw [e1]; omega
  -- `2a` is placed before `τ`
  by_contra h2a
  have ha1τ : a + 1 ∉ Y τ := by
    intro h'
    have := I1 (a + 1) (Finset.mem_union_left _ h') (by omega) (by omega)
    omega
  have hfull : ∀ x, 1 ≤ x → x ≤ N → x ∈ Y n := fun x h1 h2 => by
    rw [hP.full]; exact Finset.mem_Icc.2 ⟨h1, h2⟩
  obtain ⟨i1, hi1a, hi1b, hei1, hi1Y⟩ := hP.exists_step (by omega : τ ≤ n) le_rfl ha1τ
    (hfull (a + 1) (by omega) (by omega))
  obtain ⟨i2, hi2a, hi2b, hei2, hi2Y⟩ := hP.exists_step (by omega : τ ≤ n) le_rfl h2a
    (hfull (2 * a) (by omega) (by omega))
  have hi1τ : τ < i1 := by
    rcases Nat.lt_or_ge τ i1 with h' | h'
    · exact h'
    · exfalso; have : i1 = τ := by omega
      subst this; omega
  have hi2τ : τ < i2 := by
    rcases Nat.lt_or_ge τ i2 with h' | h'
    · exact h'
    · exfalso; have : i2 = τ := by omega
      subst this; omega
  have hT : ∀ i, τ < i → i ≤ n → 2 * a + 1 ∈ Y i := fun i h1 h2 =>
    hP.mono (by omega) h2 (heτ ▸ hP.mem_succ hτ)
  rcases Nat.lt_trichotomy i1 i2 with h12 | h12 | h12
  · -- `a + 1` first: its left arm holds all of `[1, a]` that is placed, at least `a`
    have h2a1 : 2 * a ∉ Y i1 := fun h' => hi2Y (hP.mono (by omega) (by omega) h')
    have hv1 := hP.valid i1 hi1b
    rw [hei1] at hv1
    unfold lc rc at hv1
    have hr1 : reach N (a + 1) = a := by unfold reach; omega
    rw [hr1] at hv1
    have hl1 : p + 1 ≤ ((Y i1).filter (fun x => a + 1 - a ≤ x ∧ x < a + 1)).card := by
      calc p + 1 = (insert a (Z.filter (· < a))).card := by
            rw [Finset.card_insert_of_notMem (by simp)]
        _ ≤ _ := Finset.card_le_card (fun x hx => by
            rw [Finset.mem_insert, Finset.mem_filter, hZ, Finset.mem_union, Finset.mem_insert,
              Finset.mem_singleton] at hx
            rw [Finset.mem_filter]
            rcases hx with rfl | ⟨h' | h' | h', h''⟩
            · exact ⟨hP.mono (Nat.zero_le _) (by omega) ha, by omega, by omega⟩
            · have := hYN x h'
              exact ⟨hP.mono (by omega) (by omega) h', by omega, by omega⟩
            · omega
            · omega)
    have hr1' : ((Y i1).filter (fun x => a + 1 < x ∧ x ≤ a + 1 + a)).card ≤ a - 1 := by
      calc _ ≤ ((Finset.Icc (a + 2) (2 * a + 1)).erase (2 * a)).card :=
            Finset.card_le_card (fun x hx => by
              rw [Finset.mem_filter] at hx
              rw [Finset.mem_erase, Finset.mem_Icc]
              refine ⟨fun h' => h2a1 (h' ▸ hx.1), by omega, by omega⟩)
        _ = a - 1 := by
            rw [Finset.card_erase_of_mem (by rw [Finset.mem_Icc]; omega), Nat.card_Icc]; omega
    omega
  · rw [h12] at hei1; omega
  · -- `2a` first: its left arm misses `a + 1`, its right arm holds `[2a+1, 4a-1]`
    have ha12 : a + 1 ∉ Y i2 := fun h' => hi1Y (hP.mono (by omega) (by omega) h')
    have hv2 := hP.valid i2 hi2b
    rw [hei2] at hv2
    unfold lc rc at hv2
    have hr2 : reach N (2 * a) = 2 * a - 1 := by unfold reach; omega
    rw [hr2] at hv2
    have hl2 : ((Y i2).filter (fun x => 2 * a - (2 * a - 1) ≤ x ∧ x < 2 * a)).card ≤
        2 * a - 2 := by
      calc _ ≤ ((Finset.Icc 1 (2 * a - 1)).erase (a + 1)).card :=
            Finset.card_le_card (fun x hx => by
              rw [Finset.mem_filter] at hx
              rw [Finset.mem_erase, Finset.mem_Icc]
              refine ⟨fun h' => ha12 (h' ▸ hx.1), by omega, by omega⟩)
        _ = 2 * a - 2 := by
            rw [Finset.card_erase_of_mem (by rw [Finset.mem_Icc]; omega), Nat.card_Icc]; omega
    have hr2' : 2 * a - 1 ≤
        ((Y i2).filter (fun x => 2 * a < x ∧ x ≤ 2 * a + (2 * a - 1))).card := by
      calc 2 * a - 1 = (Finset.Icc (2 * a + 1) (4 * a - 1)).card := by
            rw [Nat.card_Icc]; omega
        _ ≤ _ := Finset.card_le_card (fun x hx => by
            rw [Finset.mem_Icc] at hx
            rw [Finset.mem_filter]
            refine ⟨?_, by omega, by omega⟩
            by_cases hx1 : x = 2 * a + 1
            · rw [hx1]; exact hT i2 hi2τ (by omega)
            · exact hP.mono (Nat.zero_le _) (by omega) (hb x (by omega) (by omega)))
    omega

/-! ## The two-sided family `S_a` -/

/-- **The two-sided family is dead.**  Let `a ≥ 2` and `N ≥ 6a`, and let `D ⊆ [1, N]` contain
both anchors `a` and `N + 1 - a` and the whole block `[2a+2, N-2a-1]`, and nothing of
`[a+1, 2a+1]` or of `[N-2a, N-a]` (anything outside `[a, N+1-a]` is allowed).  Then `D` is
not co-reachable.  For `N = 6a` and `N = 6a + 1` these are the sets `S_a`; for `N ≥ 6a + 2`
they are also covered by `B_a`.  Proof: apply `left_side` to the play and to its mirror image;
whichever top panel (`2a+1` or `N-2a`) is placed second sees `2a` panels in its outer arm. -/
theorem not_coReach_twoSided {N a : Nat} {D : Finset Nat} (hD : D ⊆ Finset.Icc 1 N)
    (ha2 : 2 ≤ a) (hN : 6 * a ≤ N) (haL : a ∈ D) (haR : N + 1 - a ∈ D)
    (hgapL : ∀ x ∈ D, ¬ (a < x ∧ x < 2 * a + 2))
    (hgapR : ∀ x ∈ D, ¬ (N - 2 * a - 1 < x ∧ x < N + 1 - a))
    (hblk : ∀ x, 2 * a + 2 ≤ x → x ≤ N - 2 * a - 1 → x ∈ D) : ¬ CoReach N D := by
  classical
  intro h
  obtain ⟨n, Y, e, hP, hY0⟩ := play_of_coReach hD h
  subst hY0
  obtain ⟨τL, hτL, heL, hcL, h2L⟩ := left_side hP ha2 (by omega) haL hgapL
    (fun x h1 h2 => hblk x h1 (by omega))
  have hM := hP.mirror
  have hD0 := hP.sub 0 (Nat.zero_le _)
  obtain ⟨τR, hτR, heR, hcR, h2R⟩ := left_side hM ha2 (by omega)
    (by rw [mem_image_mirror hD0]; exact ⟨by omega, by omega, haR⟩)
    (fun x hx hx' => by
      rw [mem_image_mirror hD0] at hx
      exact hgapR _ hx.2.2 ⟨by omega, by omega⟩)
    (fun x h1 h2 => by
      rw [mem_image_mirror hD0]
      exact ⟨by omega, by omega, hblk _ (by omega) (by omega)⟩)
  have heRN := Finset.mem_Icc.1 (hP.sub (τR + 1) hτR (hP.mem_succ hτR))
  have heR' : e τR = N - 2 * a := by omega
  rw [mem_image_mirror (hP.sub τR (by omega))] at h2R
  have h2R' : N + 1 - 2 * a ∈ Y τR := h2R.2.2
  rcases Nat.lt_trichotomy τL τR with hlt | heq | hgt
  · -- the right top panel is placed second
    have hT : 2 * a + 1 ∈ Y τR := hP.mono (by omega) (by omega) (heL ▸ hP.mem_succ hτL)
    have h2 : 2 * a ∈ Y τR := hP.mono (by omega) (by omega) h2L
    rw [card_filter_image_mirror _ (hP.sub τR (by omega))] at hcR
    have : 2 * a ≤ ((Y τR).filter
        (fun x => 2 * a + 1 < N + 1 - x ∧ N + 1 - x ≤ 4 * a + 1)).card := by
      calc 2 * a = (Finset.Icc (N - 4 * a) (N - 2 * a - 1)).card := by
            rw [Nat.card_Icc]; omega
        _ ≤ _ := Finset.card_le_card (fun x hx => by
            rw [Finset.mem_Icc] at hx
            rw [Finset.mem_filter]
            refine ⟨?_, by omega, by omega⟩
            rcases Nat.lt_trichotomy x (2 * a + 1) with h' | h' | h'
            · rw [show x = 2 * a by omega]; exact h2
            · rw [h']; exact hT
            · exact hP.mono (Nat.zero_le _) (by omega) (hblk x (by omega) (by omega)))
    omega
  · rw [heq] at heL; omega
  · -- the left top panel is placed second
    have hT : N - 2 * a ∈ Y τL := hP.mono (by omega) (by omega) (heR' ▸ hP.mem_succ hτR)
    have h2 : N + 1 - 2 * a ∈ Y τL := hP.mono (by omega) (by omega) h2R'
    have : 2 * a ≤ ((Y τL).filter (fun x => 2 * a + 1 < x ∧ x ≤ 4 * a + 1)).card := by
      calc 2 * a = (Finset.Icc (2 * a + 2) (4 * a + 1)).card := by rw [Nat.card_Icc]; omega
        _ ≤ _ := Finset.card_le_card (fun x hx => by
            rw [Finset.mem_Icc] at hx
            rw [Finset.mem_filter]
            refine ⟨?_, by omega, by omega⟩
            by_cases h' : x ≤ N - 2 * a - 1
            · exact hP.mono (Nat.zero_le _) (by omega) (hblk x (by omega) h')
            · by_cases h'' : x = N - 2 * a
              · rw [h'']; exact hT
              · rw [show x = N + 1 - 2 * a by omega]; exact h2)
    omega

end EkStar
end Folds

namespace Folds
namespace EkStar

open Live2

/-- The two-sided set `S_a = {a, N+1-a} ∪ [2a+2, N-2a-1]`. -/
def sSet (a N : Nat) : Finset Nat := insert a (insert (N + 1 - a) (Finset.Icc (2 * a + 2) (N - 2 * a - 1)))

theorem mem_sSet {a N x : Nat} :
    x ∈ sSet a N ↔ x = a ∨ x = N + 1 - a ∨ (2 * a + 2 ≤ x ∧ x ≤ N - 2 * a - 1) := by
  simp [sSet]

/-- **`S_a` is dead** for every `a ≥ 2` and `N ≥ 6a` (in particular at `N = 6a` and
`N = 6a + 1`, where it is not covered by the one-sided family `B_a`). -/
theorem not_coReach_sSet {a N : Nat} (ha2 : 2 ≤ a) (hN : 6 * a ≤ N) :
    ¬ CoReach N (sSet a N) :=
  not_coReach_twoSided (fun x hx => by rw [mem_sSet] at hx; rw [Finset.mem_Icc]; omega) ha2 hN
    (by rw [mem_sSet]; omega) (by rw [mem_sSet]; omega)
    (fun x hx => by rw [mem_sSet] at hx; omega) (fun x hx => by rw [mem_sSet] at hx; omega)
    (fun x h1 h2 => by rw [mem_sSet]; omega)

theorem card_sSet {a N : Nat} (ha2 : 2 ≤ a) (hN : 6 * a ≤ N) :
    (sSet a N).card = N - 4 * a := by
  rw [sSet, Finset.card_insert_of_notMem (by rw [Finset.mem_insert, Finset.mem_Icc]; omega),
    Finset.card_insert_of_notMem (by rw [Finset.mem_Icc]; omega), Nat.card_Icc]
  omega

/-- The exception of `E_4`: `{2, 6, 7, 11}` is dead at `N = 12`. -/
theorem not_coReach_2_6_7_11 : ¬ CoReach 12 {2, 6, 7, 11} := by
  have : sSet 2 12 = {2, 6, 7, 11} := by decide
  rw [← this]; exact not_coReach_sSet le_rfl le_rfl

/-- `{2, 6, 7, 8, 12}` is dead at `N = 13` (`S_2`, `N = 6a + 1`). -/
theorem not_coReach_2_6_7_8_12 : ¬ CoReach 13 {2, 6, 7, 8, 12} := by
  have : sSet 2 13 = {2, 6, 7, 8, 12} := by decide
  rw [← this]; exact not_coReach_sSet le_rfl (by norm_num)

end EkStar
end Folds
