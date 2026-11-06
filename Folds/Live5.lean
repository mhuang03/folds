import Folds.Adjacent

/-!
# Live pairs, part 5: Beatty transfers and the pairs `{1, N}`

`experiments/live5/PROOFS.txt`.
-/

namespace Folds

/-! ## Arm counts of a copy given by a counting function -/

theorem CountEmb.countP_left {N p : Nat} {φ c : Nat → Nat} (h : CountEmb N p φ c) {m : Nat}
    (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    ((List.range' 1 p).map φ).countP (fun x => decide (m - reach N m ≤ x ∧ x < m)) =
      c (m - 1) - c (m - reach N m - 1) := by
  rw [List.countP_map]
  have hr : reach N m ≤ m - 1 := by unfold reach; omega
  have L : (List.range' 1 p).countP ((fun x => decide (m - reach N m ≤ x ∧ x < m)) ∘ φ) =
      (List.range' 1 p).countP
        (fun y => decide (c (m - reach N m - 1) + 1 ≤ y ∧ y ≤ c (m - 1))) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    have a := h.gal y (m - 1) hy.1
    have b := h.gal y (m - reach N m - 1) hy.1
    omega
  rw [L, countP_range'_interval]
  have := h.c_mono (show m - 1 ≤ N by omega); rw [h.top] at this
  have := h.c_mono (show m - reach N m - 1 ≤ m - 1 by omega)
  omega

theorem CountEmb.countP_right {N p : Nat} {φ c : Nat → Nat} (h : CountEmb N p φ c) {m : Nat}
    (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    ((List.range' 1 p).map φ).countP (fun x => decide (m < x ∧ x ≤ m + reach N m)) =
      c (m + reach N m) - c m := by
  rw [List.countP_map]
  have hr : m + reach N m ≤ N := by unfold reach; omega
  have R : (List.range' 1 p).countP ((fun x => decide (m < x ∧ x ≤ m + reach N m)) ∘ φ) =
      (List.range' 1 p).countP (fun y => decide (c m + 1 ≤ y ∧ y ≤ c (m + reach N m))) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    have a := h.gal y m hy.1
    have b := h.gal y (m + reach N m) hy.1
    omega
  rw [R, countP_range'_interval]
  have := h.c_mono hr; rw [h.top] at this
  have := h.c_mono (show m ≤ m + reach N m by omega)
  omega

/-- A panel outside the image does not raise the counting function. -/
theorem CountEmb.c_pred_of_not_mem {N p : Nat} {φ c : Nat → Nat} (h : CountEmb N p φ c)
    {m : Nat} (hm1 : 1 ≤ m) (hmN : m ≤ N) (hm : ∀ y, 1 ≤ y → y ≤ p → φ y ≠ m) :
    c m = c (m - 1) := by
  have hle := h.c_mono (show m - 1 ≤ m by omega)
  by_contra hne
  have hpos : 1 ≤ c m := by omega
  have hcp : c m ≤ p := by have := h.c_mono hmN; rw [h.top] at this; exact this
  have a := (h.gal (c m) m hpos).2 le_rfl
  have b := h.gal (c m) (m - 1) hpos
  have : ¬ φ (c m) ≤ m - 1 := fun h' => by have := b.1 h'; omega
  exact hm (c m) hpos hcp (by omega)

namespace Live5

open Live2 Live4 Adjacent

/-- The image list of an injective map on `[1, p]` is a permutation of its `toList`. -/
theorem image_toList_perm {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ) :
    ((Finset.Icc 1 p).image φ).toList.Perm ((List.range' 1 p).map φ) := by
  refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _)
    (hφ.nodup_map (List.nodup_range' ..) fun y hy => by
      rw [List.mem_range'_1] at hy; omega)).2 fun x => ?_
  simp only [Finset.mem_toList, Finset.mem_image, Finset.mem_Icc, List.mem_map,
    List.mem_range'_1]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, ⟨hy.1, by omega⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, ⟨hy.1, by omega⟩, rfl⟩

/-! ## Right-aligned Beatty copies are co-reachable -/

/-- The key inequality: for `h ≤ 1` and `k = c(m - 1)`, `2 k N ≤ 2 p m + h - 1`. -/
theorem beatty_key {N p h m : Nat} (hN : 0 < N) (hp : 1 ≤ p) (hm : 1 ≤ m) (h1 : h ≤ 1) :
    2 * (beattyCnt N p h (m - 1)) ≤ (2 * (p * m) + h - 1) / N := by
  unfold beattyCnt
  have e : p * (m - 1) + p + h - 1 = p * m + h - 1 := by
    rw [Nat.mul_sub_one]; have : p ≤ p * m := Nat.le_mul_of_pos_right p hm; omega
  rw [e, Nat.le_div_iff_mul_le hN]
  have := Nat.div_mul_le_self (p * m + h - 1) N
  have : p ≤ p * m := Nat.le_mul_of_pos_right p hm
  rw [Nat.mul_assoc]
  omega

/-- **Right-aligned Beatty copies pull every other panel to the right**: for `h ≤ 1` the
Beatty set `{⌊(rN - h)/p⌋}` satisfies the criterion of Theorem G with the centre right of
the strip. -/
theorem inward_beatty {N p h : Nat} (hp : 1 ≤ p) (hh : h + 2 * p ≤ N + 1) (h1 : h ≤ 1) :
    Inward N (2 * N + 1) ((Finset.Icc 1 p).image (beatty N p h)) := by
  have hN : 0 < N := by omega
  have hc := countEmb_beatty hp hh
  have hφ := winEmb_beatty hp hh
  have hperm := image_toList_perm hφ
  have hnd := Finset.nodup_toList ((Finset.Icc 1 p).image (beatty N p h))
  intro m hm1 hmN hmB
  refine ⟨by omega, fun _ => ?_, fun h' => by omega⟩
  have hnot : ∀ y, 1 ≤ y → y ≤ p → beatty N p h y ≠ m := fun y hy1 hyp e =>
    hmB (Finset.mem_image.2 ⟨y, Finset.mem_Icc.2 ⟨hy1, hyp⟩, e⟩)
  have hcm := hc.c_pred_of_not_mem hm1 hmN hnot
  rw [leftCount_eq hnd, rightCount_eq hnd, hperm.countP_eq, hperm.countP_eq,
    hc.countP_left hm1 hmN, hc.countP_right hm1 hmN, hcm]
  have key := beatty_key (h := h) hN hp hm1 h1
  rcases Nat.le_total (m - 1) (N - m) with hle | hle
  · have hr : reach N m = m - 1 := by unfold reach; omega
    rw [hr, show m - (m - 1) - 1 = 0 by omega, hc.zero,
      show m + (m - 1) = 2 * m - 1 by omega]
    have e : beattyCnt N p h (2 * m - 1) = (2 * (p * m) + h - 1) / N := by
      unfold beattyCnt
      congr 1
      rw [Nat.mul_sub_one, Nat.mul_left_comm]
      have : p ≤ 2 * (p * m) := by
        have := Nat.le_mul_of_pos_right p hm1; omega
      omega
    rw [e]; omega
  · have hr : reach N m = N - m := by unfold reach; omega
    rw [hr, show m + (N - m) = N by omega, hc.top,
      show m - (N - m) - 1 = 2 * m - N - 1 by omega]
    have e : beattyCnt N p h (2 * m - N - 1) + p = (2 * (p * m) + h - 1) / N := by
      unfold beattyCnt
      obtain ⟨t, ht⟩ : ∃ t, 2 * m = N + 1 + t := ⟨2 * m - N - 1, by omega⟩
      have et : 2 * m - N - 1 = t := by omega
      have e2 : 2 * (p * m) = p * N + p + p * t := by
        rw [show 2 * (p * m) = p * (2 * m) by ring, ht, Nat.mul_add, Nat.mul_add, Nat.mul_one]
      have e1 : p * (2 * m - N - 1) + p + h - 1 = (2 * (p * m) + h - 1) - p * N := by
        rw [et]; omega
      rw [e1]
      conv_rhs => rw [show 2 * (p * m) + h - 1 = (2 * (p * m) + h - 1 - p * N) + p * N by
        omega]
      rw [Nat.add_mul_div_right _ _ hN]
    have := hc.c_mono (show m - 1 ≤ N by omega); rw [hc.top] at this
    omega

/-- Right-aligned Beatty copies are co-reachable. -/
theorem coReach_beatty {N p h : Nat} (hp : 1 ≤ p) (hh : h + 2 * p ≤ N + 1) (h1 : h ≤ 1) :
    CoReach N ((Finset.Icc 1 p).image (beatty N p h)) := by
  refine coReach_of_inward (fun x hx => ?_) (inward_beatty hp hh h1)
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
  rw [Finset.mem_Icc] at hy ⊢
  exact (winEmb_beatty hp hh).bound y hy.1 hy.2

/-- **Beatty transfer**: co-reachable sets of the `p`-strip stay co-reachable through a
right-aligned Beatty copy (`h ≤ 1`). -/
theorem coReach_beatty_transfer {N p h : Nat} (hp : 1 ≤ p) (hh : h + 2 * p ≤ N + 1)
    (h1 : h ≤ 1) {D : Finset Nat} (hDs : D ⊆ Finset.Icc 1 p) (hD : CoReach p D) :
    CoReach N (D.image (beatty N p h)) :=
  coReach_winEmb (winEmb_beatty hp hh) (coReach_beatty hp hh h1) hDs hD

/-! ## Splits into two copies -/

/-- The empty set is co-reachable: every strip has a full semi-symmetric sequence. -/
theorem coReach_empty (q : Nat) : CoReach q ∅ := by
  refine coReach_of_inward (c2 := 1) (by simp) ?_
  intro m hm1 _ _
  refine ⟨by omega, fun h => by omega, fun _ => ?_⟩
  simp [leftCount, rightCount]

theorem exists_full (q : Nat) :
    ∃ σ : List Nat, σ.Nodup ∧ σ.toFinset = Finset.Icc 1 q ∧ SemiSymmetric q σ := by
  have h := coReach_empty q
  unfold CoReach g at h
  rw [Finset.card_pos] at h
  obtain ⟨σ, hσ⟩ := h
  rw [mem_semiOrders] at hσ
  exact ⟨σ, hσ.1.1, by rw [hσ.1.2, Finset.sdiff_empty], hσ.2⟩

/-- **Transfer through a split** `[N] = φ([p]) ⊔ ψ([q])` into two window copies: the
complement of `φ([p])` is the copy `ψ([q])`, ordered by any full sequence of the `q`-strip,
so co-reachable sets of the `p`-strip stay co-reachable.  (Instances: the general doubling
splits `N = (2j+1) n` of `Copies.lean`, `split_res`, in both directions.) -/
theorem coReach_split {N p q : Nat} {φ ψ : Nat → Nat} (hs : Split N p q φ ψ)
    {D : Finset Nat} (hDs : D ⊆ Finset.Icc 1 p) (hD : CoReach p D) :
    CoReach N (D.image φ) := by
  refine coReach_winEmb hs.emb₁ ?_ hDs hD
  obtain ⟨σ, hnd, hset, hv⟩ := exists_full q
  have hb : ∀ y ∈ σ, 1 ≤ y ∧ y ≤ q := fun y hy => by
    have := List.mem_toFinset.2 hy; rw [hset, Finset.mem_Icc] at this; exact this
  have hndc := hs.cover.nodup_iff.2 (List.nodup_range' ..)
  unfold g
  rw [Finset.card_pos]
  refine ⟨σ.map ψ, mem_semiOrders.2 ⟨⟨hs.emb₂.nodup_map hnd hb, ?_⟩,
    (hs.emb₂.semiSymmetric_iff hnd hb).2 hv⟩⟩
  ext x
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_sdiff, Finset.mem_Icc,
    Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' := hb y hy
    have hmem : ψ y ∈ (List.range' 1 p).map φ ++ (List.range' 1 q).map ψ :=
      List.mem_append_right _ (List.mem_map.2 ⟨y, List.mem_range'_1.2 ⟨hy'.1, by omega⟩, rfl⟩)
    have := hs.cover.subset hmem
    rw [List.mem_range'_1] at this
    refine ⟨⟨this.1, by omega⟩, ?_⟩
    rintro ⟨z, hz, e⟩
    exact (List.nodup_append.1 hndc).2.2 (φ z)
      (List.mem_map.2 ⟨z, List.mem_range'_1.2 ⟨hz.1, by omega⟩, rfl⟩) (ψ y)
      (List.mem_map.2 ⟨y, List.mem_range'_1.2 ⟨hy'.1, by omega⟩, rfl⟩) e
  · rintro ⟨hx, hnot⟩
    have : x ∈ (List.range' 1 p).map φ ++ (List.range' 1 q).map ψ :=
      hs.cover.symm.subset (List.mem_range'_1.2 ⟨hx.1, by omega⟩)
    rcases List.mem_append.1 this with h | h
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 h
      rw [List.mem_range'_1] at hz
      exact absurd ⟨z, ⟨hz.1, by omega⟩, rfl⟩ hnot
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
      rw [List.mem_range'_1] at hy
      exact ⟨y, by rw [← List.mem_toFinset, hset, Finset.mem_Icc]; omega, rfl⟩

/-! ## Counting helpers -/

theorem countP_odd_le (B : Nat) : ∀ R, (List.range' 1 R).countP
    (fun d => decide (d % 2 = 1 ∧ d ≤ B)) = (min R B + 1) / 2
  | 0 => by simp
  | R + 1 => by
    rw [List.range'_concat, List.countP_append, countP_odd_le B R]
    simp only [List.countP_cons, List.countP_nil]
    by_cases h : (1 + R) % 2 = 1 ∧ 1 + R ≤ B
    · simp [h]; omega
    · simp [h]; omega

theorem countP_eq_le (a : Nat) (R : Nat) :
    (List.range' 1 R).countP (fun d => decide (d = a)) ≤ if a ≤ R then 1 else 0 := by
  have := countP_range'_interval a a R
  rw [show (fun d => decide (a ≤ d ∧ d ≤ a)) = fun d => decide (d = a) by
    funext d; simp only [decide_eq_decide]; omega] at this
  rw [this]; split_ifs <;> omega

theorem countP_or_le (l : List Nat) (f g : Nat → Bool) :
    l.countP (fun d => f d || g d) ≤ l.countP f + l.countP g := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    cases f a <;> cases g a <;> simp <;> omega

theorem countP_add_le (l : List Nat) (f g h : Nat → Bool)
    (hd : ∀ x ∈ l, ¬ (f x = true ∧ g x = true)) (hfh : ∀ x ∈ l, f x = true → h x = true)
    (hgh : ∀ x ∈ l, g x = true → h x = true) :
    l.countP f + l.countP g ≤ l.countP h := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have := ih (fun x hx => hd x (List.mem_cons_of_mem a hx))
      (fun x hx => hfh x (List.mem_cons_of_mem a hx)) (fun x hx => hgh x (List.mem_cons_of_mem a hx))
    have h1 := hd a (List.mem_cons_self ..)
    have h2 := hfh a (List.mem_cons_self ..)
    have h3 := hgh a (List.mem_cons_self ..)
    cases hf : f a <;> cases hg : g a <;> cases hh : h a <;> simp_all <;> omega

theorem leftCount_finset (N m : Nat) (S : Finset Nat) :
    leftCount N S.toList m = (List.range' 1 (reach N m)).countP (fun d => decide (m - d ∈ S)) := by
  unfold leftCount; simp only [Finset.mem_toList]

theorem rightCount_finset (N m : Nat) (S : Finset Nat) :
    rightCount N S.toList m = (List.range' 1 (reach N m)).countP (fun d => decide (m + d ∈ S)) := by
  unfold rightCount; simp only [Finset.mem_toList]

/-! ## The set `F = {2, 4, …, n-4} ∪ {n-1}` (n even): `F` and its complement satisfy Theorem G -/

/-- `F = {2, 4, …, n - 4} ∪ {n - 1}`. -/
def fSet (n : Nat) : Finset Nat :=
  (Finset.Icc 1 n).filter (fun x => (x % 2 = 0 ∧ x + 4 ≤ n) ∨ x = n - 1)

theorem mem_fSet {n x : Nat} :
    x ∈ fSet n ↔ 1 ≤ x ∧ x ≤ n ∧ ((x % 2 = 0 ∧ x + 4 ≤ n) ∨ x = n - 1) := by
  unfold fSet; rw [Finset.mem_filter, Finset.mem_Icc]; tauto

/-- `F` pulls no panel to the right (centre left of the strip). -/
theorem inward_fSet {n : Nat} (hn : 6 ≤ n) (he : n % 2 = 0) : Inward n 0 (fSet n) := by
  intro m hm1 hmn hmF
  refine ⟨by omega, fun h => by omega, fun _ => ?_⟩
  rw [mem_fSet] at hmF
  rw [leftCount_finset, rightCount_finset]
  simp only [mem_fSet]
  rcases Nat.lt_or_ge (m + 2) n with hlt | hge
  · -- `m` odd, `m ≤ n - 3`
    have hr1 : reach n m ≤ m - 1 := by unfold reach; omega
    have hr2 : reach n m ≤ n - m := by unfold reach; omega
    have L : (List.range' 1 (reach n m)).countP (fun d => decide
        (1 ≤ m - d ∧ m - d ≤ n ∧ ((m - d) % 2 = 0 ∧ m - d + 4 ≤ n ∨ m - d = n - 1))) =
        (List.range' 1 (reach n m)).countP (fun d => decide (d % 2 = 1 ∧ d ≤ reach n m)) := by
      apply List.countP_congr; intro d hd; rw [List.mem_range'_1] at hd
      simp only [decide_eq_true_eq]; omega
    have R : (List.range' 1 (reach n m)).countP (fun d => decide
        (1 ≤ m + d ∧ m + d ≤ n ∧ ((m + d) % 2 = 0 ∧ m + d + 4 ≤ n ∨ m + d = n - 1))) ≤
        (List.range' 1 (reach n m)).countP (fun d => decide (d % 2 = 1 ∧ d ≤ n - 4 - m)) +
        (List.range' 1 (reach n m)).countP (fun d => decide (d = n - 1 - m)) := by
      refine le_trans (le_of_eq (List.countP_congr fun d hd => ?_)) (countP_or_le _ _ _)
      rw [List.mem_range'_1] at hd
      simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
    rw [L, countP_odd_le]
    rw [countP_odd_le] at R
    have := countP_eq_le (n - 1 - m) (reach n m)
    split_ifs at this <;> omega
  · rcases Nat.lt_or_ge m n with hlt' | hge'
    · -- `m = n - 2`
      have hr : reach n m = 2 := by unfold reach; omega
      rw [hr]
      simp only [List.range', List.countP_cons, List.countP_nil]
      split_ifs <;> simp only [decide_eq_true_eq] at * <;> omega
    · have hr : reach n m = 0 := by unfold reach; omega
      rw [hr]; simp

/-- The complement of `F` pulls no panel to the left (centre right of the strip). -/
theorem inward_fSet_compl {n : Nat} (hn : 6 ≤ n) (he : n % 2 = 0) :
    Inward n (2 * n + 1) (Finset.Icc 1 n \ fSet n) := by
  intro m hm1 hmn hmG
  refine ⟨by omega, fun _ => ?_, fun h => by omega⟩
  have hmF : m ∈ fSet n := by
    by_contra h; exact hmG (Finset.mem_sdiff.2 ⟨Finset.mem_Icc.2 ⟨hm1, hmn⟩, h⟩)
  rw [mem_fSet] at hmF
  rw [leftCount_finset, rightCount_finset]
  simp only [Finset.mem_sdiff, Finset.mem_Icc, mem_fSet]
  rcases hmF.2.2 with ⟨hev, hm4⟩ | hm
  · have hr1 : reach n m ≤ m - 1 := by unfold reach; omega
    have hr2 : reach n m ≤ n - m := by unfold reach; omega
    have L : (List.range' 1 (reach n m)).countP (fun d => decide
        ((1 ≤ m - d ∧ m - d ≤ n) ∧ ¬(1 ≤ m - d ∧ m - d ≤ n ∧
          ((m - d) % 2 = 0 ∧ m - d + 4 ≤ n ∨ m - d = n - 1)))) =
        (List.range' 1 (reach n m)).countP (fun d => decide (d % 2 = 1 ∧ d ≤ reach n m)) := by
      apply List.countP_congr; intro d hd; rw [List.mem_range'_1] at hd
      simp only [decide_eq_true_eq]; omega
    have R : (List.range' 1 (reach n m)).countP (fun d => decide (d % 2 = 1 ∧ d ≤ n - 3 - m)) +
        (List.range' 1 (reach n m)).countP (fun d => decide (d = n - 2 - m)) ≤
        (List.range' 1 (reach n m)).countP (fun d => decide
        ((1 ≤ m + d ∧ m + d ≤ n) ∧ ¬(1 ≤ m + d ∧ m + d ≤ n ∧
          ((m + d) % 2 = 0 ∧ m + d + 4 ≤ n ∨ m + d = n - 1)))) := by
      refine countP_add_le _ _ _ _ (fun d hd => ?_) (fun d hd => ?_) (fun d hd => ?_)
      all_goals rw [List.mem_range'_1] at hd; simp only [decide_eq_true_eq]; omega
    rw [L, countP_odd_le]
    rw [countP_odd_le] at R
    have e := countP_range'_interval (n - 2 - m) (n - 2 - m) (reach n m)
    rw [show (fun d => decide (n - 2 - m ≤ d ∧ d ≤ n - 2 - m)) = fun d => decide (d = n - 2 - m)
      by funext d; simp only [decide_eq_decide]; omega] at e
    rw [e] at R
    omega
  · have hr : reach n m = 1 := by unfold reach; omega
    rw [hr]
    simp only [List.range', List.countP_cons, List.countP_nil]
    split_ifs <;> simp only [decide_eq_true_eq] at * <;> omega

/-! ## The copy `X_N = {1, 4, 6, …, N-3, N}` (`N = 2n - 1`, `n` even) is co-reachable

Its complement `{2, N-1} ∪ {3, 5, …, N-2}` is the image of `[1, n]` under `psiX`
(`1 ↦ 2`, `n ↦ N - 1`, `y ↦ 2y - 1`), which preserves the window relation except for the
pairs `(1, 2)` and `(n, n - 1)`.  A full sequence of the `n`-strip placing `1` before `2` and
`n` before `n - 1` is `τ ++ reverse φ`, with `τ` ordering the complement of `F` and `φ`
ordering `F` from scratch (both by Theorem G). -/

/-- `1 ↦ 2`, `n ↦ 2n - 2`, `y ↦ 2y - 1`. -/
def psiX (n y : Nat) : Nat := if y = 1 then 2 else if y = n then 2 * n - 2 else 2 * y - 1

/-- `1 ↦ 1`, `n - 1 ↦ 2n - 1`, `y ↦ 2y`: the copy `X_N`. -/
def chiX (n y : Nat) : Nat := if y = 1 then 1 else if y = n - 1 then 2 * n - 1 else 2 * y

/-- The pairs where `psiX` does not preserve the window relation. -/
def excX (n i j : Nat) : Prop := (i = 1 ∧ j = 2) ∨ (i = n ∧ j = n - 1)

theorem agree_psiX {n i j : Nat} (hn : 6 ≤ n) (hi1 : 1 ≤ i) (hin : i ≤ n) (hj1 : 1 ≤ j)
    (hjn : j ≤ n) (_hij : i ≠ j) (he : ¬ excX n i j) : Agree (2 * n - 1) n (psiX n) i j := by
  unfold excX at he; unfold Agree psiX reach; split_ifs <;> omega

theorem psiX_inj {n a b : Nat} (hn : 6 ≤ n) (ha1 : 1 ≤ a) (han : a ≤ n) (hb1 : 1 ≤ b)
    (hbn : b ≤ n) (e : psiX n a = psiX n b) : a = b := by
  unfold psiX at e; split_ifs at e <;> omega

theorem winEmb_chiX {n : Nat} (hn : 6 ≤ n) : WinEmb (2 * n - 1) (n - 1) (chiX n) := by
  refine ⟨fun y h1 h2 => ?_, fun x y hx1 hxp hy1 hyp e => ?_, fun j y hj1 hjp hy1 hyp => ?_,
    fun j y hj1 hjp hy1 hyp => ?_⟩
  · unfold chiX; split_ifs <;> omega
  · unfold chiX at e; split_ifs at e <;> omega
  · unfold chiX reach; split_ifs <;> omega
  · unfold chiX reach; split_ifs <;> omega

theorem mem_image_psiX {n x : Nat} (hn : 6 ≤ n) :
    x ∈ (Finset.Icc 1 n).image (psiX n) ↔
      x = 2 ∨ x = 2 * n - 2 ∨ (x % 2 = 1 ∧ 3 ≤ x ∧ x ≤ 2 * n - 3) := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rw [Finset.mem_Icc] at hy; unfold psiX; split_ifs <;> omega
  · intro h
    rcases h with rfl | rfl | h
    · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, by simp [psiX]⟩
    · exact ⟨n, Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, by unfold psiX; split_ifs <;> omega⟩
    · exact ⟨(x + 1) / 2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by
        unfold psiX; split_ifs <;> omega⟩

theorem mem_image_chiX {n x : Nat} (hn : 6 ≤ n) :
    x ∈ (Finset.Icc 1 (n - 1)).image (chiX n) ↔
      x = 1 ∨ x = 2 * n - 1 ∨ (x % 2 = 0 ∧ 4 ≤ x ∧ x ≤ 2 * n - 4) := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; rw [Finset.mem_Icc] at hy; unfold chiX; split_ifs <;> omega
  · intro h
    rcases h with rfl | rfl | h
    · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, by simp [chiX]⟩
    · exact ⟨n - 1, Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, by unfold chiX; split_ifs <;> omega⟩
    · exact ⟨x / 2, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by
        unfold chiX; split_ifs <;> omega⟩

/-- An ordering of `[1, n]` given by a list with the right set is a complete sequence. -/
theorem isFoldSeq_of_toFinset {n : Nat} {l : List Nat} (hnd : l.Nodup)
    (hs : l.toFinset = Finset.Icc 1 n) : IsFoldSeq n l := by
  unfold IsFoldSeq
  rw [List.perm_ext_iff_of_nodup hnd (List.nodup_range' ..)]
  intro x
  rw [← List.mem_toFinset, hs, Finset.mem_Icc, List.mem_range'_1]
  omega

/-- A set `B ⊆ [1, N]` that is co-reachable: an ordering of its complement. -/
theorem coReach_list {N : Nat} {B : Finset Nat} (h : CoReach N B) :
    ∃ l : List Nat, l.Nodup ∧ l.toFinset = Finset.Icc 1 N \ B ∧ SemiSymmetric N l := by
  unfold CoReach g at h
  rw [Finset.card_pos] at h
  obtain ⟨l, hl⟩ := h
  rw [mem_semiOrders] at hl
  exact ⟨l, hl.1.1, hl.1.2, hl.2⟩

/-- **`X_N` is co-reachable** (`N = 2n - 1`, `n` even, `n ≥ 6`). -/
theorem coReach_X {n : Nat} (hn : 6 ≤ n) (he : n % 2 = 0) :
    0 < g (2 * n - 1) (Finset.Icc 1 (2 * n - 1) \ (Finset.Icc 1 (n - 1)).image (chiX n)) := by
  have hF : fSet n ⊆ Finset.Icc 1 n := fun x hx => by
    rw [mem_fSet] at hx; rw [Finset.mem_Icc]; omega
  obtain ⟨τ, hτn, hτs, hτv⟩ := coReach_list (coReach_of_inward hF (inward_fSet hn he))
  obtain ⟨φ, hφn, hφs, hφv⟩ := coReach_list (coReach_of_inward Finset.sdiff_subset
    (inward_fSet_compl hn he))
  rw [Finset.sdiff_sdiff_eq_self hF] at hφs
  have hτm : ∀ x, x ∈ τ ↔ x ∈ Finset.Icc 1 n ∧ x ∉ fSet n := fun x => by
    rw [← List.mem_toFinset, hτs, Finset.mem_sdiff]
  have hφm : ∀ x, x ∈ φ ↔ x ∈ fSet n := fun x => by rw [← List.mem_toFinset, hφs]
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = τ ++ φ.reverse := ⟨_, rfl⟩
  have hρn : ρ.Nodup := by
    rw [hρ, List.nodup_append]
    refine ⟨hτn, List.nodup_reverse.2 hφn, fun a ha b hb e => ?_⟩
    subst e
    rw [List.mem_reverse, hφm] at hb
    exact ((hτm a).1 ha).2 hb
  have hρs : ρ.toFinset = Finset.Icc 1 n := by
    ext x
    rw [List.mem_toFinset, hρ, List.mem_append, List.mem_reverse, hτm, hφm]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact hF h
    · intro h; by_cases hx : x ∈ fSet n
      · exact Or.inr hx
      · exact Or.inl ⟨h, hx⟩
  have hρb : ∀ x ∈ ρ, 1 ≤ x ∧ x ≤ n := fun x hx => by
    have := List.mem_toFinset.2 hx; rw [hρs, Finset.mem_Icc] at this; exact this
  have hρf := isFoldSeq_of_toFinset hρn hρs
  have hρv : SemiSymmetric n ρ := by
    subst hρ
    exact semiSymmetric_append_rev hρf hτv (by rw [List.reverse_reverse]; exact hφv)
  have h1 : (1 : Nat) ∉ fSet n := by rw [mem_fSet]; omega
  have hn' : n ∉ fSet n := by rw [mem_fSet]; omega
  have h2 : (2 : Nat) ∈ fSet n := by rw [mem_fSet]; omega
  have hn1 : n - 1 ∈ fSet n := by rw [mem_fSet]; omega
  -- `1` and `n` come before `2` and `n - 1`
  have hprec : Prec (excX n) ρ := by
    intro p hp j hj hex
    subst hρ
    have hpos : ∀ a, (τ ++ φ.reverse)[p] = a → a ∉ fSet n → p < τ.length ∧ j ∈ τ := by
      intro a ha haF
      have hpt : p < τ.length := by
        by_contra hge
        push Not at hge
        have : (τ ++ φ.reverse)[p] ∈ φ.reverse := by
          rw [List.getElem_append_right hge]; exact List.getElem_mem _
        rw [List.mem_reverse, hφm, ha] at this
        exact haF this
      refine ⟨hpt, ?_⟩
      rw [List.take_append_of_le_length hpt.le] at hj
      exact List.mem_of_mem_take hj
    rcases hex with ⟨ha, rfl⟩ | ⟨ha, rfl⟩
    · exact ((hτm 2).1 (hpos 1 ha h1).2).2 h2
    · exact ((hτm (n - 1)).1 (hpos n ha hn').2).2 hn1
  have hmap : SemiSymmetric (2 * n - 1) (ρ.map (psiX n)) :=
    semiSymmetric_near hρb hρn hρv hprec (fun a b ha1 han hb1 hbn e => psiX_inj hn ha1 han hb1 hbn e)
      (fun _ _ hi1 hin hj1 hjn hij he' => agree_psiX hn hi1 hin hj1 hjn hij he')
  unfold g
  rw [Finset.card_pos]
  refine ⟨ρ.map (psiX n), mem_semiOrders.2 ⟨⟨nodup_map_of_injOn hρn fun a ha b hb e =>
    psiX_inj hn (hρb a ha).1 (hρb a ha).2 (hρb b hb).1 (hρb b hb).2 e, ?_⟩, hmap⟩⟩
  ext x
  have hx : x ∈ ρ.map (psiX n) ↔ x ∈ (Finset.Icc 1 n).image (psiX n) := by
    rw [List.mem_map, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, e⟩
      exact ⟨a, by rw [← hρs, List.mem_toFinset]; exact ha, e⟩
    · rintro ⟨a, ha, e⟩
      exact ⟨a, by rw [← List.mem_toFinset, hρs]; exact ha, e⟩
  rw [List.mem_toFinset, hx, mem_image_psiX hn, Finset.mem_sdiff, mem_image_chiX hn,
    Finset.mem_Icc]
  omega

/-- **Transfer through `X_N`**: `{1, n - 1}` co-reachable in `[n - 1]` gives `{1, 2n - 1}`
co-reachable in `[2n - 1]`. -/
theorem coReach_one_X {n : Nat} (hn : 6 ≤ n) (he : n % 2 = 0)
    (h : CoReach (n - 1) {1, n - 1}) : CoReach (2 * n - 1) {1, 2 * n - 1} := by
  have := coReach_winEmb (winEmb_chiX hn) (coReach_X hn he) (D := {1, n - 1})
    (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]; omega) h
  convert this using 1
  rw [Finset.image_insert, Finset.image_singleton]
  have e1 : chiX n 1 = 1 := by simp [chiX]
  have e2 : chiX n (n - 1) = 2 * n - 1 := by unfold chiX; split_ifs <;> omega
  rw [e1, e2]

/-! ## `{1, N}` for odd `N` -/

theorem wit13 : witOK 13 (1, 13, [10, 12, 5, 6, 8, 11, 9, 2, 3, 4, 7]) = true := by
  decide +kernel

theorem wit15 : witOK 15 (1, 15, [12, 14, 4, 7, 13, 6, 9, 10, 11, 2, 3, 5, 8]) = true := by
  decide +kernel

theorem coReach_of_witOK {N u v : Nat} {l : List Nat} (h : witOK N (u, v, l) = true) :
    CoReach N {u, v} := by
  unfold witOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hnd, hs⟩, hv⟩ := h
  unfold CoReach g
  rw [Finset.card_pos]
  exact ⟨l, mem_semiOrders.2 ⟨⟨hnd, hs⟩, hv⟩⟩

/-- **`{1, N}` is co-reachable for every odd `N ≠ 7`.**  Strong induction:
`N ≡ 1 (mod 4)`: through the odd class (the Beatty copy `X(N, (N+1)/2, 0)`) from
`{1, (N+1)/2}`; `N ≡ 3 (mod 4)`: through `X_N` from `{1, (N-1)/2}`; the recursion hits the
dead pair `{1, 7}` only from `N = 13, 15`, which are checked directly. -/
theorem coReach_one_N : ∀ N, N % 2 = 1 → N ≠ 7 → CoReach N {1, N} := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hodd h7
    by_cases hsmall : N ≤ 3
    · apply coReach_small
      have : Finset.Icc 1 N \ {1, N} ⊆ Finset.Icc 2 2 := by
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_insert,
          Finset.mem_singleton] at hx
        rw [Finset.mem_Icc]; omega
      have := Finset.card_le_card this
      simpa using this
    by_cases h12 : N ≤ 12
    · refine coReach_base h12 le_rfl (by omega) le_rfl ?_
      interval_cases N <;> simp_all [deadB]
    by_cases h13 : N = 13
    · subst h13; exact coReach_of_witOK (N := 13) (u := 1) (v := 13) wit13
    by_cases h15 : N = 15
    · subst h15; exact coReach_of_witOK (N := 15) (u := 1) (v := 15) wit15
    rcases Nat.lt_or_ge (N % 4) 2 with h1 | h3
    · -- `N ≡ 1 (mod 4)`
      have hp := ih ((N + 1) / 2) (by omega) (by omega) (by omega)
      have := coReach_beatty_transfer (N := N) (p := (N + 1) / 2) (h := 0) (by omega)
        (by omega) (by omega) (D := {1, (N + 1) / 2}) (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Finset.mem_Icc]; omega) hp
      convert this using 1
      rw [Finset.image_insert, Finset.image_singleton]
      have e1 : beatty N ((N + 1) / 2) 0 1 = 1 := by
        unfold beatty
        rw [Nat.one_mul, Nat.sub_zero]
        apply Nat.div_eq_of_lt_le <;> omega
      have e2 : beatty N ((N + 1) / 2) 0 ((N + 1) / 2) = N := by
        unfold beatty
        rw [Nat.sub_zero, Nat.mul_comm, Nat.mul_div_cancel _ (by omega)]
      rw [e1, e2]
    · -- `N ≡ 3 (mod 4)`
      have hp := ih ((N - 1) / 2) (by omega) (by omega) (by omega)
      have := coReach_one_X (n := (N + 1) / 2) (by omega) (by omega)
        (by rw [show (N + 1) / 2 - 1 = (N - 1) / 2 by omega]; exact hp)
      rwa [show 2 * ((N + 1) / 2) - 1 = N by omega] at this

/-! ## The enlarged proven family -/

/-- `Cov5`: the closure of `Cov3` and of the pairs `{1, N}` (`N` odd, `N ≠ 7`) under residue
transfers through good classes and through the multiples of `q` (`q ∣ N + 1`), transfers
through right-aligned Beatty copies (`h ≤ 1`) and through splits into two window copies
(e.g. the doubling splits `split_res`), and the mirror. -/
inductive Cov5 : Nat → Finset Nat → Prop
  | cov3 {N : Nat} {D : Finset Nat} : Cov3 N D → Cov5 N D
  | one {N : Nat} : N % 2 = 1 → N ≠ 7 → Cov5 N {1, N}
  | res {q N s : Nat} {D : Finset Nat} : 2 ≤ q → q ≤ N → Good q (N % q) s →
      D ⊆ Finset.Icc 1 (ccount q s N) → Cov5 (ccount q s N) D → Cov5 N (D.image (cls q s))
  | mult {q N : Nat} {D : Finset Nat} : 2 ≤ q → q ≤ N → (N + 1) % q = 0 →
      D ⊆ Finset.Icc 1 (ccount q q N) → Cov5 (ccount q q N) D → Cov5 N (D.image (cls q q))
  | beatty {N p h : Nat} {D : Finset Nat} : 1 ≤ p → h + 2 * p ≤ N + 1 → h ≤ 1 →
      D ⊆ Finset.Icc 1 p → Cov5 p D → Cov5 N (D.image (beatty N p h))
  | split {N p q : Nat} {φ ψ : Nat → Nat} {D : Finset Nat} : Split N p q φ ψ →
      D ⊆ Finset.Icc 1 p → Cov5 p D → Cov5 N (D.image φ)
  | mirror {N : Nat} {D : Finset Nat} : Cov5 N D → Cov5 N (D.image (N + 1 - ·))

theorem Cov5.coReach {N : Nat} {D : Finset Nat} (h : Cov5 N D) : CoReach N D := by
  induction h with
  | cov3 h => exact h.coReach
  | one h1 h7 => exact coReach_one_N _ h1 h7
  | res hq2 hqN hg hDs _ ih => exact coReach_good (by omega) hqN hg hDs ih
  | mult hq2 hqN hN hDs _ ih => exact coReach_mult_transfer (by omega) hqN hN hDs ih
  | beatty hp hh h1 hDs _ ih => exact coReach_beatty_transfer hp hh h1 hDs ih
  | split hs hDs _ ih => exact coReach_split hs hDs ih
  | mirror _ ih => exact coReach_mirror ih

/-- Doubling split `N = (2j+1) n`, the odd positions of each block (a copy of the
`(j+1)n`-strip). -/
theorem Cov5.oddRes {j n : Nat} (hj : 1 ≤ j) {D : Finset Nat}
    (hDs : D ⊆ Finset.Icc 1 ((j + 1) * n)) (h : Cov5 ((j + 1) * n) D) :
    Cov5 ((2 * j + 1) * n) (D.image (oddRes j)) :=
  Cov5.split (split_res hj n).symm hDs h

/-- Doubling split `N = (2j+1) n`, the even positions of each block. -/
theorem Cov5.evenRes {j n : Nat} (hj : 1 ≤ j) {D : Finset Nat}
    (hDs : D ⊆ Finset.Icc 1 (j * n)) (h : Cov5 (j * n) D) :
    Cov5 ((2 * j + 1) * n) (D.image (evenRes j)) :=
  Cov5.split (split_res hj n) hDs h

/-- Every valid 2-prefix whose set is in the family is live. -/
theorem Cov5.extends {N u v : Nat} (h : Cov5 N {u, v}) (hu : 1 ≤ u ∧ u ≤ N)
    (hv : 1 ≤ v ∧ v ≤ N) (huv : u ≠ v) (hval : SemiSymmetric N [u, v]) :
    Extends N [u, v] := by
  rw [extends_iff_coReach (by simp [huv]) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption) hval]
  convert h.coReach using 2
  ext x; simp

/-- **`{1, N}` as a prefix**: for odd `N ≥ 3`, `N ≠ 7`, the valid 2-prefix `[1, N]` is live. -/
theorem extends_one_N {N : Nat} (h1 : N % 2 = 1) (h7 : N ≠ 7) (h3 : 3 ≤ N) :
    Extends N [1, N] := by
  have hval : SemiSymmetric N [1, N] := by
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k <;> simp [SemiStep, leftCount, rightCount, reach]
  exact (Cov5.one h1 h7).extends ⟨le_rfl, by omega⟩ ⟨by omega, le_rfl⟩ (by omega) hval

end Live5
end Folds
