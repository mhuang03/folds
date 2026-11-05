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

end Live5
end Folds
