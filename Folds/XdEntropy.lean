import Folds.PathLemma
import Folds.Wallis
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Entropy-type upper bounds: revelation orders, admissible ranks, and the kick budget

See `experiments/xd_entropy/NOTES.txt`.

## 1. Admissible ranks (the random-walk lemma)

Reveal the time `t_m` of panel `m` *after* the other `2r` panels of its window.  Sort those
`2r` panels by time and record which arm each lies in; let `L ⊆ {0, …, 2r-1}` be the set of
positions of the left-arm panels.  The rank `j` (number of window panels placed before `m`)
is *admissible* iff exactly half of the first `j` are left-arm panels, i.e. iff the bridge
`L/R ↦ ±1` is at `0` at time `j`.

* `card_admissible_le`: at most `r + 1` of the `2r + 1` ranks are admissible (worst case);
* `card_wallis_middle`: summed over all `(2r)!` arrangements the number of admissible ranks is
  `4^r · (r!)²`, i.e. `4^r / C(2r, r) ≈ √(π r)` on average (a restatement of the Wallis count).

## 2. The cap of "window last" revelation orders

* `last_in_window_double`: in *any* revelation order, two left-half panels `m < m'` that are
  both revealed after their whole windows satisfy `2m ≤ m'`.  Hence at most
  `⌊log₂ N⌋ + 1` panels per half can use the admissible-rank lemma.
* `card_windowsThrough_ge`: every panel lies in at least `⌊N/2⌋` windows, so the panel revealed
  last completes at least `⌊N/2⌋` windows at once: at most `⌈N/2⌉ + 1` windows can be completed
  at pairwise different times.

## 3. The kick budget (a time-averaged parity bound)

Along a valid sequence let `V_k` be the number of valid moves after `k` steps.  When `x = a_k`
is placed, every free panel `m` whose window contains `x` changes the parity of its window
count, so `m` is invalid before or after the step (`kicked_not_both`):
`#kicked_k + V_k + V_{k+1} ≤ (N-k) + (N-k-1)` (`kicked_card_add`).  Two panels that lie in
each other's windows (`mutualPairs N`, about `N²/6` pairs) kick each other in one of the two
orders (`card_mutualPairs_le_sum_kicked`).  Hence
`sum_moves_le : E(N) + 2 ∑ V_k ≤ 2 ∑ (N-k)`, a lower bound on the total deficiency.

`semiCount_le_budget`: with per-state caps `V_k ≤ B k ≤ N - k`, and `c` such that
`2 ∑ (B k - c) + 2 ∑ (N - k - B k) ≤ E(N)`, we get `a(N) ≤ ∏ min (B k) c`
(weighted AM–GM along the path).  `semiCount_le_kick` is the case `B k = N - k`:
`a(N) ≤ ∏_{k<N} min (N-k) c = c! · c^(N-c)` when `(N-c)(N-c+1) ≤ E(N)`, which is
`N! · exp(-(0.1164… + o(1)) N)` for **all** `N` (odd `N` included).
-/

namespace Folds
namespace XdEntropy

open Finset

/-! ## 1. Admissible ranks -/

/-- The admissible ranks for a panel whose `2r` window neighbours, sorted by time, have their
left-arm members at the positions `L ⊆ {0, …, 2r-1}`: rank `j` is admissible iff exactly half
of the first `j` neighbours are left-arm panels. -/
def admissible (L : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (range (2 * r + 1)).filter fun j => 2 * (L.filter (· < j)).card = j

theorem zero_mem_admissible (L : Finset ℕ) (r : ℕ) : 0 ∈ admissible L r := by
  simp [admissible]

theorem top_mem_admissible {L : Finset ℕ} {r : ℕ} (hL : L ⊆ range (2 * r)) (hc : L.card = r) :
    2 * r ∈ admissible L r := by
  simp only [admissible, mem_filter, mem_range]
  refine ⟨by omega, ?_⟩
  have : L.filter (· < 2 * r) = L := by
    apply filter_true_of_mem
    intro x hx; exact mem_range.1 (hL hx)
  rw [this, hc]

/-- **Worst case.**  At most `r + 1` of the `2r + 1` ranks are admissible (they are even). -/
theorem card_admissible_le (L : Finset ℕ) (r : ℕ) : (admissible L r).card ≤ r + 1 := by
  have hsub : admissible L r ⊆ (range (r + 1)).image (2 * ·) := by
    intro j hj
    simp only [admissible, mem_filter, mem_range] at hj
    simp only [mem_image, mem_range]
    exact ⟨(L.filter (· < j)).card, by omega, hj.2⟩
  calc (admissible L r).card ≤ ((range (r + 1)).image (2 * ·)).card := card_le_card hsub
    _ ≤ (range (r + 1)).card := card_image_le
    _ = r + 1 := card_range _

/-- **Average case.**  For the middle panel `r + 1` of a strip of `2r + 1` panels the window is
the whole strip.  The number of orderings in which its step is valid, i.e. the number of pairs
(arrangement of the other `2r` panels, admissible rank), is `4^r · (r!)²`: on average
`4^r / C(2r, r)` admissible ranks per arrangement. -/
theorem card_wallis_middle (r : ℕ) :
    (wallisSeqs (2 * r + 1) (r + 1)).card = 4 ^ r * (Nat.factorial r) ^ 2 := by
  have h := card_wallisSeqs (N := 2 * r + 1) (m := r + 1) (by omega) (by omega)
  have hr : reach (2 * r + 1) (r + 1) = r := by unfold reach; omega
  rw [hr] at h
  have hpos : 0 < Nat.factorial (2 * r + 1) := Nat.factorial_pos _
  have h' : (wallisSeqs (2 * r + 1) (r + 1)).card * Nat.factorial (2 * r + 1) =
      (4 ^ r * (Nat.factorial r) ^ 2) * Nat.factorial (2 * r + 1) := by
    rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos h'

/-! ## 2. The cap of "window last" orders -/

/-- **Doubling of window-last panels.**  Let `τ` be any revelation order (injective on the
panels).  If two left-half panels `m < m'` are both revealed after all other panels of their
windows, then `2m ≤ m'`. -/
theorem last_in_window_double {N m m' : ℕ} (τ : ℕ → ℕ) (hinj : Set.InjOn τ (Set.Icc 1 N))
    (hm : 1 ≤ m) (hmm : m < m') (hm' : 2 * m' ≤ N + 1)
    (hlast : ∀ x, m - reach N m ≤ x → x ≤ m + reach N m → τ x ≤ τ m)
    (hlast' : ∀ x, m' - reach N m' ≤ x → x ≤ m' + reach N m' → τ x ≤ τ m') : 2 * m ≤ m' := by
  by_contra hcon
  have r1 : reach N m = m - 1 := by unfold reach; omega
  have r2 : reach N m' = m' - 1 := by unfold reach; omega
  have h1 : τ m' ≤ τ m := hlast m' (by rw [r1]; omega) (by rw [r1]; omega)
  have h2 : τ m ≤ τ m' := hlast' m (by rw [r2]; omega) (by rw [r2]; omega)
  have he : τ m = τ m' := le_antisymm h2 h1
  have := hinj (by simp only [Set.mem_Icc]; omega) (by simp only [Set.mem_Icc]; omega) he
  omega

/-- The panels whose window contains `z`. -/
def windowsThrough (N z : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun m => m - reach N m ≤ z ∧ z ≤ m + reach N m

/-- Every panel lies in at least `⌊N/2⌋` windows. -/
theorem card_windowsThrough_ge {N z : ℕ} (hz1 : 1 ≤ z) (hzN : z ≤ N) :
    N / 2 ≤ (windowsThrough N z).card := by
  have hsub : Icc (z / 2 + 1) ((N + z) / 2) ⊆ windowsThrough N z := by
    intro m hm
    simp only [mem_Icc] at hm
    simp only [windowsThrough, mem_filter, mem_Icc]
    unfold reach
    refine ⟨by omega, by omega, by omega⟩
  have := card_le_card hsub
  rw [Nat.card_Icc] at this
  omega

/-! ## 3. The kick budget -/

/-- `x` lies in the window of `m` and is not `m` itself. -/
def Sees (N m x : ℕ) : Prop := x ≠ m ∧ m - reach N m ≤ x ∧ x ≤ m + reach N m

instance (N m x : ℕ) : Decidable (Sees N m x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Pairs `x < y` of panels lying in each other's windows. -/
def mutualPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun p =>
    p.1 < p.2 ∧ p.2 - p.1 ≤ reach N p.1 ∧ p.2 - p.1 ≤ reach N p.2

/-- The panels still free after step `k` (0-based: the panel `a[k]` has just been placed) whose
window contains `a[k]`. -/
def kicked (N : ℕ) (a : List ℕ) (k : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun m => m ∉ a.take (k + 1) ∧ Sees N m (a.getD k 0)

/-- A kicked panel is not a valid move both before and after the kick: its window count
changes parity. -/
theorem kicked_not_both {N : ℕ} {a : List ℕ} (hnd : a.Nodup) {k : ℕ} (hk : k < a.length)
    {m : ℕ} (hm : m ∈ kicked N a k) (h1 : m ∈ moves N (a.take k))
    (h2 : m ∈ moves N (a.take (k + 1))) : False := by
  simp only [kicked, mem_filter, mem_Icc, List.getD_eq_getElem _ _ hk] at hm
  simp only [moves, mem_filter, mem_Icc] at h1 h2
  have c1 := window_count_even (hnd.sublist (List.take_sublist _ _)) h1.2.1 h1.2.2
  have c2 := window_count_even (hnd.sublist (List.take_sublist _ _)) h2.2.1 h2.2.2
  rw [List.take_succ_eq_append_getElem hk, List.countP_append, List.countP_singleton] at c2
  obtain ⟨_, _, _, hlo, hhi⟩ := hm
  have : decide (m - reach N m ≤ a[k] ∧ a[k] ≤ m + reach N m) = true := by
    simp only [decide_eq_true_eq]; exact ⟨hlo, hhi⟩
  rw [this] at c2
  simp only [if_true] at c2
  omega

theorem card_free {N : ℕ} {p : List ℕ} (hnd : p.Nodup) (hb : ∀ x ∈ p, 1 ≤ x ∧ x ≤ N) :
    (Icc 1 N \ p.toFinset).card = N - p.length := by
  have hp : p.toFinset ⊆ Icc 1 N := by
    intro x hx; rw [List.mem_toFinset] at hx; rw [mem_Icc]; exact hb x hx
  rw [card_sdiff_of_subset hp, Nat.card_Icc, List.toFinset_card_of_nodup hnd]
  omega

/-- **One step of the kick budget.** -/
theorem kicked_card_add {N : ℕ} {a : List ℕ} (ha : a ∈ semiSeqs N) {k : ℕ} (hk : k + 1 < N) :
    (kicked N a k).card + (moves N (a.take k)).card + (moves N (a.take (k + 1))).card ≤
      (N - k) + (N - (k + 1)) := by
  have ha' := mem_semiSeqs.1 ha
  have hnd := nodup_of_foldSeq ha'.1
  have hlen : a.length = N := by rw [ha'.1.length_eq]; simp
  have hbd : ∀ j, ∀ x ∈ a.take j, 1 ≤ x ∧ x ≤ N := fun j x hx =>
    (mem_range'_of_perm ha'.1).1 (List.mem_of_mem_take hx)
  have hndt : ∀ j, (a.take j).Nodup := fun j => hnd.sublist (List.take_sublist _ _)
  set X := kicked N a k with hX
  set M0 := moves N (a.take k) with hM0
  set M1 := moves N (a.take (k + 1)) with hM1
  set F0 := Icc 1 N \ (a.take k).toFinset with hF0
  set F1 := Icc 1 N \ (a.take (k + 1)).toFinset with hF1
  have cF0 : F0.card = N - k := by
    rw [hF0, card_free (hndt k) (hbd k), List.length_take]; omega
  have cF1 : F1.card = N - (k + 1) := by
    rw [hF1, card_free (hndt (k + 1)) (hbd (k + 1)), List.length_take]; omega
  have hM0F : M0 ⊆ F0 := by
    intro m hm
    simp only [hM0, moves, mem_filter] at hm
    simp only [hF0, mem_sdiff, List.mem_toFinset]
    exact ⟨hm.1, hm.2.1⟩
  have hM1F : M1 ⊆ F1 := by
    intro m hm
    simp only [hM1, moves, mem_filter] at hm
    simp only [hF1, mem_sdiff, List.mem_toFinset]
    exact ⟨hm.1, hm.2.1⟩
  have hXF1 : X ⊆ F1 := by
    intro m hm
    simp only [hX, kicked, mem_filter] at hm
    simp only [hF1, mem_sdiff, List.mem_toFinset]
    exact ⟨hm.1, hm.2.1⟩
  have hF10 : F1 ⊆ F0 := by
    intro m hm
    simp only [hF1, hF0, mem_sdiff, List.mem_toFinset] at hm ⊢
    refine ⟨hm.1, fun h => hm.2 ?_⟩
    exact (List.take_sublist_take_left (Nat.le_succ k)).subset h
  have h0 : M0.card + (X \ M0).card ≤ F0.card := by
    rw [← card_union_of_disjoint disjoint_sdiff]
    exact card_le_card (union_subset hM0F (sdiff_subset.trans (hXF1.trans hF10)))
  have h1 : M1.card + (X \ M1).card ≤ F1.card := by
    rw [← card_union_of_disjoint disjoint_sdiff]
    exact card_le_card (union_subset hM1F (sdiff_subset.trans hXF1))
  have h2 : X.card ≤ (X \ M0).card + (X \ M1).card := by
    refine le_trans (card_le_card ?_) (card_union_le _ _)
    intro m hm
    simp only [mem_union, mem_sdiff]
    by_contra hcon
    push_neg at hcon
    exact kicked_not_both hnd (by omega) hm (hcon.1 hm) (hcon.2 hm)
  omega

theorem getD_idxOf {a : List ℕ} {x : ℕ} (hx : x ∈ a) : a.getD (a.idxOf x) 0 = x := by
  have h := List.idxOf_lt_length_of_mem hx
  rw [List.getD_eq_getElem _ _ h, List.getElem_idxOf h]

theorem idxOf_injOn {a : List ℕ} {x y : ℕ} (hx : x ∈ a) (hy : y ∈ a)
    (e : a.idxOf x = a.idxOf y) : x = y := by
  rw [← getD_idxOf hx, ← getD_idxOf hy, e]

theorem mem_kicked_of_before {N : ℕ} {a : List ℕ} (ha : IsFoldSeq N a) {x y : ℕ}
    (hx : x ∈ a) (hy : y ∈ a) (hxy : a.idxOf x < a.idxOf y) (hs : Sees N y x) :
    y ∈ kicked N a (a.idxOf x) := by
  have hnd := nodup_of_foldSeq ha
  simp only [kicked, mem_filter, mem_Icc, getD_idxOf hx]
  refine ⟨(mem_range'_of_perm ha).1 hy, fun h => ?_, hs⟩
  have hy' := List.idxOf_lt_length_of_mem hy
  have := (getElem_mem_take_iff hnd hy').1 (by rw [List.getElem_idxOf hy']; exact h)
  omega

/-- Mutually visible pairs are kicks in one of the two orders. -/
theorem card_mutualPairs_le_sum_kicked {N : ℕ} {a : List ℕ} (ha : IsFoldSeq N a) :
    (mutualPairs N).card ≤ ∑ k ∈ range (N - 1), (kicked N a k).card := by
  have hlen : a.length = N := by rw [ha.length_eq]; simp
  rw [← card_sigma]
  apply card_le_card_of_injOn
    (fun p : ℕ × ℕ => if a.idxOf p.1 < a.idxOf p.2 then (⟨a.idxOf p.1, p.2⟩ : (_ : ℕ) × ℕ)
      else ⟨a.idxOf p.2, p.1⟩)
  · intro p hp
    simp only [mutualPairs, coe_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at hp
    obtain ⟨⟨hx, hy⟩, hlt, h1, h2⟩ := hp
    have hxa : p.1 ∈ a := (mem_range'_of_perm ha).2 hx
    have hya : p.2 ∈ a := (mem_range'_of_perm ha).2 hy
    have ix := List.idxOf_lt_length_of_mem hxa
    have iy := List.idxOf_lt_length_of_mem hya
    have hne : a.idxOf p.1 ≠ a.idxOf p.2 := fun e => by
      have := idxOf_injOn hxa hya e; omega
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_range]
    split
    · next h =>
      exact ⟨by omega, mem_kicked_of_before ha hxa hya h ⟨by omega, by omega, by omega⟩⟩
    · next h =>
      exact ⟨by omega, mem_kicked_of_before ha hya hxa (by omega) ⟨by omega, by omega, by omega⟩⟩
  · intro p hp q hq e
    simp only [mutualPairs, coe_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at hp hq
    obtain ⟨⟨hx, hy⟩, hlt, -, -⟩ := hp
    obtain ⟨⟨hx', hy'⟩, hlt', -, -⟩ := hq
    have hxa : p.1 ∈ a := (mem_range'_of_perm ha).2 hx
    have hya : p.2 ∈ a := (mem_range'_of_perm ha).2 hy
    have hxa' : q.1 ∈ a := (mem_range'_of_perm ha).2 hx'
    have hya' : q.2 ∈ a := (mem_range'_of_perm ha).2 hy'
    simp only at e
    split at e <;> split at e <;> simp only [Sigma.mk.injEq, heq_eq_eq] at e
    · exact Prod.ext (idxOf_injOn hxa hxa' e.1) e.2
    · have := idxOf_injOn hxa hya' e.1; omega
    · have := idxOf_injOn hya hxa' e.1; omega
    · exact Prod.ext e.2 (idxOf_injOn hya hya' e.1)

/-- **The kick budget.**  Along every valid sequence the total deficiency
`∑_k ((N - k) - V_k)` is at least half the number of mutually visible pairs. -/
theorem sum_moves_le {N : ℕ} {a : List ℕ} (ha : a ∈ semiSeqs N) :
    (mutualPairs N).card + 2 * ∑ k ∈ range N, (moves N (a.take k)).card ≤
      2 * ∑ k ∈ range N, (N - k) := by
  have ha' := mem_semiSeqs.1 ha
  have hnd := nodup_of_foldSeq ha'.1
  have hlen : a.length = N := by rw [ha'.1.length_eq]; simp
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp [mutualPairs]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  set V : ℕ → ℕ := fun k => (moves (n + 1) (a.take k)).card with hV
  set f : ℕ → ℕ := fun k => n + 1 - k with hf
  have hstep : ∑ k ∈ range n, ((kicked (n + 1) a k).card + V k + V (k + 1)) ≤
      ∑ k ∈ range n, (f k + f (k + 1)) := by
    apply sum_le_sum
    intro k hk
    rw [mem_range] at hk
    exact kicked_card_add ha (by omega)
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib] at hstep
  have hE := card_mutualPairs_le_sum_kicked ha'.1
  rw [Nat.add_sub_cancel] at hE
  have T1 : ∑ k ∈ range (n + 1), V k = ∑ k ∈ range n, V k + V n := sum_range_succ _ _
  have T2 : ∑ k ∈ range (n + 1), V k = ∑ k ∈ range n, V (k + 1) + V 0 := sum_range_succ' _ _
  have F1 : ∑ k ∈ range (n + 1), f k = ∑ k ∈ range n, f k + f n := sum_range_succ _ _
  have F2 : ∑ k ∈ range (n + 1), f k = ∑ k ∈ range n, f (k + 1) + f 0 := sum_range_succ' _ _
  have hV0 : V 0 ≤ n + 1 := by
    have := card_moves_le (N := n + 1) (p := []) List.nodup_nil (by simp)
    simpa [hV] using this
  have hVn : V n ≤ 1 := by
    have := card_moves_le (N := n + 1) (p := a.take n) (hnd.sublist (List.take_sublist _ _))
      (fun x hx => (mem_range'_of_perm ha'.1).1 (List.mem_of_mem_take hx))
    rw [List.length_take] at this
    simp only [hV]; omega
  have hfn : f n = 1 := by simp only [hf]; omega
  have hf0 : f 0 = n + 1 := by simp only [hf]; omega
  omega

/-- **Weighted AM–GM along a path.**  Per-state caps `V_k ≤ B k ≤ N - k` together with the
kick budget give `∏ V_k ≤ ∏ min (B k) c` as soon as
`2 ∑ (B k - c) + 2 ∑ (N - k - B k) ≤ E(N)`. -/
theorem pathProd_le_of_budget {N c : ℕ} (hc : 1 ≤ c) (B : ℕ → ℕ) {a : List ℕ}
    (ha : a ∈ semiSeqs N) (hVB : ∀ k, k < N → (moves N (a.take k)).card ≤ B k)
    (hBle : ∀ k, k < N → B k ≤ N - k)
    (hbud : 2 * ∑ k ∈ range N, (B k - c) + 2 * ∑ k ∈ range N, (N - k - B k) ≤
      (mutualPairs N).card) :
    pathProd N a ≤ ∏ k ∈ range N, min (B k) c := by
  have hlen : a.length = N := by rw [(mem_semiSeqs.1 ha).1.length_eq]; simp
  set V : ℕ → ℕ := fun k => (moves N (a.take k)).card with hV
  have hVpos : ∀ k, k < N → 1 ≤ V k := fun k hk => card_moves_take_pos ha hk
  -- the natural-number budget
  have hsum := sum_moves_le ha
  have hsplit : ∑ k ∈ range N, (N - k) = ∑ k ∈ range N, B k + ∑ k ∈ range N, (N - k - B k) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    have := hBle k (mem_range.1 hk)
    omega
  have hnat : ∑ k ∈ range N, (B k - c) + ∑ k ∈ range N, V k ≤ ∑ k ∈ range N, B k := by
    simp only [hV]; omega
  -- real computation
  have key : ∏ k ∈ range N, ((V k : ℝ) / (min (B k) c : ℕ)) ≤ 1 := by
    have h1 : ∏ k ∈ range N, ((V k : ℝ) / (min (B k) c : ℕ)) ≤
        ∏ k ∈ range N, Real.exp ((V k : ℝ) / (min (B k) c : ℕ) - 1) := by
      apply prod_le_prod
      · intro k _; positivity
      · intro k _
        have := Real.add_one_le_exp ((V k : ℝ) / (min (B k) c : ℕ) - 1)
        linarith
    rw [← Real.exp_sum] at h1
    refine h1.trans (Real.exp_le_one_iff.2 ?_)
    have hterm : ∀ k ∈ range N, (V k : ℝ) / (min (B k) c : ℕ) - 1 ≤
        (((B k - c : ℕ) : ℝ) - ((B k : ℝ) - (V k : ℝ))) / c := by
      intro k hk
      rw [mem_range] at hk
      have hv1 := hVpos k hk
      have hvb : V k ≤ B k := hVB k hk
      have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
      have hBpos : (0 : ℝ) < B k := by
        have : 0 < B k := by omega
        exact_mod_cast this
      have hvb' : (V k : ℝ) ≤ B k := by exact_mod_cast hvb
      rcases le_or_gt (B k) c with hle | hgt
      · rw [min_eq_left hle, Nat.sub_eq_zero_of_le hle]
        have hle' : (B k : ℝ) ≤ c := by exact_mod_cast hle
        have e : (V k : ℝ) / B k - 1 = -(((B k : ℝ) - V k) / B k) := by
          field_simp; ring
        rw [e, Nat.cast_zero, zero_sub, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left (by linarith) hBpos hle'
      · rw [min_eq_right hgt.le, Nat.cast_sub hgt.le]
        have e : (V k : ℝ) / c - 1 = ((B k : ℝ) - c - ((B k : ℝ) - V k)) / c := by
          field_simp; ring
        rw [e]
    refine (sum_le_sum hterm).trans ?_
    rw [← sum_div]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    rw [sum_sub_distrib, sum_sub_distrib]
    have hnat' : ((∑ k ∈ range N, (B k - c) + ∑ k ∈ range N, V k : ℕ) : ℝ) ≤
        ((∑ k ∈ range N, B k : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hnat'
    linarith
  have hprod : ((pathProd N a : ℕ) : ℝ) =
      (∏ k ∈ range N, ((V k : ℝ) / (min (B k) c : ℕ))) *
        ((∏ k ∈ range N, min (B k) c : ℕ) : ℝ) := by
    unfold pathProd
    rw [hlen]
    push_cast
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro k hk
    rw [mem_range] at hk
    have h1 := hVpos k hk
    have h2 : V k ≤ B k := hVB k hk
    have : (0 : ℝ) < ((min (B k) c : ℕ) : ℝ) := by
      have : 0 < min (B k) c := by
        rw [lt_min_iff]; omega
      exact_mod_cast this
    simp only [hV]
    field_simp
  have hfin : ((pathProd N a : ℕ) : ℝ) ≤ ((∏ k ∈ range N, min (B k) c : ℕ) : ℝ) := by
    rw [hprod]
    have hnn : (0 : ℝ) ≤ ((∏ k ∈ range N, min (B k) c : ℕ) : ℝ) := by positivity
    calc _ ≤ 1 * ((∏ k ∈ range N, min (B k) c : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right key hnn
      _ = _ := one_mul _
  exact_mod_cast hfin

/-- **Budget bound.**  Per-state caps `B` (as in `semiCount_le_prod`) and the kick budget:
`a(N) ≤ ∏_{k<N} min (B k) c` whenever
`2 ∑ (B k - c) + 2 ∑ (N - k - B k) ≤ E(N) = |mutualPairs N|`. -/
theorem semiCount_le_budget (N c : ℕ) (hc : 1 ≤ c) (B : ℕ → ℕ)
    (hB : ∀ p : List Nat, p.length < N → p.Nodup → (∀ x ∈ p, 1 ≤ x ∧ x ≤ N) →
      SemiSymmetric N p → (moves N p).card ≤ B p.length)
    (hBle : ∀ k, k < N → B k ≤ N - k)
    (hbud : 2 * ∑ k ∈ range N, (B k - c) + 2 * ∑ k ∈ range N, (N - k - B k) ≤
      (mutualPairs N).card) :
    semiCount N ≤ ∏ k ∈ range N, min (B k) c := by
  apply semiCount_le_of_pathProd_le
  intro a ha
  refine pathProd_le_of_budget hc B ha (fun k hk => ?_) hBle hbud
  obtain ⟨hl, hnd, hb, hs⟩ := mem_prefixes (take_mem_prefixes ha k hk.le)
  have := hB (a.take k) (by omega) hnd hb hs
  rwa [hl] at this

/-- **Kick bound.**  `a(N) ≤ ∏_{k<N} min (N-k) c = c! · c^(N-c)` whenever
`2 ∑_{k<N} (N-k-c) = (N-c)(N-c+1) ≤ E(N)`.  Since `E(N) ~ N²/6` this is
`N! · exp(-(0.1164… + o(1)) N)` for every `N`, even or odd. -/
theorem semiCount_le_kick (N c : ℕ) (hc : 1 ≤ c)
    (hbud : 2 * ∑ k ∈ range N, (N - k - c) ≤ (mutualPairs N).card) :
    semiCount N ≤ ∏ k ∈ range N, min (N - k) c := by
  apply semiCount_le_budget N c hc (fun k => N - k)
  · intro p _ hnd hb _
    exact card_moves_le hnd hb
  · intro k _; exact le_rfl
  · simpa using hbud

/-- A small instance: `E(10) = 12`, `c = 7`, so `a(10) ≤ 7! · 7³ = 1728720`
(the true value is `17878`; the bound only becomes effective for large `N`). -/
theorem semiCount_ten_le : semiCount 10 ≤ 1728720 := by
  have h := semiCount_le_kick 10 7 (by norm_num) (by decide +kernel)
  have e : ∏ k ∈ range 10, min (10 - k) 7 = 1728720 := by decide +kernel
  rwa [e] at h

end XdEntropy
end Folds
