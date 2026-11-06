import Folds.Growth
import Folds.Asymptotics
import Mathlib.Data.Finset.Max

/-!
# Upper bounds on `a(N)`: the odd parity bound and the discrepancy transfer

See `experiments/upper/PROOFS.txt`.

## 1. Parity bound for odd `N`

For `N = 2h + 1` and a set `S` of odd size:

* the middle panel `h + 1` is never valid (its window is the whole strip);
* `m` and `m + h + 1` (`1 ≤ m ≤ h`, windows `[1, 2m-1]` and `[2m+1, N]`) are both valid only
  if `2m ∈ S` (`odd_pair_even`);
* `m` and `m + h` (`2 ≤ m ≤ h`, windows `[1, 2m-1]` and `[2m-1, N]`) are both valid only if
  `2m - 1 ∈ S` (`odd_pair_odd`).

Counting the two pairings gives `V(S) ≤ h + 1 + ⌊|S|/2⌋` (`card_moves_odd_odd_le`), hence
`semiCount_odd_le_prod`:
`a(2h+1) ≤ ∏_{i < 2h+1} (if i odd then min(2h+1-i, h+1+⌊i/2⌋) else 2h+1-i)`,
which is `(2h+1)! · exp(-(0.0589… + o(1)) N)`.  Together with `semiCount_even_le_prod`
(`Growth.lean`) this gives an exponential saving over `N!` for every `N`.

## 2. Discrepancy transfer

`cycDefect N S m = P̃(2m-1) - 2 P(m-1)` is the cyclic defect; a free panel `m` is valid iff it
vanishes (`semiStep_iff_cycDefect`), and for free `m` it equals the imbalance `J(m)`.
`disc_le_of_cycDefect_le`: if `|cycDefect N S m| ≤ B` for **every** `m ∈ [1, N]`, then
`|N · P(y) - |S| · y| ≤ N (B + 1)` for all `y ≤ N`, i.e. the discrepancy of `S` is at most
`B + 1`.  (Proof: `N · cycDefect(y+1) = e(2y+1 mod N) - 2 e(y) + |S|` with
`e(y) = N P(y) - |S| y`; apply it at a maximiser of `|e|`.)  With Schmidt's theorem on the
irregularity of distribution of sequences this shows that along every fold sequence the
imbalance field is unbounded (of order `log N`) at some time; see PROOFS.txt.
-/

namespace Folds

open Finset

/-! ## 1. Parity bound for odd `N` -/

/-- For `N = 2h + 1` and `|S|` odd, the middle panel is never valid. -/
theorem middle_not_valid {h : Nat} {S : List Nat} (hnd : S.Nodup)
    (hb : ∀ x ∈ S, 1 ≤ x ∧ x ≤ 2 * h + 1) (hodd : S.length % 2 = 1)
    (h1 : h + 1 ∉ S ∧ SemiStep (2 * h + 1) S (h + 1)) : False := by
  have c := window_count_even hnd h1.1 h1.2
  have r : reach (2 * h + 1) (h + 1) = h := by unfold reach; omega
  rw [r] at c
  have e : S.countP (fun x => decide (h + 1 - h ≤ x ∧ x ≤ h + 1 + h)) = S.length := by
    rw [List.countP_eq_length]; intro x hx; have := hb x hx; simp; omega
  omega

/-- For `N = 2h + 1`, `|S|` odd and `1 ≤ m ≤ h`: if `m` and `m + h + 1` are both valid, then
`2m ∈ S` (their windows `[1, 2m-1]` and `[2m+1, N]` cover everything except `2m`). -/
theorem odd_pair_even {h m : Nat} {S : List Nat} (hnd : S.Nodup)
    (hb : ∀ x ∈ S, 1 ≤ x ∧ x ≤ 2 * h + 1) (hodd : S.length % 2 = 1) (hm1 : 1 ≤ m)
    (hmh : m ≤ h) (h1 : m ∉ S ∧ SemiStep (2 * h + 1) S m)
    (h2 : m + h + 1 ∉ S ∧ SemiStep (2 * h + 1) S (m + h + 1)) : 2 * m ∈ S := by
  by_contra h2m
  have c1 := window_count_even hnd h1.1 h1.2
  have c2 := window_count_even hnd h2.1 h2.2
  have r1 : reach (2 * h + 1) m = m - 1 := by unfold reach; omega
  have r2 : reach (2 * h + 1) (m + h + 1) = h - m := by unfold reach; omega
  rw [r1] at c1; rw [r2] at c2
  have hsplit := countP_split S (fun _ => true) (fun x => decide (x ≤ 2 * m - 1))
  rw [List.countP_true] at hsplit
  have e1 : S.countP (fun x => true && decide (x ≤ 2 * m - 1)) =
      S.countP (fun x => decide (m - (m - 1) ≤ x ∧ x ≤ m + (m - 1))) := by
    apply List.countP_congr; intro x hx; have := hb x hx; simp; omega
  have e2 : S.countP (fun x => true && !decide (x ≤ 2 * m - 1)) =
      S.countP (fun x => decide (m + h + 1 - (h - m) ≤ x ∧ x ≤ m + h + 1 + (h - m))) := by
    apply List.countP_congr; intro x hx
    have := hb x hx
    have hx2 : x ≠ 2 * m := fun e => h2m (e ▸ hx)
    simp; omega
  omega

/-- For `N = 2h + 1`, `|S|` odd and `2 ≤ m ≤ h`: if `m` and `m + h` are both valid, then
`2m - 1 ∈ S` (their windows `[1, 2m-1]` and `[2m-1, N]` overlap exactly in `2m - 1`). -/
theorem odd_pair_odd {h m : Nat} {S : List Nat} (hnd : S.Nodup)
    (hb : ∀ x ∈ S, 1 ≤ x ∧ x ≤ 2 * h + 1) (hodd : S.length % 2 = 1) (hm2 : 2 ≤ m)
    (hmh : m ≤ h) (h1 : m ∉ S ∧ SemiStep (2 * h + 1) S m)
    (h2 : m + h ∉ S ∧ SemiStep (2 * h + 1) S (m + h)) : 2 * m - 1 ∈ S := by
  by_contra h2m
  have c1 := window_count_even hnd h1.1 h1.2
  have c2 := window_count_even hnd h2.1 h2.2
  have r1 : reach (2 * h + 1) m = m - 1 := by unfold reach; omega
  have r2 : reach (2 * h + 1) (m + h) = h + 1 - m := by unfold reach; omega
  rw [r1] at c1; rw [r2] at c2
  have hsplit := countP_split S (fun _ => true) (fun x => decide (x ≤ 2 * m - 1))
  rw [List.countP_true] at hsplit
  have e1 : S.countP (fun x => true && decide (x ≤ 2 * m - 1)) =
      S.countP (fun x => decide (m - (m - 1) ≤ x ∧ x ≤ m + (m - 1))) := by
    apply List.countP_congr; intro x hx; have := hb x hx; simp; omega
  have e2 : S.countP (fun x => true && !decide (x ≤ 2 * m - 1)) =
      S.countP (fun x => decide (m + h - (h + 1 - m) ≤ x ∧ x ≤ m + h + (h + 1 - m))) := by
    apply List.countP_congr; intro x hx
    have := hb x hx
    have hx2 : x ≠ 2 * m - 1 := fun e => h2m (e ▸ hx)
    simp; omega
  omega

theorem mem_moves {N m : Nat} {S : List Nat} :
    m ∈ moves N S ↔ (1 ≤ m ∧ m ≤ N) ∧ m ∉ S ∧ SemiStep N S m := by
  simp [moves]

/-- **Parity bound for odd `N`.**  For `N = 2h + 1` and `|S|` odd, at most
`h + 1 + ⌊|S|/2⌋` panels are valid. -/
theorem card_moves_odd_odd_le {h : Nat} {S : List Nat} (hnd : S.Nodup)
    (hb : ∀ x ∈ S, 1 ≤ x ∧ x ≤ 2 * h + 1) (hodd : S.length % 2 = 1) :
    (moves (2 * h + 1) S).card ≤ h + 1 + S.length / 2 := by
  set Z := moves (2 * h + 1) S with hZ
  set A := Z.filter (· ≤ h) with hA
  set B := Z.filter (fun m => ¬ m ≤ h) with hB
  have hZAB : Z.card = A.card + B.card := (Finset.card_filter_add_card_filter_not _).symm
  -- every element of `B` is at least `h + 2` (the middle panel is invalid)
  have hBlo : ∀ m ∈ B, h + 2 ≤ m := by
    intro m hm
    rw [hB, Finset.mem_filter, hZ, mem_moves] at hm
    by_contra hlt
    obtain rfl : m = h + 1 := by omega
    exact middle_not_valid hnd hb hodd hm.1.2
  have hAsub : A ⊆ Finset.Icc 1 h := by
    intro m hm
    rw [hA, Finset.mem_filter, hZ, mem_moves] at hm
    rw [Finset.mem_Icc]; omega
  -- first pairing: m ↔ m + h + 1
  set B1 := B.image (fun m => m - (h + 1)) with hB1
  have hB1card : B1.card = B.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy e
    have := hBlo x hx; have := hBlo y hy
    simp only at e; omega
  have hB1sub : B1 ⊆ Finset.Icc 1 h := by
    intro m hm
    rw [hB1, Finset.mem_image] at hm
    obtain ⟨x, hx, rfl⟩ := hm
    have hlo := hBlo x hx
    rw [hB, Finset.mem_filter, hZ, mem_moves] at hx
    rw [Finset.mem_Icc]; omega
  set E := (Finset.Icc 1 h).filter (fun m => 2 * m ∈ S) with hE
  have hinter1 : A ∩ B1 ⊆ E := by
    intro m hm
    rw [Finset.mem_inter] at hm
    obtain ⟨hmA, hmB⟩ := hm
    rw [hB1, Finset.mem_image] at hmB
    obtain ⟨x, hx, hxm⟩ := hmB
    have hlo := hBlo x hx
    have hx' := hx
    rw [hB, Finset.mem_filter, hZ, mem_moves] at hx
    have hmA' := hmA
    rw [hA, Finset.mem_filter, hZ, mem_moves] at hmA
    obtain rfl : x = m + h + 1 := by omega
    rw [hE, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hmA.1.1.1, hmA.2⟩,
      odd_pair_even hnd hb hodd hmA.1.1.1 hmA.2 hmA.1.2 hx.1.2⟩
  have k1 : Z.card ≤ h + E.card := by
    have u := Finset.card_union_add_card_inter A B1
    have hu : (A ∪ B1).card ≤ h := by
      have := Finset.card_le_card (Finset.union_subset hAsub hB1sub)
      simpa using this
    have hi := Finset.card_le_card hinter1
    omega
  -- second pairing: m ↔ m + h
  set B2 := B.image (fun m => m - h) with hB2
  have hB2card : B2.card = B.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy e
    have := hBlo x hx; have := hBlo y hy
    simp only at e; omega
  have hB2sub : B2 ⊆ Finset.Icc 1 (h + 1) := by
    intro m hm
    rw [hB2, Finset.mem_image] at hm
    obtain ⟨x, hx, rfl⟩ := hm
    have hlo := hBlo x hx
    rw [hB, Finset.mem_filter, hZ, mem_moves] at hx
    rw [Finset.mem_Icc]; omega
  have hAsub' : A ⊆ Finset.Icc 1 (h + 1) := hAsub.trans (Finset.Icc_subset_Icc le_rfl (by omega))
  set O := (Finset.Icc 2 h).filter (fun m => 2 * m - 1 ∈ S) with hO
  have hinter2 : A ∩ B2 ⊆ O := by
    intro m hm
    rw [Finset.mem_inter] at hm
    obtain ⟨hmA, hmB⟩ := hm
    rw [hB2, Finset.mem_image] at hmB
    obtain ⟨x, hx, hxm⟩ := hmB
    have hlo := hBlo x hx
    rw [hB, Finset.mem_filter, hZ, mem_moves] at hx
    rw [hA, Finset.mem_filter, hZ, mem_moves] at hmA
    obtain rfl : x = m + h := by omega
    rw [hO, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hmA.2⟩,
      odd_pair_odd hnd hb hodd (by omega) hmA.2 hmA.1.2 hx.1.2⟩
  have k2 : Z.card ≤ h + 1 + O.card := by
    have u := Finset.card_union_add_card_inter A B2
    have hu : (A ∪ B2).card ≤ h + 1 := by
      have := Finset.card_le_card (Finset.union_subset hAsub' hB2sub)
      simpa using this
    have hi := Finset.card_le_card hinter2
    omega
  -- the two exceptional sets inject disjointly into `S`
  have k3 : E.card + O.card ≤ S.length := by
    have hEi : (E.image (fun m => 2 * m)).card = E.card :=
      Finset.card_image_of_injOn (fun x _ y _ e => by omega)
    have hOi : (O.image (fun m => 2 * m - 1)).card = O.card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy e
      have hx' := Finset.mem_coe.1 hx
      have hy' := Finset.mem_coe.1 hy
      rw [hO, Finset.mem_filter, Finset.mem_Icc] at hx' hy'
      dsimp only at e; omega
    have hdisj : Disjoint (E.image (fun m => 2 * m)) (O.image (fun m => 2 * m - 1)) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      rw [Finset.mem_image] at hz1 hz2
      obtain ⟨x, hx, rfl⟩ := hz1
      obtain ⟨y, hy, e⟩ := hz2
      rw [hO, Finset.mem_filter, Finset.mem_Icc] at hy
      omega
    have hsub : E.image (fun m => 2 * m) ∪ O.image (fun m => 2 * m - 1) ⊆ S.toFinset := by
      intro z hz
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hz
      rw [List.mem_toFinset]
      rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
      · rw [hE, Finset.mem_filter] at hx; exact hx.2
      · rw [hO, Finset.mem_filter] at hx; exact hx.2
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hEi, hOi,
      List.toFinset_card_of_nodup hnd] at this
    exact this
  omega

/-- **Parity upper bound for odd `N`.**
`a(2h+1) ≤ ∏_{i < 2h+1} (if i odd then min(2h+1-i, h+1+⌊i/2⌋) else 2h+1-i)`. -/
theorem semiCount_odd_le_prod (h : Nat) :
    semiCount (2 * h + 1) ≤
      ∏ i ∈ Finset.range (2 * h + 1),
        (if i % 2 = 1 then min (2 * h + 1 - i) (h + 1 + i / 2) else 2 * h + 1 - i) := by
  apply semiCount_le_prod
  intro p hl hnd hb _
  have c1 := card_moves_le hnd hb
  split
  · next hodd => exact le_min c1 (card_moves_odd_odd_le hnd hb hodd)
  · exact c1

/-! ## 2. Discrepancy transfer -/

/-- The cyclic defect `P̃(2m-1) - 2 P(m-1)`. -/
def cycDefect (N : Nat) (S : List Nat) (m : Nat) : Int :=
  (cycBelow N S (2 * m - 1) : Int) - 2 * (below S (m - 1) : Int)

/-- A free panel is valid iff its cyclic defect vanishes. -/
theorem semiStep_iff_cycDefect {N m : Nat} {S : List Nat} (hnd : S.Nodup)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (hm1 : 1 ≤ m) (hmN : m ≤ N) (hmS : m ∉ S) :
    SemiStep N S m ↔ cycDefect N S m = 0 := by
  rw [semiStep_iff_cyclicStep hnd hS hm1 hmN hmS]
  unfold CyclicStep cycDefect
  omega

theorem length_le_of_bounds {N : Nat} {S : List Nat} (hnd : S.Nodup)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) : S.length ≤ N := by
  have hsub : S.toFinset ⊆ Finset.Icc 1 N := by
    intro x hx; rw [List.mem_toFinset] at hx; rw [Finset.mem_Icc]; exact hS x hx
  have := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hnd, Nat.card_Icc, Nat.add_sub_cancel] at this

/-- The key identity: with `e(y) = N P(y) - |S| y`,
`N · cycDefect(y + 1) = e((2y+1) mod N) - 2 e(y) + |S|`. -/
theorem cycDefect_identity {N : Nat} (S : List Nat) (y : Nat) :
    (N : Int) * cycDefect N S (y + 1) =
      ((N : Int) * below S ((2 * y + 1) % N) - S.length * (((2 * y + 1) % N : Nat) : Int))
      - 2 * ((N : Int) * below S y - S.length * (y : Int)) + S.length := by
  unfold cycDefect cycBelow
  have e1 : 2 * (y + 1) - 1 = 2 * y + 1 := by omega
  have e2 : y + 1 - 1 = y := by omega
  rw [e1, e2]
  have hdm := Nat.div_add_mod (2 * y + 1) N
  set q := (2 * y + 1) / N
  set z := (2 * y + 1) % N
  have hz : ((2 * y + 1 : Nat) : Int) = (N : Int) * q + z := by exact_mod_cast hdm.symm
  push_cast at hz ⊢
  nlinarith [hz]

/-- **Discrepancy transfer.**  If the cyclic defect is at most `B` in absolute value at every
panel, then every prefix count is within `B + 1` of its mean:
`|N · P(y) - |S| · y| ≤ N (B + 1)` for all `y ≤ N`. -/
theorem disc_le_of_cycDefect_le {N : Nat} {S : List Nat} (hnd : S.Nodup)
    (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) (B : Int)
    (hB : ∀ m, 1 ≤ m → m ≤ N → |cycDefect N S m| ≤ B) :
    ∀ y, y ≤ N → |(N : Int) * below S y - S.length * (y : Int)| ≤ N * (B + 1) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · intro y hy
    subst hN0
    have : y = 0 := by omega
    subst this
    simp
  have hlen := length_le_of_bounds hnd hS
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 1 le_rfl hN)
  set e : Nat → Int := fun y => (N : Int) * below S y - S.length * (y : Int) with he
  obtain ⟨y0, hy0, hmax⟩ := Finset.exists_max_image (Finset.range N) (fun y => |e y|)
    ⟨0, Finset.mem_range.2 hN⟩
  rw [Finset.mem_range] at hy0
  -- the bound at the maximiser
  have key : |e y0| ≤ N * (B + 1) := by
    have hid := cycDefect_identity (N := N) S y0
    have hz : (2 * y0 + 1) % N < N := Nat.mod_lt _ hN
    have hmz := hmax ((2 * y0 + 1) % N) (Finset.mem_range.2 hz)
    have hd := hB (y0 + 1) (by omega) (by omega)
    have hd2 := abs_le.1 hd
    have hl : (S.length : Int) ≤ N := by exact_mod_cast hlen
    have hN' : (0 : Int) ≤ N := by positivity
    have hc1 : (N : Int) * cycDefect N S (y0 + 1) ≤ N * B :=
      mul_le_mul_of_nonneg_left hd2.2 hN'
    have hc2 : -((N : Int) * B) ≤ (N : Int) * cycDefect N S (y0 + 1) := by
      have := mul_le_mul_of_nonneg_left hd2.1 hN'
      linarith
    have h2 : 2 * e y0 = e ((2 * y0 + 1) % N) - (N : Int) * cycDefect N S (y0 + 1) + S.length := by
      simp only [he]; linarith [hid]
    have hl0 : (0 : Int) ≤ S.length := by positivity
    have z1 := le_abs_self (e ((2 * y0 + 1) % N))
    have z2 := neg_abs_le (e ((2 * y0 + 1) % N))
    rcases abs_cases (e y0) with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha] at hmz ⊢ <;> nlinarith
  intro y hy
  rcases Nat.lt_or_ge y N with hlt | hge
  · exact (hmax y (Finset.mem_range.2 hlt)).trans key
  · have hbN : below S N = S.length := below_eq_length (fun x hx => (hS x hx).2)
    rw [show y = N by omega, hbN,
      show (N : Int) * S.length - S.length * N = 0 by ring, abs_zero]
    exact mul_nonneg (by positivity) (by linarith)

end Folds
