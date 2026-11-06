import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Card
import Folds.Decide

/-!
# Parity balance of symmetric (3-AP-free) fold sequences

See `experiments/symparity/PROOFS.txt`.  By `symmetric_iff_apFree` the symmetric fold
sequences of `[N]` are the permutations of `[1..N]` without a 3-term arithmetic
progression as a subsequence (OEIS A003407).

* `orient` (**orientation theorem**): let `a` be a 3-AP-free list whose entries are
  exactly the integers of an interval, with first entry `w`.  For every 3-term
  progression `x, x+t, x+2t` with **odd** `t`, the entry that comes first in `a` has the
  parity of `w`.  (Equivalently the middle term `x+t` comes first iff `x+t ≡ w`.)
* `head_last_parity`: the first and last panels have different parities (`N ≥ 2`).
* `prefix_parity`: the first `⌊(N+1)/4⌋` panels all have the parity of the first one.
* `two_mul_card_head_odd`: for every `N ≥ 2`, exactly half of the symmetric fold
  sequences start with an odd panel (odd `N` included).
* `two_mul_card_getElem_odd`: the same for the panel at 0-based index `k` whenever
  `4(k+1) ≤ N+1`, i.e. for the first `⌊(N+1)/4⌋` steps.
-/

namespace Folds
namespace SymParity

open scoped List

/-! ## "Comes before" and AP-freeness in sublist form -/

/-- `x` comes before `y` in `a`. -/
abbrev Bef (a : List ℕ) (x y : ℕ) : Prop := [x, y] <+ a

/-- No 3-term arithmetic progression as a subsequence (sublist form of `APFree`). -/
def APF (a : List ℕ) : Prop := ∀ x y z, [x, y, z] <+ a → x + z ≠ 2 * y

theorem APF.sublist {a b : List ℕ} (h : APF a) (hs : b <+ a) : APF b :=
  fun x y z hxyz => h x y z (hxyz.trans hs)

theorem bef_reverse {a : List ℕ} {x y : ℕ} : Bef a.reverse x y ↔ Bef a y x := by
  unfold Bef
  rw [← List.reverse_sublist]
  simp

theorem APF.reverse {a : List ℕ} (h : APF a) : APF a.reverse := by
  intro x y z hs e
  have hs' : [z, y, x] <+ a := by
    have := List.reverse_sublist.2 hs
    simpa using this
  exact h z y x hs' (by omega)

theorem bef_mem {a : List ℕ} {x y : ℕ} (h : Bef a x y) : x ∈ a ∧ y ∈ a :=
  ⟨h.subset (by simp), h.subset (by simp)⟩

theorem bef_ne {a : List ℕ} (hnd : a.Nodup) {x y : ℕ} (h : Bef a x y) : x ≠ y := by
  have := hnd.sublist h
  simp at this
  exact this

theorem bef_total : ∀ {a : List ℕ}, a.Nodup → ∀ {x y : ℕ}, x ∈ a → y ∈ a → x ≠ y →
    Bef a x y ∨ Bef a y x
  | [], _, _, _, hx, _, _ => by simp at hx
  | h :: t, hnd, x, y, hx, hy, hxy => by
    rw [List.nodup_cons] at hnd
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd rfl hxy
      · left; exact List.Sublist.cons_cons _ (List.singleton_sublist.2 hy)
    · rcases hy with rfl | hy
      · right; exact List.Sublist.cons_cons _ (List.singleton_sublist.2 hx)
      · rcases bef_total hnd.2 hx hy hxy with h1 | h1
        · left; exact h1.cons _
        · right; exact h1.cons _

theorem bef_cons_iff {h : ℕ} {t : List ℕ} {x y : ℕ} :
    Bef (h :: t) x y ↔ Bef t x y ∨ (x = h ∧ y ∈ t) := by
  unfold Bef
  rw [List.sublist_cons_iff]
  constructor
  · rintro (h1 | ⟨r, hr, h2⟩)
    · exact Or.inl h1
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact Or.inr ⟨rfl, List.singleton_sublist.1 h2⟩
  · rintro (h1 | ⟨rfl, h2⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨[y], rfl, List.singleton_sublist.2 h2⟩

theorem bef_asymm : ∀ {a : List ℕ}, a.Nodup → ∀ {x y : ℕ}, Bef a x y → ¬ Bef a y x
  | [], _, _, _, h1, _ => by simpa [Bef] using h1.subset (List.mem_cons_self ..)
  | h :: t, hnd, x, y, h1, h2 => by
    rw [List.nodup_cons] at hnd
    rw [bef_cons_iff] at h1 h2
    rcases h1 with h1 | ⟨rfl, hy⟩
    · rcases h2 with h2 | ⟨rfl, hx⟩
      · exact bef_asymm hnd.2 h1 h2
      · exact hnd.1 (bef_mem h1).2
    · rcases h2 with h2 | ⟨rfl, -⟩
      · exact hnd.1 (bef_mem h2).2
      · exact hnd.1 hy

theorem bef_trans3 : ∀ {a : List ℕ}, a.Nodup → ∀ {x y z : ℕ}, Bef a x y → Bef a y z →
    [x, y, z] <+ a
  | [], _, _, _, _, h1, _ => by simpa [Bef] using h1.subset (List.mem_cons_self ..)
  | h :: t, hnd, x, y, z, h1, h2 => by
    rw [List.nodup_cons] at hnd
    rw [bef_cons_iff] at h1 h2
    rcases h1 with h1 | ⟨rfl, hy⟩
    · rcases h2 with h2 | ⟨rfl, -⟩
      · exact (bef_trans3 hnd.2 h1 h2).cons _
      · exact absurd (bef_mem h1).2 hnd.1
    · rcases h2 with h2 | ⟨rfl, -⟩
      · exact List.Sublist.cons_cons _ h2
      · exact absurd hy hnd.1

theorem bef_trans {a : List ℕ} (hnd : a.Nodup) {x y z : ℕ} (h1 : Bef a x y)
    (h2 : Bef a y z) : Bef a x z :=
  (show [x, z] <+ [x, y, z] by simp).trans (bef_trans3 hnd h1 h2)

theorem bef_head {w : ℕ} {t : List ℕ} {y : ℕ} (hy : y ∈ t) : Bef (w :: t) w y :=
  List.Sublist.cons_cons _ (List.singleton_sublist.2 hy)

theorem bef_tail_iff {w : ℕ} {t : List ℕ} {x y : ℕ} (hx : x ≠ w) :
    Bef (w :: t) x y ↔ Bef t x y := by
  rw [bef_cons_iff]
  constructor
  · rintro (h | ⟨rfl, -⟩)
    · exact h
    · exact absurd rfl hx
  · exact Or.inl

theorem bef_filter_iff {a : List ℕ} {p : ℕ → Bool} {x y : ℕ} (hx : p x) (hy : p y) :
    Bef (a.filter p) x y ↔ Bef a x y := by
  unfold Bef
  constructor
  · intro h; exact h.trans (List.filter_sublist)
  · intro h
    have := h.filter p
    simpa [List.filter_cons, hx, hy] using this

/-- The middle term of a progression is never between the other two. -/
theorem middle {a : List ℕ} (hnd : a.Nodup) (hap : APF a) {x y z : ℕ} (e : x + z = 2 * y)
    (hzy : z ≠ y) (hz : z ∈ a) (h : Bef a y x) : Bef a y z := by
  rcases bef_total hnd (bef_mem h).1 hz (Ne.symm hzy) with h1 | h1
  · exact h1
  · exact absurd (by omega) (hap z y x (bef_trans3 hnd h1 h))

/-! ## The ζ-lemma -/

/-- Let `hi = lo + 2t` with `t ≥ 3` odd, and let `Y` be the integers `y ≡ lo (mod 2)` with
`lo + 2 ≤ y ≤ hi - 2`.  In a 3-AP-free list containing `[lo, hi]`, the two ends `lo` and
`hi` cannot both come before every element of `Y`. -/
theorem zeta {a : List ℕ} (hnd : a.Nodup) (hap : APF a) {lo hi t : ℕ}
    (hI : ∀ v, lo ≤ v → v ≤ hi → v ∈ a) (hhi : hi = lo + 2 * t) (ht : t % 2 = 1)
    (ht3 : 3 ≤ t)
    (hY : ∀ y, y % 2 = lo % 2 → lo + 2 ≤ y → y + 2 ≤ hi → Bef a lo y ∧ Bef a hi y) :
    False := by
  set l := a.filter (fun v => decide (v % 2 = lo % 2 ∧ lo + 2 ≤ v ∧ v + 2 ≤ hi)) with hl
  have hmem : ∀ v, v ∈ l ↔ v ∈ a ∧ (v % 2 = lo % 2 ∧ lo + 2 ≤ v ∧ v + 2 ≤ hi) := by
    intro v; simp [hl, List.mem_filter]
  have hne : lo + 2 ∈ l := (hmem _).2 ⟨hI _ (by omega) (by omega), by omega, le_refl _, by omega⟩
  obtain ⟨ζ, r, hlr⟩ : ∃ ζ r, l = ζ :: r := by
    cases h : l with
    | nil => rw [h] at hne; simp at hne
    | cons ζ r => exact ⟨ζ, r, rfl⟩
  have hζ := (hmem ζ).1 (by rw [hlr]; simp)
  have first : ∀ v, v % 2 = lo % 2 → lo + 2 ≤ v → v + 2 ≤ hi → v ≠ ζ → Bef a ζ v := by
    intro v h1 h2 h3 hv
    have hvl : v ∈ l := (hmem v).2 ⟨hI _ (by omega) (by omega), h1, h2, h3⟩
    have hvr : v ∈ r := by
      rw [hlr] at hvl; simp at hvl; tauto
    have : Bef l ζ v := by rw [hlr]; exact bef_head hvr
    exact this.trans (List.filter_sublist)
  obtain ⟨hz1, hz2, hz3⟩ := hζ.2
  rcases Nat.lt_trichotomy (2 * ζ) (lo + hi) with hlt | heq | hgt
  · have hb := first (2 * ζ - lo) (by omega) (by omega) (by omega) (by omega)
    exact hap lo ζ (2 * ζ - lo) (bef_trans3 hnd (hY ζ hz1 hz2 hz3).1 hb) (by omega)
  · omega
  · have hb := first (2 * ζ - hi) (by omega) (by omega) (by omega) (by omega)
    exact hap hi ζ (2 * ζ - hi) (bef_trans3 hnd (hY ζ hz1 hz2 hz3).2 hb) (by omega)

/-! ## The orientation theorem -/

/-- **Orientation theorem.**  `a = w :: tl` is a 3-AP-free list whose entries are exactly
the integers of `[lo, hi]`.  For every progression `x, x+t, x+2t` in `[lo, hi]` with odd
`t`, the middle term comes before `x` (equivalently, it comes first) iff it has the parity
of the first entry `w`. -/
theorem orient : ∀ (d : ℕ) (a : List ℕ) (lo hi w : ℕ) (tl : List ℕ), hi = lo + d →
    a = w :: tl → a.Nodup → (∀ v, v ∈ a ↔ lo ≤ v ∧ v ≤ hi) → APF a →
    ∀ x t, t % 2 = 1 → lo ≤ x → x + 2 * t ≤ hi →
      (Bef a (x + t) x ↔ (x + t) % 2 = w % 2) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro a lo hi w tl hd ha hnd hI hap x t ht hx hxt
  have memI : ∀ v, lo ≤ v → v ≤ hi → v ∈ a := fun v h1 h2 => (hI v).2 ⟨h1, h2⟩
  have hw : w ∈ a := by rw [ha]; simp
  have hwI := (hI w).1 hw
  have hnd' := hnd
  rw [ha, List.nodup_cons] at hnd'
  -- restriction to `[lo+1, hi]` when `w ≠ lo`
  have resL : w ≠ lo → ∀ x' t', t' % 2 = 1 → lo + 1 ≤ x' → x' + 2 * t' ≤ hi →
      (Bef a (x' + t') x' ↔ (x' + t') % 2 = w % 2) := by
    intro hwl x' t' ht' hx' hxt'
    have hp : (fun v => decide (v ≠ lo)) w = true := by simpa using hwl
    have e := ih (d - 1) (by omega) (a.filter (fun v => decide (v ≠ lo))) (lo + 1) hi w
      (tl.filter (fun v => decide (v ≠ lo))) (by omega)
      (by rw [ha]; simp [List.filter_cons]; omega) (hnd.filter _)
      (by intro v; simp only [List.mem_filter, hI]; simp; omega)
      (hap.sublist List.filter_sublist) x' t' ht' hx' hxt'
    rwa [bef_filter_iff (by simp; omega) (by simp; omega)] at e
  -- restriction to `[lo, hi-1]` when `w ≠ hi`
  have resR : w ≠ hi → ∀ x' t', t' % 2 = 1 → lo ≤ x' → x' + 2 * t' + 1 ≤ hi →
      (Bef a (x' + t') x' ↔ (x' + t') % 2 = w % 2) := by
    intro hwh x' t' ht' hx' hxt'
    have hp : (fun v => decide (v ≠ hi)) w = true := by simpa using hwh
    have e := ih (d - 1) (by omega) (a.filter (fun v => decide (v ≠ hi))) lo (hi - 1) w
      (tl.filter (fun v => decide (v ≠ hi))) (by omega)
      (by rw [ha]; simp [List.filter_cons]; omega) (hnd.filter _)
      (by intro v; simp only [List.mem_filter, hI]; simp; omega)
      (hap.sublist List.filter_sublist) x' t' ht' hx' (by omega)
    rwa [bef_filter_iff (by simp; omega) (by simp; omega)] at e
  -- the tail `tl`, an interval list with one end removed, when `w` is an end
  have tlI : w = lo ∨ w = hi → ∀ v, v ∈ tl ↔ v ∈ a ∧ v ≠ w := by
    intro _ v
    rw [ha]; simp only [List.mem_cons]
    constructor
    · intro hv; exact ⟨Or.inr hv, fun e => hnd'.1 (e ▸ hv)⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact h1
  by_cases c1 : x ≠ lo ∧ w ≠ lo
  · exact resL c1.2 x t ht (by omega) hxt
  by_cases c2 : x + 2 * t ≠ hi ∧ w ≠ hi
  · exact resR c2.2 x t ht hx (by omega)
  have hb : x + t ∈ a := memI _ (by omega) (by omega)
  have hx2 : x + 2 * t ∈ a := memI _ (by omega) (by omega)
  have hxa : x ∈ a := memI _ (by omega) (by omega)
  by_cases hwlo : w = lo
  · subst hwlo
    by_cases hxw : x = w
    · subst hxw
      have h1 : Bef a x (x + t) := by
        rw [ha]; exact bef_head (((tlI (Or.inl rfl)) _).2 ⟨hb, by omega⟩)
      constructor
      · intro h2; exact absurd h2 (bef_asymm hnd h1)
      · intro h2; omega
    · -- the tail is an interval list `[w+1, hi]` with head `f`
      obtain ⟨f, tl2, htl⟩ : ∃ f tl2, tl = f :: tl2 := by
        cases h : tl with
        | nil =>
          have := ((tlI (Or.inl rfl)) x).2 ⟨hxa, hxw⟩
          rw [h] at this; simp at this
        | cons f tl2 => exact ⟨f, tl2, rfl⟩
      have tlI' : ∀ v, v ∈ tl ↔ w + 1 ≤ v ∧ v ≤ hi := by
        intro v; rw [tlI (Or.inl rfl), hI]; omega
      have hndt : tl.Nodup := hnd'.2
      have hapt : APF tl := hap.sublist (by rw [ha]; exact List.sublist_cons_self _ _)
      have IH := ih (d - 1) (by omega) tl (w + 1) hi f tl2 (by omega) htl hndt tlI' hapt
      by_cases hf : f % 2 = w % 2
      · have e := IH x t ht (by omega) hxt
        rw [ha, bef_tail_iff (by omega), e, hf]
      · exfalso
        have e := IH (w + 1) 1 rfl le_rfl (by omega)
        have hn : ¬ Bef tl (w + 1 + 1) (w + 1) := by rw [e]; omega
        have h12 : Bef tl (w + 1) (w + 1 + 1) := by
          rcases bef_total hndt ((tlI' (w + 1)).2 ⟨le_rfl, by omega⟩) ((tlI' (w + 1 + 1)).2 ⟨by omega, by omega⟩)
            (by omega) with h | h
          · exact h
          · exact absurd h hn
        have h0 : Bef a w (w + 1) := by
          rw [ha]; exact bef_head ((tlI' (w + 1)).2 ⟨le_rfl, by omega⟩)
        have h12' : Bef a (w + 1) (w + 1 + 1) := by rw [ha]; exact h12.cons _
        exact hap _ _ _ (bef_trans3 hnd h0 h12') (by omega)
  by_cases hwhi : w = hi
  · subst hwhi
    by_cases hxw : x + 2 * t = w
    · have h1 : Bef a w (x + t) := by
        rw [ha]; exact bef_head (((tlI (Or.inr rfl)) _).2 ⟨hb, by omega⟩)
      constructor
      · intro h2
        exact (hap w (x + t) x (bef_trans3 hnd h1 h2) (by omega)).elim
      · intro h2; omega
    · obtain ⟨f, tl2, htl⟩ : ∃ f tl2, tl = f :: tl2 := by
        cases h : tl with
        | nil =>
          have := ((tlI (Or.inr rfl)) x).2 ⟨hxa, by omega⟩
          rw [h] at this; simp at this
        | cons f tl2 => exact ⟨f, tl2, rfl⟩
      have tlI' : ∀ v, v ∈ tl ↔ lo ≤ v ∧ v ≤ w - 1 := by
        intro v; rw [tlI (Or.inr rfl), hI]; omega
      have hndt : tl.Nodup := hnd'.2
      have hapt : APF tl := hap.sublist (by rw [ha]; exact List.sublist_cons_self _ _)
      have IH := ih (d - 1) (by omega) tl lo (w - 1) f tl2 (by omega) htl hndt tlI' hapt
      by_cases hf : f % 2 = w % 2
      · have e := IH x t ht hx (by omega)
        rw [ha, bef_tail_iff (by omega), e, hf]
      · exfalso
        have e := IH (w - 3) 1 rfl (by omega) (by omega)
        have hn : ¬ Bef tl (w - 3 + 1) (w - 3) := by rw [e]; omega
        have m3 : w - 3 ∈ tl := (tlI' _).2 ⟨by omega, by omega⟩
        have m2 : w - 3 + 1 ∈ tl := (tlI' _).2 ⟨by omega, by omega⟩
        have m1 : w - 1 ∈ tl := (tlI' _).2 ⟨by omega, by omega⟩
        have h32 : Bef tl (w - 3) (w - 3 + 1) := by
          rcases bef_total hndt m3 m2 (by omega) with h | h
          · exact h
          · exact absurd h hn
        have h12 : Bef tl (w - 1) (w - 3 + 1) := by
          rcases bef_total hndt m1 m2 (by omega) with h | h
          · exact h
          · exact absurd (by omega) (hap.sublist (by rw [ha]; exact List.sublist_cons_self _ _)
              _ _ _ (bef_trans3 hndt h32 h))
        have h0 : Bef a w (w - 1) := by rw [ha]; exact bef_head m1
        have h12' : Bef a (w - 1) (w - 3 + 1) := by rw [ha]; exact h12.cons _
        exact hap _ _ _ (bef_trans3 hnd h0 h12') (by omega)
  -- Case I: the progression is `lo, lo + t, hi` and `w` is not an end
  have hxlo : x = lo := by omega
  have hxhi : x + 2 * t = hi := by omega
  subst hxlo
  by_cases ht1 : t = 1
  · subst ht1
    have hwb : w = x + 1 := by omega
    subst hwb
    constructor
    · intro _; rfl
    · intro _
      have hxtl : x ∈ tl := by
        have := memI x le_rfl (by omega)
        rw [ha] at this; simpa using this
      rw [ha]; exact bef_head hxtl
  have ht3 : 3 ≤ t := by omega
  -- for `y ≡ lo` strictly inside, the progression `y, lo+t, 2(lo+t)-y` obeys the rule
  have claim : ∀ y, y % 2 = x % 2 → x + 2 ≤ y → y + 2 ≤ hi →
      (Bef a (x + t) y ↔ (x + t) % 2 = w % 2) := by
    intro y hy1 hy2 hy3
    rcases Nat.lt_or_ge y (x + t) with hlt | hge
    · have e := resL hwlo y (x + t - y) (by omega) (by omega) (by omega)
      rwa [show y + (x + t - y) = x + t by omega] at e
    · have e := resL hwlo (2 * (x + t) - y) (y - (x + t)) (by omega) (by omega) (by omega)
      rw [show 2 * (x + t) - y + (y - (x + t)) = x + t by omega] at e
      rw [← e]
      have hy : y ∈ a := memI _ (by omega) (by omega)
      have hy' : 2 * (x + t) - y ∈ a := memI _ (by omega) (by omega)
      constructor
      · intro h; exact middle hnd hap (by omega) (by omega) hy' h
      · intro h; exact middle hnd hap (by omega) (by omega) hy h
  by_cases hbw : (x + t) % 2 = w % 2
  · rw [iff_true_right hbw]
    by_contra hn
    have h1 : Bef a x (x + t) := by
      rcases bef_total hnd hxa hb (by omega) with h | h
      · exact h
      · exact absurd h hn
    have h2 : Bef a (x + 2 * t) (x + t) := by
      rcases bef_total hnd hx2 hb (by omega) with h | h
      · exact h
      · exact absurd (by omega) (hap _ _ _ (bef_trans3 hnd h1 h))
    exact zeta hnd hap (fun v h1 h2 => memI v h1 h2) hxhi.symm ht ht3 fun y hy1 hy2 hy3 =>
      ⟨bef_trans hnd h1 ((claim y hy1 hy2 hy3).2 hbw),
        bef_trans hnd (by rwa [hxhi] at h2) ((claim y hy1 hy2 hy3).2 hbw)⟩
  · rw [iff_false_right hbw]
    intro h1
    have h2 : Bef a (x + t) (x + 2 * t) := middle hnd hap (by omega) (by omega) hx2 h1
    have hY : ∀ y, y % 2 = x % 2 → x + 2 ≤ y → y + 2 ≤ hi → Bef a y (x + t) := by
      intro y hy1 hy2 hy3
      have hn : ¬ Bef a (x + t) y := fun h => hbw ((claim y hy1 hy2 hy3).1 h)
      rcases bef_total hnd (memI y (by omega) (by omega)) hb (by omega) with h | h
      · exact h
      · exact absurd h hn
    refine zeta (List.nodup_reverse.2 hnd) hap.reverse
      (fun v h1 h2 => List.mem_reverse.2 (memI v h1 h2)) hxhi.symm ht ht3
      fun y hy1 hy2 hy3 => ?_
    rw [bef_reverse, bef_reverse]
    exact ⟨bef_trans hnd (hY y hy1 hy2 hy3) h1,
      bef_trans hnd (hY y hy1 hy2 hy3) (by rwa [hxhi] at h2)⟩

/-! ## Fold sequences: from `APFree` to the sublist form -/

theorem apf_of_apFree {a : List ℕ} (h : APFree a) : APF a := by
  intro x y z hs e
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.1 hs
  have h01 : f ⟨0, by simp⟩ < f ⟨1, by simp⟩ := f.strictMono (Fin.mk_lt_mk.2 (by decide))
  have h12 : f ⟨1, by simp⟩ < f ⟨2, by simp⟩ := f.strictMono (Fin.mk_lt_mk.2 (by decide))
  have e0 := hf ⟨0, by simp⟩
  have e1 := hf ⟨1, by simp⟩
  have e2 := hf ⟨2, by simp⟩
  simp only [List.get_eq_getElem] at e0 e1 e2
  refine h (f ⟨0, by simp⟩) (f ⟨1, by simp⟩) (f ⟨2, by simp⟩) h01 h12 (f ⟨2, by simp⟩).2 ?_
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2
  rw [← e0, ← e1, ← e2]; exact e

theorem apFree_reverse {a : List ℕ} (h : APFree a) : APFree a.reverse := by
  intro i j k hi hj hk e
  simp only [List.length_reverse] at hk
  simp only [List.getElem_reverse] at e
  exact h (a.length - 1 - k) (a.length - 1 - j) (a.length - 1 - i) (by omega) (by omega)
    (by omega) (by omega)

/-- If `y` comes before `u` in `l₁ ++ u :: l₂` (no repetitions), then `y ∈ l₁`. -/
theorem mem_of_bef_append : ∀ {l₁ l₂ : List ℕ} {u y : ℕ}, (l₁ ++ u :: l₂).Nodup →
    Bef (l₁ ++ u :: l₂) y u → y ∈ l₁
  | [], l₂, u, y, hnd, h => by
    rw [List.nil_append, List.nodup_cons] at hnd
    rw [List.nil_append, bef_cons_iff] at h
    rcases h with h | ⟨rfl, h⟩
    · exact absurd (bef_mem h).2 hnd.1
    · exact absurd h hnd.1
  | v :: t, l₂, u, y, hnd, h => by
    rw [List.cons_append, List.nodup_cons] at hnd
    rw [List.cons_append, bef_cons_iff] at h
    rcases h with h | ⟨rfl, -⟩
    · exact List.mem_cons_of_mem _ (mem_of_bef_append hnd.2 h)
    · exact List.mem_cons_self ..

/-- In a 3-AP-free permutation of `[1..N]` with first entry `w`, let `u ≢ w` and `y ≢ u`.
If `y` and `u` lie in a common 3-term progression inside `[1, N]`, then `y` comes before
`u`. -/
theorem bef_of_window {N : ℕ} {a : List ℕ} {w : ℕ} {tl : List ℕ} (ha : a = w :: tl)
    (hnd : a.Nodup) (hI : ∀ v, v ∈ a ↔ 1 ≤ v ∧ v ≤ N) (hap : APF a) {u y : ℕ}
    (hu : 1 ≤ u ∧ u ≤ N) (hy : 1 ≤ y ∧ y ≤ N) (huw : u % 2 ≠ w % 2) (hyu : y % 2 ≠ u % 2)
    (hc : (u < 2 * y ∧ 2 * y ≤ N + u) ∨ (y < 2 * u ∧ 2 * u ≤ N + y)) : Bef a y u := by
  have O := orient (N - 1) a 1 N w tl (by omega) ha hnd hI hap
  have memI : ∀ v, 1 ≤ v → v ≤ N → v ∈ a := fun v h1 h2 => (hI v).2 ⟨h1, h2⟩
  have hua := memI u hu.1 hu.2
  have hya := memI y hy.1 hy.2
  rcases Nat.lt_or_gt_of_ne (show y ≠ u by omega) with hlt | hgt
  · rcases hc with hc | hc
    · have e := O (2 * y - u) (u - y) (by omega) (by omega) (by omega)
      rw [show 2 * y - u + (u - y) = y by omega] at e
      exact middle hnd hap (x := 2 * y - u) (by omega) (by omega) hua (e.2 (by omega))
    · have e := O y (u - y) (by omega) (by omega) (by omega)
      rw [show y + (u - y) = u by omega] at e
      rcases bef_total hnd hya hua (by omega) with h | h
      · exact h
      · exact absurd (e.1 h) huw
  · rcases hc with hc | hc
    · have e := O u (y - u) (by omega) (by omega) (by omega)
      rw [show u + (y - u) = y by omega] at e
      exact e.2 (by omega)
    · have e := O (2 * u - y) (y - u) (by omega) (by omega) (by omega)
      rw [show 2 * u - y + (y - u) = u by omega] at e
      have hxa := memI (2 * u - y) (by omega) (by omega)
      have h1 : Bef a (2 * u - y) u := by
        rcases bef_total hnd hxa hua (by omega) with h | h
        · exact h
        · exact absurd (e.1 h) huw
      rcases bef_total hnd hya hua (by omega) with h | h
      · exact h
      · exact absurd (by omega) (hap _ _ _ (bef_trans3 hnd h1 h))

/-- **Prefix parity.**  In a 3-AP-free permutation of `[1..N]`, the entries at 0-based
indices `k` with `4(k+1) ≤ N+1` (the first `⌊(N+1)/4⌋` entries) all have the parity of
the first entry. -/
theorem prefix_parity {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a) (hfree : APFree a) {k : ℕ}
    (hk : k < a.length) (hK : 4 * (k + 1) ≤ N + 1) :
    a[k] % 2 = a[0]'(by omega) % 2 := by
  by_contra hne
  have hnd : a.Nodup := hf.nodup_iff.2 (List.nodup_range' ..)
  have hI : ∀ v, v ∈ a ↔ 1 ≤ v ∧ v ≤ N := fun v => by rw [mem_range'_of_perm hf]
  obtain ⟨w, tl, ha⟩ : ∃ w tl, a = w :: tl := by
    cases a with
    | nil => simp at hk
    | cons w tl => exact ⟨w, tl, rfl⟩
  have hw0 : a[0]'(by omega) = w := by subst ha; rfl
  rw [hw0] at hne
  set u := a[k] with hu_def
  have hu : 1 ≤ u ∧ u ≤ N := (hI u).1 (List.getElem_mem hk)
  have hap := apf_of_apFree hfree
  let yf : ℕ → ℕ := fun j =>
    if 2 * u ≤ N + 1 then 2 * j + 1 + u % 2 else N - 2 * j - (N + 1 - u) % 2
  have hsplit : a = a.take k ++ u :: a.drop (k + 1) := by
    rw [hu_def, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hsub : (Finset.range (k + 1)).image yf ⊆ (a.take k).toFinset := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    rw [List.mem_toFinset]
    have hb : Bef a (yf j) u := by
      refine bef_of_window ha hnd hI hap hu ?_ hne ?_ ?_ <;> simp only [yf] <;>
        split_ifs <;> omega
    rw [hsplit] at hb hnd
    exact mem_of_bef_append hnd hb
  have hcard : ((Finset.range (k + 1)).image yf).card = k + 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    simp only [yf] at e
    split_ifs at e <;> omega
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le (a.take k)
  rw [List.length_take] at h2
  omega

/-- The first and the last entry of a 3-AP-free permutation of `[1..N]`, `N ≥ 2`, have
different parities: otherwise their average would lie between them. -/
theorem head_last_parity {N : ℕ} {a : List ℕ} (hf : IsFoldSeq N a) (hfree : APFree a)
    (hN : 2 ≤ N) (h0 : 0 < a.length) :
    a[0] % 2 ≠ a[a.length - 1]'(by omega) % 2 := by
  intro e
  have hnd : a.Nodup := hf.nodup_iff.2 (List.nodup_range' ..)
  have hlen : a.length = N := by rw [hf.length_eq]; simp
  have hI : ∀ v, v ∈ a ↔ 1 ≤ v ∧ v ≤ N := fun v => by rw [mem_range'_of_perm hf]
  have b0 := (hI _).1 (List.getElem_mem h0)
  have b1 := (hI _).1 (List.getElem_mem (show a.length - 1 < a.length by omega))
  have hne : a[0] ≠ a[a.length - 1]'(by omega) := fun h => by
    have := (List.Nodup.getElem_inj hnd).1 h; omega
  obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.1
    ((hI ((a[0] + a[a.length - 1]'(by omega)) / 2)).2 ⟨by omega, by omega⟩)
  have hj0 : j ≠ 0 := by rintro rfl; omega
  have hj1 : j ≠ a.length - 1 := by rintro rfl; omega
  exact hfree 0 j (a.length - 1) (by omega) (by omega) (by omega) (by omega)

/-! ## Counting -/

/-- The symmetric fold sequences of length `N` (the 3-AP-free permutations of `[1..N]`). -/
def symSeqs (N : ℕ) : Finset (List ℕ) :=
  (List.range' 1 N).permutations.toFinset.filter (Symmetric N)

theorem mem_symSeqs {N : ℕ} {a : List ℕ} :
    a ∈ symSeqs N ↔ IsFoldSeq N a ∧ Symmetric N a := by
  simp [symSeqs, List.mem_permutations, IsFoldSeq]

theorem apFree_of_mem {N : ℕ} {a : List ℕ} (h : a ∈ symSeqs N) : APFree a :=
  (symmetric_iff_apFree (mem_symSeqs.1 h).1).1 (mem_symSeqs.1 h).2

theorem length_of_mem {N : ℕ} {a : List ℕ} (h : a ∈ symSeqs N) : a.length = N := by
  rw [(mem_symSeqs.1 h).1.length_eq]; simp

theorem reverse_mem_symSeqs {N : ℕ} {a : List ℕ} (h : a ∈ symSeqs N) :
    a.reverse ∈ symSeqs N := by
  have hf' : IsFoldSeq N a.reverse := (List.reverse_perm _).trans (mem_symSeqs.1 h).1
  exact mem_symSeqs.2 ⟨hf', (symmetric_iff_apFree hf').2 (apFree_reverse (apFree_of_mem h))⟩

/-- The entry at index `k` exists and has parity `r`. -/
def ParAt (k r : ℕ) (a : List ℕ) : Prop := ∃ x, a[k]? = some x ∧ x % 2 = r

instance (k r : ℕ) (a : List ℕ) : Decidable (ParAt k r a) :=
  decidable_of_iff (∃ x ∈ a[k]?, x % 2 = r) (by simp [ParAt])

theorem parAt_iff {k r : ℕ} {a : List ℕ} (hk : k < a.length) :
    ParAt k r a ↔ a[k] % 2 = r := by
  simp [ParAt, List.getElem?_eq_getElem hk]

/-- Reversal is a bijection from the odd-first to the even-first symmetric sequences. -/
theorem card_head_odd_eq_even {N : ℕ} (hN : 2 ≤ N) :
    ((symSeqs N).filter (ParAt 0 1)).card = ((symSeqs N).filter (ParAt 0 0)).card := by
  have key : ∀ a ∈ symSeqs N, a[0]? ≠ none →
      ∀ x y, a[0]? = some x → a.reverse[0]? = some y → x % 2 ≠ y % 2 := by
    intro a ha _ x y hx hy
    have hlen := length_of_mem ha
    have h0 : 0 < a.length := by omega
    have hp := head_last_parity (mem_symSeqs.1 ha).1 (apFree_of_mem ha) hN h0
    rw [List.getElem?_eq_getElem h0] at hx
    rw [List.getElem?_eq_getElem (by simpa using h0)] at hy
    simp only [Option.some.injEq] at hx hy
    rw [List.getElem_reverse] at hy
    rw [← hx, ← hy]
    simpa using hp
  have rev : ∀ a ∈ symSeqs N, ∀ r, r < 2 → (ParAt 0 r a ↔ ¬ ParAt 0 r a.reverse) := by
    intro a ha r hr
    have hlen := length_of_mem ha
    have h0 : 0 < a.length := by omega
    have h0' : 0 < a.reverse.length := by simpa using h0
    have := key a ha (by simp [List.getElem?_eq_getElem h0]) _ _
      (List.getElem?_eq_getElem h0) (List.getElem?_eq_getElem h0')
    rw [parAt_iff h0, parAt_iff h0']
    omega
  refine Finset.card_nbij' List.reverse List.reverse ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    refine ⟨reverse_mem_symSeqs ha.1, ?_⟩
    have hlen := length_of_mem ha.1
    have h1 := (rev a ha.1 1 (by omega)).1 ha.2
    rw [parAt_iff (by simp; omega)] at h1 ⊢
    omega
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    refine ⟨reverse_mem_symSeqs ha.1, ?_⟩
    have hlen := length_of_mem ha.1
    have h1 := (rev a ha.1 0 (by omega)).1 ha.2
    rw [parAt_iff (by simp; omega)] at h1 ⊢
    omega
  · intro a _; simp
  · intro a _; simp

/-- **Parity balance.**  For every `N ≥ 2`, exactly half of the symmetric (3-AP-free)
fold sequences of `[N]` start with an odd panel. -/
theorem two_mul_card_head_odd {N : ℕ} (hN : 2 ≤ N) :
    2 * ((symSeqs N).filter (ParAt 0 1)).card = (symSeqs N).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := symSeqs N) (ParAt 0 1)
  have hneg : (symSeqs N).filter (fun a => ¬ ParAt 0 1 a) =
      (symSeqs N).filter (ParAt 0 0) := by
    apply Finset.filter_congr
    intro a ha
    have h0 : 0 < a.length := by rw [length_of_mem ha]; omega
    rw [parAt_iff h0, parAt_iff h0]; omega
  rw [hneg, ← card_head_odd_eq_even hN] at hsplit
  omega

/-- **Parity balance at step `k+1`.**  If `4(k+1) ≤ N+1`, exactly half of the symmetric
fold sequences of `[N]` have an odd panel at 0-based index `k` (so each of the first
`⌊(N+1)/4⌋` steps is parity-balanced). -/
theorem two_mul_card_getElem_odd {N k : ℕ} (hK : 4 * (k + 1) ≤ N + 1) :
    2 * ((symSeqs N).filter (ParAt k 1)).card = (symSeqs N).card := by
  have e : (symSeqs N).filter (ParAt k 1) = (symSeqs N).filter (ParAt 0 1) := by
    apply Finset.filter_congr
    intro a ha
    have hlen := length_of_mem ha
    rw [parAt_iff (by omega), parAt_iff (by omega),
      prefix_parity (mem_symSeqs.1 ha).1 (apFree_of_mem ha) (by omega) hK]
  rw [e]; exact two_mul_card_head_odd (by omega)

end SymParity
end Folds
