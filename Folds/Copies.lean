import Folds.Growth
import Folds.Live

/-!
# Window copies: general doubling splits, Beatty copies

## General doubling splits

For `q = 2j + 1` and `N = qn`, the panels with residue in `{2, 4, …, 2j}` mod `q` form a
doubling set of size `jn` (`doubling_evenRes`), with counting function
`c(x) = j⌊x/q⌋ + ⌊(x mod q)/2⌋`, and the remaining panels (residues `{1, 3, …, 2j-1, 0}`)
one of size `(j+1)n` (`doubling_oddRes`), with counting function `x - c(x)`.  Hence
(`semiCount_doubling`)  `2 · a(jn) · a((j+1)n) ≤ a((2j+1)n)`  for all `j, n ≥ 1`,
generalising `semiCount_three`, `semiCount_five`, `semiCount_seven`.

See `experiments/growth/PROOFS.txt` §1.2.
-/

namespace Folds

/-! ## General doubling splits -/

/-- The `y`-th panel (`y ≥ 1`) with residue in `{2, 4, …, 2j}` mod `2j+1`. -/
def evenRes (j y : Nat) : Nat := (2 * j + 1) * ((y - 1) / j) + 2 * ((y - 1) % j) + 2

/-- The `y`-th panel (`y ≥ 1`) with residue in `{1, 3, …, 2j-1, 0}` mod `2j+1`. -/
def oddRes (j y : Nat) : Nat :=
  (2 * j + 1) * ((y - 1) / (j + 1)) + 2 * ((y - 1) % (j + 1)) + 1

/-- Counting function of `evenRes j`: `#{y ≥ 1 : evenRes j y ≤ x}`. -/
def evenCnt (j x : Nat) : Nat := j * (x / (2 * j + 1)) + x % (2 * j + 1) / 2

/-- Counting function of `oddRes j`. -/
def oddCnt (j x : Nat) : Nat := x - evenCnt j x

theorem evenCnt_eq {j a r : Nat} (hr : r < 2 * j + 1) :
    evenCnt j (2 * (j * a) + a + r) = j * a + r / 2 := by
  unfold evenCnt
  have e : 2 * (j * a) + a + r = (2 * j + 1) * a + r := by ring
  rw [e, Nat.mul_add_div (by omega), Nat.mul_add_mod, Nat.div_eq_of_lt hr,
    Nat.mod_eq_of_lt hr]
  simp

theorem decomp (q x : Nat) (hq : 0 < q) : ∃ a r, r < q ∧ x = q * a + r :=
  ⟨x / q, x % q, Nat.mod_lt _ hq, (Nat.div_add_mod x q).symm⟩

/-- Every `x` is `(2j+1) a + r` with `r ≤ 2j`, written linearly in the atom `j * a`. -/
theorem decompQ (j x : Nat) : ∃ a r, r < 2 * j + 1 ∧ x = 2 * (j * a) + a + r := by
  obtain ⟨a, r, hr, rfl⟩ := decomp (2 * j + 1) x (by omega)
  exact ⟨a, r, hr, by ring⟩

theorem evenCnt_le (j x : Nat) : evenCnt j x ≤ x := by
  obtain ⟨a, r, hr, rfl⟩ := decompQ j x
  rw [evenCnt_eq hr]; omega

theorem evenRes_eq {j u v : Nat} (hv : v < j) :
    evenRes j (j * u + v + 1) = 2 * (j * u) + u + 2 * v + 2 := by
  unfold evenRes
  rw [show j * u + v + 1 - 1 = j * u + v by omega, Nat.mul_add_div (by omega),
    Nat.mul_add_mod, Nat.div_eq_of_lt hv, Nat.mod_eq_of_lt hv]
  ring

theorem oddRes_eq {j u v : Nat} (hv : v < j + 1) :
    oddRes j ((j + 1) * u + v + 1) = 2 * (j * u) + u + 2 * v + 1 := by
  unfold oddRes
  rw [show (j + 1) * u + v + 1 - 1 = (j + 1) * u + v by omega, Nat.mul_add_div (by omega),
    Nat.mul_add_mod, Nat.div_eq_of_lt hv, Nat.mod_eq_of_lt hv]
  ring

/-- Products of the atom `j * a` with comparisons of `a`. -/
theorem mul_cmp (j u a : Nat) :
    (u < a ∧ j * u + j ≤ j * a) ∨ u = a ∨ (a < u ∧ j * a + j ≤ j * u) := by
  rcases lt_trichotomy u a with h | h | h
  · left; refine ⟨h, ?_⟩
    have := Nat.mul_le_mul_left j (show u + 1 ≤ a by omega); rw [Nat.mul_add] at this; omega
  · right; left; exact h
  · right; right; refine ⟨h, ?_⟩
    have := Nat.mul_le_mul_left j (show a + 1 ≤ u by omega); rw [Nat.mul_add] at this; omega

theorem evenCnt_double (j x : Nat) :
    evenCnt j (2 * x + 1) = evenCnt j x + evenCnt j (x + 1) := by
  obtain ⟨a, r, hr, rfl⟩ := decompQ j x
  have e2 : j * (2 * a) = 2 * (j * a) := by ring
  have e3 : j * (2 * a + 1) = 2 * (j * a) + j := by ring
  have e4 : j * (a + 1) = j * a + j := by ring
  rw [evenCnt_eq hr]
  rcases Nat.lt_or_ge (2 * r + 1) (2 * j + 1) with h1 | h1
  · rw [show 2 * (2 * (j * a) + a + r) + 1 = 2 * (j * (2 * a)) + 2 * a + (2 * r + 1) by
      rw [e2]; ring, evenCnt_eq h1, e2]
    rcases Nat.lt_or_ge (r + 1) (2 * j + 1) with h2 | h2
    · rw [show 2 * (j * a) + a + r + 1 = 2 * (j * a) + a + (r + 1) by ring, evenCnt_eq h2]
      omega
    · rw [show 2 * (j * a) + a + r + 1 = 2 * (j * (a + 1)) + (a + 1) + 0 by rw [e4]; omega,
        evenCnt_eq (by omega), e4]
      omega
  · rw [show 2 * (2 * (j * a) + a + r) + 1 =
        2 * (j * (2 * a + 1)) + (2 * a + 1) + (2 * r + 1 - (2 * j + 1)) by rw [e3]; omega,
      evenCnt_eq (by omega), e3]
    rcases Nat.lt_or_ge (r + 1) (2 * j + 1) with h2 | h2
    · rw [show 2 * (j * a) + a + r + 1 = 2 * (j * a) + a + (r + 1) by ring, evenCnt_eq h2]
      omega
    · rw [show 2 * (j * a) + a + r + 1 = 2 * (j * (a + 1)) + (a + 1) + 0 by rw [e4]; omega,
        evenCnt_eq (by omega), e4]
      omega

theorem evenCnt_mirror (j n x : Nat) (hx : x ≤ (2 * j + 1) * n) :
    evenCnt j x + evenCnt j ((2 * j + 1) * n - x) = j * n := by
  obtain ⟨a, r, hr, rfl⟩ := decompQ j x
  rw [evenCnt_eq hr]
  have hN : (2 * j + 1) * n = 2 * (j * n) + n := by ring
  rcases mul_cmp j n a with ⟨h, h'⟩ | rfl | ⟨h, h'⟩
  · omega
  · rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rw [show (2 * j + 1) * n - (2 * (j * n) + n + 0) = 2 * (j * 0) + 0 + 0 by
        rw [hN]; simp, evenCnt_eq (by omega)]
      simp
    · omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = a + k := ⟨n - a, by omega⟩
    have e : j * (a + k) = j * a + j * k := by ring
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rw [show (2 * j + 1) * (a + k) - (2 * (j * a) + a + 0) = 2 * (j * k) + k + 0 by
        rw [hN, e]; omega, evenCnt_eq (by omega), e]
      omega
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp at h'; omega
        · omega⟩
      have e' : j * (k + 1) = j * k + j := by ring
      rw [show (2 * j + 1) * (a + (k + 1)) - (2 * (j * a) + a + r) =
          2 * (j * k) + k + (2 * j + 1 - r) by rw [hN, e, e']; omega,
        evenCnt_eq (by omega), e, e']
      omega

theorem doubling_evenRes {j : Nat} (hj : 1 ≤ j) (n : Nat) :
    DoublingSet ((2 * j + 1) * n) (j * n) (evenRes j) (evenCnt j) := by
  refine ⟨?_, ?_, by simp [evenCnt], evenCnt_double j, evenCnt_mirror j n⟩
  · intro y t hy
    obtain ⟨u, v, hv, rfl⟩ : ∃ u v, v < j ∧ y = j * u + v + 1 := by
      obtain ⟨u, v, hv, e⟩ := decomp j (y - 1) (by omega); exact ⟨u, v, hv, by omega⟩
    obtain ⟨a, r, hr, rfl⟩ := decompQ j t
    rw [evenRes_eq hv, evenCnt_eq hr]
    rcases mul_cmp j u a with ⟨h, h'⟩ | rfl | ⟨h, h'⟩ <;> omega
  · intro y hy
    obtain ⟨u, v, hv, rfl⟩ : ∃ u v, v < j ∧ y = j * u + v + 1 := by
      obtain ⟨u, v, hv, e⟩ := decomp j (y - 1) (by omega); exact ⟨u, v, hv, by omega⟩
    rw [evenRes_eq hv]
    rcases Nat.lt_or_ge (v + 1) j with h | h
    · rw [show j * u + v + 1 + 1 = j * u + (v + 1) + 1 by ring, evenRes_eq h]; omega
    · rw [show j * u + v + 1 + 1 = j * (u + 1) + 0 + 1 by rw [Nat.mul_add]; omega,
        evenRes_eq (u := u + 1) (v := 0) (by omega), Nat.mul_add]
      omega

theorem doubling_oddRes {j : Nat} (n : Nat) :
    DoublingSet ((2 * j + 1) * n) ((j + 1) * n) (oddRes j) (oddCnt j) := by
  refine ⟨?_, ?_, by simp [oddCnt, evenCnt], fun x => ?_, fun x hx => ?_⟩
  · intro y t hy
    obtain ⟨u, v, hv, rfl⟩ : ∃ u v, v < j + 1 ∧ y = (j + 1) * u + v + 1 := by
      obtain ⟨u, v, hv, e⟩ := decomp (j + 1) (y - 1) (by omega); exact ⟨u, v, hv, by omega⟩
    obtain ⟨a, r, hr, rfl⟩ := decompQ j t
    rw [oddRes_eq hv]
    unfold oddCnt; rw [evenCnt_eq hr]
    have e : (j + 1) * u = j * u + u := by ring
    rw [e]
    rcases mul_cmp j u a with ⟨h, h'⟩ | rfl | ⟨h, h'⟩ <;> omega
  · intro y hy
    obtain ⟨u, v, hv, rfl⟩ : ∃ u v, v < j + 1 ∧ y = (j + 1) * u + v + 1 := by
      obtain ⟨u, v, hv, e⟩ := decomp (j + 1) (y - 1) (by omega); exact ⟨u, v, hv, by omega⟩
    rw [oddRes_eq hv]
    rcases Nat.lt_or_ge (v + 1) (j + 1) with h | h
    · rw [show (j + 1) * u + v + 1 + 1 = (j + 1) * u + (v + 1) + 1 by ring, oddRes_eq h]
      omega
    · rw [show (j + 1) * u + v + 1 + 1 = (j + 1) * (u + 1) + 0 + 1 by
        rw [Nat.mul_add]; omega, oddRes_eq (u := u + 1) (v := 0) (by omega), Nat.mul_add]
      omega
  · unfold oddCnt
    have := evenCnt_double j x
    have := evenCnt_le j x; have := evenCnt_le j (x + 1); have := evenCnt_le j (2 * x + 1)
    omega
  · unfold oddCnt
    have := evenCnt_mirror j n x hx
    have := evenCnt_le j x; have := evenCnt_le j ((2 * j + 1) * n - x)
    have hN : (2 * j + 1) * n = 2 * (j * n) + n := by ring
    have e : (j + 1) * n = j * n + n := by ring
    omega

/-- The residues `{2, …, 2j}` and `{1, 3, …, 2j-1, 0}` mod `2j+1` split `[1..(2j+1)n]`. -/
theorem split_res {j : Nat} (hj : 1 ≤ j) (n : Nat) :
    Split ((2 * j + 1) * n) (j * n) ((j + 1) * n) (evenRes j) (oddRes j) :=
  split_of_doubling (doubling_evenRes hj n) (doubling_oddRes n) fun x => by
    unfold oddCnt; have := evenCnt_le j x; omega

/-- **General doubling splits.**  `2 · a(jn) · a((j+1)n) ≤ a((2j+1)n)` for `j, n ≥ 1`. -/
theorem semiCount_doubling {j n : Nat} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    2 * (semiCount (j * n) * semiCount ((j + 1) * n)) ≤ semiCount ((2 * j + 1) * n) :=
  (split_res hj n).card_le (Nat.mul_pos hj hn) (Nat.mul_pos (by omega) hn)

/-! ## The copy criterion

`φ : [1..p] → [1..N]` strictly increasing with counting function `c`
(`c t = #{y ≥ 1 : φ y ≤ t}`).  Its image `X` is a window copy of the `p`-strip iff every
element of `X` is a valid last step of `X`, iff the extended counting function satisfies
`c~(2x - 1) = 2 c(x) - 1` at every `x ∈ X` (`CopyAt`). -/

/-- `φ` is strictly increasing on `[1..p]` with counting function `c` on `[0..N]`. -/
structure CountEmb (N p : Nat) (φ c : Nat → Nat) : Prop where
  gal : ∀ y t, 1 ≤ y → (φ y ≤ t ↔ y ≤ c t)
  mono : ∀ y, 1 ≤ y → φ y < φ (y + 1)
  zero : c 0 = 0
  top : c N = p

/-- The copy condition at the `j`-th element `x = φ j`: `c~(2x - 1) = 2j - 1`, where
`c~(y) = p + c(y - N)` for `y > N`. -/
def CopyAt (N p : Nat) (φ c : Nat → Nat) (j : Nat) : Prop :=
  (2 * φ j ≤ N + 1 → c (2 * φ j - 1) = 2 * j - 1) ∧
    (N + 1 ≤ 2 * φ j → c (2 * φ j - N - 1) + p = 2 * j - 1)

namespace CountEmb

variable {N p : Nat} {φ c : Nat → Nat}

theorem c_mono (h : CountEmb N p φ c) {x x' : Nat} (hx : x ≤ x') : c x ≤ c x' := by
  rcases Nat.eq_zero_or_pos (c x) with h0 | hpos
  · omega
  · have := (h.gal (c x) x hpos).2 le_rfl
    exact (h.gal (c x) x' hpos).1 (by omega)

theorem phi_pos (h : CountEmb N p φ c) {y : Nat} (hy : 1 ≤ y) : 1 ≤ φ y := by
  refine Decidable.byContradiction fun hc => ?_
  have := (h.gal y 0 hy).1 (by omega)
  rw [h.zero] at this; omega

theorem phi_le (h : CountEmb N p φ c) {y : Nat} (hy1 : 1 ≤ y) (hyp : y ≤ p) : φ y ≤ N :=
  (h.gal y N hy1).2 (by rw [h.top]; exact hyp)

theorem c_phi (h : CountEmb N p φ c) {j : Nat} (hj : 1 ≤ j) : c (φ j) = j := by
  have a := (h.gal j (φ j) hj).1 le_rfl
  have b := h.gal (j + 1) (φ j) (by omega)
  have := h.mono j hj
  refine Decidable.byContradiction fun hne => ?_
  have := b.2 (by omega); omega

theorem c_phi_pred (h : CountEmb N p φ c) {j : Nat} (hj : 1 ≤ j) :
    c (φ j - 1) = j - 1 := by
  have p1 := h.phi_pos hj
  have a := h.gal j (φ j - 1) hj
  have lt : c (φ j - 1) < j := by
    refine Decidable.byContradiction fun hh => ?_
    have := a.2 (by omega); omega
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · omega
  · have b := (h.gal (j - 1) (φ j - 1) (by omega)).1
    have := h.mono (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at this
    have := b (by omega); omega

/-- Every doubling set is a `CountEmb`. -/
theorem of_doubling (h : DoublingSet N p φ c) : CountEmb N p φ c :=
  ⟨h.gal, h.mono, h.zero, h.c_N⟩

/-- **Copy criterion, sufficiency.**  The copy condition at every element makes `φ` a
window embedding. -/
theorem winEmb (h : CountEmb N p φ c) (hc : ∀ j, 1 ≤ j → j ≤ p → CopyAt N p φ c j) :
    WinEmb N p φ := by
  refine ⟨fun y h1 h2 => ⟨h.phi_pos h1, h.phi_le h1 h2⟩, fun x y hx1 _ hy1 _ e => ?_, ?_, ?_⟩
  · have a := h.c_phi hx1; have b := h.c_phi hy1; rw [e] at a; omega
  · intro j y hj1 hjp hy1 hyp
    have hm1 := h.phi_pos hj1; have hmN := h.phi_le hj1 hjp
    have cm := h.c_phi hj1; have cm1 := h.c_phi_pred hj1
    have a := h.gal y (φ j - 1) hy1
    have b := h.gal y (φ j - reach N (φ j) - 1) hy1
    have hcj := hc j hj1 hjp
    rcases Nat.le_total (φ j - 1) (N - φ j) with hle | hle
    · have hr' : reach N (φ j) = φ j - 1 := by unfold reach; omega
      rw [hr'] at b ⊢; rw [show φ j - (φ j - 1) - 1 = 0 by omega, h.zero] at b
      have d := hcj.1 (by omega)
      have bd := h.c_mono (show 2 * φ j - 1 ≤ N by omega); rw [h.top] at bd
      have hrp : reach p j = j - 1 := by unfold reach; omega
      rw [hrp]; omega
    · have hr' : reach N (φ j) = N - φ j := by unfold reach; omega
      rw [hr'] at b ⊢
      rw [show φ j - (N - φ j) - 1 = 2 * φ j - N - 1 by omega] at b
      have d := hcj.2 (by omega)
      have hrp : reach p j = p - j := by unfold reach; omega
      rw [hrp]; omega
  · intro j y hj1 hjp hy1 hyp
    have hm1 := h.phi_pos hj1; have hmN := h.phi_le hj1 hjp
    have cm := h.c_phi hj1; have cm1 := h.c_phi_pred hj1
    have a := h.gal y (φ j) hy1
    have b := h.gal y (φ j + reach N (φ j)) hy1
    have hcj := hc j hj1 hjp
    rcases Nat.le_total (φ j - 1) (N - φ j) with hle | hle
    · have hr' : reach N (φ j) = φ j - 1 := by unfold reach; omega
      have d := hcj.1 (by omega)
      rw [hr'] at b ⊢; rw [show φ j + (φ j - 1) = 2 * φ j - 1 by omega, d] at b
      have bd := h.c_mono (show 2 * φ j - 1 ≤ N by omega)
      rw [h.top, d] at bd
      have hrp : reach p j = j - 1 := by unfold reach; omega
      rw [hrp]; omega
    · have hr' : reach N (φ j) = N - φ j := by unfold reach; omega
      rw [hr'] at b ⊢
      rw [show φ j + (N - φ j) = N by omega, h.top] at b
      have d := hcj.2 (by omega)
      have hrp : reach p j = p - j := by unfold reach; omega
      rw [hrp]; omega

/-- **Copy criterion, the counting form.**  The image of `φ` is balanced around `φ j` iff
the copy condition holds at `j`. -/
theorem balanced_iff (h : CountEmb N p φ c) {j : Nat} (hj1 : 1 ≤ j) (hjp : j ≤ p) :
    Balanced N ((List.range' 1 p).map φ) (φ j) ↔ CopyAt N p φ c j := by
  have hm1 := h.phi_pos hj1; have hmN := h.phi_le hj1 hjp
  have cm := h.c_phi hj1; have cm1 := h.c_phi_pred hj1
  unfold Balanced CopyAt
  generalize hm : φ j = m at hm1 hmN cm cm1 ⊢
  rw [List.countP_map, List.countP_map]
  have hr : reach N m ≤ m - 1 := by unfold reach; omega
  have L : (List.range' 1 p).countP ((fun x => decide (m - reach N m ≤ x ∧ x < m)) ∘ φ) =
      (List.range' 1 p).countP
        (fun y => decide (c (m - reach N m - 1) + 1 ≤ y ∧ y ≤ c (m - 1))) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    have a := h.gal y (m - 1) hy.1
    have b := h.gal y (m - reach N m - 1) hy.1
    omega
  have R : (List.range' 1 p).countP
        ((fun x => decide (m < x ∧ x ≤ m + reach N m)) ∘ φ) =
      (List.range' 1 p).countP
        (fun y => decide (c m + 1 ≤ y ∧ y ≤ c (m + reach N m))) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    have a := h.gal y m hy.1
    have b := h.gal y (m + reach N m) hy.1
    omega
  rw [L, R, countP_range'_interval, countP_range'_interval]
  have b1 := h.c_mono hmN; rw [h.top] at b1
  rcases Nat.le_total (m - 1) (N - m) with hle | hle
  · have hr' : reach N m = m - 1 := by unfold reach; omega
    rw [hr', show m - (m - 1) - 1 = 0 by omega, show m + (m - 1) = 2 * m - 1 by omega,
      h.zero]
    have b2 := h.c_mono (show 2 * m - 1 ≤ N by omega); rw [h.top] at b2
    have b3 := h.c_mono (show m ≤ 2 * m - 1 by omega)
    constructor
    · intro e
      refine ⟨fun _ => by omega, fun h2 => ?_⟩
      have : 2 * m - 1 = N := by omega
      rw [this, h.top] at e
      rw [show 2 * m - N - 1 = 0 by omega, h.zero]; omega
    · intro e; have := e.1 (by omega); omega
  · have hr' : reach N m = N - m := by unfold reach; omega
    rw [hr', show m - (N - m) - 1 = 2 * m - N - 1 by omega, show m + (N - m) = N by omega,
      h.top]
    have b2 := h.c_mono (show 2 * m - N - 1 ≤ m - 1 by omega)
    constructor
    · intro e
      refine ⟨fun h2 => ?_, fun _ => by omega⟩
      have : 2 * m - 1 = N := by omega
      rw [this, h.top]
      rw [show 2 * m - N - 1 = 0 by omega, h.zero] at e; omega
    · intro e; have := e.2 (by omega); omega

end CountEmb

/-- A window copy is balanced around each of its own elements (its arms around `φ j` are
the images of the arms of `j`, which have `reach p j` elements each). -/
theorem WinEmb.balanced_self {N p : Nat} {φ : Nat → Nat} (hφ : WinEmb N p φ) {j : Nat}
    (hj1 : 1 ≤ j) (hjp : j ≤ p) : Balanced N ((List.range' 1 p).map φ) (φ j) := by
  unfold Balanced
  rw [List.countP_map, List.countP_map]
  have L : (List.range' 1 p).countP
        ((fun x => decide (φ j - reach N (φ j) ≤ x ∧ x < φ j)) ∘ φ) =
      (List.range' 1 p).countP (fun y => decide (j - reach p j ≤ y ∧ y ≤ j - 1)) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    rw [hφ.left j y hj1 hjp hy.1 (by omega)]; omega
  have R : (List.range' 1 p).countP
        ((fun x => decide (φ j < x ∧ x ≤ φ j + reach N (φ j))) ∘ φ) =
      (List.range' 1 p).countP (fun y => decide (j + 1 ≤ y ∧ y ≤ j + reach p j)) := by
    apply List.countP_congr; intro y hy; rw [List.mem_range'_1] at hy
    simp only [Function.comp_apply, decide_eq_true_eq]
    rw [hφ.right j y hj1 hjp hy.1 (by omega)]; omega
  rw [L, R, countP_range'_interval, countP_range'_interval]
  unfold reach; omega

/-- **Copy criterion.**  For a strictly increasing `φ` with counting function `c`, the
image is a window copy of the `p`-strip iff it is balanced around each of its elements
iff the copy condition holds at every element. -/
theorem CountEmb.winEmb_iff {N p : Nat} {φ c : Nat → Nat} (h : CountEmb N p φ c) :
    (WinEmb N p φ ↔ ∀ j, 1 ≤ j → j ≤ p → Balanced N ((List.range' 1 p).map φ) (φ j)) ∧
      (WinEmb N p φ ↔ ∀ j, 1 ≤ j → j ≤ p → CopyAt N p φ c j) := by
  have e : (∀ j, 1 ≤ j → j ≤ p → Balanced N ((List.range' 1 p).map φ) (φ j)) ↔
      ∀ j, 1 ≤ j → j ≤ p → CopyAt N p φ c j :=
    forall_congr' fun j => imp_congr_right fun hj1 => imp_congr_right fun hjp =>
      h.balanced_iff hj1 hjp
  refine ⟨⟨fun hφ j hj1 hjp => hφ.balanced_self hj1 hjp, fun hb => h.winEmb (e.1 hb)⟩,
    ⟨fun hφ => e.1 fun j hj1 hjp => hφ.balanced_self hj1 hjp, h.winEmb⟩⟩

/-- A step `(S, m)` is valid iff `S ∪ {m}` is balanced around `m`. -/
theorem semiStep_iff_balanced {N m : Nat} {S : List Nat} (hnd : S.Nodup) :
    SemiStep N S m ↔ Balanced N (S ++ [m]) m := by
  unfold SemiStep Balanced
  rw [leftCount_eq hnd, rightCount_eq hnd, List.countP_append, List.countP_append]
  simp

/-- **Copy criterion, "valid last step" form.**  The image `X` of a strictly increasing
`φ` is a window copy iff every element `x ∈ X` is a valid last step of `X`: for every
ordering `S` of `X \ {x}`, the step `(S, x)` is valid. -/
theorem CountEmb.winEmb_iff_lastStep {N p : Nat} {φ c : Nat → Nat} (h : CountEmb N p φ c) :
    WinEmb N p φ ↔ ∀ j, 1 ≤ j → j ≤ p → ∀ S : List Nat,
      (S ++ [φ j]).Perm ((List.range' 1 p).map φ) → SemiStep N S (φ j) := by
  rw [h.winEmb_iff.1]
  refine forall_congr' fun j => imp_congr_right fun hj1 => imp_congr_right fun hjp => ?_
  have hndX : ((List.range' 1 p).map φ).Nodup :=
    nodup_map_of_injOn (List.nodup_range' ..) fun x hx y hy e => by
      rw [List.mem_range'_1] at hx hy
      have a := h.c_phi (j := x) (by omega); have b := h.c_phi (j := y) (by omega)
      rw [e] at a; omega
  constructor
  · intro hb S e
    have hndS : S.Nodup := (e.nodup_iff.2 hndX).sublist (List.sublist_append_left _ _)
    exact (semiStep_iff_balanced hndS).2 (hb.perm e.symm)
  · intro hs
    have hmem : φ j ∈ (List.range' 1 p).map φ :=
      List.mem_map.2 ⟨j, List.mem_range'_1.2 ⟨hj1, by omega⟩, rfl⟩
    have e : ((((List.range' 1 p).map φ).erase (φ j)) ++ [φ j]).Perm
        ((List.range' 1 p).map φ) :=
      (List.perm_append_comm.trans (List.perm_cons_erase hmem).symm)
    exact ((semiStep_iff_balanced (hndX.erase _)).1 (hs _ e)).perm e

/-! ## Beatty copies

For `1 ≤ p`, `0 ≤ h` and `h + 2p ≤ N + 1` (i.e. `g = -h` with `2p - 1 - N ≤ g ≤ 0`), the
Beatty set `X(N, p, -h) = {⌊(rN - h)/p⌋ : r = 1..p}` is a window copy of the `p`-strip
(`winEmb_beatty`).  Its counting function is `c(t) = ⌊(pt + p + h - 1)/N⌋`, which also
gives the extension `c~(t + N) = c~(t) + p` (`beattyCnt_add`), and the copy condition reads
`c(2x_r - 1) = 2r - 1`. -/

/-- The `r`-th element of the Beatty set `X(N, p, -h)`. -/
def beatty (N p h r : Nat) : Nat := (r * N - h) / p

/-- Counting function of `beatty N p h`. -/
def beattyCnt (N p h t : Nat) : Nat := (p * t + p + h - 1) / N

theorem beattyCnt_add {N p h : Nat} (hN : 0 < N) (hp : 1 ≤ p) (t : Nat) :
    beattyCnt N p h (t + N) = beattyCnt N p h t + p := by
  unfold beattyCnt
  rw [show p * (t + N) + p + h - 1 = (p * t + p + h - 1) + p * N by
    rw [Nat.mul_add]; omega, Nat.add_mul_div_right _ _ hN]

theorem countEmb_beatty {N p h : Nat} (hp : 1 ≤ p) (hh : h + 2 * p ≤ N + 1) :
    CountEmb N p (beatty N p h) (beattyCnt N p h) := by
  have hN : 0 < N := by omega
  refine ⟨fun y t hy => ?_, fun y hy => ?_, ?_, ?_⟩
  · unfold beatty beattyCnt
    have hyN : N ≤ y * N := Nat.le_mul_of_pos_left N hy
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by omega), Nat.le_div_iff_mul_le hN]
    have : (t.succ) * p = p * t + p := by rw [Nat.succ_mul, Nat.mul_comm]
    rw [this]; omega
  · unfold beatty
    have hyN : N ≤ y * N := Nat.le_mul_of_pos_left N hy
    have e : (y + 1) * N - h = (y * N - h + p) + (N - p) := by rw [Nat.succ_mul]; omega
    rw [e]
    calc (y * N - h) / p < (y * N - h) / p + 1 := Nat.lt_succ_self _
      _ = (y * N - h + p) / p := (Nat.add_div_right _ (by omega)).symm
      _ ≤ (y * N - h + p + (N - p)) / p := Nat.div_le_div_right (by omega)
  · unfold beattyCnt; rw [Nat.div_eq_of_lt (by omega)]
  · unfold beattyCnt
    rw [show p * N + p + h - 1 = (p + h - 1) + p * N by omega, Nat.add_mul_div_right _ _ hN,
      Nat.div_eq_of_lt (by omega)]
    simp

/-- The copy condition for Beatty sets: `c(2 x_r - 1) = 2r - 1`. -/
theorem beattyCnt_double {N p h r : Nat} (hp : 1 ≤ p) (hh : h + 2 * p ≤ N + 1) (hr : 1 ≤ r) :
    beattyCnt N p h (2 * beatty N p h r - 1) = 2 * r - 1 := by
  have hN : 0 < N := by omega
  have hrN : N ≤ r * N := Nat.le_mul_of_pos_left N hr
  unfold beattyCnt beatty
  generalize hm : (r * N - h) / p = m
  have d := Nat.div_add_mod (r * N - h) p
  have md := Nat.mod_lt (r * N - h) (show 0 < p by omega)
  rw [hm] at d
  have hm1 : 1 ≤ m := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0] at d; omega
  have e1 : p * (2 * m - 1) = 2 * (p * m) - p := by
    rw [Nat.mul_sub_one]; ring_nf
  have e2 : (2 * r - 1) * N = 2 * (r * N) - N := by
    rw [Nat.sub_mul, one_mul, Nat.mul_assoc]
  have e3 : (2 * r - 1 + 1) * N = 2 * (r * N) := by
    rw [Nat.sub_add_cancel (by omega), Nat.mul_assoc]
  have hpm : p ≤ p * m := Nat.le_mul_of_pos_right p hm1
  apply Nat.div_eq_of_lt_le
  · rw [e2, e1]; omega
  · rw [e3, e1]; omega

/-- **Beatty copies.**  For `1 ≤ p` and `h + 2p ≤ N + 1`, the Beatty set
`{⌊(rN - h)/p⌋ : r = 1..p}` is a window copy of the `p`-strip. -/
theorem winEmb_beatty {N p h : Nat} (hp : 1 ≤ p) (hh : h + 2 * p ≤ N + 1) :
    WinEmb N p (beatty N p h) := by
  have hN : 0 < N := by omega
  refine (countEmb_beatty hp hh).winEmb fun j hj1 _ => ⟨fun _ => beattyCnt_double hp hh hj1,
    fun h2 => ?_⟩
  have := beattyCnt_add (p := p) (h := h) hN hp (2 * beatty N p h j - N - 1)
  rw [show 2 * beatty N p h j - N - 1 + N = 2 * beatty N p h j - 1 by omega,
    beattyCnt_double hp hh hj1] at this
  omega

/-- **Weak split through a Beatty copy.**  If the complement of a Beatty copy can be
ordered semi-symmetrically from scratch, live prefixes of the `p`-strip stay live. -/
theorem extends_beatty {N p h : Nat} (hp : 1 ≤ p) (hh : h + 2 * p ≤ N + 1) {r : List Nat}
    (hr : Extends p r)
    (hY : 0 < g N (Finset.Icc 1 N \ (Finset.Icc 1 p).image (beatty N p h))) :
    Extends N (r.map (beatty N p h)) :=
  extends_winEmb (winEmb_beatty hp hh) hr hY

end Folds

