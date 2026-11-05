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

end Folds
