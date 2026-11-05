import Folds.Descents

/-!
# Admissible labellings: reduction to finitely many cases

Proofs on paper: `experiments/labelling2/PROOFS.txt`.

A labelling `c` of the panels `1..N` is *admissible* if the window inequality
`#{d ≤ r : c (m-d) ≤ c m} ≤ #{d ≤ r : c (m+d) < c m}` (`r = reach N m`) holds at every panel.
By `window_lemma` every level labelling of a semi-symmetric fold sequence (the run index, the
patience level, ...) is admissible.

Conjecture: an admissible labelling with `t` labels has `N ≤ 2^(t+1) - 2`.

## Results
* `leftWin_of_admissible`: the constraints of the left-half panels (`2m ≤ N+1`) do not depend
  on `N`, so an admissible labelling of `[1, N]` satisfies them on every prefix `[1, K]`,
  `K ≤ N`.  Hence the *left-half-only* problem is monotone in `N`.
* `bound_of_checks`: if the left-half-only problem with `t` labels is infeasible at `K`, and the
  full problem is infeasible for every `N ∈ [2^(t+1)-1, K)`, then the conjecture holds for `t`
  and EVERY `N`.  Feasibility is decided by a search over prefixes (`levelsFrom`, with an
  optimistic test `stepOK`); `pre_mem_levelsFrom` is its soundness, and `dead_of_children`
  splits a search into subtrees.
* The finite checks for `t ≤ 2` (`K = 3, 9`; full problem at `N = 7, 8`) are evaluated by the
  kernel: `admissible_le_two`, and for fold sequences `lds_exact_le_two`,
  `descents_exact_le_two`: `min (⌊log₂(N+1)⌋, 3) ≤ des a + 1`.
  (For `t = 3, 4, 5` the same reduction applies with `K = 21, 61, 160`; the checks were done
  by SAT, `experiments/labelling2`, but are too large for the kernel.)
-/

namespace Folds

/-! ## Admissibility -/

/-- The window inequality at panel `m`. -/
def WinIneq (N : Nat) (c : Nat → Nat) (m : Nat) : Prop :=
  (List.range' 1 (reach N m)).countP (fun d => decide (c (m - d) ≤ c m)) ≤
    (List.range' 1 (reach N m)).countP (fun d => decide (c (m + d) < c m))

instance (N : Nat) (c : Nat → Nat) (m : Nat) : Decidable (WinIneq N c m) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- `c` satisfies the window inequality at every panel of `[1, N]`. -/
def Admissible (N : Nat) (c : Nat → Nat) : Prop :=
  ∀ m, 1 ≤ m → m ≤ N → WinIneq N c m

/-- The constraints that the search checks: all panels with a nonempty window
(`left = true`: only those of the left half, `2m ≤ N+1`). -/
def checked (left : Bool) (N m : Nat) : Bool :=
  decide (0 < reach N m) && (!left || decide (2 * m ≤ N + 1))

/-- Monotonicity: the left-half constraints of a prefix `[1, K]` are constraints of `[1, N]`. -/
theorem leftWin_of_admissible {N K : Nat} {c : Nat → Nat} (hKN : K ≤ N) (h : Admissible N c)
    (m : Nat) (hm1 : 1 ≤ m) (hmK : m ≤ K) (hchk : checked true K m = true) :
    WinIneq K c m := by
  have h2 : 2 * m ≤ K + 1 := by
    simp only [checked, Bool.and_eq_true, decide_eq_true_eq, Bool.not_true, Bool.false_or] at hchk
    exact hchk.2
  have hr : reach K m = reach N m := by unfold reach; omega
  have := h m hm1 (by omega)
  unfold WinIneq at this ⊢
  rw [hr]; exact this

/-! ## The search -/

/-- Optimistic window inequality at `m` for a prefix `l` of length `k` (`l[i-1]` is the label
of panel `i`): the panels `m + d > k` are not known yet and count in favour of `m`. -/
def condO (N k : Nat) (l : List Nat) (m : Nat) : Bool :=
  decide ((List.range' 1 (reach N m)).countP
      (fun d => decide (l.getD (m - d - 1) 0 ≤ l.getD (m - 1) 0)) ≤
    (List.range' 1 (reach N m)).countP
      (fun d => decide (k < m + d) || decide (l.getD (m + d - 1) 0 < l.getD (m - 1) 0)))

/-- The checked constraints whose window reaches panel `k` hold optimistically for `l`. -/
def stepOK (left : Bool) (N k : Nat) (l : List Nat) : Bool :=
  (List.range' 1 k).all
    (fun m => !(decide (k ≤ m + reach N m) && checked left N m) || condO N k l m)

/-- Extend every prefix of length `k` in `L` by one label `< t`, keeping the good ones. -/
def extend (left : Bool) (N t k : Nat) (L : List (List Nat)) : List (List Nat) :=
  L.flatMap (fun l => (List.range t).flatMap
    (fun v => if stepOK left N (k + 1) (l ++ [v]) then [l ++ [v]] else []))

/-- From the prefixes `L` of length `k`: the surviving prefixes of length `k + j`. -/
def levelsFrom (left : Bool) (N t : Nat) : List (List Nat) → Nat → Nat → List (List Nat)
  | L, _, 0 => L
  | L, k, j + 1 => levelsFrom left N t (extend left N t k L) (k + 1) j

/-- No extension of the prefix `q` to a labelling of `[1, N]` survives the search. -/
abbrev Dead (left : Bool) (N t : Nat) (q : List Nat) : Prop :=
  (levelsFrom left N t [q] q.length (N - q.length)).isEmpty = true

/-- The prefix `[c 1, ..., c k]`. -/
def pre (c : Nat → Nat) (k : Nat) : List Nat := (List.range' 1 k).map c

theorem pre_succ (c : Nat → Nat) (k : Nat) : pre c (k + 1) = pre c k ++ [c (k + 1)] := by
  unfold pre
  rw [← List.range'_append_1 (s := 1) (m := k) (n := 1)]
  simp [Nat.add_comm]

theorem getD_pre (c : Nat → Nat) {k i : Nat} (hi1 : 1 ≤ i) (hik : i ≤ k) :
    (pre c k).getD (i - 1) 0 = c i := by
  unfold pre
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range' (by omega)]
  simp only [Option.map_some, Option.getD_some]
  congr 1; omega

/-- The optimistic test is passed by the prefixes of a labelling satisfying (WI) at `m`. -/
theorem condO_pre (N : Nat) (c : Nat → Nat) {k m : Nat} (hm1 : 1 ≤ m) (hmk : m ≤ k)
    (h : WinIneq N c m) : condO N k (pre c k) m = true := by
  unfold condO
  rw [decide_eq_true_iff]
  unfold WinIneq at h
  have hr : reach N m ≤ m - 1 := by unfold reach; omega
  have hcm : (pre c k).getD (m - 1) 0 = c m := getD_pre c hm1 hmk
  rw [hcm]
  have h1 : (List.range' 1 (reach N m)).countP
        (fun d => decide ((pre c k).getD (m - d - 1) 0 ≤ c m)) =
      (List.range' 1 (reach N m)).countP (fun d => decide (c (m - d) ≤ c m)) := by
    apply List.countP_congr
    intro d hd
    rw [List.mem_range'_1] at hd
    rw [show m - d - 1 = (m - d) - 1 by omega, getD_pre c (by omega) (by omega)]
  rw [h1]
  refine le_trans h (List.countP_mono_left ?_)
  intro d hd hlt
  rw [List.mem_range'_1] at hd
  simp only [decide_eq_true_eq] at hlt
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  by_cases hk : k < m + d
  · exact Or.inl hk
  · right
    rw [show m + d - 1 = (m + d) - 1 by omega, getD_pre c (by omega) (by omega)]
    exact hlt

/-- **Soundness of the search.**  The prefixes of a labelling with labels `< t` that satisfies
all checked constraints survive. -/
theorem pre_mem_levelsFrom (left : Bool) (N t : Nat) (c : Nat → Nat)
    (ht : ∀ x, 1 ≤ x → x ≤ N → c x < t)
    (hc : ∀ m, 1 ≤ m → m ≤ N → checked left N m = true → WinIneq N c m) :
    ∀ j L k, pre c k ∈ L → k + j ≤ N → pre c (k + j) ∈ levelsFrom left N t L k j := by
  intro j
  induction j with
  | zero => intro L k hL _; simpa [levelsFrom] using hL
  | succ j ih =>
    intro L k hL hk
    simp only [levelsFrom]
    rw [show k + (j + 1) = (k + 1) + j by omega]
    refine ih _ _ ?_ (by omega)
    simp only [extend, List.mem_flatMap, List.mem_range]
    refine ⟨pre c k, hL, c (k + 1), ht (k + 1) (by omega) (by omega), ?_⟩
    rw [← pre_succ]
    have hok : stepOK left N (k + 1) (pre c (k + 1)) = true := by
      unfold stepOK
      rw [List.all_eq_true]
      intro m hm
      rw [List.mem_range'_1] at hm
      by_cases hg : (decide (k + 1 ≤ m + reach N m) && checked left N m) = true
      · rw [Bool.and_eq_true] at hg
        rw [Bool.or_eq_true]; right
        exact condO_pre N c hm.1 (by omega) (hc m hm.1 (by omega) hg.2)
      · simp only [Bool.not_eq_true] at hg
        simp [hg]
    simp [hok]

theorem levelsFrom_nil (left : Bool) (N t : Nat) : ∀ j k, levelsFrom left N t [] k j = [] := by
  intro j; induction j with
  | zero => intro k; rfl
  | succ j ih => intro k; simp only [levelsFrom, extend, List.flatMap_nil]; exact ih _

theorem levelsFrom_append (left : Bool) (N t : Nat) :
    ∀ j A B k, levelsFrom left N t (A ++ B) k j =
      levelsFrom left N t A k j ++ levelsFrom left N t B k j := by
  intro j; induction j with
  | zero => intro A B k; rfl
  | succ j ih => intro A B k; simp only [levelsFrom, extend, List.flatMap_append]; exact ih _ _ _

theorem levelsFrom_flatMap (left : Bool) (N t : Nat) (f : Nat → List (List Nat)) (j k : Nat) :
    ∀ xs : List Nat, levelsFrom left N t (xs.flatMap f) k j =
      xs.flatMap (fun x => levelsFrom left N t (f x) k j) := by
  intro xs; induction xs with
  | nil => simp [levelsFrom_nil]
  | cons x xs ih => simp only [List.flatMap_cons]; rw [levelsFrom_append, ih]

/-- A prefix is dead if each of its extensions either fails the test or is dead. -/
theorem dead_of_children {left : Bool} {N t : Nat} (q : List Nat) (hq : q.length < N)
    (h : ∀ v, v < t → stepOK left N (q.length + 1) (q ++ [v]) = false ∨
      Dead left N t (q ++ [v])) : Dead left N t q := by
  unfold Dead
  rw [show N - q.length = (N - (q.length + 1)) + 1 by omega]
  simp only [levelsFrom, extend, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [levelsFrom_flatMap, List.isEmpty_iff, List.flatMap_eq_nil_iff]
  intro v hv
  rw [List.mem_range] at hv
  by_cases hs : stepOK left N (q.length + 1) (q ++ [v]) = true
  · simp only [hs, ↓reduceIte]
    rcases h v hv with h1 | h1
    · rw [hs] at h1; exact absurd h1 (by decide)
    · unfold Dead at h1
      rw [List.length_append, List.length_singleton] at h1
      exact List.isEmpty_iff.1 h1
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, levelsFrom_nil]

/-- If the search dies out, no labelling with labels `< t` satisfies the checked constraints. -/
theorem no_labelling_of_dead (left : Bool) (N t : Nat) (hN : Dead left N t [])
    (c : Nat → Nat) (ht : ∀ x, 1 ≤ x → x ≤ N → c x < t)
    (hc : ∀ m, 1 ≤ m → m ≤ N → checked left N m = true → WinIneq N c m) : False := by
  have := pre_mem_levelsFrom left N t c ht hc N [[]] 0 (by simp [pre]) (by omega)
  unfold Dead at hN
  simp only [List.length_nil, Nat.sub_zero] at hN
  rw [List.isEmpty_iff] at hN
  rw [Nat.zero_add, hN] at this
  simp at this

/-- **Reduction to finitely many cases.**  If the left-half-only search dies out at `K` and the
full search dies out for every `N ∈ [2^(t+1) - 1, K)`, then every admissible labelling with
labels `< t` has `N ≤ 2^(t+1) - 2`. -/
theorem bound_of_checks (t K : Nat) (hK : Dead true K t [])
    (hfull : ∀ N, 2 ^ (t + 1) - 1 ≤ N → N < K → Dead false N t [])
    {N : Nat} {c : Nat → Nat} (hadm : Admissible N c) (ht : ∀ x, 1 ≤ x → x ≤ N → c x < t) :
    N ≤ 2 ^ (t + 1) - 2 := by
  by_contra hN
  rcases Nat.lt_or_ge N K with hNK | hKN
  · exact no_labelling_of_dead false N t (hfull N (by omega) hNK) c ht
      (fun m hm1 hmN _ => hadm m hm1 hmN)
  · exact no_labelling_of_dead true K t hK c (fun x hx1 hxK => ht x hx1 (by omega))
      (fun m hm1 hmK hchk => leftWin_of_admissible hKN hadm m hm1 hmK hchk)

/-! ## The finite checks for `t ≤ 2` (kernel evaluation) -/

theorem deadL3_root : Dead true 3 1 [] := by decide +kernel

theorem deadL9_root : Dead true 9 2 [] := by decide +kernel

theorem deadF7_root : Dead false 7 2 [] := by decide +kernel

theorem deadF8_root : Dead false 8 2 [] := by decide +kernel

/-- **The conjecture for at most two labels.**  An admissible labelling with labels `< t`,
`t ≤ 2`, has `N ≤ 2^(t+1) - 2`. -/
theorem admissible_le_two {N t : Nat} {c : Nat → Nat} (htt : t ≤ 2) (hadm : Admissible N c)
    (ht : ∀ x, 1 ≤ x → x ≤ N → c x < t) : N ≤ 2 ^ (t + 1) - 2 := by
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with h | h | h <;> subst h
  · by_contra hN
    have := ht 1 le_rfl (by omega); omega
  · exact bound_of_checks 1 3 deadL3_root (fun N h1 h2 => by norm_num at h1; omega) hadm ht
  · refine bound_of_checks 2 9 deadL9_root (fun N h1 h2 => ?_) hadm ht
    norm_num at h1
    rcases (show N = 7 ∨ N = 8 by omega) with rfl | rfl
    · exact deadF7_root
    · exact deadF8_root

/-! ## Fold sequences -/

section sequences

variable {N : Nat} {a : List Nat}

/-- Every level labelling of a semi-symmetric fold sequence is admissible. -/
theorem admissible_of_labelling (hf : IsFoldSeq N a) (h : SemiSymmetric N a) (c : Nat → Nat)
    (hc : ∀ i j (hij : i < j) (hj : j < a.length),
      a[j] < a[i]'(Nat.lt_trans hij hj) → c a[i] < c a[j]) :
    Admissible N c := by
  intro m hm1 hmN
  have hlev : LevelLabelling N (fun x => a.idxOf x) c := by
    intro x y hx1 hxN hy1 hyN hτ hyx
    have hya : y ∈ a := (mem_range'_of_perm hf).2 ⟨hy1, hyN⟩
    have hiy : a.idxOf y < a.length := List.idxOf_lt_length_of_mem hya
    have := hc (a.idxOf x) (a.idxOf y) hτ hiy
    simp only [List.getElem_idxOf] at this
    exact this hyx
  have := window_lemma (τ := fun x => a.idxOf x) (c := c) (idxOf_injOn hf)
    (timeBalanced_of_semiSymmetric hf h) hlev hm1 hmN
  unfold WinIneq
  rw [countP_range'_eq_card, countP_range'_eq_card]
  simpa only [decide_eq_true_eq] using this

/-- A level labelling with at most two values forces `N ≤ 2^(t+1) - 2`. -/
theorem labelling_le_two (hf : IsFoldSeq N a) (h : SemiSymmetric N a) (c : Nat → Nat)
    {t : Nat} (htt : t ≤ 2)
    (hc : ∀ i j (hij : i < j) (hj : j < a.length),
      a[j] < a[i]'(Nat.lt_trans hij hj) → c a[i] < c a[j])
    (ht : ∀ x ∈ a, c x < t) : N ≤ 2 ^ (t + 1) - 2 :=
  admissible_le_two htt (admissible_of_labelling hf h c hc)
    (fun x hx1 hxN => ht x ((mem_range'_of_perm hf).2 ⟨hx1, hxN⟩))

/-- `N ≤ 2^(t+1) - 2` for `t ≤ 2` rewritten with logarithms. -/
theorem min_log_le {N t : Nat} (H : t ≤ 2 → N ≤ 2 ^ (t + 1) - 2) :
    min (Nat.log 2 (N + 1)) 3 ≤ t := by
  rcases Nat.lt_or_ge t 3 with ht | ht
  · have hN := H (by omega)
    have hlt : N + 1 < 2 ^ (t + 1) := by
      have : 2 ≤ 2 ^ (t + 1) := Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num)
      omega
    have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hlt
    omega
  · omega

/-- **Exact bound for at most two levels.**  If `c` increases strictly along inversions of a
semi-symmetric fold sequence and takes values `< t`, then `min(⌊log₂(N+1)⌋, 3) ≤ t`.  With the
patience level, `t = LDS(a)`: `LDS(a) ≥ ⌊log₂(N+1)⌋` for `N ≤ 14`, and `LDS(a) ≥ 3` for
`N ≥ 7`. -/
theorem lds_exact_le_two (hf : IsFoldSeq N a) (h : SemiSymmetric N a) (c : Nat → Nat)
    {t : Nat}
    (hc : ∀ i j (hij : i < j) (hj : j < a.length),
      a[j] < a[i]'(Nat.lt_trans hij hj) → c a[i] < c a[j])
    (ht : ∀ x ∈ a, c x < t) : min (Nat.log 2 (N + 1)) 3 ≤ t :=
  min_log_le (fun htt => labelling_le_two hf h c htt hc ht)

/-- **Descents.**  A semi-symmetric fold sequence has `des a + 1 ≥ min(⌊log₂(N+1)⌋, 3)`:
`des a ≥ ⌊log₂(N+1)⌋ - 1` for `N ≤ 14`, and `des a ≥ 2` for every `N ≥ 7`. -/
theorem descents_exact_le_two (hf : IsFoldSeq N a) (h : SemiSymmetric N a) :
    min (Nat.log 2 (N + 1)) 3 ≤ des a + 1 := by
  refine lds_exact_le_two hf h (fun x => desBefore a (a.idxOf x)) ?_ ?_
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
