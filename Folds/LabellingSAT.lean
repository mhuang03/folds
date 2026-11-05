import Folds.Labelling

/-!
# Admissible labellings: the finite checks by verified LRAT certificates

`bound_of_checks` (`Folds/Labelling.lean`) reduces the labelling conjecture for a fixed number
`t` of labels to finitely many infeasibility checks.  The prefix search of `Labelling.lean` is
too expensive for the kernel at `t ≥ 3`.  Here the same checks are certified by SAT-solver
proofs (LRAT, i.e. reverse unit propagation with explicit hints), which are replayed by a small
checker written for kernel evaluation (`decide +kernel`): no `native_decide`, no
`Lean.ofReduceBool`.

## The checker (`Cert.check`)
* Literals are natural numbers: `2 * x` is the variable `x`, `2 * x + 1` its negation.
* A partial assignment is a natural number used as a bitmask (bit `l` set: literal `l` true);
  the kernel evaluates the bit operations with GMP.
* The clause database is a binary trie keyed by the clause id (`Trie`).
* Every proof step adds a clause `C` with hints `h₁, …, hₖ`: starting from the negation of `C`,
  every hint clause must become unit (its literal is set) and the last one must be falsified.
  Deletions are not needed.  The step that adds the empty clause ends the proof.
* Soundness (`checkSteps_sound`): a model of the database satisfies every added clause, hence no
  model exists once the empty clause is added.

## The encoding (`CTag`, `gen`)
The CNF is not generated in Lean.  Each clause of the certificate's CNF carries a *tag* naming
the rule that produced it (`CTag`), and the kernel recomputes the clause of the tag (`gen`) in
terms of *meaningful variables* (`VarTag`), and compares it with the certificate's clause through
the certificate's variable table.  Each rule is sound for every labelling
(`gen_sound`): with `y m u = [c m < u]` and the totalizer outputs
`o m v lo hi i = [i ≤ #{p ∈ [lo, hi) : input p of the window sum of (m, v)}]`, every generated
clause holds.  Hence only the clauses the SAT proof uses need to be checked, and the variable
table maps the compact solver variables to their meaning.

The window inequality at `m` with `c m = v` reads `#{x ∈ L(m) : c x ≤ v} + #{x ∈ R(m) : c x ≥ v}
≤ r(m)`; it is the clause `win m v`, whose sum is the root of a totalizer over the `2 r` inputs.

## Results
`no_labelling_of_cert` (soundness of a certificate) and `bound_of_certs` (the analogue of
`bound_of_checks`).  The certificates themselves are in `Folds/LabellingSAT3.lean` (`t = 3`),
...; they are produced by `experiments/labelling_lrat/gen.py`.
-/

namespace Folds
namespace LSAT

/-! ## A binary trie keyed by natural numbers -/

/-- Binary trie: the root holds key `0`, key `k ≥ 1` goes left (key `k / 2`) if `k` is odd and
right (key `k / 2 - 1`) if `k` is even. -/
inductive Trie (α : Type) where
  | leaf : Trie α
  | node : Option α → Trie α → Trie α → Trie α

namespace Trie

variable {α : Type}

/-- Lookup with depth bound `d`. -/
def get : Nat → Trie α → Nat → Option α
  | _, leaf, _ => none
  | 0, node _ _ _, _ => none
  | d + 1, node v l r, k =>
    if k = 0 then v else if k % 2 = 1 then get d l (k / 2) else get d r (k / 2 - 1)

/-- Insertion with depth bound `d` (does nothing beyond the bound). -/
def insert : Nat → Trie α → Nat → α → Trie α
  | 0, t, _, _ => t
  | d + 1, leaf, k, a =>
    if k = 0 then node (some a) leaf leaf
    else if k % 2 = 1 then node none (insert d leaf (k / 2) a) leaf
    else node none leaf (insert d leaf (k / 2 - 1) a)
  | d + 1, node v l r, k, a =>
    if k = 0 then node (some a) l r
    else if k % 2 = 1 then node v (insert d l (k / 2) a) r
    else node v l (insert d r (k / 2 - 1) a)

theorem get_leaf (d k : Nat) : get d (leaf : Trie α) k = none := by
  cases d <;> rfl

/-- What is found after an insertion was inserted or was there before. -/
theorem get_insert : ∀ (d : Nat) (t : Trie α) (k k' : Nat) (a c : α),
    get d (insert d t k a) k' = some c → c = a ∨ get d t k' = some c := by
  intro d
  induction d with
  | zero => intro t k k' a c h; exact Or.inr h
  | succ d ih =>
    intro t k k' a c h
    cases t with
    | leaf =>
      simp only [insert] at h
      split_ifs at h <;> simp only [get] at h <;> split_ifs at h <;>
        first
        | (simp_all; done)
        | (rcases ih _ _ _ _ _ h with h5 | h5 <;> simp_all [get_leaf])
    | node v l r =>
      simp only [insert] at h
      split_ifs at h <;> simp only [get] at h <;> split_ifs at h <;>
        first
        | (simp_all [get]; done)
        | (rcases ih _ _ _ _ _ h with h5 | h5 <;> simp_all [get])

/-- The trie with keys `k, k+1, ...` holding the elements of a list. -/
def ofList (d : Nat) : Trie α → Nat → List α → Trie α
  | t, _, [] => t
  | t, k, a :: as => ofList d (insert d t k a) (k + 1) as

/-- An invariant of the stored values is preserved by `ofList`. -/
theorem get_ofList (d : Nat) (P : α → Prop) :
    ∀ (as : List α) (t : Trie α) (k : Nat), (∀ a ∈ as, P a) →
      (∀ k' c, get d t k' = some c → P c) →
      ∀ k' c, get d (ofList d t k as) k' = some c → P c := by
  intro as
  induction as with
  | nil => intro t k _ ht; exact ht
  | cons a as ih =>
    intro t k has ht
    refine ih _ _ (fun b hb => has b (List.mem_cons_of_mem _ hb)) ?_
    intro k' c hc
    rcases get_insert d t k k' a c hc with h | h
    · subst h; exact has _ List.mem_cons_self
    · exact ht k' c h

end Trie

/-- Depth bound of the tries (keys below `2^64`). -/
def D : Nat := 64

/-! ## Literals, assignments, reverse unit propagation -/

/-- The value of the literal `l` (`2x`: variable `x`, `2x+1`: its negation). -/
def litVal (σ : Nat → Bool) (l : Nat) : Bool :=
  if l % 2 = 0 then σ (l / 2) else !σ (l / 2)

/-- The negated literal. -/
def neg (l : Nat) : Nat := if l % 2 = 0 then l + 1 else l - 1

theorem litVal_neg (σ : Nat → Bool) (l : Nat) : litVal σ (neg l) = !litVal σ l := by
  unfold litVal neg
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) % 2 ≠ 0 := by omega
    have h2 : (l + 1) / 2 = l / 2 := by omega
    simp [h, h1, h2]
  · have h1 : (l - 1) % 2 = 0 := by omega
    have h2 : (l - 1) / 2 = l / 2 := by omega
    simp [h, h1, h2]

/-- Set the literal `l` in the bitmask `A`. -/
def setLit (A l : Nat) : Nat := A ||| 2 ^ l

/-- `l` is falsified by `A`. -/
def isFalse (A l : Nat) : Bool := A.testBit (neg l)

theorem testBit_setLit (A l k : Nat) : (setLit A l).testBit k = (A.testBit k || decide (l = k)) := by
  unfold setLit
  rw [Nat.testBit_or, Nat.testBit_two_pow]

/-- All literals set in `A` are true under `σ`. -/
def Sound (σ : Nat → Bool) (A : Nat) : Prop := ∀ l, A.testBit l = true → litVal σ l = true

theorem sound_setLit {σ : Nat → Bool} {A l : Nat} (hA : Sound σ A) (hl : litVal σ l = true) :
    Sound σ (setLit A l) := by
  intro k hk
  rw [testBit_setLit, Bool.or_eq_true, decide_eq_true_eq] at hk
  rcases hk with hk | rfl
  · exact hA k hk
  · exact hl

/-- The assignment falsifying the clause `C`. -/
def initA (C : List Nat) : Nat := C.foldl (fun A l => setLit A (neg l)) 0

theorem sound_initA (σ : Nat → Bool) (C : List Nat) (hC : ∀ l ∈ C, litVal σ l = false) :
    Sound σ (initA C) := by
  unfold initA
  suffices ∀ A, Sound σ A → Sound σ (C.foldl (fun A l => setLit A (neg l)) A) from
    this 0 (fun l h => by simp at h)
  induction C with
  | nil => intro A h; exact h
  | cons l C ih =>
    intro A hA
    refine ih (fun l' hl' => hC l' (List.mem_cons_of_mem _ hl')) _ (sound_setLit hA ?_)
    rw [litVal_neg, hC l List.mem_cons_self]; rfl

/-- Clause database: all stored clauses. -/
abbrev DB := Trie (List Nat)

/-- `σ` satisfies every clause of the database. -/
def DBSat (σ : Nat → Bool) (db : DB) : Prop :=
  ∀ k c, db.get D k = some c → ∃ l ∈ c, litVal σ l = true

/-- Unit propagation along the hints, from the assignment `A`: `true` iff a conflict is
reached, every hint before it being unit. -/
def rup (db : DB) : Nat → List Nat → Bool
  | _, [] => false
  | A, h :: hs =>
    match db.get D h with
    | none => false
    | some c =>
      match c.filter (fun l => !isFalse A l) with
      | [] => true
      | [u] => rup db (setLit A u) hs
      | _ :: _ :: _ => false

theorem rup_sound (σ : Nat → Bool) (db : DB) (hdb : DBSat σ db) :
    ∀ (hs : List Nat) (A : Nat), Sound σ A → rup db A hs = true → False := by
  intro hs
  induction hs with
  | nil => intro A _ h; simp [rup] at h
  | cons h hs ih =>
    intro A hA hr
    simp only [rup] at hr
    split at hr
    · cases hr
    · next c hc =>
      obtain ⟨l, hl, hlv⟩ := hdb h c hc
      -- `l` is not falsified
      have hnf : isFalse A l = false := by
        cases hf : isFalse A l
        · rfl
        · have := hA _ hf
          rw [litVal_neg, hlv] at this; cases this
      have hmem : l ∈ c.filter (fun l => !isFalse A l) := by
        rw [List.mem_filter]; exact ⟨hl, by simp [hnf]⟩
      split at hr
      · next he => rw [he] at hmem; simp at hmem
      · next u he =>
        rw [he, List.mem_singleton] at hmem
        subst hmem
        exact ih _ (sound_setLit hA hlv) hr
      · cases hr

/-- A proof step adds `C` (the clause, then the hints); ids are consecutive from `next`. -/
def checkSteps : DB → Nat → List (List Nat × List Nat) → Bool
  | _, _, [] => false
  | db, next, (C, hs) :: ss =>
    rup db (initA C) hs && (C.isEmpty || checkSteps (db.insert D next C) (next + 1) ss)

theorem rup_clause (σ : Nat → Bool) (db : DB) (hdb : DBSat σ db) (C hs : List Nat)
    (h : rup db (initA C) hs = true) : ∃ l ∈ C, litVal σ l = true := by
  by_contra hn
  push Not at hn
  exact rup_sound σ db hdb hs _ (sound_initA σ C (fun l hl => by simpa using hn l hl)) h

theorem checkSteps_sound (σ : Nat → Bool) :
    ∀ (ss : List (List Nat × List Nat)) (db : DB) (next : Nat), DBSat σ db →
      checkSteps db next ss = true → False := by
  intro ss
  induction ss with
  | nil => intro db next _ h; simp [checkSteps] at h
  | cons s ss ih =>
    intro db next hdb h
    obtain ⟨C, hs⟩ := s
    simp only [checkSteps, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨l, hl, hlv⟩ := rup_clause σ db hdb C hs h.1
    rcases h.2 with h2 | h2
    · rw [List.isEmpty_iff] at h2; subst h2; simp at hl
    · refine ih _ _ ?_ h2
      intro k c hc
      rcases Trie.get_insert D db next k C c hc with h3 | h3
      · subst h3; exact ⟨l, hl, hlv⟩
      · exact hdb k c h3

/-! ## The encoding -/

/-- Meaningful variables: `y m u = [c m < u]`, and the totalizer outputs
`o m v lo hi i = [i ≤ #{p ∈ [lo, hi) : input p of (m, v)}]`. -/
inductive VarTag where
  | none : VarTag
  | y (m u : Nat) : VarTag
  | o (m v lo hi i : Nat) : VarTag

/-- Boolean equality of variable tags. -/
def VarTag.beq : VarTag → VarTag → Bool
  | .none, .none => true
  | .y m u, .y m' u' => m == m' && u == u'
  | .o m v lo hi i, .o m' v' lo' hi' i' =>
    m == m' && v == v' && lo == lo' && hi == hi' && i == i'
  | _, _ => false

theorem VarTag.eq_of_beq : ∀ {a b : VarTag}, a.beq b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [VarTag.beq]

/-- Literals over meaningful variables. -/
abbrev TLit := VarTag × Bool

/-- Input `p` of the window sum of `(m, v)`: for `p < r`, `[c (m - 1 - p) ≤ v]` (left window),
for `p ≥ r`, `[c (m + 1 + (p - r)) ≥ v]` (right window). -/
def inLit (N m v p : Nat) : TLit :=
  if p < reach N m then (.y (m - 1 - p) (v + 1), true) else (.y (m + 1 + (p - reach N m)) v, false)

/-- Totalizer output: a leaf is its input. -/
def oLit (N m v lo hi i : Nat) : TLit :=
  if hi = lo + 1 ∧ i = 1 then inLit N m v lo else (.o m v lo hi i, true)

/-- The negated literal. -/
def tneg (x : TLit) : TLit := (x.1, !x.2)

/-- Clause tags. -/
inductive CTag where
  /-- `¬ [c m < 0]` -/
  | lo (m : Nat) : CTag
  /-- `[c m < t]` -/
  | hi (m : Nat) : CTag
  /-- `[c m < u] → [c m < u + 1]` -/
  | ord (m u : Nat) : CTag
  /-- totalizer: `out(lo, mid, i) ∧ out(mid, hi, j) → out(lo, hi, k)` (`k ≤ i + j`) -/
  | tot (m v lo mid hi i j k : Nat) : CTag
  /-- the window inequality at `m` when `c m = v`: the root output `r + 1` is false -/
  | win (m v : Nat) : CTag

/-- The clause of a tag. -/
def gen (N t : Nat) : CTag → List TLit
  | .lo m => [(.y m 0, false)]
  | .hi m => [(.y m t, true)]
  | .ord m u => [(.y m u, false), (.y m (u + 1), true)]
  | .tot m v lo mid hi i j k =>
    (if i = 0 then [] else [tneg (oLit N m v lo mid i)]) ++
      (if j = 0 then [] else [tneg (oLit N m v mid hi j)]) ++ [oLit N m v lo hi k]
  | .win m v =>
    [(.y m (v + 1), false), (.y m v, true), tneg (oLit N m v 0 (2 * reach N m) (reach N m + 1))]

/-- The side conditions of a tag. -/
def valid (left : Bool) (N : Nat) : CTag → Bool
  | .lo _ => true
  | .hi m => decide (1 ≤ m) && decide (m ≤ N)
  | .ord _ _ => true
  | .tot _ _ lo mid hi i j k => decide (lo ≤ mid) && decide (mid ≤ hi) && decide (k ≤ i + j)
  | .win m _ => decide (1 ≤ m) && decide (m ≤ N) && checked left N m

section semantics

variable (N : Nat) (c : Nat → Nat)

/-- The meaning of a variable `y` under the labelling `c`. -/
def semY : VarTag → Bool
  | .y m u => decide (c m < u)
  | _ => false

/-- Number of true inputs of `(m, v)` in `[lo, hi)`. -/
def cnt (m v lo hi : Nat) : Nat :=
  (List.range' lo (hi - lo)).countP (fun p => semY c (inLit N m v p).1 == (inLit N m v p).2)

/-- The meaning of a variable under the labelling `c`. -/
def sem : VarTag → Bool
  | .none => false
  | .y m u => decide (c m < u)
  | .o m v lo hi i => decide (i ≤ cnt N c m v lo hi)

/-- The value of a literal. -/
def tsem (x : TLit) : Bool := sem N c x.1 == x.2

end semantics

/-! ## Soundness of the encoding -/

section soundness

variable {N t : Nat} {c : Nat → Nat}

theorem tsem_tneg (x : TLit) : tsem N c (tneg x) = !tsem N c x := by
  unfold tsem tneg
  cases sem N c x.1 <;> cases x.2 <;> rfl

theorem tsem_inLit (m v p : Nat) :
    tsem N c (inLit N m v p) = (semY c (inLit N m v p).1 == (inLit N m v p).2) := by
  unfold tsem inLit
  split <;> rfl

theorem cnt_split {m v lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    cnt N c m v lo hi = cnt N c m v lo mid + cnt N c m v mid hi := by
  unfold cnt
  rw [← List.countP_append]
  congr 1
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega, ← List.range'_append_1]
  congr 2; omega

theorem tsem_oLit (m v lo hi i : Nat) :
    tsem N c (oLit N m v lo hi i) = decide (i ≤ cnt N c m v lo hi) := by
  unfold oLit
  split
  · next h =>
    obtain ⟨rfl, rfl⟩ := h
    rw [tsem_inLit]
    simp only [cnt, Nat.add_sub_cancel_left, List.range'_one, List.countP_singleton]
    split <;> simp_all
  · simp [tsem, sem]

/-- The window sum of `(m, v)` is at most `r` when `c m = v`. -/
theorem cnt_window {m : Nat} (hr : 0 < reach N m) (hw : WinIneq N c m) :
    cnt N c m (c m) 0 (2 * reach N m) ≤ reach N m := by
  set r := reach N m with hrdef
  have hm : r ≤ m - 1 := by rw [hrdef]; unfold reach; omega
  rw [cnt_split (mid := r) (by omega) (by omega)]
  have hA : cnt N c m (c m) 0 r =
      (List.range' 1 r).countP (fun d => decide (c (m - d) ≤ c m)) := by
    unfold cnt
    rw [show (List.range' 1 r) = (List.range' 0 r).map (1 + ·) by
      rw [List.map_add_range']]
    rw [List.countP_map]
    apply List.countP_congr
    intro p hp
    rw [List.mem_range'_1] at hp
    simp only [inLit, ← hrdef, show p < r by omega, ↓reduceIte, semY, Function.comp,
      beq_true, decide_eq_true_eq]
    rw [show m - 1 - p = m - (1 + p) by omega]
    omega
  have hB : cnt N c m (c m) r (2 * r) =
      (List.range' 1 r).countP (fun d => !decide (c (m + d) < c m)) := by
    unfold cnt
    rw [show 2 * r - r = r by omega,
      show (List.range' r r) = (List.range' 1 r).map ((r - 1) + ·) by
      rw [List.map_add_range']; congr 1; omega]
    rw [List.countP_map]
    apply List.countP_congr
    intro d hd
    rw [List.mem_range'_1] at hd
    simp only [inLit, ← hrdef, show ¬ (r - 1 + d < r) by omega, ↓reduceIte, semY,
      Function.comp]
    rw [show m + 1 + (r - 1 + d - r) = m + d by omega]
    cases decide (c (m + d) < c m) <;> simp
  rw [hA, hB]
  unfold WinIneq at hw
  rw [← hrdef] at hw
  have htot := List.length_eq_countP_add_countP (fun d => decide (c (m + d) < c m))
    (l := List.range' 1 r)
  rw [List.length_range'] at htot
  have : (List.range' 1 r).countP (fun d => !decide (c (m + d) < c m)) =
      (List.range' 1 r).countP (fun d => ¬ (decide (c (m + d) < c m) = true)) := by
    apply List.countP_congr; intro d _; simp
  omega

/-- **Soundness of the encoding.**  Every generated clause holds for a labelling with labels
`< t` that satisfies the checked window inequalities. -/
theorem gen_sound (left : Bool) (tag : CTag) (hv : valid left N tag = true)
    (ht : ∀ x, 1 ≤ x → x ≤ N → c x < t)
    (hc : ∀ m, 1 ≤ m → m ≤ N → checked left N m = true → WinIneq N c m) :
    ∃ x ∈ gen N t tag, tsem N c x = true := by
  cases tag with
  | lo m => exact ⟨_, List.mem_singleton_self _, by simp [tsem, sem]⟩
  | hi m =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact ⟨_, List.mem_singleton_self _, by simp [tsem, sem, ht m hv.1 hv.2]⟩
  | ord m u =>
    by_cases h : c m < u
    · exact ⟨(.y m (u + 1), true), by simp [gen], by simp [tsem, sem]; omega⟩
    · exact ⟨(.y m u, false), by simp [gen], by simp [tsem, sem]; omega⟩
  | tot m v lo mid hi i j k =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨h1, h2⟩, h3⟩ := hv
    by_cases hi' : i ≠ 0 ∧ tsem N c (oLit N m v lo mid i) = false
    · refine ⟨tneg (oLit N m v lo mid i), by simp [gen, hi'.1], ?_⟩
      rw [tsem_tneg, hi'.2]; rfl
    by_cases hj' : j ≠ 0 ∧ tsem N c (oLit N m v mid hi j) = false
    · refine ⟨tneg (oLit N m v mid hi j), by simp [gen, hj'.1], ?_⟩
      rw [tsem_tneg, hj'.2]; rfl
    refine ⟨oLit N m v lo hi k, by simp [gen], ?_⟩
    rw [tsem_oLit, decide_eq_true_eq, cnt_split h1 h2]
    rw [tsem_oLit] at hi' hj'
    simp only [ne_eq, decide_eq_false_iff_not, not_le, not_and, not_lt] at hi' hj'
    by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
    all_goals omega
  | win m v =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨h1, h2⟩, h3⟩ := hv
    rcases Nat.lt_trichotomy (c m) v with hlt | rfl | hgt
    · exact ⟨(.y m v, true), by simp [gen], by simp [tsem, sem, hlt]⟩
    · refine ⟨tneg (oLit N m (c m) 0 (2 * reach N m) (reach N m + 1)), by simp [gen], ?_⟩
      have hr : 0 < reach N m := by
        unfold checked at h3
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
        exact h3.1
      have := cnt_window hr (hc m h1 h2 h3)
      rw [tsem_tneg, tsem_oLit]
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_le]
      omega
    · exact ⟨(.y m (v + 1), false), by simp [gen], by simp [tsem, sem]; omega⟩

end soundness

/-! ## Certificates -/

/-- The model of the compact (solver) variables, through the variable table `vt`. -/
def model (N : Nat) (c : Nat → Nat) (vt : Trie VarTag) (x : Nat) : Bool :=
  match vt.get D x with
  | some g => sem N c g
  | none => false

/-- The compact literal `l` is the meaningful literal `x`. -/
def matchLit (vt : Trie VarTag) (x : TLit) (l : Nat) : Bool :=
  match vt.get D (l / 2) with
  | some g => g.beq x.1 && ((l % 2 == 0) == x.2)
  | none => false

theorem litVal_model {N : Nat} {c : Nat → Nat} {vt : Trie VarTag} {x : TLit} {l : Nat}
    (h : matchLit vt x l = true) : litVal (model N c vt) l = tsem N c x := by
  obtain ⟨g', b⟩ := x
  unfold matchLit at h
  unfold litVal model tsem
  split at h
  · next g hg =>
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have := VarTag.eq_of_beq h1
    subst this
    by_cases hl : l % 2 = 0
    · have : b = true := by cases b <;> simp_all
      subst this
      simp only [hl, ↓reduceIte]
      cases sem N c g <;> rfl
    · have : b = false := by cases b <;> simp_all
      subst this
      simp only [hl, ↓reduceIte]
      cases sem N c g <;> rfl
  · cases h

/-- An initial clause: its tag is valid and its generated clause is contained in it. -/
def initOK (left : Bool) (N t : Nat) (vt : Trie VarTag) (tc : CTag × List Nat) : Bool :=
  valid left N tc.1 && (gen N t tc.1).all (fun x => tc.2.any (matchLit vt x))

/-- A certificate: the variable table (compact variable `k` means `vt[k]`), the initial clauses
with their tags (ids `1, 2, ...`), and the proof steps (ids continue). -/
structure Cert where
  vt : List VarTag
  init : List (CTag × List Nat)
  steps : List (List Nat × List Nat)

/-- The check, with the variable table as a trie. -/
def checkWith (left : Bool) (N t : Nat) (vt : Trie VarTag) (cert : Cert) : Bool :=
  cert.init.all (initOK left N t vt) &&
    checkSteps (Trie.ofList D .leaf 1 (cert.init.map Prod.snd)) (cert.init.length + 1) cert.steps

/-- The certificate check. -/
def Cert.check (left : Bool) (N t : Nat) (cert : Cert) : Bool :=
  checkWith left N t (Trie.ofList D .leaf 0 cert.vt) cert

/-- No labelling with labels `< t` satisfies the checked window inequalities. -/
def NoLab (left : Bool) (N t : Nat) : Prop :=
  ∀ c : Nat → Nat, (∀ x, 1 ≤ x → x ≤ N → c x < t) →
    (∀ m, 1 ≤ m → m ≤ N → checked left N m = true → WinIneq N c m) → False

/-- **Soundness of the certificates.** -/
theorem Cert.sound {left : Bool} {N t : Nat} (cert : Cert) (h : cert.check left N t = true) :
    NoLab left N t := by
  intro c ht hc
  set vt := Trie.ofList D .leaf 0 cert.vt
  unfold Cert.check checkWith at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hinit, hsteps⟩ := h
  refine checkSteps_sound (model N c vt) _ _ _ ?_ hsteps
  intro k cl hk
  refine Trie.get_ofList D (fun cl => ∃ l ∈ cl, litVal (model N c vt) l = true) _ _ _ ?_
    (fun k' c' h' => by simp [Trie.get_leaf] at h') k cl hk
  intro cl hcl
  rw [List.mem_map] at hcl
  obtain ⟨tc, htc, rfl⟩ := hcl
  have h1 := hinit tc htc
  unfold initOK at h1
  rw [Bool.and_eq_true, List.all_eq_true] at h1
  obtain ⟨x, hx, hxv⟩ := gen_sound left tc.1 h1.1 ht hc
  obtain ⟨l, hl, hlx⟩ := List.any_eq_true.1 (h1.2 x hx)
  exact ⟨l, hl, by rw [litVal_model hlx, hxv]⟩

/-! ## The reduction with certificates -/

theorem noLab_of_dead {left : Bool} {N t : Nat} (h : Dead left N t []) : NoLab left N t :=
  fun c ht hc => no_labelling_of_dead left N t h c ht hc

/-- **Reduction to finitely many cases** (`bound_of_checks` with `NoLab`). -/
theorem bound_of_noLab (t K : Nat) (hK : NoLab true K t)
    (hfull : ∀ N, 2 ^ (t + 1) - 1 ≤ N → N < K → NoLab false N t)
    {N : Nat} {c : Nat → Nat} (hadm : Admissible N c) (ht : ∀ x, 1 ≤ x → x ≤ N → c x < t) :
    N ≤ 2 ^ (t + 1) - 2 := by
  by_contra hN
  rcases Nat.lt_or_ge N K with hNK | hKN
  · exact hfull N (by omega) hNK c ht (fun m hm1 hmN _ => hadm m hm1 hmN)
  · exact hK c (fun x hx1 hxK => ht x hx1 (by omega))
      (fun m hm1 hmK hchk => leftWin_of_admissible hKN hadm m hm1 hmK hchk)

/-- Full problems on an empty range of `N`. -/
theorem noLab_nil {t lo : Nat} : ∀ N, lo ≤ N → N < lo → NoLab false N t :=
  fun _ h1 h2 => absurd h2 (by omega)

/-- Full problems on a range of `N`, one at a time. -/
theorem noLab_cons {t lo hi : Nat} (h0 : NoLab false lo t)
    (h : ∀ N, lo + 1 ≤ N → N < hi → NoLab false N t) :
    ∀ N, lo ≤ N → N < hi → NoLab false N t := by
  intro N h1 h2
  rcases Nat.eq_or_lt_of_le h1 with rfl | h3
  · exact h0
  · exact h N h3 h2

/-! ## Consequences of an admissibility bound for all `t ≤ T` -/

/-- The admissibility bound for every number of labels `t ≤ T`. -/
def AdmBound (T : Nat) : Prop :=
  ∀ {N t : Nat} {c : Nat → Nat}, t ≤ T → Admissible N c → (∀ x, 1 ≤ x → x ≤ N → c x < t) →
    N ≤ 2 ^ (t + 1) - 2

/-- `N ≤ 2^(t+1) - 2` for `t ≤ T` rewritten with logarithms. -/
theorem min_log_le_of {N t T : Nat} (H : t ≤ T → N ≤ 2 ^ (t + 1) - 2) :
    min (Nat.log 2 (N + 1)) (T + 1) ≤ t := by
  rcases Nat.lt_or_ge t (T + 1) with ht | ht
  · have hN := H (by omega)
    have hlt : N + 1 < 2 ^ (t + 1) := by
      have : 2 ≤ 2 ^ (t + 1) := Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num)
      omega
    have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hlt
    omega
  · omega

section sequences

variable {N : Nat} {a : List Nat}

/-- Level labellings of semi-symmetric fold sequences: `min(⌊log₂(N+1)⌋, T+1) ≤ t`. -/
theorem lds_of_bound {T : Nat} (hB : AdmBound T) (hf : IsFoldSeq N a) (h : SemiSymmetric N a)
    (c : Nat → Nat) {t : Nat}
    (hc : ∀ i j (hij : i < j) (hj : j < a.length),
      a[j] < a[i]'(Nat.lt_trans hij hj) → c a[i] < c a[j])
    (ht : ∀ x ∈ a, c x < t) : min (Nat.log 2 (N + 1)) (T + 1) ≤ t :=
  min_log_le_of (fun htt => hB htt (admissible_of_labelling hf h c hc)
    (fun x hx1 hxN => ht x ((mem_range'_of_perm hf).2 ⟨hx1, hxN⟩)))

/-- Descents of semi-symmetric fold sequences: `min(⌊log₂(N+1)⌋, T+1) ≤ des a + 1`. -/
theorem descents_of_bound {T : Nat} (hB : AdmBound T) (hf : IsFoldSeq N a)
    (h : SemiSymmetric N a) : min (Nat.log 2 (N + 1)) (T + 1) ≤ des a + 1 := by
  refine lds_of_bound hB hf h (fun x => desBefore a (a.idxOf x)) ?_ ?_
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

theorem admBound_two : AdmBound 2 := fun htt hadm ht => admissible_le_two htt hadm ht

/-- Extend an admissibility bound by one more number of labels. -/
theorem admBound_succ {T : Nat} (hT : AdmBound T)
    (h : ∀ {N : Nat} {c : Nat → Nat}, Admissible N c → (∀ x, 1 ≤ x → x ≤ N → c x < T + 1) →
      N ≤ 2 ^ (T + 2) - 2) : AdmBound (T + 1) := by
  intro N t c htt hadm ht
  rcases Nat.lt_or_ge t (T + 1) with h1 | h1
  · exact hT (by omega) hadm ht
  · obtain rfl : t = T + 1 := by omega
    exact h hadm ht

end LSAT
end Folds
