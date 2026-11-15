import Folds.Recursion
import Folds.Wallis

/-!
# The graded graph `Γ_N` and its up and down operators

(Cross-domain campaign, angle "differential posets and dual graded graphs";
see `experiments/xd_graded/NOTES.txt`.)

`Γ_N` has the subsets `S ⊆ [N]` as vertices, ranked by `|S|`, and an edge `S → S ∪ {m}`
whenever the step `(S, m)` is semi-symmetric.  `a(N)` is the number of maximal chains
`∅ → [N]`.

Contents (all for every `N`, unless a specific `N` is named):

* `Valid N S m`: the step condition as a property of the set `S`; it does not depend on
  whether `m ∈ S` (`valid_insert_self`, `valid_erase_self`), and it only depends on `S`
  inside the window of `m` (`valid_insert_of_outside`).
* `up N S`, `down N S`: the valid additions to and the valid removals from `S`.
* **Self-duality** (`valid_co`, `up_co`, `down_co`): complementation `S ↦ [N] \ S` is an
  anti-automorphism of `Γ_N`; `D_eq_U_co`, `chain_co`, `coReach_iff_reach_co`.
* The **operators** `U N`, `D N` on functions `Finset ℕ → R`; they are adjoint
  (`sum_U_mul`), `g N` is the orbit of `δ_∅` under `U` (`g_eq_U`, `g_eq_iterate`,
  `semiCount_eq_iterate`), and `∑_{|T|=k+1} g(T) = ∑_{|S|=k} g(S) · |up S|`
  (`sum_g_succ`).
* The **commutator** `comm N = D U − U D`: its diagonal entry at `S` is
  `|up S| − |down S|` (`comm_diag`), its trace on rank `k+1` is `e_{k+1} − e_k`
  (`trace_comm`), where `e_k = edges N k` and `e_k = e_{N-1-k}` (`edges_symm`); it is
  **not diagonal** for any `N ≥ 3` (`comm_offdiag`: the entry at `({1}, {2})` is `-1`).
* **Chains**: `Chain`, `Reach`, `CoReach`, `Live`; `reach_iff_g_pos`; a decidable
  deadness certificate `Dead` (`not_coReach_of_dead`).
* **An obstruction to any `sl₂` / differential structure** (`twins_nine`): for `N = 9` the
  two live 3-sets `{1,4,9}` and `{1,6,9}` have one and the same unique live successor
  `{1,4,6,9}`.  Hence no weighting of the edges of the live graph makes the up operator
  injective on rank `3 < 9/2`, so (Proctor's theorem) the poset of live sets is not Peck,
  and no lowering operator `D'` with `D'U − UD' = (N − 2k) I` exists for any weighting.
-/

namespace Folds
namespace XdGraded

open Finset

private theorem ifNeg {c : Prop} [Decidable c] {α : Sort*} {t e : α} (h : ¬ c) :
    ite c t e = e := by simp [h]

/-! ## The step condition for sets -/

/-- `Valid N S m`: adding panel `m` when the panels of `S` are present is a semi-symmetric
step.  The definition makes sense for every `m`, whether or not `m ∈ S`. -/
def Valid (N : ℕ) (S : Finset ℕ) (m : ℕ) : Prop := BalancedBefore N m S

instance (N : ℕ) (S : Finset ℕ) (m : ℕ) : Decidable (Valid N S m) :=
  inferInstanceAs (Decidable (BalancedBefore N m S))

theorem valid_iff_setStep {N m : ℕ} {S : Finset ℕ} : Valid N S m ↔ SetStep N S m := by
  unfold Valid SetStep
  rw [semiStep_iff_balanced (Finset.sort_nodup _ _), Finset.sort_toFinset]

/-- A panel outside the window of `m` (or `m` itself) does not influence the step. -/
theorem valid_insert_of_outside {N m a : ℕ} {S : Finset ℕ}
    (h : a < m - reach N m ∨ a = m ∨ m + reach N m < a) :
    Valid N (insert a S) m ↔ Valid N S m := by
  unfold Valid BalancedBefore
  rw [filter_insert, filter_insert, ifNeg (by omega), ifNeg (by omega)]

theorem valid_insert_self {N m : ℕ} {S : Finset ℕ} : Valid N (insert m S) m ↔ Valid N S m :=
  valid_insert_of_outside (Or.inr (Or.inl rfl))

theorem valid_erase_self {N m : ℕ} {S : Finset ℕ} : Valid N (S.erase m) m ↔ Valid N S m := by
  by_cases hm : m ∈ S
  · conv_rhs => rw [← insert_erase hm]
    exact valid_insert_self.symm
  · rw [erase_eq_of_notMem hm]

/-! ## Up and down sets, complement -/

/-- The valid additions to `S`. -/
def up (N : ℕ) (S : Finset ℕ) : Finset ℕ := (Icc 1 N \ S).filter (Valid N S)

/-- The valid removals from `S`: the possible last panels of a valid ordering of `S`. -/
def down (N : ℕ) (S : Finset ℕ) : Finset ℕ := S.filter (Valid N S)

/-- The complement in `[N]`. -/
def co (N : ℕ) (S : Finset ℕ) : Finset ℕ := Icc 1 N \ S

theorem mem_up {N m : ℕ} {S : Finset ℕ} :
    m ∈ up N S ↔ (1 ≤ m ∧ m ≤ N) ∧ m ∉ S ∧ Valid N S m := by
  simp only [up, mem_filter, mem_sdiff, mem_Icc, and_assoc]

theorem mem_down {N m : ℕ} {S : Finset ℕ} : m ∈ down N S ↔ m ∈ S ∧ Valid N S m := by
  simp only [down, mem_filter]

theorem mem_co {N m : ℕ} {S : Finset ℕ} : m ∈ co N S ↔ (1 ≤ m ∧ m ≤ N) ∧ m ∉ S := by
  simp only [co, mem_sdiff, mem_Icc]

theorem co_subset (N : ℕ) (S : Finset ℕ) : co N S ⊆ Icc 1 N := sdiff_subset

theorem co_co {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) : co N (co N S) = S :=
  Finset.sdiff_sdiff_eq_self hS

theorem co_insert (N m : ℕ) (S : Finset ℕ) : co N (insert m S) = (co N S).erase m := by
  ext x; simp only [mem_co, mem_insert, mem_erase]; tauto

theorem co_erase {N m : ℕ} {S : Finset ℕ} (hm : 1 ≤ m ∧ m ≤ N) :
    co N (S.erase m) = insert m (co N S) := by
  ext x; simp only [mem_co, mem_insert, mem_erase]
  constructor
  · rintro ⟨hx, h⟩
    by_cases e : x = m
    · exact Or.inl e
    · exact Or.inr ⟨hx, fun hxS => h ⟨e, hxS⟩⟩
  · rintro (rfl | ⟨hx, h⟩)
    · exact ⟨hm, fun h => h.1 rfl⟩
    · exact ⟨hx, fun h' => h h'.2⟩

theorem card_co {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) : (co N S).card = N - S.card := by
  rw [co, card_sdiff_of_subset hS, Nat.card_Icc]; simp

/-- **Self-duality, step level.**  Complementing the set of present panels preserves the
validity of the step at `m`. -/
theorem valid_co {N m : ℕ} {S : Finset ℕ} (hm : 1 ≤ m ∧ m ≤ N) :
    Valid N (co N S) m ↔ Valid N S m := by
  rw [valid_iff_setStep, valid_iff_setStep]
  unfold SetStep
  symm
  apply semiStep_iff_of_compl
  intro d hd1 hd2
  simp only [Finset.mem_sort, mem_co]
  unfold reach at hd2
  exact ⟨⟨fun h => h.2, fun h => ⟨⟨by omega, by omega⟩, h⟩⟩,
    ⟨fun h => h.2, fun h => ⟨⟨by omega, by omega⟩, h⟩⟩⟩

/-- **Self-duality**: the valid additions to the complement are the valid removals. -/
theorem up_co {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) : up N (co N S) = down N S := by
  ext m
  rw [mem_up, mem_down, mem_co]
  constructor
  · rintro ⟨hm, h, hv⟩
    have hmS : m ∈ S := by by_contra h'; exact h ⟨hm, h'⟩
    exact ⟨hmS, (valid_co hm).1 hv⟩
  · rintro ⟨hmS, hv⟩
    have hm := mem_Icc.1 (hS hmS)
    exact ⟨hm, fun h => h.2 hmS, (valid_co hm).2 hv⟩

/-- **Self-duality**: the valid removals from the complement are the valid additions. -/
theorem down_co (N : ℕ) (S : Finset ℕ) : down N (co N S) = up N S := by
  ext m
  rw [mem_up, mem_down, mem_co]
  constructor
  · rintro ⟨⟨hm, h⟩, hv⟩; exact ⟨hm, h, (valid_co hm).1 hv⟩
  · rintro ⟨hm, h, hv⟩; exact ⟨⟨hm, h⟩, (valid_co hm).2 hv⟩

theorem mem_down_insert {N m : ℕ} {S : Finset ℕ} (h : m ∈ up N S) :
    m ∈ down N (insert m S) :=
  mem_down.2 ⟨mem_insert_self _ _, valid_insert_self.2 (mem_up.1 h).2.2⟩

theorem mem_up_erase {N m : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) (h : m ∈ down N S) :
    m ∈ up N (S.erase m) :=
  mem_up.2 ⟨mem_Icc.1 (hS (mem_down.1 h).1), notMem_erase _ _,
    valid_erase_self.2 (mem_down.1 h).2⟩

/-! ## The up and down operators -/

section Operators

variable {R : Type*}

/-- The up operator: `(U f)(T) = ∑_{S → T} f(S)`. -/
def U [AddCommMonoid R] (N : ℕ) (f : Finset ℕ → R) (T : Finset ℕ) : R :=
  ∑ m ∈ down N T, f (T.erase m)

/-- The down operator: `(D f)(S) = ∑_{S → T} f(T)`. -/
def D [AddCommMonoid R] (N : ℕ) (f : Finset ℕ → R) (S : Finset ℕ) : R :=
  ∑ m ∈ up N S, f (insert m S)

/-- **Self-duality, operator level**: `D = J U J`, where `J` is complementation. -/
theorem D_eq_U_co [AddCommMonoid R] {N : ℕ} (f : Finset ℕ → R) {S : Finset ℕ}
    (hS : S ⊆ Icc 1 N) : D N f S = U N (fun X => f (co N X)) (co N S) := by
  unfold D U
  rw [down_co]
  apply sum_congr rfl
  intro m hm
  show f (insert m S) = f (co N ((co N S).erase m))
  rw [co_erase (mem_up.1 hm).1, co_co hS]

/-- **Adjointness** of `U` and `D` between consecutive ranks. -/
theorem sum_U_mul [CommSemiring R] (N k : ℕ) (f h : Finset ℕ → R) :
    ∑ T ∈ (Icc 1 N).powersetCard (k + 1), U N f T * h T =
      ∑ S ∈ (Icc 1 N).powersetCard k, f S * D N h S := by
  unfold U D
  simp only [sum_mul, mul_sum]
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.1.erase x.2, x.2⟩) (fun x _ => ⟨insert x.2 x.1, x.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨T, m⟩ hx
    simp only [mem_sigma, mem_powersetCard] at hx ⊢
    obtain ⟨⟨hT, hc⟩, hm⟩ := hx
    refine ⟨⟨(erase_subset _ _).trans hT, ?_⟩, mem_up_erase hT hm⟩
    rw [card_erase_of_mem (mem_down.1 hm).1, hc]; rfl
  · rintro ⟨S, m⟩ hx
    simp only [mem_sigma, mem_powersetCard] at hx ⊢
    obtain ⟨⟨hS, hc⟩, hm⟩ := hx
    refine ⟨⟨?_, ?_⟩, mem_down_insert hm⟩
    · exact insert_subset (mem_Icc.2 (mem_up.1 hm).1) hS
    · rw [card_insert_of_notMem (mem_up.1 hm).2.1, hc]
  · rintro ⟨T, m⟩ hx
    simp only [mem_sigma] at hx
    simp only [insert_erase (mem_down.1 hx.2).1]
  · rintro ⟨S, m⟩ hx
    simp only [mem_sigma] at hx
    simp only [erase_insert (mem_up.1 hx.2).2.1]
  · rintro ⟨T, m⟩ hx
    simp only [mem_sigma] at hx
    simp only [insert_erase (mem_down.1 hx.2).1]

end Operators

/-! ## `g` is the orbit of `δ_∅` under `U` -/

/-- The subset recursion in operator form: `g = U g` away from the empty set. -/
theorem g_eq_U {N : ℕ} {T : Finset ℕ} (hT : T.Nonempty) : g N T = U N (g N) T := by
  rw [g_eq_sum hT, U, down]
  congr 1
  apply filter_congr
  intro m _
  rw [← valid_iff_setStep, valid_erase_self]

/-- `g(T) = (U^{|T|} δ_∅)(T)`. -/
theorem g_eq_iterate (N : ℕ) : ∀ (k : ℕ) (T : Finset ℕ), T.card = k →
    g N T = (U N)^[k] (Pi.single ∅ 1) T := by
  intro k
  induction k with
  | zero =>
    intro T hT
    rw [card_eq_zero] at hT
    subst hT
    simp [g_empty]
  | succ k ih =>
    intro T hT
    have hne : T.Nonempty := by rw [← card_pos]; omega
    rw [Function.iterate_succ_apply', g_eq_U hne, U, U]
    apply sum_congr rfl
    intro m hm
    exact ih _ (by rw [card_erase_of_mem (mem_down.1 hm).1, hT]; rfl)

/-- `a(N) = ⟨[N] | U^N | ∅⟩`: the number of maximal chains of `Γ_N`. -/
theorem semiCount_eq_iterate (N : ℕ) :
    semiCount N = (U N)^[N] (Pi.single ∅ 1) (Icc 1 N) := by
  rw [semiCount_eq_g, g_eq_iterate N N _ (by simp)]

/-- The reversal identity in the language of the graph: `a(N) = ∑_{|S|=k} g(S) g(Sᶜ)`. -/
theorem semiCount_eq_sum_co {N k : ℕ} (hk : k ≤ N) :
    semiCount N = ∑ S ∈ (Icc 1 N).powersetCard k, g N S * g N (co N S) :=
  semiCount_eq_sum_split hk

/-- **Prefix counts**: `∑_{|T| = k+1} g(T) = ∑_{|S| = k} g(S) · (number of valid additions
to S)`. -/
theorem sum_g_succ (N k : ℕ) :
    ∑ T ∈ (Icc 1 N).powersetCard (k + 1), g N T =
      ∑ S ∈ (Icc 1 N).powersetCard k, g N S * (up N S).card := by
  have h := sum_U_mul N k (g N) (fun _ => 1)
  simp only [mul_one, D, sum_const, nsmul_eq_mul, Nat.cast_id] at h
  rw [← h]
  apply sum_congr rfl
  intro T hT
  have hne : T.Nonempty := by rw [← card_pos, (mem_powersetCard.1 hT).2]; omega
  exact g_eq_U hne

/-! ## Edge counts -/

/-- The number of edges of `Γ_N` from rank `k` to rank `k + 1`. -/
def edges (N k : ℕ) : ℕ := ∑ S ∈ (Icc 1 N).powersetCard k, (up N S).card

/-- Counting the edges from above. -/
theorem sum_down_card (N k : ℕ) :
    ∑ T ∈ (Icc 1 N).powersetCard (k + 1), (down N T).card = edges N k := by
  have h := sum_U_mul N k (fun _ => (1 : ℕ)) (fun _ => 1)
  simpa only [U, D, sum_const, nsmul_eq_mul, Nat.cast_id, mul_one, one_mul, edges] using h

/-- **Self-duality of the edge counts**: `e_k = e_{N-1-k}`. -/
theorem edges_symm {N k : ℕ} (hk : k < N) : edges N (N - 1 - k) = edges N k := by
  rw [← sum_down_card, edges]
  refine sum_nbij' (co N) (co N) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [mem_powersetCard] at hS ⊢
    exact ⟨co_subset _ _, by rw [card_co hS.1, hS.2]; omega⟩
  · intro S hS
    rw [mem_powersetCard] at hS ⊢
    exact ⟨co_subset _ _, by rw [card_co hS.1, hS.2]; omega⟩
  · intro S hS; exact co_co (mem_powersetCard.1 hS).1
  · intro S hS; exact co_co (mem_powersetCard.1 hS).1
  · intro S hS; rw [up_co (mem_powersetCard.1 hS).1]

/-! ## The commutator `D U − U D` -/

/-- The commutator of the down and up operators. -/
def comm (N : ℕ) (f : Finset ℕ → ℤ) (S : Finset ℕ) : ℤ := D N (U N f) S - U N (D N f) S

theorem DU_single_diag (N : ℕ) (S : Finset ℕ) :
    D N (U N (Pi.single S (1 : ℤ))) S = (up N S).card := by
  unfold D
  rw [card_eq_sum_ones, Nat.cast_sum]
  apply sum_congr rfl
  intro m hm
  unfold U
  rw [sum_eq_single_of_mem m (mem_down_insert hm)]
  · rw [erase_insert (mem_up.1 hm).2.1]; simp
  · intro m' hm' hne
    rw [Pi.single_apply, ifNeg]
    intro h
    have : m ∈ (insert m S).erase m' := mem_erase.2 ⟨fun e => hne e.symm, mem_insert_self _ _⟩
    rw [h] at this
    exact (mem_up.1 hm).2.1 this

theorem UD_single_diag {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) :
    U N (D N (Pi.single S (1 : ℤ))) S = (down N S).card := by
  unfold U
  rw [card_eq_sum_ones, Nat.cast_sum]
  apply sum_congr rfl
  intro m hm
  unfold D
  rw [sum_eq_single_of_mem m (mem_up_erase hS hm)]
  · rw [insert_erase (mem_down.1 hm).1]; simp
  · intro m' hm' hne
    rw [Pi.single_apply, ifNeg]
    intro h
    have h1 : m ∈ insert m' (S.erase m) := by rw [h]; exact (mem_down.1 hm).1
    rcases mem_insert.1 h1 with e | e
    · exact hne e.symm
    · exact notMem_erase _ _ e

/-- **The diagonal of the commutator**: the entry at `(S, S)` is the number of valid
additions minus the number of valid removals. -/
theorem comm_diag {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) :
    comm N (Pi.single S 1) S = (up N S).card - (down N S).card := by
  rw [comm, DU_single_diag, UD_single_diag hS]

/-- **The trace of the commutator** on rank `k + 1` is `e_{k+1} − e_k`. -/
theorem trace_comm (N k : ℕ) :
    ∑ S ∈ (Icc 1 N).powersetCard (k + 1), comm N (Pi.single S 1) S =
      (edges N (k + 1) : ℤ) - edges N k := by
  rw [← sum_down_card N k, edges, Nat.cast_sum, Nat.cast_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro S hS
  exact comm_diag (mem_powersetCard.1 hS).1

theorem valid_one (N : ℕ) (S : Finset ℕ) : Valid N S 1 := by
  unfold Valid BalancedBefore
  have h : reach N 1 = 0 := by unfold reach; omega
  rw [h, filter_false_of_mem (by intro x _; omega), filter_false_of_mem (by intro x _; omega)]

theorem not_valid_one_two {N : ℕ} (hN : 3 ≤ N) : ¬ Valid N {1} 2 := by
  unfold Valid BalancedBefore
  have h : reach N 2 = 1 := by unfold reach; omega
  rw [h]
  decide

/-- **The commutator is not diagonal** for `N ≥ 3`: its entry at `({1}, {2})` is `-1`
(the exchange `1 ↔ 2` is possible through `∅` but not through `{1, 2}`). -/
theorem comm_offdiag {N : ℕ} (hN : 3 ≤ N) : comm N (Pi.single {2} 1) {1} = -1 := by
  have h1 : D N (U N (Pi.single ({2} : Finset ℕ) (1 : ℤ))) {1} = 0 := by
    unfold D
    apply sum_eq_zero
    intro m hm
    unfold U
    apply sum_eq_zero
    intro m' _
    rw [Pi.single_apply, ifNeg]
    intro h
    have h2 : (2 : ℕ) ∈ (insert m ({1} : Finset ℕ)).erase m' := by rw [h]; simp
    have h3 : (2 : ℕ) = m := by
      have := mem_of_mem_erase h2
      simpa using this
    subst h3
    exact not_valid_one_two hN (mem_up.1 hm).2.2
  have h2 : U N (D N (Pi.single ({2} : Finset ℕ) (1 : ℤ))) {1} = 1 := by
    have hd : down N {1} = {1} := by
      ext x
      rw [mem_down, mem_singleton]
      constructor
      · intro h; exact h.1
      · rintro rfl; exact ⟨rfl, valid_one N _⟩
    unfold U
    rw [hd, sum_singleton, erase_singleton]
    unfold D
    have hu : (2 : ℕ) ∈ up N ∅ := by
      rw [mem_up]
      refine ⟨⟨by omega, by omega⟩, by simp, ?_⟩
      unfold Valid BalancedBefore
      simp
    rw [sum_eq_single_of_mem 2 hu]
    · simp
    · intro m' _ hne
      rw [Pi.single_apply, ifNeg]
      intro h
      have : m' ∈ ({2} : Finset ℕ) := by rw [← h]; simp
      exact hne (mem_singleton.1 this)
  rw [comm, h1, h2]; rfl

/-! ## Chains, reachability, liveness -/

/-- `Chain N S T`: there is a valid chain `S → … → T` in `Γ_N`. -/
inductive Chain (N : ℕ) : Finset ℕ → Finset ℕ → Prop
  | refl (S : Finset ℕ) : Chain N S S
  | step {S T : Finset ℕ} {m : ℕ} : m ∈ up N S → Chain N (insert m S) T → Chain N S T

/-- `S` is reachable: it is the set of some valid prefix. -/
abbrev Reach (N : ℕ) (S : Finset ℕ) : Prop := Chain N ∅ S

/-- `S` is co-reachable: it can be completed to `[N]`. -/
abbrev CoReach (N : ℕ) (S : Finset ℕ) : Prop := Chain N S (Icc 1 N)

/-- `S` is live: it lies on a maximal chain of `Γ_N`. -/
def Live (N : ℕ) (S : Finset ℕ) : Prop := Reach N S ∧ CoReach N S

theorem Chain.trans {N : ℕ} {S T V : Finset ℕ} (h1 : Chain N S T) (h2 : Chain N T V) :
    Chain N S V := by
  induction h1 with
  | refl => exact h2
  | step hm _ ih => exact Chain.step hm (ih h2)

theorem Chain.tail {N m : ℕ} {S T : Finset ℕ} (h : Chain N S T) (hm : m ∈ up N T) :
    Chain N S (insert m T) :=
  h.trans (Chain.step hm (Chain.refl _))

/-- The last step of a nontrivial chain. -/
theorem Chain.tail_cases {N : ℕ} {S T : Finset ℕ} (h : Chain N S T) :
    S = T ∨ ∃ m, m ∈ down N T ∧ m ∉ S ∧ Chain N S (T.erase m) := by
  induction h with
  | refl => exact Or.inl rfl
  | @step S T m hm hc ih =>
    right
    rcases ih with e | ⟨m', hm', hn, hc'⟩
    · subst e
      refine ⟨m, mem_down_insert hm, (mem_up.1 hm).2.1, ?_⟩
      rw [erase_insert (mem_up.1 hm).2.1]
      exact Chain.refl _
    · exact ⟨m', hm', fun h => hn (mem_insert_of_mem h), Chain.step hm hc'⟩

theorem co_Icc (N : ℕ) : co N (Icc 1 N) = ∅ := by simp [co]

theorem co_empty (N : ℕ) : co N ∅ = Icc 1 N := by simp [co]

/-- **Self-duality, chain level**: complementation reverses chains. -/
theorem chain_co {N : ℕ} {S T : Finset ℕ} (hS : S ⊆ Icc 1 N) (h : Chain N S T) :
    Chain N (co N T) (co N S) := by
  induction h with
  | refl => exact Chain.refl _
  | @step S T m hm _ ih =>
    have hm' := mem_up.1 hm
    have h1 := ih (insert_subset (mem_Icc.2 hm'.1) hS)
    rw [co_insert] at h1
    have hmem : m ∈ co N S := mem_co.2 ⟨hm'.1, hm'.2.1⟩
    have h2 : m ∈ up N ((co N S).erase m) :=
      mem_up.2 ⟨hm'.1, notMem_erase _ _, valid_erase_self.2 ((valid_co hm'.1).2 hm'.2.2)⟩
    have h3 := h1.tail h2
    rwa [insert_erase hmem] at h3

theorem coReach_iff_reach_co {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) :
    CoReach N S ↔ Reach N (co N S) := by
  constructor
  · intro h
    have h1 := chain_co hS h
    rwa [co_Icc] at h1
  · intro h
    have h1 := chain_co (empty_subset _) h
    rwa [co_co hS, co_empty] at h1

/-- Reachable sets are exactly the sets with `g > 0`. -/
theorem reach_iff_g_pos {N : ℕ} : ∀ (k : ℕ) (S : Finset ℕ), S.card = k → S ⊆ Icc 1 N →
    (Reach N S ↔ 0 < g N S) := by
  intro k
  induction k with
  | zero =>
    intro S hc _
    rw [card_eq_zero] at hc
    subst hc
    simp [g_empty, Chain.refl]
  | succ k ih =>
    intro S hc hS
    have hne : S.Nonempty := by rw [← card_pos]; omega
    have hcard : ∀ m ∈ down N S, (S.erase m).card = k := by
      intro m hm
      rw [card_erase_of_mem (mem_down.1 hm).1, hc]; rfl
    rw [g_eq_U hne, U]
    constructor
    · intro h
      rcases Chain.tail_cases h with e | ⟨m, hm, -, hch⟩
      · exact absurd e.symm hne.ne_empty
      · have hpos := (ih (S.erase m) (hcard m hm) ((erase_subset _ _).trans hS)).1 hch
        exact lt_of_lt_of_le hpos
          (single_le_sum (f := fun m => g N (S.erase m)) (fun _ _ => Nat.zero_le _) hm)
    · intro h
      obtain ⟨m, hm, hpos⟩ : ∃ m ∈ down N S, 0 < g N (S.erase m) := by
        by_contra hcon
        push Not at hcon
        have h0 : ∑ m ∈ down N S, g N (S.erase m) = 0 :=
          sum_eq_zero (fun m hm => Nat.le_zero.1 (hcon m hm))
        omega
      have hch := (ih (S.erase m) (hcard m hm) ((erase_subset _ _).trans hS)).2 hpos
      have h3 := Chain.tail hch (mem_up_erase hS hm)
      rwa [insert_erase (mem_down.1 hm).1] at h3

/-- Live sets are exactly the sets that contribute to `a(N) = ∑ g(S) g(Sᶜ)`. -/
theorem live_iff_g_pos {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) :
    Live N S ↔ 0 < g N S ∧ 0 < g N (co N S) := by
  unfold Live
  rw [coReach_iff_reach_co hS, reach_iff_g_pos _ S rfl hS,
    reach_iff_g_pos _ (co N S) rfl (co_subset _ _)]

/-- A decidable certificate that `S` cannot be completed: every valid continuation dies
within `f` steps. -/
def Dead (N : ℕ) : ℕ → Finset ℕ → Prop
  | 0, _ => False
  | f + 1, S => S ≠ Icc 1 N ∧ ∀ m ∈ up N S, Dead N f (insert m S)

instance decDead (N : ℕ) : ∀ (f : ℕ) (S : Finset ℕ), Decidable (Dead N f S)
  | 0, _ => inferInstanceAs (Decidable False)
  | f + 1, S =>
    haveI := decDead N f
    inferInstanceAs (Decidable (S ≠ Icc 1 N ∧ ∀ m ∈ up N S, Dead N f (insert m S)))

theorem not_coReach_of_dead {N : ℕ} : ∀ (f : ℕ) (S : Finset ℕ), Dead N f S → ¬ CoReach N S := by
  intro f
  induction f with
  | zero => intro S h; exact h.elim
  | succ f ih =>
    intro S h hco
    obtain ⟨hne, hall⟩ := h
    cases hco with
    | refl => exact hne rfl
    | step hm hc => exact ih _ (hall _ hm) hc

/-- The steps of the list `l`, started from the set `S`, are all valid. -/
def Steps (N : ℕ) : Finset ℕ → List ℕ → Prop
  | _, [] => True
  | S, m :: l => m ∈ up N S ∧ Steps N (insert m S) l

instance decSteps (N : ℕ) : ∀ (S : Finset ℕ) (l : List ℕ), Decidable (Steps N S l)
  | _, [] => inferInstanceAs (Decidable True)
  | S, m :: l =>
    haveI := decSteps N (insert m S) l
    inferInstanceAs (Decidable (m ∈ up N S ∧ Steps N (insert m S) l))

theorem chain_of_steps {N : ℕ} : ∀ (l : List ℕ) (S : Finset ℕ), Steps N S l →
    Chain N S (l.foldl (fun X m => insert m X) S)
  | [], S, _ => Chain.refl S
  | m :: l, S, h => Chain.step h.1 (chain_of_steps l (insert m S) h.2)

/-! ## An obstruction for `N = 9` -/

/-- **Twin live sets.**  For `N = 9` the live 3-sets `{1,4,9}` and `{1,6,9}` have the same
unique live successor `{1,4,6,9}`.  So for *any* weights on the edges of the live graph, the
up operator sends `δ_{1,4,9}` and `δ_{1,6,9}` to multiples of `δ_{1,4,6,9}`: it is not
injective on rank `3 < 9/2`.  By Proctor's theorem the poset of live sets is therefore not
an `sl₂`-poset (not Peck), for any choice of order-raising operator. -/
theorem twins_nine :
    Live 9 {1, 4, 9} ∧ Live 9 {1, 6, 9} ∧
    (∀ m ∈ up 9 {1, 4, 9}, CoReach 9 (insert m {1, 4, 9}) →
      insert m ({1, 4, 9} : Finset ℕ) = {1, 4, 6, 9}) ∧
    (∀ m ∈ up 9 {1, 6, 9}, CoReach 9 (insert m {1, 6, 9}) →
      insert m ({1, 6, 9} : Finset ℕ) = {1, 4, 6, 9}) := by
  have r1 : Reach 9 {1, 4, 9} := by
    have h := chain_of_steps (N := 9) [4, 1, 9] ∅ (by decide +kernel)
    have e : ([4, 1, 9] : List ℕ).foldl (fun X m => insert m X) (∅ : Finset ℕ) = {1, 4, 9} := by
      decide
    rwa [e] at h
  have c1 : CoReach 9 {1, 4, 9} := by
    have h := chain_of_steps (N := 9) [6, 3, 2, 7, 8, 5] {1, 4, 9} (by decide +kernel)
    have e : ([6, 3, 2, 7, 8, 5] : List ℕ).foldl (fun X m => insert m X)
        ({1, 4, 9} : Finset ℕ) = Icc 1 9 := by decide
    rwa [e] at h
  have r2 : Reach 9 {1, 6, 9} := by
    have h := chain_of_steps (N := 9) [1, 6, 9] ∅ (by decide +kernel)
    have e : ([1, 6, 9] : List ℕ).foldl (fun X m => insert m X) (∅ : Finset ℕ) = {1, 6, 9} := by
      decide
    rwa [e] at h
  have c2 : CoReach 9 {1, 6, 9} := by
    have h := chain_of_steps (N := 9) [4, 3, 2, 7, 8, 5] {1, 6, 9} (by decide +kernel)
    have e : ([4, 3, 2, 7, 8, 5] : List ℕ).foldl (fun X m => insert m X)
        ({1, 6, 9} : Finset ℕ) = Icc 1 9 := by decide
    rwa [e] at h
  refine ⟨⟨r1, c1⟩, ⟨r2, c2⟩, ?_, ?_⟩
  · intro m hm hco
    have hu : up 9 {1, 4, 9} = {3, 6} := by decide +kernel
    rw [hu] at hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact absurd hco (not_coReach_of_dead 2 _ (by decide +kernel))
    · decide
  · intro m hm hco
    have hu : up 9 {1, 6, 9} = {4, 7} := by decide +kernel
    rw [hu] at hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl
    · decide
    · exact absurd hco (not_coReach_of_dead 2 _ (by decide +kernel))

end XdGraded
end Folds
