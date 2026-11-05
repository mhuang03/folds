import Folds.Live2

/-!
# Live pairs, part 3: residue chains at `ν = ±1`

`experiments/live3/PROOFS.txt`, sections 1 and 2.

* `CycBal` toolkit: the counting form `cycBal_iff`, the duality `ρ ↔ q - 1 - ρ`
  (`cycBal_dual`), invariance under the reflection `sig q ν` and the rotation `rot q` of the
  labels, and the strip form `semiStep_iff_cycBal` (`N = q`).
* `chainOK_of_valid`: if `π` and `σ ∘ π` are valid sequences of the `q`-strip,
  `σ t = ((ν - t) mod q) + 1`, then `π` is a residue chain (`ChainOK q ν π`).
* **Lemma W** (`lemmaW`): valid sequences of the `k`-strip with any odd start in which `v`
  comes before `2v`; `semiSymmetric_shift` lifts them to the `(k+1)`-strip.
* **Theorem H** (`palindromic_chain`): for `q = 2k + 1` and odd `v₀ ≤ k`, an explicit chain
  for `ν = 1` (odd panels `2β + 1` then `1`, then the even panels in reversed mirrored order),
  which is also a chain when reversed, from `2v₀ + 1` to `q + 1 - 2v₀`.
  Consequences for EVERY odd `q` (Conjecture RS was known only for `q ≤ 12` before):
  `coReach_nu_one` (`N ≡ 1`, classes `≡ 3` and `≡ q - 1 (mod 4)`) and, through the rotation
  `chainOK_rot`, `coReach_nu_neg_one` (`N ≡ -1`, classes `≡ 2` and `≡ q - 2 (mod 4)`).
* **Lemma P / Theorem E** (`prec`, `no_chain_exc`): at `ν = 1` the second chain condition at
  `s` says that class `1` is placed iff class `D(s) = 2s - 1 (mod q)` is; hence, if `q` has an
  odd divisor `b > 1`, no order of the classes `2..q` is a chain: the exceptions of
  Conjecture RS are genuine.
* **Lemma N** (`winEmb_near`): the near class `C₁ - {1} + {2}` (`N ≡ 1 (mod q)`, `q ≥ 3`) is a
  window copy.  (Its complement is reachable only numerically; see PROOFS.txt section 3.)
-/

namespace Folds
namespace Live3

open Live2

/-! ## Elementary arithmetic -/

theorem mod_two {x q : Nat} (h : x < 2 * q) : x % q = if x < q then x else x - q := by
  split_ifs with hx
  · exact Nat.mod_eq_of_lt hx
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem div_two {x q : Nat} (h : x < 2 * q) : x / q = if x < q then 0 else 1 := by
  split_ifs with hx
  · exact Nat.div_eq_of_lt hx
  · have hq : 0 < q := by omega
    rw [Nat.div_eq_sub_div hq (by omega), Nat.div_eq_of_lt (by omega)]

/-- The cyclic offset `(s - t) mod q`. -/
def cc (q s t : Nat) : Nat := (s + q - t) % q

theorem cc_eq {q s t : Nat} (hs : s ≤ q) (ht : 1 ≤ t ∧ t ≤ q) :
    cc q s t = if t ≤ s then s - t else s + q - t := by
  unfold cc
  rw [mod_two (by omega)]
  split_ifs <;> omega

theorem cc_lt {q s t : Nat} (hs : s ≤ q) (ht : 1 ≤ t ∧ t ≤ q) : cc q s t < q := by
  rw [cc_eq hs ht]; split_ifs <;> omega

/-- The left summand of `CycBal` is the indicator of `1 ≤ cc ≤ ρ`. -/
theorem termL {q s t ρ : Nat} (hs : 1 ≤ s ∧ s ≤ q) (ht : 1 ≤ t ∧ t ≤ q) (hρ : ρ < q) :
    ((s + 2 * q - ρ - 1 - t) % q + ρ) / q =
      if 1 ≤ cc q s t ∧ cc q s t ≤ ρ then 1 else 0 := by
  have hc := cc_lt hs.2 ht
  have e : (s + 2 * q - ρ - 1 - t) % q = (cc q s t + (q - ρ - 1)) % q := by
    unfold cc
    rw [show s + 2 * q - ρ - 1 - t = (s + q - t) + (q - ρ - 1) by omega, Nat.add_mod,
      Nat.mod_eq_of_lt (show q - ρ - 1 < q by omega)]
  rw [e, mod_two (by omega)]
  split_ifs with h1 h2 h2
  · rw [div_two (by omega)]; split_ifs <;> omega
  · rw [div_two (by omega)]; split_ifs <;> omega
  · rw [div_two (by omega)]; split_ifs <;> omega
  · rw [div_two (by omega)]; split_ifs <;> omega

/-- The right summand of `CycBal` is the indicator of `q - ρ ≤ cc`. -/
theorem termR {q s t ρ : Nat} (hs : 1 ≤ s ∧ s ≤ q) (ht : 1 ≤ t ∧ t ≤ q) (hρ : ρ < q) :
    ((s + q - t) % q + ρ) / q = if q - ρ ≤ cc q s t then 1 else 0 := by
  have hc := cc_lt hs.2 ht
  have : (s + q - t) % q = cc q s t := rfl
  rw [this, div_two (by omega)]
  split_ifs <;> omega

theorem sum_ite_eq_countP (A : List Nat) (p : Nat → Prop) [DecidablePred p] :
    (A.map fun t => if p t then 1 else 0).sum = A.countP (fun t => decide (p t)) := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    by_cases h : p a <;> simp [h, Nat.add_comm]

/-- **Counting form of `CycBal`.** -/
theorem cycBal_iff {q s ρ : Nat} {A : List Nat} (hA : ∀ t ∈ A, 1 ≤ t ∧ t ≤ q)
    (hs : 1 ≤ s ∧ s ≤ q) (hρ : ρ < q) :
    CycBal q A s ρ ↔ A.countP (fun t => decide (1 ≤ cc q s t ∧ cc q s t ≤ ρ)) =
      A.countP (fun t => decide (q - ρ ≤ cc q s t)) := by
  unfold CycBal
  rw [List.map_congr_left (fun t ht => termL hs (hA t ht) hρ),
    List.map_congr_left (fun t ht => termR hs (hA t ht) hρ),
    sum_ite_eq_countP, sum_ite_eq_countP]

theorem countP_add_of {A : List Nat} {p r u : Nat → Bool}
    (h : ∀ t ∈ A, (if p t then 1 else 0) + (if r t then 1 else 0) = (if u t then 1 else 0)) :
    A.countP p + A.countP r = A.countP u := by
  induction A with
  | nil => simp
  | cons a A ih =>
    simp only [List.countP_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun t ht => h t (by simp [ht]))
    split_ifs at h1 ⊢ <;> simp_all <;> omega

/-- **Duality** `ρ ↔ q - 1 - ρ`. -/
theorem cycBal_dual {q s ρ : Nat} {A : List Nat} (hA : ∀ t ∈ A, 1 ≤ t ∧ t ≤ q)
    (hs : 1 ≤ s ∧ s ≤ q) (hρ : ρ < q) :
    CycBal q A s ρ ↔ CycBal q A s (q - 1 - ρ) := by
  rw [cycBal_iff hA hs hρ, cycBal_iff hA hs (by omega)]
  have e1 : A.countP (fun t => decide (1 ≤ cc q s t ∧ cc q s t ≤ q - 1 - ρ)) +
      A.countP (fun t => decide (q - ρ ≤ cc q s t)) = A.countP (fun t => decide (1 ≤ cc q s t)) :=
    countP_add_of fun t ht => by
      have := cc_lt hs.2 (hA t ht)
      simp only [decide_eq_true_eq]; split_ifs <;> omega
  have e2 : A.countP (fun t => decide (q - (q - 1 - ρ) ≤ cc q s t)) +
      A.countP (fun t => decide (1 ≤ cc q s t ∧ cc q s t ≤ ρ)) =
        A.countP (fun t => decide (1 ≤ cc q s t)) :=
    countP_add_of fun t ht => by
      have := cc_lt hs.2 (hA t ht)
      simp only [decide_eq_true_eq]; split_ifs <;> omega
  omega

/-- The reflection `σ t = ((ν - t) mod q) + 1` of the class labels. -/
def sig (q ν t : Nat) : Nat := (ν + q - t) % q + 1

theorem sig_eq {q ν t : Nat} (hν : ν < q) (ht : 1 ≤ t ∧ t ≤ q) :
    sig q ν t = if t ≤ ν then ν - t + 1 else ν + q - t + 1 := by
  unfold sig
  rw [mod_two (by omega)]
  split_ifs <;> omega

theorem sig_mem {q ν t : Nat} (hν : ν < q) (ht : 1 ≤ t ∧ t ≤ q) : 1 ≤ sig q ν t ∧ sig q ν t ≤ q := by
  rw [sig_eq hν ht]; split_ifs <;> omega

theorem sig_sig {q ν t : Nat} (hν : ν < q) (ht : 1 ≤ t ∧ t ≤ q) : sig q ν (sig q ν t) = t := by
  have h1 := sig_mem hν ht
  rw [sig_eq hν h1, sig_eq hν ht]
  split_ifs <;> omega

theorem cc_sig {q ν s t : Nat} (hν : ν < q) (hs : 1 ≤ s ∧ s ≤ q) (ht : 1 ≤ t ∧ t ≤ q) :
    cc q (sig q ν s) (sig q ν t) = cc q t s := by
  have h1 := sig_mem hν hs
  have h2 := sig_mem hν ht
  rw [cc_eq h1.2 h2, cc_eq ht.2 hs, sig_eq hν hs, sig_eq hν ht]
  split_ifs <;> omega

/-- **Reflection** of the class labels exchanges the two sides of `CycBal`. -/
theorem cycBal_sig {q ν s ρ : Nat} {A : List Nat} (hν : ν < q)
    (hA : ∀ t ∈ A, 1 ≤ t ∧ t ≤ q) (hs : 1 ≤ s ∧ s ≤ q) (hρ : ρ < q) :
    CycBal q (A.map (sig q ν)) (sig q ν s) ρ ↔ CycBal q A s ρ := by
  have hA' : ∀ t ∈ A.map (sig q ν), 1 ≤ t ∧ t ≤ q := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
    exact sig_mem hν (hA u hu)
  rw [cycBal_iff hA' (sig_mem hν hs) hρ, cycBal_iff hA hs hρ, List.countP_map, List.countP_map]
  have e1 : A.countP ((fun t => decide (1 ≤ cc q (sig q ν s) t ∧ cc q (sig q ν s) t ≤ ρ)) ∘
      sig q ν) = A.countP (fun t => decide (q - ρ ≤ cc q s t)) := by
    apply List.countP_congr
    intro t ht
    have := cc_lt hs.2 (hA t ht)
    have := hA t ht
    simp only [Function.comp, decide_eq_true_eq, cc_sig hν hs (hA t ht)]
    rw [cc_eq (hA t ht).2 hs, cc_eq hs.2 (hA t ht)]
    split_ifs <;> omega
  have e2 : A.countP ((fun t => decide (q - ρ ≤ cc q (sig q ν s) t)) ∘ sig q ν) =
      A.countP (fun t => decide (1 ≤ cc q s t ∧ cc q s t ≤ ρ)) := by
    apply List.countP_congr
    intro t ht
    have := hA t ht
    simp only [Function.comp, decide_eq_true_eq, cc_sig hν hs (hA t ht)]
    rw [cc_eq (hA t ht).2 hs, cc_eq hs.2 (hA t ht)]
    split_ifs <;> omega
  rw [e1, e2]
  exact eq_comm

/-- **Strip form**: in the `q`-strip, a valid step is a `CycBal` condition at the reach. -/
theorem semiStep_iff_cycBal {q s : Nat} {A : List Nat} (hnd : A.Nodup)
    (hA : ∀ t ∈ A, 1 ≤ t ∧ t ≤ q) (hs : 1 ≤ s ∧ s ≤ q) :
    SemiStep q A s ↔ CycBal q A s (reach q s) := by
  rw [cycBal_iff hA hs (by unfold reach; omega)]
  unfold SemiStep
  rw [leftCount_eq hnd, rightCount_eq hnd]
  have e1 : A.countP (fun x => decide (s - reach q s ≤ x ∧ x < s)) =
      A.countP (fun t => decide (1 ≤ cc q s t ∧ cc q s t ≤ reach q s)) := by
    apply List.countP_congr
    intro t ht
    simp only [decide_eq_true_eq]
    rw [cc_eq hs.2 (hA t ht)]
    have := hA t ht
    unfold reach
    split_ifs <;> omega
  have e2 : A.countP (fun x => decide (s < x ∧ x ≤ s + reach q s)) =
      A.countP (fun t => decide (q - reach q s ≤ cc q s t)) := by
    apply List.countP_congr
    intro t ht
    simp only [decide_eq_true_eq]
    rw [cc_eq hs.2 (hA t ht)]
    have := hA t ht
    unfold reach
    split_ifs <;> omega
  rw [e1, e2]

theorem sig_injOn {q ν : Nat} (hν : ν < q) {l : List Nat} (hl : ∀ t ∈ l, 1 ≤ t ∧ t ≤ q) :
    ∀ x ∈ l, ∀ y ∈ l, sig q ν x = sig q ν y → x = y := by
  intro x hx y hy e
  have h1 := sig_sig hν (hl x hx)
  rw [e, sig_sig hν (hl y hy)] at h1
  exact h1.symm

/-- **Chains from strip sequences** (live2 2.2, PROOFS.txt 1.1(e)): if `π` and `σ ∘ π` are
both valid sequences of the `q`-strip, `π` is a residue chain for `ν`. -/
theorem chainOK_of_valid {q ν : Nat} (hν : ν < q) {π : List Nat} (hf : IsFoldSeq q π)
    (h1 : SemiSymmetric q π) (h2 : SemiSymmetric q (π.map (sig q ν))) : ChainOK q ν π := by
  have hnd := nodup_of_foldSeq hf
  have hb : ∀ t ∈ π, 1 ≤ t ∧ t ≤ q := fun t ht => (mem_range'_of_perm hf).1 ht
  intro i hi
  have hs : 1 ≤ π[i] ∧ π[i] ≤ q := hb _ (List.getElem_mem hi)
  have hA : ∀ t ∈ π.take i, 1 ≤ t ∧ t ≤ q := fun t ht => hb t (List.mem_of_mem_take ht)
  have hndA := take_nodup hnd i
  constructor
  · have h := (semiStep_iff_cycBal hndA hA hs).1 (h1 i hi)
    unfold reach at h
    rcases Nat.le_total (π[i] - 1) (q - π[i]) with hle | hle
    · rwa [min_eq_left hle] at h
    · rw [min_eq_right hle, show q - π[i] = q - 1 - (π[i] - 1) by omega,
        ← cycBal_dual hA hs (by omega)] at h
      exact h
  · have h2i := h2 i (by simpa using hi)
    rw [List.getElem_map, ← List.map_take] at h2i
    have hndA' : ((π.take i).map (sig q ν)).Nodup := nodup_map_of_injOn hndA (sig_injOn hν hA)
    have hA' : ∀ t ∈ (π.take i).map (sig q ν), 1 ≤ t ∧ t ≤ q := by
      intro t ht
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
      exact sig_mem hν (hA u hu)
    have hsm := sig_mem hν hs
    have h := (semiStep_iff_cycBal hndA' hA' hsm).1 h2i
    have hsig : sig q ν π[i] - 1 = (ν + q - π[i]) % q := by unfold sig; omega
    have hlt : (ν + q - π[i]) % q < q := Nat.mod_lt _ (by omega)
    unfold reach at h
    rcases Nat.le_total (sig q ν π[i] - 1) (q - sig q ν π[i]) with hle | hle
    · rw [min_eq_left hle, cycBal_sig hν hA hs (by omega), hsig] at h
      exact h
    · rw [min_eq_right hle, show q - sig q ν π[i] = q - 1 - (sig q ν π[i] - 1) by omega,
        ← cycBal_dual hA' hsm (by omega), cycBal_sig hν hA hs (by omega), hsig] at h
      exact h

/-! ## Lemma W: doubling-ordered sequences -/

/-- Every even entry `v` of `β` comes after `v / 2`. -/
def Doubling (β : List Nat) : Prop :=
  ∀ i (h : i < β.length), β[i] % 2 = 0 → β[i] / 2 ∈ β.take i

theorem doubling_nil : Doubling [] := fun i h => absurd h (by simp)

/-- **Lemma W.**  For every odd `v₀ ≤ k` there is a valid sequence of the `k`-strip starting
with `v₀` in which `v` comes before `2v` (for all `v` with `2v ≤ k`). -/
theorem lemmaW : ∀ k v₀, v₀ % 2 = 1 → v₀ ≤ k →
    ∃ β, IsFoldSeq k β ∧ SemiSymmetric k β ∧ β.head? = some v₀ ∧ Doubling β := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro v₀ hv hvk
    obtain ⟨σ, hσf, hσs, hpre⟩ := extends_single ((k + 1) / 2) ((v₀ + 1) / 2) (by omega)
      (by omega)
    obtain ⟨τ, hτf, hτs, hτd⟩ : ∃ τ, IsFoldSeq (k / 2) τ ∧ SemiSymmetric (k / 2) τ ∧
        Doubling τ := by
      by_cases hk : k / 2 = 0
      · rw [hk]
        exact ⟨[], List.Perm.refl _, fun i h => absurd h (by simp), doubling_nil⟩
      · obtain ⟨τ, h1, h2, -, h4⟩ := ih (k / 2) (by omega) 1 rfl (by omega)
        exact ⟨τ, h1, h2, h4⟩
    have hτf' : IsFoldSeq ((k + (1 - 1)) / 2) τ := by simpa using hτf
    refine ⟨σ.map (scale 1) ++ τ.map (scale 0), hσf.blocks (by norm_num) hτf',
      (semiSymmetric_blocks_iff (by norm_num) hσf hτf').2 ⟨hσs, by simpa using hτs⟩, ?_, ?_⟩
    · obtain ⟨t, rfl⟩ := hpre
      simp only [List.map_cons, List.cons_append, List.head?_cons, Option.some.injEq]
      unfold scale; omega
    · intro i hi heven
      have hlen : (σ.map (scale 1)).length = (k + 1) / 2 := by
        rw [List.length_map, hσf.length_eq]; simp
      by_cases hiσ : i < (σ.map (scale 1)).length
      · exfalso
        rw [List.getElem_append_left hiσ, List.getElem_map] at heven
        have := (mem_range'_of_perm hσf).1 (List.getElem_mem (l := σ) (by simpa using hiσ))
        unfold scale at heven; omega
      · obtain ⟨j, rfl⟩ : ∃ j, i = (σ.map (scale 1)).length + j :=
          ⟨i - (σ.map (scale 1)).length, by omega⟩
        have hj : j < τ.length := by simp at hi; omega
        rw [List.getElem_append_right (by omega)] at heven ⊢
        simp only [Nat.add_sub_cancel_left, List.getElem_map] at heven ⊢
        rw [List.take_length_add_append, List.mem_append]
        have hτj := (mem_range'_of_perm hτf).1 (List.getElem_mem hj)
        have e2 : scale 0 τ[j] / 2 = τ[j] := by unfold scale; omega
        rw [e2]
        by_cases hodd : τ[j] % 2 = 1
        · left
          refine List.mem_map.2 ⟨(τ[j] + 1) / 2, (mem_range'_of_perm hσf).2 ⟨by omega, by omega⟩,
            by unfold scale; omega⟩
        · right
          have := hτd j hj (by omega)
          rw [← List.map_take]
          exact List.mem_map.2 ⟨τ[j] / 2, this, by unfold scale; omega⟩

/-- In a doubling-ordered sequence, `2 β[i]` is not placed before `β[i]`. -/
theorem double_not_before {β : List Nat} (hnd : β.Nodup) (hd : Doubling β) {i : Nat}
    (hi : i < β.length) : 2 * β[i] ∉ β.take i := by
  intro hm
  obtain ⟨m, hm', e⟩ := List.getElem_of_mem hm
  have hmi : m < i := by simp at hm'; omega
  rw [List.getElem_take] at e
  have h := hd m (by omega) (by rw [e]; omega)
  rw [e, show 2 * β[i] / 2 = β[i] by omega] at h
  obtain ⟨m', hm'', e'⟩ := List.getElem_of_mem h
  rw [List.getElem_take] at e'
  have : m' = i := (hnd.getElem_inj_iff).1 e'
  simp at hm''; omega

theorem semiStep_reach_zero {N m : Nat} {S : List Nat} (h : reach N m = 0) : SemiStep N S m := by
  unfold SemiStep leftCount rightCount; rw [h]; simp

/-- **Shift**: `β + 1` followed by `1` is valid in the `(k+1)`-strip. -/
theorem semiSymmetric_shift {k : Nat} {β : List Nat} (hf : IsFoldSeq k β)
    (hs : SemiSymmetric k β) (hd : Doubling β) :
    SemiSymmetric (k + 1) (β.map (· + 1) ++ [1]) := by
  have hnd := nodup_of_foldSeq hf
  have hb : ∀ t ∈ β, 1 ≤ t ∧ t ≤ k := fun t ht => (mem_range'_of_perm hf).1 ht
  rw [semiSymmetric_append_iff]
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · simp only [List.length_map] at hi
    rw [List.getElem_map, ← List.map_take]
    have h := hs i hi
    have hndt := take_nodup hnd i
    have hndt' : ((β.take i).map (· + 1)).Nodup :=
      nodup_map_of_injOn hndt fun x _ y _ e => by omega
    have hbi := hb _ (List.getElem_mem hi)
    have hnot := double_not_before hnd hd hi
    have hS : ∀ x ∈ β.take i, 1 ≤ x ∧ x ≤ k := fun x hx => hb x (List.mem_of_mem_take hx)
    unfold SemiStep at h ⊢
    rw [leftCount_eq hndt, rightCount_eq hndt] at h
    rw [leftCount_eq hndt', rightCount_eq hndt', List.countP_map, List.countP_map]
    have e1 : (β.take i).countP ((fun x => decide (β[i] + 1 - reach (k + 1) (β[i] + 1) ≤ x ∧
        x < β[i] + 1)) ∘ (· + 1)) =
        (β.take i).countP (fun x => decide (β[i] - reach k β[i] ≤ x ∧ x < β[i])) := by
      apply List.countP_congr
      intro x hx
      have := hS x hx
      simp only [Function.comp, decide_eq_true_eq]
      unfold reach; omega
    have e2 : (β.take i).countP ((fun x => decide (β[i] + 1 < x ∧
        x ≤ β[i] + 1 + reach (k + 1) (β[i] + 1))) ∘ (· + 1)) =
        (β.take i).countP (fun x => decide (β[i] < x ∧ x ≤ β[i] + reach k β[i])) := by
      apply List.countP_congr
      intro x hx
      have := hS x hx
      have hx2 : x ≠ 2 * β[i] := fun e => hnot (e ▸ hx)
      simp only [Function.comp, decide_eq_true_eq]
      unfold reach; omega
    rw [e1, e2]; exact h
  · have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    exact semiStep_reach_zero (by simp [reach])

/-! ## Theorem H: palindromic chains at `ν = 1` -/

theorem sig_one_odd {k v : Nat} (hv : 1 ≤ v ∧ v ≤ k) :
    sig (2 * k + 1) 1 (2 * v + 1) = 2 * (k + 1 - v) := by
  rw [sig_eq (by omega) ⟨by omega, by omega⟩]; split_ifs <;> omega

theorem sig_one_even {k v : Nat} (hv : 1 ≤ v ∧ v ≤ k) :
    sig (2 * k + 1) 1 (2 * (k + 1 - v)) = 2 * v + 1 := by
  rw [sig_eq (by omega) ⟨by omega, by omega⟩]; split_ifs <;> omega

/-- **Theorem H** (PROOFS.txt 1.4).  For `q = 2k + 1` and odd `v₀ ≤ k` there is a residue chain
`π` for `ν = 1` whose reverse is a chain too, starting with `2 v₀ + 1` and ending with
`q + 1 - 2 v₀`. -/
theorem palindromic_chain {k v₀ : Nat} (hv : v₀ % 2 = 1) (hvk : v₀ ≤ k) :
    ∃ π, IsFoldSeq (2 * k + 1) π ∧ ChainOK (2 * k + 1) 1 π ∧
      ChainOK (2 * k + 1) 1 π.reverse ∧ π.head? = some (2 * v₀ + 1) ∧
      π.reverse.head? = some (2 * (k + 1 - v₀)) := by
  obtain ⟨β, hf, hs, hhead, hd⟩ := lemmaW k v₀ hv hvk
  have hnd := nodup_of_foldSeq hf
  have hb : ∀ t ∈ β, 1 ≤ t ∧ t ≤ k := fun t ht => (mem_range'_of_perm hf).1 ht
  set α := β.map (· + 1) ++ [1] with hαdef
  have hαf : IsFoldSeq (k + 1) α := by
    refine perm_range'_of_nodup_subset ?_ ?_ ?_
    · rw [List.nodup_append]
      refine ⟨nodup_map_of_injOn hnd fun x _ y _ e => by omega, List.nodup_singleton 1, ?_⟩
      intro a ha b hb'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      simp at hb'; have := hb x hx; omega
    · intro y hy
      rw [List.mem_append, List.mem_map] at hy
      rcases hy with ⟨x, hx, rfl⟩ | hy
      · have := hb x hx; omega
      · simp at hy; omega
    · rw [hαdef, List.length_append, List.length_map, hf.length_eq]; simp
  have hαs : SemiSymmetric (k + 1) α := semiSymmetric_shift hf hs hd
  set δ := revMirror k β with hδdef
  have hδf : IsFoldSeq k δ := hf.revMirror
  have hδs : SemiSymmetric k δ := SemiSymmetric.revMirror hf hs
  have hα' : IsFoldSeq ((2 * k + 1 + 1) / 2) α := by
    rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega]; exact hαf
  have hδ' : IsFoldSeq ((2 * k + 1 + (1 - 1)) / 2) δ := by
    rw [show (2 * k + 1 + (1 - 1)) / 2 = k by omega]; exact hδf
  set π := α.map (scale 1) ++ δ.map (scale 0) with hπdef
  have hπf : IsFoldSeq (2 * k + 1) π := hα'.blocks (by norm_num) hδ'
  have hπs : SemiSymmetric (2 * k + 1) π :=
    (semiSymmetric_blocks_iff (by norm_num) hα' hδ').2
      ⟨by rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega]; exact hαs,
       by rw [show (2 * k + 1 + (1 - 1)) / 2 = k by omega]; exact hδs⟩
  -- the explicit form of `π`
  have hA : α.map (scale 1) = β.map (fun v => 2 * v + 1) ++ [1] := by
    rw [hαdef, List.map_append, List.map_map]
    refine congrArg₂ (· ++ ·) (List.map_congr_left fun v _ => ?_) rfl
    show scale 1 (v + 1) = 2 * v + 1
    unfold scale; omega
  have hB : δ.map (scale 0) = (β.map (fun v => 2 * (k + 1 - v))).reverse := by
    rw [hδdef]
    unfold revMirror
    rw [List.map_reverse, List.map_map]
    exact congrArg List.reverse (List.map_congr_left fun v _ => by
      show scale 0 (k + 1 - v) = 2 * (k + 1 - v)
      unfold scale; omega)
  have hπe : π = β.map (fun v => 2 * v + 1) ++ [1] ++
      (β.map (fun v => 2 * (k + 1 - v))).reverse := by
    rw [hπdef, hA, hB]
  have hmap : π.map (sig (2 * k + 1) 1) = π.reverse := by
    rw [hπe]
    simp only [List.map_append, List.map_reverse, List.map_map, List.reverse_append,
      List.reverse_reverse, List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    have e1 : β.map (sig (2 * k + 1) 1 ∘ fun v => 2 * v + 1) =
        β.map (fun v => 2 * (k + 1 - v)) :=
      List.map_congr_left fun v hv' => sig_one_odd (hb v hv')
    have e2 : β.map (sig (2 * k + 1) 1 ∘ fun v => 2 * (k + 1 - v)) =
        β.map (fun v => 2 * v + 1) :=
      List.map_congr_left fun v hv' => sig_one_even (hb v hv')
    have e3 : sig (2 * k + 1) 1 1 = 1 := by unfold sig; simp
    rw [e1, e2, e3]
  refine ⟨π, hπf, ?_, ?_, ?_, ?_⟩
  · exact chainOK_of_valid (by omega) hπf hπs (by rw [hmap]; exact hπs.reverse hπf)
  · refine chainOK_of_valid (by omega) ((List.reverse_perm _).trans hπf) (hπs.reverse hπf) ?_
    rw [List.map_reverse, hmap, List.reverse_reverse]; exact hπs
  · rw [hπe]
    cases β with
    | nil => simp at hhead
    | cons b β' =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead; simp
  · rw [hπe]
    cases β with
    | nil => simp at hhead
    | cons b β' =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead; simp

/-! ## From chains to co-reachability -/

theorem chainOK_append_left {q ν : Nat} {A B : List Nat} (h : ChainOK q ν (A ++ B)) :
    ChainOK q ν A := by
  intro i hi
  have := h i (by simp; omega)
  rwa [List.take_append_of_le_length (by omega), List.getElem_append_left hi] at this

/-- A full chain ending with `s` gives the residue transfer through the class of `s`. -/
theorem coReach_of_chain_last {q N s : Nat} (hq : 0 < q) (hqN : q ≤ N) {L : List Nat}
    (hf : IsFoldSeq q L) (hc : ChainOK q (N % q) L) (hlast : L.reverse.head? = some s)
    {D : Finset Nat} (hDs : D ⊆ Finset.Icc 1 (ccount q s N))
    (hD : CoReach (ccount q s N) D) : CoReach N (D.image (cls q s)) := by
  obtain ⟨R, hR⟩ : ∃ R, L.reverse = s :: R := by
    cases h : L.reverse with
    | nil => rw [h] at hlast; simp at hlast
    | cons a R => rw [h] at hlast; simp at hlast; exact ⟨R, by rw [hlast]⟩
  have hL : L = R.reverse ++ [s] := by
    rw [← List.reverse_reverse L, hR, List.reverse_cons]
  have hnd := nodup_of_foldSeq hf
  rw [hL] at hnd hc
  have hmem : ∀ t, t ∈ L ↔ 1 ≤ t ∧ t ≤ q := fun t => mem_range'_of_perm hf
  have hs := (hmem s).1 (by rw [hL]; simp)
  rw [List.nodup_append] at hnd
  refine coReach_res hq hqN hs.1 hs.2 (π := R.reverse) ?_ hnd.1 (chainOK_append_left hc) hDs hD
  intro t
  constructor
  · intro ht
    have htL : t ∈ L := by rw [hL]; simp [ht]
    have h12 := (hmem t).1 htL
    refine ⟨h12.1, h12.2, ?_⟩
    rintro rfl
    exact hnd.2.2 t ht t (by simp) rfl
  · rintro ⟨h1, h2, hne⟩
    have htL := (hmem t).2 ⟨h1, h2⟩
    rw [hL, List.mem_append, List.mem_singleton] at htL
    rcases htL with h | h
    · exact h
    · exact absurd h hne

/-- **Residue transfer at `ν = 1` for every odd `q`** (Corollary of PROOFS.txt 1.4): for
`N ≡ 1 (mod q)` the classes `s = 2 v₀ + 1` and `s = q + 1 - 2 v₀` (`v₀` odd, `2 v₀ < q`), i.e.
`s ≡ 3` and `s ≡ q - 1 (mod 4)`, have a reachable complement, so co-reachable sets of their
class strip stay co-reachable. -/
theorem coReach_nu_one {q N s v₀ : Nat} (hqodd : q % 2 = 1) (hqN : q ≤ N) (hN : N % q = 1)
    (hv : v₀ % 2 = 1) (hvq : 2 * v₀ < q) (hs : s = 2 * v₀ + 1 ∨ s = q + 1 - 2 * v₀)
    {D : Finset Nat} (hDs : D ⊆ Finset.Icc 1 (ccount q s N))
    (hD : CoReach (ccount q s N) D) : CoReach N (D.image (cls q s)) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
  obtain ⟨π, hf, hc, hcr, hh, hl⟩ := palindromic_chain (k := k) hv (by omega)
  have hc' : ChainOK (2 * k + 1) (N % (2 * k + 1)) π := by rw [hN]; exact hc
  have hcr' : ChainOK (2 * k + 1) (N % (2 * k + 1)) π.reverse := by rw [hN]; exact hcr
  rcases hs with rfl | rfl
  · exact coReach_of_chain_last (by omega) hqN ((List.reverse_perm _).trans hf) hcr'
      (by rw [List.reverse_reverse]; exact hh) hDs hD
  · exact coReach_of_chain_last (by omega) hqN hf hc'
      (by rw [hl]; congr 1; omega) hDs hD

/-! ## Rotation: `ν = 1` and `ν = q - 1` -/

/-- The rotation `t ↦ t - 1` of the class labels (`1 ↦ q`). -/
def rot (q t : Nat) : Nat := (t + q - 2) % q + 1

theorem rot_eq {q t : Nat} (_hq : 2 ≤ q) (ht : 1 ≤ t ∧ t ≤ q) :
    rot q t = if t = 1 then q else t - 1 := by
  unfold rot
  rw [mod_two (by omega)]
  split_ifs <;> omega

theorem rot_mem {q t : Nat} (hq : 2 ≤ q) (ht : 1 ≤ t ∧ t ≤ q) : 1 ≤ rot q t ∧ rot q t ≤ q := by
  rw [rot_eq hq ht]; split_ifs <;> omega

theorem cycBal_rot {q s ρ : Nat} {A : List Nat} (hq : 2 ≤ q)
    (hA : ∀ t ∈ A, 1 ≤ t ∧ t ≤ q) (hs : 1 ≤ s ∧ s ≤ q) (hρ : ρ < q) :
    CycBal q (A.map (rot q)) (rot q s) ρ ↔ CycBal q A s ρ := by
  have hA' : ∀ t ∈ A.map (rot q), 1 ≤ t ∧ t ≤ q := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
    exact rot_mem hq (hA u hu)
  have hcc : ∀ t ∈ A, cc q (rot q s) (rot q t) = cc q s t := by
    intro t ht
    have := hA t ht
    rw [cc_eq (rot_mem hq hs).2 (rot_mem hq (hA t ht)), cc_eq hs.2 (hA t ht), rot_eq hq hs,
      rot_eq hq (hA t ht)]
    split_ifs <;> omega
  rw [cycBal_iff hA' (rot_mem hq hs) hρ, cycBal_iff hA hs hρ, List.countP_map, List.countP_map]
  have e1 : A.countP ((fun t => decide (1 ≤ cc q (rot q s) t ∧ cc q (rot q s) t ≤ ρ)) ∘
      rot q) = A.countP (fun t => decide (1 ≤ cc q s t ∧ cc q s t ≤ ρ)) :=
    List.countP_congr fun t ht => by simp only [Function.comp, hcc t ht]
  have e2 : A.countP ((fun t => decide (q - ρ ≤ cc q (rot q s) t)) ∘ rot q) =
      A.countP (fun t => decide (q - ρ ≤ cc q s t)) :=
    List.countP_congr fun t ht => by simp only [Function.comp, hcc t ht]
  rw [e1, e2]

/-- A chain for `ν = 1`, rotated by one step, is a chain for `ν = q - 1`. -/
theorem chainOK_rot {q : Nat} (hq : 2 ≤ q) {π : List Nat} (hb : ∀ t ∈ π, 1 ≤ t ∧ t ≤ q)
    (hc : ChainOK q 1 π) : ChainOK q (q - 1) (π.map (rot q)) := by
  intro i hi
  simp only [List.length_map] at hi
  have hs := hb _ (List.getElem_mem hi)
  have hA : ∀ t ∈ π.take i, 1 ≤ t ∧ t ≤ q := fun t ht => hb t (List.mem_of_mem_take ht)
  obtain ⟨c1, c2⟩ := hc i hi
  rw [List.getElem_map, ← List.map_take]
  generalize π[i] = s at c1 c2 hs ⊢
  have hr1 : rot q s - 1 < q := by have := rot_mem hq hs; omega
  have hr2 : (q - 1 + q - rot q s) % q < q := Nat.mod_lt _ (by omega)
  rw [cycBal_rot hq hA hs hr1, cycBal_rot hq hA hs hr2, rot_eq hq hs]
  by_cases h1 : s = 1
  · rw [if_pos h1]
    subst h1
    have c0 : CycBal q (π.take i) 1 (q - 1) := by
      have := (cycBal_dual hA ⟨le_rfl, by omega⟩ (show 0 < q by omega)).1 (by simpa using c1)
      simpa using this
    have e : (q - 1 + q - q) % q = q - 1 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [e]; exact ⟨c0, c0⟩
  · rw [if_neg h1]
    have e1 : (1 + q - s) % q = q + 1 - s := by
      rw [Nat.mod_eq_of_lt (show 1 + q - s < q by omega)]; omega
    rw [e1] at c2
    have e2 : (q - 1 + q - (s - 1)) % q = q - 1 - (s - 1) := by
      rw [mod_two (by omega)]; split_ifs <;> omega
    rw [e2, ← cycBal_dual hA hs (by omega),
      show s - 1 - 1 = q - 1 - (q + 1 - s) by omega, ← cycBal_dual hA hs (by omega)]
    exact ⟨c2, c1⟩

theorem isFoldSeq_map_rot {q : Nat} (hq : 2 ≤ q) {L : List Nat} (hf : IsFoldSeq q L) :
    IsFoldSeq q (L.map (rot q)) := by
  have hb : ∀ t ∈ L, 1 ≤ t ∧ t ≤ q := fun t ht => (mem_range'_of_perm hf).1 ht
  refine perm_range'_of_nodup_subset ?_ ?_ (by rw [List.length_map, hf.length_eq]; simp)
  · refine nodup_map_of_injOn (nodup_of_foldSeq hf) fun x hx y hy e => ?_
    have h1 := hb x hx; have h2 := hb y hy
    rw [rot_eq hq h1, rot_eq hq h2] at e
    split_ifs at e <;> omega
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy
    exact rot_mem hq (hb u hu)

/-- **Residue transfer at `ν = q - 1` for every odd `q`**: for `N ≡ -1 (mod q)` the classes
`s = 2 v₀` and `s = q - 2 v₀` (`v₀` odd, `2 v₀ < q`), i.e. `s ≡ 2` and `s ≡ q - 2 (mod 4)`. -/
theorem coReach_nu_neg_one {q N s v₀ : Nat} (hqodd : q % 2 = 1) (hqN : q ≤ N)
    (hN : N % q = q - 1) (hv : v₀ % 2 = 1) (hvq : 2 * v₀ < q) (hs : s = 2 * v₀ ∨ s = q - 2 * v₀)
    {D : Finset Nat} (hDs : D ⊆ Finset.Icc 1 (ccount q s N))
    (hD : CoReach (ccount q s N) D) : CoReach N (D.image (cls q s)) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
  have hq2 : 2 ≤ 2 * k + 1 := by omega
  obtain ⟨π, hf, hc, hcr, hh, hl⟩ := palindromic_chain (k := k) hv (by omega)
  have hb : ∀ t ∈ π, 1 ≤ t ∧ t ≤ 2 * k + 1 := fun t ht => (mem_range'_of_perm hf).1 ht
  have hbr : ∀ t ∈ π.reverse, 1 ≤ t ∧ t ≤ 2 * k + 1 := fun t ht => hb t (List.mem_reverse.1 ht)
  have hc' : ChainOK (2 * k + 1) (N % (2 * k + 1)) (π.map (rot (2 * k + 1))) := by
    rw [hN]; exact chainOK_rot hq2 hb hc
  have hcr' : ChainOK (2 * k + 1) (N % (2 * k + 1)) (π.reverse.map (rot (2 * k + 1))) := by
    rw [hN]; exact chainOK_rot hq2 hbr hcr
  rcases hs with rfl | rfl
  · refine coReach_of_chain_last (by omega) hqN
      (isFoldSeq_map_rot hq2 ((List.reverse_perm _).trans hf)) hcr' ?_ hDs hD
    rw [← List.map_reverse, List.reverse_reverse]
    cases π with
    | nil => simp at hh
    | cons a π' =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simp only [List.map_cons, List.head?_cons, Option.some.injEq]
      rw [rot_eq hq2 ⟨by omega, by omega⟩]; split_ifs <;> omega
  · refine coReach_of_chain_last (by omega) hqN (isFoldSeq_map_rot hq2 hf) hc' ?_ hDs hD
    rw [← List.map_reverse]
    cases h : π.reverse with
    | nil => rw [h] at hl; simp at hl
    | cons a π' =>
      rw [h] at hl
      simp only [List.head?_cons, Option.some.injEq] at hl
      subst hl
      simp only [List.map_cons, List.head?_cons, Option.some.injEq]
      rw [rot_eq hq2 ⟨by omega, by omega⟩]; split_ifs <;> omega

/-! ## Theorem E: the exceptions of Conjecture RS are genuine -/

/-- The doubling map `D(s) - 1 = 2 (s - 1)` on the class labels. -/
def dbl (q s : Nat) : Nat := (2 * s - 2) % q + 1

theorem countP_eq_ite {A : List Nat} (hnd : A.Nodup) (x : Nat) :
    A.countP (fun t => decide (t = x)) = if x ∈ A then 1 else 0 := by
  induction A with
  | nil => simp
  | cons a A ih =>
    rw [List.nodup_cons] at hnd
    rw [List.countP_cons, ih hnd.2]
    by_cases hax : a = x
    · subst hax; simp [hnd.1]
    · simp only [hax, decide_false, List.mem_cons]
      by_cases hx : x ∈ A
      · simp [hx]
      · simp [hx, Ne.symm hax]

/-- **Lemma P** (precedence form at `ν = 1`): given the first chain condition at `s ≥ 2`,
the second one says that class `1` is placed iff class `D(s)` is. -/
theorem prec {q s : Nat} {A : List Nat} (hA : ∀ t ∈ A, 1 ≤ t ∧ t ≤ q) (hnd : A.Nodup)
    (hs : 2 ≤ s ∧ s ≤ q) (c1 : CycBal q A s (s - 1)) (c2 : CycBal q A s ((1 + q - s) % q)) :
    (1 ∈ A ↔ dbl q s ∈ A) := by
  have hs' : 1 ≤ s ∧ s ≤ q := ⟨by omega, hs.2⟩
  have e : (1 + q - s) % q = q - 1 - (s - 2) := by
    rw [Nat.mod_eq_of_lt (show 1 + q - s < q by omega)]; omega
  rw [e, ← cycBal_dual hA hs' (by omega)] at c2
  rw [cycBal_iff hA hs' (by omega)] at c1 c2
  have a1 : A.countP (fun t => decide (1 ≤ cc q s t ∧ cc q s t ≤ s - 2)) +
      A.countP (fun t => decide (cc q s t = s - 1)) =
        A.countP (fun t => decide (1 ≤ cc q s t ∧ cc q s t ≤ s - 1)) :=
    countP_add_of fun t ht => by simp only [decide_eq_true_eq]; split_ifs <;> omega
  have a2 : A.countP (fun t => decide (q - (s - 2) ≤ cc q s t)) +
      A.countP (fun t => decide (cc q s t = q + 1 - s)) =
        A.countP (fun t => decide (q - (s - 1) ≤ cc q s t)) :=
    countP_add_of fun t ht => by simp only [decide_eq_true_eq]; split_ifs <;> omega
  have b1 : A.countP (fun t => decide (cc q s t = s - 1)) = A.countP (fun t => decide (t = 1)) := by
    apply List.countP_congr
    intro t ht
    have := hA t ht
    simp only [decide_eq_true_eq]
    rw [cc_eq hs.2 (hA t ht)]
    split_ifs <;> omega
  have b2 : A.countP (fun t => decide (cc q s t = q + 1 - s)) =
      A.countP (fun t => decide (t = dbl q s)) := by
    apply List.countP_congr
    intro t ht
    have := hA t ht
    simp only [decide_eq_true_eq]
    rw [cc_eq hs.2 (hA t ht)]
    unfold dbl
    rw [mod_two (by omega)]
    split_ifs <;> omega
  have key : A.countP (fun t => decide (t = 1)) = A.countP (fun t => decide (t = dbl q s)) := by
    omega
  rw [countP_eq_ite hnd, countP_eq_ite hnd] at key
  constructor
  · intro h; rw [if_pos h] at key; split_ifs at key with h'; exact h'
  · intro h; rw [if_pos h] at key; split_ifs at key with h'; exact h'

theorem dbl_iter {q m : Nat} (_hq : 0 < q) (hm : m < q) :
    ∀ j, (dbl q)^[j] (m + 1) = (2 ^ j * m) % q + 1 := by
  intro j
  induction j with
  | zero => simp [Nat.mod_eq_of_lt hm]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold dbl
    rw [show 2 * ((2 ^ j * m) % q + 1) - 2 = 2 * ((2 ^ j * m) % q) by omega, Nat.mul_mod,
      Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, ← pow_succ']

/-- **Theorem E** (PROOFS.txt 1.3).  If `q` has an odd divisor `b > 1` (i.e. `q` is not a power
of `2`), no order of the classes `2, …, q` is a residue chain for `ν = 1`: the class `1` can
never come last (equivalently first) when `N ≡ 1 (mod q)`. -/
theorem no_chain_exc {q b : Nat} (hq : 0 < q) (hb : b ∣ q) (hb1 : 1 < b) (hbo : b % 2 = 1)
    {π : List Nat} (hmem : ∀ t, t ∈ π ↔ 2 ≤ t ∧ t ≤ q) (hnd : π.Nodup) :
    ¬ ChainOK q 1 π := by
  intro hc
  obtain ⟨m, rfl⟩ := hb
  have hm : 0 < m := by rcases Nat.eq_zero_or_pos m with h | h <;> simp_all
  have hmq : m < b * m := by nlinarith
  -- the orbit never meets `1`
  have hne : ∀ j, (dbl (b * m))^[j] (m + 1) ≠ 1 := by
    intro j h
    rw [dbl_iter hq hmq] at h
    have h0 : (2 ^ j * m) % (b * m) = 0 := by omega
    have hdvd : b * m ∣ 2 ^ j * m := Nat.dvd_of_mod_eq_zero h0
    have hb2 : b ∣ 2 ^ j := Nat.dvd_of_mul_dvd_mul_right hm hdvd
    have hcop2 : Nat.Coprime 2 b := by
      show Nat.gcd 2 b = 1
      rw [Nat.gcd_rec, hbo]; rfl
    have hcop : Nat.Coprime b (2 ^ j) := Nat.Coprime.pow_right _ (Nat.coprime_comm.1 hcop2)
    have := Nat.Coprime.eq_one_of_dvd hcop hb2
    omega
  have hle : ∀ j, (dbl (b * m))^[j] (m + 1) ≤ b * m := by
    intro j; rw [dbl_iter hq hmq]; have := Nat.mod_lt (2 ^ j * m) hq; omega
  have hpos : ∀ j, 1 ≤ (dbl (b * m))^[j] (m + 1) := by
    intro j; rw [dbl_iter hq hmq]; omega
  have hin : ∀ j, (dbl (b * m))^[j] (m + 1) ∈ π := fun j =>
    (hmem _).2 ⟨by have := hne j; have := hpos j; omega, hle j⟩
  have hb' : ∀ t ∈ π, 1 ≤ t ∧ t ≤ b * m := fun t ht => by have := (hmem t).1 ht; omega
  -- positions strictly increase along the orbit
  have step : ∀ j, ∃ i, ∃ hi : i < π.length, π[i] = (dbl (b * m))^[j] (m + 1) ∧ j ≤ i := by
    intro j
    induction j with
    | zero =>
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem (hin 0)
      exact ⟨i, hi, by simpa using e, Nat.zero_le _⟩
    | succ j ih =>
      obtain ⟨i, hi, e, hji⟩ := ih
      set s := (dbl (b * m))^[j] (m + 1) with hsdef
      have hs2 : 2 ≤ s ∧ s ≤ b * m := ⟨by have := hne j; have := hpos j; omega, hle j⟩
      obtain ⟨c1, c2⟩ := hc i hi
      rw [e] at c1 c2
      have hA : ∀ t ∈ π.take i, 1 ≤ t ∧ t ≤ b * m := fun t ht => hb' t (List.mem_of_mem_take ht)
      have h1 : (1 : Nat) ∉ π.take i := fun h => by
        have := (hmem 1).1 (List.mem_of_mem_take h); omega
      have hP := prec hA (take_nodup hnd i) hs2 c1 c2
      have hD : dbl (b * m) s ∉ π.take i := fun h => h1 (hP.2 h)
      have hDs : dbl (b * m) s = (dbl (b * m))^[j + 1] (m + 1) := by
        rw [Function.iterate_succ_apply']
      have hDmem : dbl (b * m) s ∈ π := by rw [hDs]; exact hin (j + 1)
      obtain ⟨i', hi', e'⟩ := List.getElem_of_mem hDmem
      refine ⟨i', hi', by rw [e', hDs], ?_⟩
      by_contra hlt
      rcases Nat.lt_or_ge i' i with h | h
      · exact hD (by rw [← e']; exact List.mem_iff_getElem.2 ⟨i', by simp; omega, by simp⟩)
      · have hii : i' = i := by omega
        subst hii
        rw [e] at e'
        -- `D(s) = s` forces `s = 1`
        have : dbl (b * m) s = s := e'.symm
        unfold dbl at this
        rw [mod_two (by omega)] at this
        split_ifs at this <;> omega
  obtain ⟨i, hi, -, hji⟩ := step π.length
  omega

/-! ## Lemma N: near residue classes are window copies -/

/-- The near class `C₁ - {1} + {2}`: `φ(1) = 2`, `φ(y) = 1 + (y - 1) q`. -/
def nearPhi (q y : Nat) : Nat := if y = 1 then 2 else cls q 1 y

theorem cls_one_ge {q y : Nat} (hy : 2 ≤ y) : q + 1 ≤ cls q 1 y := by
  unfold cls
  have : q ≤ (y - 1) * q := Nat.le_mul_of_pos_left q (by omega)
  omega

/-- **Lemma N** (PROOFS.txt 2).  For `q ≥ 3` and `N ≡ 1 (mod q)`, `N > q`, the near class
`C₁ - {1} + {2}` is a window copy of the strip of size `|C₁|`. -/
theorem winEmb_near {q N : Nat} (hq : 3 ≤ q) (hN : N % q = 1) (hqN : q < N) :
    WinEmb N (ccount q 1 N) (nearPhi q) := by
  have hφ := winEmb_res (q := q) (s := 1) (N := N) (by omega) le_rfl (by omega) (by omega)
  have hr2 : reach N 2 = 1 := by unfold reach; omega
  have hrp1 : reach (ccount q 1 N) 1 = 0 := by unfold reach; omega
  refine ⟨fun y h1 h2 => ?_, fun x y hx1 hxp hy1 hyp e => ?_, fun j y hj1 hjp hy1 hyp => ?_,
    fun j y hj1 hjp hy1 hyp => ?_⟩
  · unfold nearPhi; split_ifs
    · omega
    · exact hφ.bound y h1 h2
  · unfold nearPhi at e
    split_ifs at e with h1 h2 h2
    · omega
    · have := cls_one_ge (q := q) (show 2 ≤ y by omega); omega
    · have := cls_one_ge (q := q) (show 2 ≤ x by omega); omega
    · exact hφ.inj x y hx1 hxp hy1 hyp e
  · unfold nearPhi
    by_cases hj : j = 1
    · subst hj
      rw [if_pos rfl, hr2]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hy : y = 1
        · rw [if_pos hy] at h2; omega
        · rw [if_neg hy] at h2
          have := cls_one_ge (q := q) (show 2 ≤ y by omega); omega
      · rintro ⟨_, h2⟩; omega
    · rw [if_neg hj]
      have hx := cls_one_ge (q := q) (show 2 ≤ j by omega)
      by_cases hy : y = 1
      · subst hy
        rw [if_pos rfl]
        have h0 := hφ.left j 1 hj1 hjp le_rfl hyp
        have hc1 : cls q 1 1 = 1 := by unfold cls; simp
        rw [hc1] at h0
        rw [← h0]
        -- `2` and `1` lie in the same arm unless `2 x = N + 2`, impossible mod `q`
        have hne : cls q 1 j - reach N (cls q 1 j) ≠ 2 := by
          intro h2
          have hrx : reach N (cls q 1 j) = N - cls q 1 j := by unfold reach at h2 ⊢; omega
          have hNe : N = 2 * (j - 1) * q := by
            rw [hrx] at h2; unfold cls at h2 hx; rw [Nat.mul_assoc]; omega
          rw [hNe, Nat.mul_mod_left] at hN
          omega
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
      · rw [if_neg hy]
        exact hφ.left j y hj1 hjp hy1 hyp
  · unfold nearPhi
    by_cases hj : j = 1
    · subst hj
      rw [if_pos rfl, hr2, hrp1]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hy : y = 1
        · rw [if_pos hy] at h1; omega
        · rw [if_neg hy] at h1 h2
          have := cls_one_ge (q := q) (show 2 ≤ y by omega); omega
      · rintro ⟨h1, h2⟩; omega
    · rw [if_neg hj]
      have hx := cls_one_ge (q := q) (show 2 ≤ j by omega)
      by_cases hy : y = 1
      · subst hy
        rw [if_pos rfl]
        constructor
        · rintro ⟨h1, _⟩; omega
        · rintro ⟨h1, _⟩; omega
      · rw [if_neg hy]
        exact hφ.right j y hj1 hjp hy1 hyp

end Live3
end Folds
