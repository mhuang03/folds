import Folds.SuperExp8

/-!
# Palindromic chains: the parity obstruction

`experiments/superexp10/PROOFS.txt`.

A *palindromic chain* (`Live4.goodL_palin`) is a complete sequence
`π = x ++ [t₀] ++ reverse (σ ∘ x)` of the `q`-strip, `σ = sig q ν`, with `σ t₀ = t₀`.
Its middle step is the step of `t₀` after `x`.  The window of `t₀` is `σ`-invariant (`σ`
is the reflection `t ↦ 2 t₀ - t` on it, `sig_window`), and `x` holds exactly one class of each
`σ`-pair, so `x` meets the window in exactly `reach q t₀` classes; a balanced middle step
splits them evenly:

* `palin_reach_even`: if `π` is a complete sequence and the middle step is valid, then
  `reach q t₀` is even.
* `palin_mod_four`: for odd `q` this means `ν ≡ 1 (mod 4)` or `q - ν ≡ 1 (mod 4)`.
* `palin_goodL_mod_four`: the same for every good sequence `π` with `σ ∘ π = reverse π`
  (every such `π` is a palindromic chain).

So palindromic chains (with any transversal of the `σ`-pairs) never give `H(q, ν)` for odd
`q` and `ν ≡ 3 (mod 4)` (and these residues are unavoidable for the all-`N` bound, e.g.
`N = 2^L - 1`).  Numerically (`experiments/superexp10`, `obstr.py`) the condition is also
sufficient for every odd `q ≤ 25`.  Hypothesis H for `ρ ≤ q/K` is NOT proven here; the
all-`N` exponent stays `1/16` unconditionally (`1/12` conditional, `SuperExp8.allN_of_smallH`).
-/

namespace Folds
namespace SuperExp10

open Live2 Live3 Live4

/-- On the window of a fixed point `t₀`, `σ` is the reflection through `t₀`. -/
theorem sig_window {q ν t₀ t : Nat} (hν : ν < q) (ht0 : 1 ≤ t₀ ∧ t₀ ≤ q)
    (hfix : sig q ν t₀ = t₀) (ht : t₀ - reach q t₀ ≤ t ∧ t ≤ t₀ + reach q t₀) :
    sig q ν t + t = 2 * t₀ := by
  have ht' : 1 ≤ t ∧ t ≤ q := by unfold reach at ht; omega
  rw [sig_eq hν ht0] at hfix
  rw [sig_eq hν ht']
  unfold reach at ht
  split_ifs at hfix ⊢ <;> omega

/-- `σ` maps the right half of the window of `t₀` onto the left half. -/
theorem sig_left_iff {q ν t₀ t : Nat} (hν : ν < q) (ht0 : 1 ≤ t₀ ∧ t₀ ≤ q)
    (hfix : sig q ν t₀ = t₀) (ht : 1 ≤ t ∧ t ≤ q) :
    (t₀ - reach q t₀ ≤ sig q ν t ∧ sig q ν t < t₀) ↔ (t₀ < t ∧ t ≤ t₀ + reach q t₀) := by
  constructor
  · intro h
    have hs := sig_mem hν ht
    have e := sig_window hν ht0 hfix (t := sig q ν t) ⟨h.1, by omega⟩
    rw [sig_sig hν ht] at e
    omega
  · intro h
    have e := sig_window hν ht0 hfix (t := t) ⟨by omega, h.2⟩
    omega

/-- **The parity obstruction.**  If `x ++ [t₀] ++ reverse (σ ∘ x)` is a complete sequence of
the `q`-strip, `σ t₀ = t₀`, and `t₀` is balanced after `x`, then `reach q t₀` is even. -/
theorem palin_reach_even {q ν t₀ : Nat} (hν : ν < q) {x : List Nat}
    (hf : IsFoldSeq q (x ++ [t₀] ++ (x.map (sig q ν)).reverse)) (hfix : sig q ν t₀ = t₀)
    (hmid : SemiStep q x t₀) : reach q t₀ % 2 = 0 := by
  have hb : ∀ z ∈ x, 1 ≤ z ∧ z ≤ q := fun z hz => (mem_range'_of_perm hf).1 (by simp [hz])
  have ht0 : 1 ≤ t₀ ∧ t₀ ≤ q := (mem_range'_of_perm hf).1 (by simp)
  have hnd : x.Nodup := by
    have := nodup_of_foldSeq hf
    rw [List.nodup_append] at this
    exact (List.nodup_append.1 this.1).1
  have hR1 : reach q t₀ ≤ t₀ - 1 := by unfold reach; omega
  -- the middle step
  unfold SemiStep at hmid
  rw [leftCount_eq hnd, rightCount_eq hnd] at hmid
  -- the whole sequence meets the left half of the window in `R` classes
  have hall : (x ++ [t₀] ++ (x.map (sig q ν)).reverse).countP
      (fun z => decide (t₀ - reach q t₀ ≤ z ∧ z < t₀)) = reach q t₀ := by
    rw [hf.countP_eq]
    have e : (List.range' 1 q).countP (fun z => decide (t₀ - reach q t₀ ≤ z ∧ z < t₀)) =
        (List.range' 1 q).countP (fun z => decide (t₀ - reach q t₀ ≤ z ∧ z ≤ t₀ - 1)) :=
      List.countP_congr fun z hz => by
        rw [List.mem_range'_1] at hz
        simp only [decide_eq_true_eq]; omega
    rw [e, countP_range'_interval]
    omega
  rw [List.countP_append, List.countP_append, List.countP_reverse, List.countP_map] at hall
  have e0 : [t₀].countP (fun z => decide (t₀ - reach q t₀ ≤ z ∧ z < t₀)) = 0 := by simp
  have e1 : x.countP ((fun z => decide (t₀ - reach q t₀ ≤ z ∧ z < t₀)) ∘ sig q ν) =
      x.countP (fun z => decide (t₀ < z ∧ z ≤ t₀ + reach q t₀)) :=
    List.countP_congr fun z hz => by
      simp only [Function.comp, decide_eq_true_eq]
      exact sig_left_iff hν ht0 hfix (hb z hz)
  rw [e0, e1] at hall
  omega

/-- For odd `q`: a palindromic chain needs `ν ≡ 1 (mod 4)` or `q - ν ≡ 1 (mod 4)`. -/
theorem palin_mod_four {q ν t₀ : Nat} (hq : q % 2 = 1) (hν : ν < q) {x : List Nat}
    (hf : IsFoldSeq q (x ++ [t₀] ++ (x.map (sig q ν)).reverse)) (hfix : sig q ν t₀ = t₀)
    (hmid : SemiStep q x t₀) : ν % 4 = 1 ∨ (q - ν) % 4 = 1 := by
  have h := palin_reach_even hν hf hfix hmid
  have ht0 : 1 ≤ t₀ ∧ t₀ ≤ q := (mem_range'_of_perm hf).1 (by simp)
  rw [sig_eq hν ht0] at hfix
  unfold reach at h
  split_ifs at hfix <;> omega

/-- A good sequence fixed by `σ` up to reversal is a palindromic chain: the obstruction
applies to every `π` with `σ ∘ π = reverse π`. -/
theorem palin_goodL_mod_four {q ν : Nat} (hq : q % 2 = 1) (hν : ν < q) {π : List Nat}
    (hπ : GoodL q ν π) (hrev : π.map (sig q ν) = π.reverse) :
    ν % 4 = 1 ∨ (q - ν) % 4 = 1 := by
  obtain ⟨hf, hs, -⟩ := hπ
  have hlen : π.length = q := hf.length_eq.trans (by simp)
  set k := q / 2 with hk
  have hkl : k < π.length := by omega
  set x := π.take k with hx
  set t₀ := π[k] with ht
  -- `π = x ++ [t₀] ++ rest`
  have hsplit : π = x ++ [t₀] ++ π.drop (k + 1) := by
    rw [hx, ht, List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hkl,
      List.take_append_drop]
  have hrest : π.drop (k + 1) = (x.map (sig q ν)).reverse := by
    have e1 : (π.map (sig q ν)).take k = x.map (sig q ν) := by rw [hx, List.map_take]
    rw [hrev] at e1
    have e2 : π.reverse.take k = (π.drop (k + 1)).reverse := by
      conv_lhs => rw [hsplit]
      rw [List.reverse_append, List.take_append_of_le_length (by simp; omega)]
      rw [List.take_of_length_le (by simp; omega)]
    rw [← List.reverse_reverse (π.drop (k + 1)), ← e2, e1]
  have hfix : sig q ν t₀ = t₀ := by
    have e : (π.map (sig q ν))[k]'(by simp; omega) = π.reverse[k]'(by simp; omega) := by
      simp only [hrev]
    rw [List.getElem_map, List.getElem_reverse] at e
    rw [ht, e]
    congr 1; omega
  have hmid : SemiStep q x t₀ := by
    have := hs k hkl
    simpa [hx, ht] using this
  rw [hrest] at hsplit
  rw [hsplit] at hf
  exact palin_mod_four hq hν hf hfix hmid

/-- In particular there is no palindromic good sequence for odd `q` and `ν ≡ 3 (mod 4)`. -/
theorem no_palin_three {q ν : Nat} (hq : q % 2 = 1) (hν : ν < q) (h3 : ν % 4 = 3)
    {π : List Nat} (hπ : GoodL q ν π) : π.map (sig q ν) ≠ π.reverse := by
  intro hrev
  have := palin_goodL_mod_four hq hν hπ hrev
  omega

end SuperExp10
end Folds
