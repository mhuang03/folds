import Folds.LabellingSAT
import Folds.LabellingSAT3Certs

/-!
# The labelling conjecture for three labels, for every `N`

`bound_of_noLab` with `K = 21`: the left-half-only problem with three labels is infeasible at
`K = 21` (`noLab_L21_3`), and the full problem at `N = 15, …, 20` (`noLab_F15_3`, …); all seven
are kernel-checked LRAT certificates (`Folds/LabellingSAT3Certs.lean`).

* `admissible_le_three`: an admissible labelling with `t ≤ 3` labels has `N ≤ 2^(t+1) - 2`.
* `lds_exact_le_three`, `descents_exact_le_three`: for semi-symmetric fold sequences,
  `min(⌊log₂(N+1)⌋, 4) ≤ des a + 1` (and `≤ t` for every level labelling with `t` labels,
  e.g. `t = LDS`).
-/

namespace Folds
namespace LSAT

/-! ## The seven checks, assembled from the kernel-checked certificates -/

theorem noLab_L21_3 : NoLab true 21 3 :=
  cert_L21_3.sound_of_refutes cert_L21_3_init <|
    cert_L21_3.refutes_seg cert_L21_3_0 <|
    cert_L21_3.refutes_end cert_L21_3_end

theorem noLab_F15_3 : NoLab false 15 3 :=
  cert_F15_3.sound_of_refutes cert_F15_3_init <|
    cert_F15_3.refutes_seg cert_F15_3_0 <|
    cert_F15_3.refutes_end cert_F15_3_end

theorem noLab_F16_3 : NoLab false 16 3 :=
  cert_F16_3.sound_of_refutes cert_F16_3_init <|
    cert_F16_3.refutes_seg cert_F16_3_0 <|
    cert_F16_3.refutes_end cert_F16_3_end

theorem noLab_F17_3 : NoLab false 17 3 :=
  cert_F17_3.sound_of_refutes cert_F17_3_init <|
    cert_F17_3.refutes_seg cert_F17_3_0 <|
    cert_F17_3.refutes_end cert_F17_3_end

theorem noLab_F18_3 : NoLab false 18 3 :=
  cert_F18_3.sound_of_refutes cert_F18_3_init <|
    cert_F18_3.refutes_seg cert_F18_3_0 <|
    cert_F18_3.refutes_end cert_F18_3_end

theorem noLab_F19_3 : NoLab false 19 3 :=
  cert_F19_3.sound_of_refutes cert_F19_3_init <|
    cert_F19_3.refutes_seg cert_F19_3_0 <|
    cert_F19_3.refutes_end cert_F19_3_end

theorem noLab_F20_3 : NoLab false 20 3 :=
  cert_F20_3.sound_of_refutes cert_F20_3_init <|
    cert_F20_3.refutes_seg cert_F20_3_0 <|
    cert_F20_3.refutes_end cert_F20_3_end

/-! ## Three labels -/

theorem admBound_three : AdmBound 3 := by
  refine admBound_succ admBound_two (fun hadm ht => ?_)
  exact bound_of_noLab 3 21 noLab_L21_3
    (noLab_cons noLab_F15_3 <| noLab_cons noLab_F16_3 <| noLab_cons noLab_F17_3 <|
      noLab_cons noLab_F18_3 <| noLab_cons noLab_F19_3 <| noLab_cons noLab_F20_3 noLab_nil)
    hadm ht

end LSAT

/-- **The conjecture for at most three labels**, for every `N`. -/
theorem admissible_le_three {N t : Nat} {c : Nat → Nat} (htt : t ≤ 3) (hadm : Admissible N c)
    (ht : ∀ x, 1 ≤ x → x ≤ N → c x < t) : N ≤ 2 ^ (t + 1) - 2 :=
  LSAT.admBound_three htt hadm ht

/-- **Level labellings, at most three levels.**  If `c` increases strictly along inversions of a
semi-symmetric fold sequence and takes values `< t`, then `min(⌊log₂(N+1)⌋, 4) ≤ t`. -/
theorem lds_exact_le_three {N : Nat} {a : List Nat} (hf : IsFoldSeq N a) (h : SemiSymmetric N a)
    (c : Nat → Nat) {t : Nat}
    (hc : ∀ i j (hij : i < j) (hj : j < a.length),
      a[j] < a[i]'(Nat.lt_trans hij hj) → c a[i] < c a[j])
    (ht : ∀ x ∈ a, c x < t) : min (Nat.log 2 (N + 1)) 4 ≤ t :=
  LSAT.lds_of_bound LSAT.admBound_three hf h c hc ht

/-- **Descents.**  A semi-symmetric fold sequence has `des a + 1 ≥ min(⌊log₂(N+1)⌋, 4)`:
`des a ≥ ⌊log₂(N+1)⌋ - 1` for `N ≤ 30`, and `des a ≥ 3` for every `N ≥ 15`. -/
theorem descents_exact_le_three {N : Nat} {a : List Nat} (hf : IsFoldSeq N a)
    (h : SemiSymmetric N a) : min (Nat.log 2 (N + 1)) 4 ≤ des a + 1 :=
  LSAT.descents_of_bound LSAT.admBound_three hf h

end Folds
