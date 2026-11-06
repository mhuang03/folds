import Folds.Residual
open Folds.Residual
-- sanity check of the definition on one example (cert.c 301 60 70)
example : RegionPF 301 60 70 := by
  refine Or.inl ⟨31476 / 1000, 26965 / 1000, -6116 / 1000, 1, 1, -1, 0, by norm_num, ?_⟩
  simp only [consZ, famCons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Aff.gap, affU1, affU2, affL1, affL2, affC, Aff.eval]
  norm_num
