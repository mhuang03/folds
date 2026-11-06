import Folds.Residual
open Folds.Residual
-- sanity checks of the definitions on examples (certificates from cert.c)

-- cert.c 301 60 70 : PF o=1 f=0, w1 = (1,1), w2 = (-1,0)
example : RegionPF 301 60 70 := by
  refine Or.inl ⟨31476 / 1000, 26965 / 1000, -6116 / 1000, 1, 1, -1, 0, by norm_num, ?_⟩
  simp only [consZ, famCons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Aff.gap, affU1, affU2, affL1, affL2, affC, Aff.eval]
  norm_num

-- cert.c 3001 900 901 : SL o=1 f=1 (X0, orientation (u', u)), p = 1, j = 1, w1 = (1,0), w2 = (0,1)
example : RegionSL 3001 900 901 := by
  refine ⟨1, 1, Or.inr (Or.inl ⟨by norm_num, 1010956 / 1000, 302836 / 1000, 3334 / 1000,
    1, 0, 0, 1, by norm_num, ?_⟩)⟩
  simp only [sliceX0, sliceCons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Aff.eval]
  norm_num
