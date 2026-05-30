/-
  EvmAsm.Evm64.DivMod.Spec.N2V5IterR2R1Bridge

  Bridges the bundle's loop iterations (`loopN2IterSelectedV5` over the
  `fullDivN2NormV/U` accessors) to the families' per-digit results
  `fullDivN2R2V5` / `fullDivN2R1V5`.  These let the per-digit `_collapse_of_shape`
  / `_step_of_shape` lemmas (stated for `fullDivN2R2V5`/`R1V5`) apply to the
  `r2`/`r1` intermediates that appear inside `loopN2SelectedBorrowCarryV5` at the
  lane level — the glue for the telescope discharge of
  `loopN2SelectedBorrowCarryV5_of_shape`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5IterSelectedEq

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The bundle's j=2 iteration (over NormV/U) equals the families' `fullDivN2R2V5`. -/
theorem loopN2IterSelectedV5_normUV_eq_R2V5
    (bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    loopN2IterSelectedV5 bltu_2
      (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
      (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0 0
      = fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 := by
  simp only [loopN2IterSelectedV5_eq_iterN2V5, fullDivN2R2V5]

/-- The bundle's j=1 iteration (over NormV/U and the R2 outputs) equals the
    families' `fullDivN2R1V5`. -/
theorem loopN2IterSelectedV5_normUV_eq_R1V5
    (bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    loopN2IterSelectedV5 bltu_1
      (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
      (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
      (fullDivN2NormU a0 a1 a2 a3 b1).2.1
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
      = fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 := by
  simp only [loopN2IterSelectedV5_eq_iterN2V5, fullDivN2R1V5]

end EvmAsm.Evm64
