/-
  EvmAsm.Evm64.DivMod.Compose.FullPathV5DivUnconditional

  The v5 DIV unconditional stack spec, with NO remaining lane hypothesis.

  `evm_div_stack_spec_unconditional_v5_div_of_n4lane` (#7570, bead `.10.2`) had
  reduced the v5 DIV spec to a single open obligation — the n=4 lane.  That lane
  is now proven from the n=4 shape alone by `evm_div_n4_lane_of_shape_native`
  (#7668), so feeding it in (reconciling `N4ShapeIs b` to `b.getLimbN 3 ≠ 0` via
  `N4ShapeIs.b3_ne_zero`) discharges the last hypothesis and yields the fully
  unconditional v5 DIV dispatch triple over `divCode_noNop_v5` with the uniform
  dispatch shift `divDispatchShiftX2 b` in `x2`.

  Bead `evm-asm-wbc4i.10.2`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathV5DivAssembly
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneOfShapeNative
import EvmAsm.Evm64.DivMod.Spec.DivisorShapeLimbProjections

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v5 DIV unconditional spec: with the uniform shift `divDispatchShiftX2 b`
    in `x2`, the full dispatch triple holds for every divisor shape, with no
    remaining lane hypothesis (the n=4 lane is discharged from shape via
    `evm_div_n4_lane_of_shape_native`). -/
theorem evm_div_stack_spec_unconditional_v5_div
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  refine evm_div_stack_spec_unconditional_v5_div_of_n4lane sp base a b
    raVal v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem halign ?lane_n4
  intro hshape
  exact evm_div_n4_lane_of_shape_native sp base a b
    raVal v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
    (N4ShapeIs.b3_ne_zero hshape) halign

end EvmAsm.Evm64
