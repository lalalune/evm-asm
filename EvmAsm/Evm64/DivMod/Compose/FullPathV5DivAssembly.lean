/-
  EvmAsm.Evm64.DivMod.Compose.FullPathV5DivAssembly

  The v5 DIV unconditional spec reduced to the single remaining n4 lane:
  instantiates the 5-lane scaffold `evm_div_stack_spec_unconditional_of_lanes_v5_div`
  with the shape-uniform shift `v2 := divDispatchShiftX2 b` and discharges the four
  proven lanes (bzero / n1 / n2 / n3) from `evm_div_bzero_lane_v5` and the
  `NkShapeIs`-form stack specs (#7567/#7568), reconciling the uniform `v2` to each
  lane's pinned `clzResult (top limb)` via `divDispatchShiftX2_n{1,2,3,4}` (#7569).

  The result `evm_div_stack_spec_unconditional_v5_div_of_n4lane` takes ONLY the n4
  lane as a hypothesis: once the n4 lane (bead `.8.2.2`) is proven, the full DIV
  stack spec follows immediately.  Bead `evm-asm-wbc4i.10.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div
import EvmAsm.Evm64.DivMod.Spec.DivDispatchShift
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Bzero
import EvmAsm.Evm64.DivMod.Compose.FullPathN1N2V5StackSpecUnconditional
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5StackSpecUnconditional

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v5 DIV unconditional spec, reduced to the n4 lane: with the uniform shift
    `divDispatchShiftX2 b` in `x2`, the full dispatch triple holds for every divisor
    shape, given only the n4 lane. -/
theorem evm_div_stack_spec_unconditional_v5_div_of_n4lane
    (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (lane_n4 : N4ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
          ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostV5 sp a b)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        (divDispatchShiftX2 b) v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  refine evm_div_stack_spec_unconditional_of_lanes_v5_div sp base a b
    (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal (divDispatchShiftX2 b) v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
    ?bzero ?n1 ?n2 ?n3 ?n4
  case bzero =>
    intro hbz
    exact evm_div_bzero_lane_v5 sp base a b
      (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal (divDispatchShiftX2 b) v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem hbz
  case n1 =>
    intro hshape
    rw [divDispatchShiftX2_n1 hshape]
    exact evm_div_n1_stack_spec_unconditional sp base a b raVal v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
      hshape halign
  case n2 =>
    intro hshape
    rw [divDispatchShiftX2_n2 hshape]
    exact evm_div_n2_stack_spec_unconditional sp base a b raVal v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
      hshape halign
  case n3 =>
    intro hshape
    rw [divDispatchShiftX2_n3 hshape]
    exact evm_div_n3_stack_spec_unconditional sp base a b raVal v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem
      hshape halign
  case n4 =>
    intro hshape
    rw [divDispatchShiftX2_n4 hshape]
    exact lane_n4 hshape

end EvmAsm.Evm64
