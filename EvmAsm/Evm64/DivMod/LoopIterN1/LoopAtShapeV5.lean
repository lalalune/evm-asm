/-
  EvmAsm.Evm64.DivMod.LoopIterN1.LoopAtShapeV5

  The v5 n=1 full loop instantiated at the normalized inputs, with all eight
  per-digit `bltu`/no-borrow hypotheses discharged from the divisor shape.  This
  is `divK_loop_n1_call_unified_v5` (the complete all-call loop) specialized to
  `v = fullDivN1NormV b`, `u = fullDivN1NormU a b`, where the shape lemmas
  (#7280 bltu, #7281 no-borrow) + the bridge equations (#7282) prove every digit
  takes the call path with no borrow.  The code-side core of the n=1 lane wrapper.
  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.LoopAtShapeBridgeV5
import EvmAsm.Evm64.DivMod.Spec.N1V5LaneBltu
import EvmAsm.Evm64.DivMod.Spec.N1V5LaneHborrow

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem divK_loop_n1_call_unified_v5_of_shape
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    cpsTripleWithin 632 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopN1UnifiedPreV5 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0 scratchMem)
      (loopN1UnifiedPostV5 sp base
        (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1 scratchMem) := by
  refine divK_loop_n1_call_unified_v5_spec_within_noNop sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).1
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0 scratchMem base halign
    ?hb3 ?hb2 ?hb1 ?hb0 ?ho3 ?ho2 ?ho1 ?ho0
  case hb3 => exact n1v5_lane_bltu_3_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case hb2 =>
    rw [← fullDivN1R3V5_eq_iterN1Call_v5]
    exact n1v5_lane_bltu_2_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case hb1 =>
    rw [fullN1S2_eq_fullDivN1R2V5]
    exact n1v5_lane_bltu_1_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case hb0 =>
    rw [fullN1S1_eq_fullDivN1R1V5]
    exact n1v5_lane_bltu_0_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case ho3 => exact n1v5_lane_hborrow_3_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case ho2 =>
    rw [← fullDivN1R3V5_eq_iterN1Call_v5]
    exact n1v5_lane_hborrow_2_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case ho1 =>
    rw [fullN1S2_eq_fullDivN1R2V5]
    exact n1v5_lane_hborrow_1_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  case ho0 =>
    rw [fullN1S1_eq_fullDivN1R1V5]
    exact n1v5_lane_hborrow_0_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz

end EvmAsm.Evm64
