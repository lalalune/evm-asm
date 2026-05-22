/-
  EvmAsm.Evm64.DivMod.Compose.LoopN3ExactX1

  Exact-`x1` frame wrappers for the n=3 no-NOP loop body.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The n=3 no-NOP loop body does not consume the caller's return address.
    This wrapper carries exact `x1` through the existing unified loop theorem,
    instead of weakening it to `regOwn .x1` in outer composition layers. -/
theorem evm_div_n3_loop_unified_inst_noNop_exact_x1_frame
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift b0' b1' b2' b3' u0 u1 u2 u3 u4 : Word)
    (v10Old v11Old jMem : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u4 b2')
    (hbltu_0 : bltu_0 = BitVec.ult
      (iterN3 bltu_1 b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2')
    (hcarry2 : Carry2NzAll b0' b1' b2' b3') :
    cpsTripleWithin 404 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN3PreWithScratch sp jMem (3 : Word) shift u0 v10Old v11Old antiShift
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word)
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPost bltu_1 bltu_0 sp base
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_frameR (.x1 ↦ᵣ raVal) (by pcFree)
    (evm_div_n3_loop_unified_inst_noNop bltu_1 bltu_0 sp base
      shift antiShift b0' b1' b2' b3' u0 u1 u2 u3 u4
      v10Old v11Old jMem retMem dMem dloMem scratch_un0
      halign hbltu_1 hbltu_0 hcarry2)

end EvmAsm.Evm64
