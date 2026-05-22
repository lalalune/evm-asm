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

/-- Max×max n=3 no-NOP loop path with caller `x1` kept as a concrete
    register atom. This is the first non-vacuous no-`x1` source path: unlike
    `loopN3PreWithScratch`, `loopN3PreWithScratchNoX1` does not already own
    `x1`. -/
theorem divK_loop_n3_max_max_spec_within_noNop_exact_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 raVal : Word)
    (base : Word)
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hbltu_0 : ¬BitVec.ult (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2 : Carry2NzAll v0 v1 v2 v3) :
    cpsTripleWithin 304 (base + loopBodyOff) (base + denormOff) (divCode_noNop base)
      (loopN3PreWithScratchNoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 ** (.x1 ↦ᵣ raVal))
      (loopN3MaxPost sp v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratch_un0) ** (.x1 ↦ᵣ raVal)) := by
  have hMM := divK_loop_n3_max_max_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
    base hbltu_1 hbltu_0 hcarry2
  have hMMF := cpsTripleWithin_frameR
    ((sp + signExtend12 3968 ↦ₘ retMem) **
     (sp + signExtend12 3960 ↦ₘ dMem) **
     (sp + signExtend12 3952 ↦ₘ dloMem) **
     (sp + signExtend12 3944 ↦ₘ scratch_un0) ** (.x1 ↦ᵣ raVal))
    (by pcFree) hMM
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopN3PreWithScratchNoX1 at hp
      xperm_hyp hp)
    (fun h hp => by xperm_hyp hp)
    hMMF

end EvmAsm.Evm64
