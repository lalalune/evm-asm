/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopLoopSelected

  v5/no-NOP n=3 LoopSelected instantiation: `evm_div_n3_loop_unified_inst_noNop_exact_x1_v5_selectedCarry`
  — the explicit-normalized-value form of the unified two-iteration loop dispatch
  (#7520 selectedCarry), plugging the preloop's normalized divisor/window
  (`shift`/`antiShift`/`b0'..b3'`/`u1..u4`, `j = 3`, `uTop = 0`) into the
  callable-ready loop source `loopN3PreWithScratchV4NoX1` and exposing
  `loopN3UnifiedPostV5NoX1`.  Mirror of the v4 analog
  (`FullPathN3V4NoNopMaxCall` :683) over `divCode_noNop_v5`.  Bead
  `evm-asm-wbc4i.9.3.3.2.5`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopUnified

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Selected-carry instantiation of the v5 no-NOP exact-`x1` n=3 loop with
    explicit normalized values (the form the preloop composition consumes). -/
theorem evm_div_n3_loop_unified_inst_noNop_exact_x1_v5_selectedCarry
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (shift antiShift b0' b1' b2' b3' u0 u1 u2 u3 u4 : Word)
    (v10Old v11Old jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 = BitVec.ult u4 b2')
    (hbltu_0 : bltu_0 =
      match bltu_1 with
      | false => BitVec.ult (iterN3Max b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2'
      | true =>
        BitVec.ult
          (iterWithDoubleAddback (divKTrialCallV5QHat u4 u3 b2')
            b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)).2.2.2.1 b2')
    (hcarry2_j1 :
      if bltu_1 then
        loopBodyN3CallAddbackCarry2NzV5 b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)
      else
        isAddbackCarry2NzN3Max b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word))
    (hcarry2_j0 :
      match bltu_1 with
      | false =>
        let r1 := iterN3Max b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV5 b0' b1' b2' b3'
            u0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max b0' b1' b2' b3'
            u0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      | true =>
        let r1 := iterWithDoubleAddback (divKTrialCallV5QHat u4 u3 b2')
          b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word)
        if bltu_0 then
          loopBodyN3CallAddbackCarry2NzV5 b0' b1' b2' b3'
            u0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
        else
          isAddbackCarry2NzN3Max b0' b1' b2' b3'
            u0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    cpsTripleWithin 468 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
      (loopN3PreWithScratchV4NoX1 sp jMem (3 : Word) shift u0 v10Old v11Old antiShift
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN3UnifiedPostV5NoX1 bltu_1 bltu_0 sp base
        b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_1 <;> cases bltu_0
  · exact divK_loop_n3_unified_from_source_exact_loopIterScratch_v5_noNop_selectedCarry
      false false sp base jMem (3 : Word) shift u0 v10Old v11Old antiShift
      b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word) raVal
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu_1 hbltu_0 hcarry2_j1 hcarry2_j0
  · exact divK_loop_n3_unified_from_source_exact_loopIterScratch_v5_noNop_selectedCarry
      false true sp base jMem (3 : Word) shift u0 v10Old v11Old antiShift
      b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word) raVal
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu_1 hbltu_0 hcarry2_j1 hcarry2_j0
  · exact divK_loop_n3_unified_from_source_exact_loopIterScratch_v5_noNop_selectedCarry
      true false sp base jMem (3 : Word) shift u0 v10Old v11Old antiShift
      b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word) raVal
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu_1 hbltu_0 hcarry2_j1 hcarry2_j0
  · exact divK_loop_n3_unified_from_source_exact_loopIterScratch_v5_noNop_selectedCarry
      true true sp base jMem (3 : Word) shift u0 v10Old v11Old antiShift
      b0' b1' b2' b3' u1 u2 u3 u4 (0 : Word) u0 (0 : Word) (0 : Word) raVal
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu_1 hbltu_0 hcarry2_j1 hcarry2_j0

end EvmAsm.Evm64
