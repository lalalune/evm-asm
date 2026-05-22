/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNopMaxCall

  Split-out n=3 max×call exact-source theorem for the v4 no-NOP loop.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Full n=3 max×call path from the callable-ready v4 loop source, preserving
    concrete `x1`, scratch, and the j=1 stored u4/q atoms. -/
theorem divK_loop_n3_max_call_from_source_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hcarry2_nz_1 : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r1.2.2.2.1 v2)
    (hcarry2_nz_0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (152 + 224) (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN3CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat r1.2.2.2.1 r1.2.2.1 v2)
        (divKTrialCallV4DLo v2)
        (divKTrialCallV4Un0 r1.2.2.1)
        (divKTrialCallV4ScratchOut r1.2.2.2.1 r1.2.2.1 v2 scratchMem)
        v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
        (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1))) := by
  intro r1 uBase1 qAddr1
  have J1 := divK_loop_body_n3_max_j1_exact_loopIterScratch_v4_noNop sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old raVal
    retMem dMem dloMem scratchUn0 scratchMem hbltu_1 hcarry2_nz_1
  subst r1
  subst uBase1
  subst qAddr1
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  have J0 := divK_loop_body_n3_call_j0_exact_loopIterScratch_v4_noNop sp base
    (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem
    halign hbltu_0 hcarry2_nz_0
  have J0f := cpsTripleWithin_frameR
    (((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN3MaxScratchX1_j1_to_call_j0_pre
      sp retMem dMem dloMem scratchUn0 scratchMem
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q0Old raVal)
    (cpsTripleWithin_weaken
      (loopN3PreWithScratchV4NoX1_to_max_j1_pre
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem)
      (fun h hp => hp)
      J1f)
    J0f

end EvmAsm.Evm64
