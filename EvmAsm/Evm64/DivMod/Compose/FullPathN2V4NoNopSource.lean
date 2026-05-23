/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNopSource

  Source-level v4/no-NOP wrappers for the n=2 DIV loop.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- First n=2 call iteration from the callable-ready v4 loop source, preserving
    concrete `x1` and carrying the j=1/j=0 source atoms as a frame. -/
theorem divK_loop_n2_call_j2_from_source_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2CallScratchNoX1 sp base (2 : Word)
        (divKTrialCallV4QHat u2 u1 v1)
        (divKTrialCallV4DLo v1)
        (divKTrialCallV4Un0 u1)
        (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop ** (.x1 ↦ᵣ raVal)) **
        ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig1) **
         ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
         (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))) := by
  have J2 := divK_loop_body_n2_call_j2_exact_loopIterScratch_v4_noNop sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu hcarry2_nz
  have J2f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig1) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      have hp' := loopN2PreWithScratchV4NoX1_to_call_j2_pre
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem h hp
      xperm_hyp hp')
    (fun h hp => hp)
    J2f

/-- First n=2 max iteration from the callable-ready v4 loop source, preserving
    concrete `x1`, scratch, and the j=1/j=0 source atoms as a frame. -/
theorem divK_loop_n2_max_j2_from_source_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu : ¬BitVec.ult u2 v1)
    (hcarry2_nz : isAddbackCarry2NzN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2Max sp (2 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig1) **
         ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
         (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig0) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))) := by
  have J2 := divK_loop_body_n2_max_j2_exact_loopIterScratch_v4_noNop sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old raVal
    retMem dMem dloMem scratchUn0 scratchMem hbltu hcarry2_nz
  have J2f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig1) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q1Old)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J2
  exact cpsTripleWithin_weaken
    (fun h hp => by
      have hp' := loopN2PreWithScratchV4NoX1_to_max_j2_pre
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem h hp
      xperm_hyp hp')
    (fun h hp => hp)
    J2f

/-- Full n=2 call×call prefix from the callable-ready v4 loop source,
    preserving concrete `x1` and carrying the j=2 stored u4/q atoms plus the
    j=0 source atoms. -/
theorem divK_loop_n2_call_call_from_source_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : BitVec.ult u2 v1)
    (hcarry2_nz_2 : loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_1 :
      BitVec.ult
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hcarry2_nz_1 :
      let r2 := iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3
        u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) :
    let r2 := iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let qHat1 := divKTrialCallV4QHat r2.2.2.1 r2.2.1 v1
    let dLo1 := divKTrialCallV4DLo v1
    let divUn01 := divKTrialCallV4Un0 r2.2.1
    let scratch2 := divKTrialCallV4ScratchOut u2 u1 v1 scratchMem
    let scratch1 := divKTrialCallV4ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
    let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
    let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
    let uBase0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (224 + 224) (base + loopBodyOff) (base + loopBodyOff)
      (divCode_noNop_v4 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN2CallScratchNoX1 sp base (1 : Word)
        qHat1 dLo1 divUn01 scratch1
        v0 v1 v2 v3 u0Orig1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 **
        (.x1 ↦ᵣ raVal)) **
        (((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) **
          (qAddr2 ↦ₘ r2.1)) **
         (((uBase0 + signExtend12 0) ↦ₘ u0Orig0) **
          (qAddr0 ↦ₘ q0Old)))) := by
  intro r2 qHat1 dLo1 divUn01 scratch2 scratch1 uBase2 qAddr2 uBase0 qAddr0
  have J2 := divK_loop_n2_call_j2_from_source_exact_loopIterScratch_v4_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu_2 hcarry2_nz_2
  subst r2
  subst qHat1
  subst dLo1
  subst divUn01
  subst scratch2
  subst scratch1
  subst uBase2
  subst qAddr2
  subst uBase0
  subst qAddr0
  have J1 := divK_loop_body_n2_call_j1_exact_loopIterScratch_v4_noNop sp base
    (2 : Word)
    ((2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (divKTrialCallV4QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q1Old raVal
    (base + div128CallRetOff) v1 (divKTrialCallV4DLo v1)
    (divKTrialCallV4Un0 u1) (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
    halign hbltu_1 hcarry2_nz_1
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
      ((sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV4QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).1)) **
     (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN2CallScratchNoX1_j2_to_call_j1_pre
      sp base (divKTrialCallV4QHat u2 u1 v1) (divKTrialCallV4DLo v1)
      (divKTrialCallV4Un0 u1) (divKTrialCallV4ScratchOut u2 u1 v1 scratchMem)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q1Old q0Old raVal)
    J2 J1f

end EvmAsm.Evm64
