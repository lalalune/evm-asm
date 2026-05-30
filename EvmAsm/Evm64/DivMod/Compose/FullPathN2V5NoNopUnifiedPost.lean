/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopUnifiedPost

  The unified postcondition `loopN2UnifiedPostV5NoX1` for the n=2 v5 loop: an
  8-arm match over `bltu_2 × bltu_1 × bltu_0` selecting the per-combo final
  postcondition.  Mirror of `loopN2UnifiedPostV4NoX1`
  (FullPathN2V4NoNopLoopUnified) with the v5 trial accessors and the v5
  per-prefix aliases (cmc/mcm/mmm reuse r1TMM/r1MTT/r1MMT).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopDispatch
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboCCC
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboCCM

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Unified n=2 v5 loop postcondition, selected by the bltu path. -/
def loopN2UnifiedPostV5NoX1 (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  let uBase2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let qAddr2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  match bltu_2, bltu_1, bltu_0 with
  | true, true, true =>
    let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1CCCN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch2 := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
    let scratch1 := divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
    let scratch0 := divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 v1 scratch1
    (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV5QHat r1.2.2.1 r1.2.1 v1) (divKTrialCallV5DLo v1)
      (divKTrialCallV5Un0 r1.2.1) scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | true, true, false =>
    let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1CCCN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch2 := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
    let scratch1 := divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v1 scratch2
    (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
      (sp + signExtend12 3960 ↦ₘ v1) **
      (sp + signExtend12 3952 ↦ₘ (divKTrialCallV5DLo v1)) **
      (sp + signExtend12 3944 ↦ₘ (divKTrialCallV5Un0 r2.2.1)) **
      (sp + signExtend12 3936 ↦ₘ scratch1)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | true, false, true =>
    let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1TMMN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch2 := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
    let scratch0 := divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 v1 scratch2
    (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV5QHat r1.2.2.1 r1.2.1 v1) (divKTrialCallV5DLo v1)
      (divKTrialCallV5Un0 r1.2.1) scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | true, false, false =>
    let r2 := r2CCCN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1TMMN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch2 := divKTrialCallV5ScratchOut u2 u1 v1 scratchMem
    (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
      (sp + signExtend12 3960 ↦ₘ v1) **
      (sp + signExtend12 3952 ↦ₘ (divKTrialCallV5DLo v1)) **
      (sp + signExtend12 3944 ↦ₘ (divKTrialCallV5Un0 u1)) **
      (sp + signExtend12 3936 ↦ₘ scratch2)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | false, true, true =>
    let r2 := r2MTTN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1MTTN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch1 := divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v1 scratchMem
    let scratch0 := divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 v1 scratch1
    (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV5QHat r1.2.2.1 r1.2.1 v1) (divKTrialCallV5DLo v1)
      (divKTrialCallV5Un0 r1.2.1) scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | false, true, false =>
    let r2 := r2MTTN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1MTTN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch1 := divKTrialCallV5ScratchOut r2.2.2.1 r2.2.1 v1 scratchMem
    (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
      (sp + signExtend12 3960 ↦ₘ v1) **
      (sp + signExtend12 3952 ↦ₘ (divKTrialCallV5DLo v1)) **
      (sp + signExtend12 3944 ↦ₘ (divKTrialCallV5Un0 r2.2.1)) **
      (sp + signExtend12 3936 ↦ₘ scratch1)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | false, false, true =>
    let r2 := r2MMTN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1MMTN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    let scratch0 := divKTrialCallV5ScratchOut r1.2.2.1 r1.2.1 v1 scratchMem
    (loopIterPostN2CallScratchNoX1 sp base (0 : Word)
      (divKTrialCallV5QHat r1.2.2.1 r1.2.1 v1) (divKTrialCallV5DLo v1)
      (divKTrialCallV5Un0 r1.2.1) scratch0
      v0 v1 v2 v3 u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))
  | false, false, false =>
    let r2 := r2MMTN2V5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let r1 := r1MMTN2V5 v0 v1 v2 v3 u0Orig1 u0 u1 u2 u3 uTop
    (loopIterPostN2Max sp (0 : Word) v0 v1 v2 v3
      u0Orig0 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
      (sp + signExtend12 3968 ↦ₘ retMem) **
      (sp + signExtend12 3960 ↦ₘ dMem) **
      (sp + signExtend12 3952 ↦ₘ dloMem) **
      (sp + signExtend12 3944 ↦ₘ scratchUn0) **
      (sp + signExtend12 3936 ↦ₘ scratchMem)) **
    (((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) ** (qAddr1 ↦ₘ r1.1)) **
     ((uBase2 + signExtend12 4064 ↦ₘ r2.2.2.2.2.2) ** (qAddr2 ↦ₘ r2.1)))

end EvmAsm.Evm64
