/-
  EvmAsm.Evm64.DivMod.Spec.N2V4ConcretePostBridge

  N=2 V4 bridge from `fullDivN2UnifiedPostNoX1V4` (with exact caller `x1`)
  to `divConcretePostNoX1ExactRegsFrame` plus the v4 scratch cell.

  Mirrors `fullDivN3UnifiedPostNoX1V4_frame_to_divConcretePostNoX1ExactRegsFrame_scratch`
  in N3V4StackPre.lean:721–836 for the n=2 case.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4Families
import EvmAsm.Evm64.DivMod.Spec.CallablePost
import EvmAsm.Evm64.DivMod.Spec.Dispatcher

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

theorem fullDivN2UnifiedPostNoX1V4_frame_to_divConcretePostNoX1ExactRegsFrame_scratch
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1V4 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word)) :
    ∀ h,
      (fullDivN2UnifiedPostNoX1V4 bltu_2 bltu_1 bltu_0 sp base
        a0 a1 a2 a3 b0 b1 b2 b3 retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      (divConcretePostNoX1ExactRegsFrame sp a b
        (signExtend12 4095) raVal
        (signExtend12 (0 : BitVec 12) - fullDivN2Shift b1)
        (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R1V4 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word)
        (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R1V4 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word)
        (((fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat) % 64)))
        (((fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat) % 64)))
        (((fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            (((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat) % 64)))
        ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN2Shift b1).toNat % 64))
        (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (fullDivN2R1V4 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2
        (0 : Word)
        (fullDivN2Shift b1) (2 : Word) (0 : Word)
        (if bltu_0 then (base + div128CallRetOff)
          else if bltu_1 then (base + div128CallRetOff)
          else if bltu_2 then (base + div128CallRetOff) else retMem)
        (if bltu_0 then (fullDivN2NormV b0 b1 b2 b3).2.1
          else if bltu_1 then (fullDivN2NormV b0 b1 b2 b3).2.1
          else if bltu_2 then (fullDivN2NormV b0 b1 b2 b3).2.1 else dMem)
        (if bltu_0 then divKTrialCallV4DLo (fullDivN2NormV b0 b1 b2 b3).2.1
          else if bltu_1 then divKTrialCallV4DLo (fullDivN2NormV b0 b1 b2 b3).2.1
          else if bltu_2 then divKTrialCallV4DLo (fullDivN2NormV b0 b1 b2 b3).2.1 else dloMem)
        (if bltu_0 then
            divKTrialCallV4Un0 (fullDivN2R1V4 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
          else if bltu_1 then
            divKTrialCallV4Un0 (fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
          else if bltu_2 then
            divKTrialCallV4Un0 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
          else scratchUn0) **
       ((sp + signExtend12 3936) ↦ₘ
        fullDivN2ScratchMemV4 bltu_2 bltu_1 bltu_0
          a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)) h := by
  intro h hq
  -- Normalize hq: expand all @[irreducible] V4 bundles and inline let-bindings.
  simp (config := { zeta := true }) only [fullDivN2UnifiedPostNoX1V4_unfold,
    fullDivN2DenormPostV4_unfold, fullDivN2FrameNoX1V4_unfold,
    fullDivN2ScratchNoX1V4_unfold, denormDivPost_unfold] at hq
  rw [word_add_zero] at hq
  -- Normalize goal: unfold all bundles in one simp pass.
  rw [divConcretePostNoX1ExactRegsFrame_unfold,
      evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.div a b)
        (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R1V4 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
        (0 : Word) hdiv0 hdiv1 hdiv2 hdiv3,
      divScratchValuesCallNoX1_unfold, divScratchValues_unfold]
  xperm_hyp hq

end EvmAsm.Evm64
