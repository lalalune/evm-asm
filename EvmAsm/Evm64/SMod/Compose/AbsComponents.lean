/-
  EvmAsm.Evm64.SMod.Compose.AbsComponents

  Shared signed-absolute-value component abbreviations for SMOD mod-call
  handoff proofs.
-/

import EvmAsm.Evm64.SMod.Compose.QuadMemBridges
import EvmAsm.Evm64.SMod.Compose.Words

namespace EvmAsm.Evm64.SMod.Compose

abbrev smodAbsSign (top : Word) : Word :=
  top >>> (63 : BitVec 6).toNat

abbrev smodAbsMask (top : Word) : Word :=
  (0 : Word) - smodAbsSign top

abbrev smodAbsSum0 (limb0 top : Word) : Word :=
  (limb0 ^^^ smodAbsMask top) + smodAbsSign top

abbrev smodAbsCarry0 (limb0 top : Word) : Word :=
  if BitVec.ult (smodAbsSum0 limb0 top) (smodAbsSign top) then (1 : Word) else 0

abbrev smodAbsSum1 (limb0 limb1 top : Word) : Word :=
  (limb1 ^^^ smodAbsMask top) + smodAbsCarry0 limb0 top

abbrev smodAbsCarry1 (limb0 limb1 top : Word) : Word :=
  if BitVec.ult (smodAbsSum1 limb0 limb1 top) (smodAbsCarry0 limb0 top) then
    (1 : Word)
  else
    0

abbrev smodAbsSum2 (limb0 limb1 limb2 top : Word) : Word :=
  (limb2 ^^^ smodAbsMask top) + smodAbsCarry1 limb0 limb1 top

abbrev smodAbsCarry2 (limb0 limb1 limb2 top : Word) : Word :=
  if BitVec.ult (smodAbsSum2 limb0 limb1 limb2 top)
      (smodAbsCarry1 limb0 limb1 top) then
    (1 : Word)
  else
    0

abbrev smodAbsSum3 (limb0 limb1 limb2 top : Word) : Word :=
  (top ^^^ smodAbsMask top) + smodAbsCarry2 limb0 limb1 limb2 top

theorem smodAbsDividendWord_eq_components
    (limb0 limb1 limb2 top : Word) :
    smodAbsDividendWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => smodAbsSum0 limb0 top
        | 1 => smodAbsSum1 limb0 limb1 top
        | 2 => smodAbsSum2 limb0 limb1 limb2 top
        | 3 => smodAbsSum3 limb0 limb1 limb2 top := by
  rfl

theorem smodAbsDivisorWord_eq_components
    (limb0 limb1 limb2 top : Word) :
    smodAbsDivisorWord limb0 limb1 limb2 top =
      EvmWord.fromLimbs fun i : Fin 4 =>
        match i with
        | 0 => smodAbsSum0 limb0 top
        | 1 => smodAbsSum1 limb0 limb1 top
        | 2 => smodAbsSum2 limb0 limb1 limb2 top
        | 3 => smodAbsSum3 limb0 limb1 limb2 top := by
  rfl

theorem smodAbsDividendWord_evmWordIs_sp_components_smodOffsets
    (sp limb0 limb1 limb2 top : Word) :
    evmWordIs sp (smodAbsDividendWord limb0 limb1 limb2 top) =
      (((sp + EvmAsm.Rv64.signExtend12 (0 : BitVec 12)) ↦ₘ smodAbsSum0 limb0 top) **
       ((sp + EvmAsm.Rv64.signExtend12 (8 : BitVec 12)) ↦ₘ
         smodAbsSum1 limb0 limb1 top) **
       ((sp + EvmAsm.Rv64.signExtend12 (16 : BitVec 12)) ↦ₘ
         smodAbsSum2 limb0 limb1 limb2 top) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDividendTopLimbOff) ↦ₘ
         smodAbsSum3 limb0 limb1 limb2 top)) := by
  rw [smodAbsDividendWord_eq_components]
  exact (evmWordIs_eq_quadMem_smodDividend
    sp (smodAbsSum0 limb0 top) (smodAbsSum1 limb0 limb1 top)
    (smodAbsSum2 limb0 limb1 limb2 top) (smodAbsSum3 limb0 limb1 limb2 top)).symm

theorem smodAbsDivisorWord_evmWordIs_sp32_components_smodOffsets
    (sp limb0 limb1 limb2 top : Word) :
    evmWordIs (sp + 32) (smodAbsDivisorWord limb0 limb1 limb2 top) =
      (((sp + EvmAsm.Rv64.signExtend12 (32 : BitVec 12)) ↦ₘ smodAbsSum0 limb0 top) **
       ((sp + EvmAsm.Rv64.signExtend12 (40 : BitVec 12)) ↦ₘ
         smodAbsSum1 limb0 limb1 top) **
       ((sp + EvmAsm.Rv64.signExtend12 (48 : BitVec 12)) ↦ₘ
         smodAbsSum2 limb0 limb1 limb2 top) **
       ((sp + EvmAsm.Rv64.signExtend12 EvmAsm.Evm64.evm_smodDivisorTopLimbOff) ↦ₘ
         smodAbsSum3 limb0 limb1 limb2 top)) := by
  rw [smodAbsDivisorWord_eq_components]
  exact (evmWordIs_eq_quadMem_smodDivisor
    sp (smodAbsSum0 limb0 top) (smodAbsSum1 limb0 limb1 top)
    (smodAbsSum2 limb0 limb1 limb2 top) (smodAbsSum3 limb0 limb1 limb2 top)).symm

end EvmAsm.Evm64.SMod.Compose
