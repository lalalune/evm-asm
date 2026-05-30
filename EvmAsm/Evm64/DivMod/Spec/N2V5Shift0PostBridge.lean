/-
  EvmAsm.Evm64.DivMod.Spec.N2V5Shift0PostBridge

  N=2 v5 SHIFT=0 post bridge: from the shift=0 epilogue post (at nopOff — the
  quotient digits `q0..q3` in the output m-cells sp+32..56 and registers, plus
  the scratch cells) to the scaffold post `divStackDispatchPostV5`.  Mirrors n1's
  `n1_denormPost_to_divStackDispatchPost_v5` via `divStackDispatchPost_weaken` +
  `evmWordIs_sp{,32}_limbs_eq` + `memIs_implies_memOwn`.  Given the quotient
  digits equal `(EvmWord.div a b).getLimbN i` (from the shift=0 quotient
  correctness, #7467), this is the post half of the n=2 shift=0 lane.
-/

import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div
import EvmAsm.Evm64.DivMod.Compose.Base

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- Shift=0 epilogue post (+ dividend & scratch frame) ⊢ `divStackDispatchPostV5`. -/
theorem n2_shift0_epiloguePost_to_divStackDispatchPostV5
    (sp : Word) (a b : EvmWord)
    (a0 a1 a2 a3 q0 q1 q2 q3 v1 v2 v11 shift : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 nMem jMem retMem dMem dloMem scratch_un0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = q0) (hdiv1 : (EvmWord.div a b).getLimbN 1 = q1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = q2) (hdiv3 : (EvmWord.div a b).getLimbN 3 = q3) :
    ∀ h,
      (((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ q0) ** (.x6 ↦ᵣ q1) ** (.x7 ↦ᵣ q2) **
        (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) ** (.x10 ↦ᵣ q3) **
        ((sp + signExtend12 3992) ↦ₘ shift) **
        ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
        ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
        ((sp + 32) ↦ₘ q0) ** ((sp + 40) ↦ₘ q1) **
        ((sp + 48) ↦ₘ q2) ** ((sp + 56) ↦ₘ q3)) **
       ((.x9 ↦ᵣ v1) ** (.x11 ↦ᵣ v11) ** regOwn .x1 **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
        ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
        ((sp + signExtend12 4024) ↦ₘ u4) ** ((sp + signExtend12 4016) ↦ₘ u5) **
        ((sp + signExtend12 4008) ↦ₘ u6) ** ((sp + signExtend12 4000) ↦ₘ u7) **
        ((sp + signExtend12 3984) ↦ₘ nMem) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        ((sp + signExtend12 3968) ↦ₘ retMem) ** ((sp + signExtend12 3960) ↦ₘ dMem) **
        ((sp + signExtend12 3952) ↦ₘ dloMem) ** ((sp + signExtend12 3944) ↦ₘ scratch_un0) **
        ((sp + signExtend12 3936) ↦ₘ scratchMem))) h →
      divStackDispatchPostV5 sp a b h := by
  intro h hp
  rw [divStackDispatchPostV5]
  apply sepConj_mono_right (P := divStackDispatchPost sp a b) memIs_implies_memOwn h
  apply sepConj_mono_left (divStackDispatchPost_weaken sp a b) h
  rw [evmWordIs_sp_limbs_eq sp a a0 a1 a2 a3 ha0 ha1 ha2 ha3,
      evmWordIs_sp32_limbs_eq sp (EvmWord.div a b) q0 q1 q2 q3 hdiv0 hdiv1 hdiv2 hdiv3,
      divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hp
  xperm_hyp hp

end EvmAsm.Evm64
