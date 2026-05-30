/-
  EvmAsm.Evm64.DivMod.Spec.N2V5PostToDispatchPostV5

  N=2 V5 post bridge to the SCAFFOLD post `divStackDispatchPostV5`
  (= `divStackDispatchPost ** memOwn (sp+3936)`).  Composes the existing
  callable-frame bridge (`fullDivN2UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch_word`,
  #7463-adjacent) with the public weakening `divStackDispatchPostCallableExactFrame_weaken`
  and `memIs_implies_memOwn`.  This is the post half of the n=2 lane (the form the
  unconditional scaffold `evm_div_stack_spec_unconditional_of_lanes_v5_div`
  consumes), mirroring n1's `n1_denormPost_to_divStackDispatchPost_v5`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5ConcretePostBridge
import EvmAsm.Evm64.DivMod.Spec.StackPostBridge
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- From the n=2 v5 unified post (with exact caller `x1`) and quotient
    correctness, conclude the scaffold post `divStackDispatchPostV5`. -/
theorem fullDivN2UnifiedPostNoX1V5_to_divStackDispatchPostV5
    (bltu_2 bltu_1 bltu_0 : Bool)
    (sp base : Word) (a b : EvmWord)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hdivWord : fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b) :
    ∀ h,
      (fullDivN2UnifiedPostNoX1V5 bltu_2 bltu_1 bltu_0 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) h →
      divStackDispatchPostV5 sp a b h := by
  intro h hp
  have h1 := fullDivN2UnifiedPostNoX1V5_frame_to_divStackDispatchPostCallableExactFrame_scratch_word
    bltu_2 bltu_1 bltu_0 sp base a b
    retMem dMem dloMem scratchUn0 scratchMem raVal hdivWord h hp
  simp only [divStackDispatchPostV5]
  revert h1
  apply sepConj_mono
  · exact fun h hp =>
      divStackDispatchPostCallableExactFrame_weaken sp a b raVal (signExtend12 4095) h hp
  · exact fun h hp => memIs_implies_memOwn h hp

end EvmAsm.Evm64
