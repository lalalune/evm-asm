import EvmAsm.Evm64.DivMod.CallableV4DivShape
import EvmAsm.Evm64.DivMod.CallableV4DivConcreteSelected

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Concrete-scratch N2 callable wrapper over bundled selected/reachable shape
    evidence. The branch booleans remain existential because the scratch value is
    indexed by them. -/
theorem evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_selectedEvidence_exists
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : N2CallableSelectedShapeEvidence a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
        (evm_div_callable_code_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
          ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
          v5 v6 v7 v10 v11Old
          q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableExactFrame sp a b raVal
          (signExtend12 4095 : Word) **
         ((sp + signExtend12 3936) ↦ₘ
          fullDivN2ScratchMemV4 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
            scratchMem)) :=
  evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_autoTrial_selected_exists
    sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hb3z hb2z hb1nz hshift_nz halign
    (N2CallableSelectedShapeEvidence.selectedCarry hevidence)
    (N2CallableSelectedShapeEvidence.arithmetic hevidence)

end EvmAsm.Evm64
