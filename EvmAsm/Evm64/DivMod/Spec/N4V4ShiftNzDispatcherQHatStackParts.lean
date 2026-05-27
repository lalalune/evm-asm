/-
  EvmAsm.Evm64.DivMod.Spec.N4V4ShiftNzDispatcherQHatStackParts

  Stack-wrapper surfaces for compact qhat/high-div n=4 shift-nonzero
  dispatcher evidence.
-/

import EvmAsm.Evm64.DivMod.Spec.N4V4ShiftNzDispatcherSemanticParts

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Compact qhat/high-div branch evidence stack surface routed through the
    repaired branch-semantic dispatcher package. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_branch_qhat_high_div_semantic
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchQHatHighDivEvidence a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_branch_semantic
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchQHatHighDivEvidence.toBranchSemanticV4
      hb3nz hshift_nz hevidence)

/-- No-NOP compact qhat/high-div branch evidence stack surface routed through
    the repaired branch-semantic dispatcher package. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_qhat_high_div_semantic
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchQHatHighDivEvidence a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_semantic
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchQHatHighDivEvidence.toBranchSemanticV4
      hb3nz hshift_nz hevidence)

end EvmAsm.Evm64
