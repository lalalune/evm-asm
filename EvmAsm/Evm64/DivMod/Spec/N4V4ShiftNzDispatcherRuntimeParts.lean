/-
  EvmAsm.Evm64.DivMod.Spec.N4V4ShiftNzDispatcherRuntimeParts

  Direct global runtime evidence-part wrappers for the n=4, shift-nonzero DIV v4 dispatcher.
-/

import EvmAsm.Evm64.DivMod.Spec.N4V4ShiftNzDispatcherSemanticParts

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Final named n=4, shift-nonzero DIV dispatcher surface from direct
    global runtime evidence parts. -/
theorem evm_div_n4_shift_nz_stack_spec_of_runtime_parts
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbranch : n4CallSkipRuntimeBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_bounds : n4CallAddbackBeqRuntimeBounds a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
by
  cases isSkipBorrowN4CallV4Evm_or_isAddbackBorrowN4CallV4Evm a b with
  | inl hskip =>
      exact evm_div_n4_shift_nz_stack_spec_of_branch_semantic
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hb3nz hshift_nz halign
        (n4ShiftNzDispatcherBranchSemanticV4.skip hskip hbranch)
  | inr hadd =>
      exact evm_div_n4_shift_nz_stack_spec_of_branch_semantic
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hb3nz hshift_nz halign
        (n4ShiftNzDispatcherBranchSemanticV4.addback hadd hcarry2
          (n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
            hb3nz hshift_nz h_bounds hadd hcarry2))

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface from direct
    global runtime evidence parts. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_runtime_parts
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbranch : n4CallSkipRuntimeBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_bounds : n4CallAddbackBeqRuntimeBounds a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
by
  cases isSkipBorrowN4CallV4Evm_or_isAddbackBorrowN4CallV4Evm a b with
  | inl hskip =>
      exact evm_div_n4_shift_nz_stack_spec_noNop_of_branch_semantic
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hb3nz hshift_nz halign
        (n4ShiftNzDispatcherBranchSemanticV4.skip hskip hbranch)
  | inr hadd =>
      exact evm_div_n4_shift_nz_stack_spec_noNop_of_branch_semantic
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hb3nz hshift_nz halign
        (n4ShiftNzDispatcherBranchSemanticV4.addback hadd hcarry2
          (n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
            hb3nz hshift_nz h_bounds hadd hcarry2))

end EvmAsm.Evm64
