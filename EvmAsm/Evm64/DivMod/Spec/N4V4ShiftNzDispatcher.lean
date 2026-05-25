/-
  EvmAsm.Evm64.DivMod.Spec.N4V4ShiftNzDispatcher

  Dispatcher-level n=4, shift-nonzero DIV v4 wrapper.
-/

import EvmAsm.Evm64.DivMod.Spec.CallSkipUnconditional
import EvmAsm.Evm64.DivMod.Spec.CallSkipV4NoWrap
import EvmAsm.Evm64.DivMod.Spec.N4V4StackPre

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- n=4, shift-nonzero DIV v4 dispatcher over the call branch.

    The call-trial predicate is discharged from the normalized top limb. The
    skip/addback split is runtime-complete, but this intermediate surface still
    carries the branch-specific semantic facts:
    * `n4CallSkipBranchV4` for call+skip.
    * `isAddbackCarry2NzN4CallV4Evm` and `n4CallAddbackBeqSemanticHolds` for
      call+addback.
-/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_branch_pred
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbranch : n4CallSkipBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  cases isSkipBorrowN4CallV4Evm_or_isAddbackBorrowN4CallV4Evm a b with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_of_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip hbranch)
  | inr hadd =>
      exact evm_div_n4_call_addback_beq_stack_spec
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu hadd hcarry2 hsem

/-- n=4, shift-nonzero DIV v4 dispatcher with the addback semantic marker
    derived from the existing compact runtime-bounds predicate in the addback
    branch. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_runtime_bounds
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbranch : n4CallSkipBranchV4 a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_bounds : n4CallAddbackBeqRuntimeBounds a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  have hbnz : b ≠ 0 := evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz
  have hbltu : isCallTrialN4Evm a b :=
    isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz
  cases isSkipBorrowN4CallV4Evm_or_isAddbackBorrowN4CallV4Evm a b with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_of_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip hbranch)
  | inr hadd =>
      have hsem : n4CallAddbackBeqSemanticHolds a b := by
        simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
          n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
            hb3nz hshift_nz h_bounds hadd hcarry2
      exact evm_div_n4_call_addback_beq_stack_spec
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu hadd hcarry2 hsem

end EvmAsm.Evm64
