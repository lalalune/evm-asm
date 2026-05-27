/-
  EvmAsm.Evm64.DivMod.Spec.N4V4ShiftNzDispatcherSemanticParts

  Addback semantic projections for the n=4, shift-nonzero DIV v4 dispatcher.
-/

import EvmAsm.Evm64.DivMod.Spec.N4V4ShiftNzDispatcher

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Addback semantic bridge from packaged n=4 shift-nonzero runtime evidence. -/
theorem n4ShiftNzDispatcherRuntimeV4.semanticHoldsV4 {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b)
    (hadd : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
    hb3nz hshift_nz
    (n4ShiftNzDispatcherRuntimeV4.addbackRuntimeBounds hruntime)
    hadd
    (n4ShiftNzDispatcherRuntimeV4.addbackCarry2 hruntime)

/-- Historical non-V4 semantic bridge from packaged n=4 shift-nonzero runtime
    evidence. -/
theorem n4ShiftNzDispatcherRuntimeV4.semanticHolds {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b)
    (hadd : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4ShiftNzDispatcherRuntimeV4.semanticHoldsV4
      hb3nz hshift_nz hruntime hadd

/-- Addback semantic bridge from branch/bounds n=4 shift-nonzero dispatcher
    evidence. -/
theorem n4ShiftNzDispatcherBranchBoundsV4.semanticHoldsV4 {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b)
    (hadd : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
    hb3nz hshift_nz
    (n4ShiftNzDispatcherBranchBoundsV4.addbackRuntimeBounds hevidence)
    hadd
    (n4ShiftNzDispatcherBranchBoundsV4.addbackCarry2 hevidence)

/-- Historical non-V4 addback semantic bridge from branch/bounds n=4
    shift-nonzero dispatcher evidence. -/
theorem n4ShiftNzDispatcherBranchBoundsV4.semanticHolds {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b)
    (hadd : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4ShiftNzDispatcherBranchBoundsV4.semanticHoldsV4
      hb3nz hshift_nz hevidence hadd

/-- Addback semantic bridge from direct packaged high-div evidence parts at the
    n=4 shift-nonzero dispatcher surface. -/
theorem n4ShiftNzDispatcherBranchHighDivEvidence.semanticHoldsV4_of_addback_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hadd : isAddbackBorrowN4CallV4Evm a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (hevidence : n4CallAddbackBeqShiftHighDivEvidence a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_evidence_and_borrow
    hb3nz hshift_nz hevidence hadd hcarry2

/-- Historical non-V4 addback semantic bridge from direct packaged high-div
    evidence parts at the n=4 shift-nonzero dispatcher surface. -/
theorem n4ShiftNzDispatcherBranchHighDivEvidence.semanticHolds_of_addback_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hadd : isAddbackBorrowN4CallV4Evm a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (hevidence : n4CallAddbackBeqShiftHighDivEvidence a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4ShiftNzDispatcherBranchHighDivEvidence.semanticHoldsV4_of_addback_parts
      hb3nz hshift_nz hadd hcarry2 hevidence

/-- Addback semantic bridge from direct raw high-div evidence parts at the n=4
    shift-nonzero dispatcher surface. -/
theorem n4ShiftNzDispatcherBranchHighDivRawEvidence.semanticHoldsV4_of_addback_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hadd : isAddbackBorrowN4CallV4Evm a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_raw_parts_and_borrow
    hb3nz hshift_nz h_rhat_hi_zero h_qhat_le_high_div
    h_high_div_le_norm_plus_one hadd hcarry2

/-- Historical non-V4 addback semantic bridge from direct raw high-div evidence
    parts at the n=4 shift-nonzero dispatcher surface. -/
theorem n4ShiftNzDispatcherBranchHighDivRawEvidence.semanticHolds_of_addback_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hadd : isAddbackBorrowN4CallV4Evm a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4ShiftNzDispatcherBranchHighDivRawEvidence.semanticHoldsV4_of_addback_parts
      hb3nz hshift_nz hadd hcarry2 h_rhat_hi_zero
      h_qhat_le_high_div h_high_div_le_norm_plus_one


/-- n=4 shift-nonzero DIV dispatcher surface consuming the repaired V4 addback
    semantic marker directly. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_branch_pred_semanticV4
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
    (hsemV4 : n4CallAddbackBeqSemanticHoldsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_branch_pred
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2
    (n4CallAddbackBeqSemanticHolds_of_v4 hsemV4)

/-- No-NOP n=4 shift-nonzero DIV dispatcher surface consuming the repaired V4
    addback semantic marker directly. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_pred_semanticV4
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
    (hsemV4 : n4CallAddbackBeqSemanticHoldsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_pred
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2
    (n4CallAddbackBeqSemanticHolds_of_v4 hsemV4)

/-- n=4 shift-nonzero DIV dispatcher surface consuming direct runtime
    branch evidence, addback carry evidence, and the repaired V4 addback semantic
    marker. This is the stack-facing target for the final runtime-only semantic
    discharger, without routing through the compact runtime-bounds package. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_runtime_parts_semanticV4
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
    (hsemV4 : n4CallAddbackBeqSemanticHoldsV4 a b) :
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
        (evm_div_n4_call_skip_stack_spec_v4_of_runtime_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip hbranch)
  | inr hadd =>
      exact evm_div_n4_call_addback_beq_stack_spec
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu hadd hcarry2
        (n4CallAddbackBeqSemanticHolds_of_v4 hsemV4)

/-- No-NOP n=4 shift-nonzero DIV dispatcher surface consuming direct runtime
    branch evidence, addback carry evidence, and the repaired V4 addback semantic
    marker. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_runtime_parts_semanticV4
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
    (hsemV4 : n4CallAddbackBeqSemanticHoldsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
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
        (evm_div_n4_call_skip_stack_spec_v4_noNop_of_runtime_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip hbranch)
  | inr hadd =>
      exact evm_div_n4_call_addback_beq_stack_spec_noNop
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu hadd hcarry2
        (n4CallAddbackBeqSemanticHolds_of_v4 hsemV4)

/-- Historical alias for the V4-semantic runtime-parts n=4 shift-nonzero
    DIV dispatcher surface. -/
theorem evm_div_n4_shift_nz_stack_spec_of_runtime_parts_semanticV4
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
    (hsemV4 : n4CallAddbackBeqSemanticHoldsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_runtime_parts_semanticV4
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2 hsemV4

/-- Historical no-NOP alias for the V4-semantic runtime-parts n=4
    shift-nonzero DIV dispatcher surface. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_runtime_parts_semanticV4
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
    (hsemV4 : n4CallAddbackBeqSemanticHoldsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_runtime_parts_semanticV4
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2 hsemV4

/-- Addback-branch n=4 shift-nonzero DIV dispatcher surface consuming the
    repaired V4 addback semantic marker directly. This branch-local wrapper does
    not require skip-branch evidence or the compact runtime-bounds package. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_branch_addback_semanticV4
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hadd : isAddbackBorrowN4CallV4Evm a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (hsemV4 : n4CallAddbackBeqSemanticHoldsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_call_addback_beq_stack_spec
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    (evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz)
    hb3nz hshift_nz halign
    (isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz)
    hadd hcarry2
    (n4CallAddbackBeqSemanticHolds_of_v4 hsemV4)

/-- No-NOP addback-branch n=4 shift-nonzero DIV dispatcher surface consuming
    the repaired V4 addback semantic marker directly. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_addback_semanticV4
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hadd : isAddbackBorrowN4CallV4Evm a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (hsemV4 : n4CallAddbackBeqSemanticHoldsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_call_addback_beq_stack_spec_noNop
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    (evmWord_ne_zero_of_getLimbN_3_ne_zero hb3nz)
    hb3nz hshift_nz halign
    (isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz)
    hadd hcarry2
    (n4CallAddbackBeqSemanticHolds_of_v4 hsemV4)

/-- Historical alias for the V4-semantic addback-branch n=4 shift-nonzero DIV
    dispatcher surface. -/
theorem evm_div_n4_shift_nz_stack_spec_of_branch_addback_semanticV4
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hadd : isAddbackBorrowN4CallV4Evm a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (hsemV4 : n4CallAddbackBeqSemanticHoldsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_branch_addback_semanticV4
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hadd hcarry2 hsemV4

/-- Historical no-NOP alias for the V4-semantic addback-branch n=4
    shift-nonzero DIV dispatcher surface. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_branch_addback_semanticV4
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hadd : isAddbackBorrowN4CallV4Evm a b)
    (hcarry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (hsemV4 : n4CallAddbackBeqSemanticHoldsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_addback_semanticV4
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hadd hcarry2 hsemV4

/-- Historical alias for the V4-semantic n=4 shift-nonzero DIV dispatcher
    surface. -/
theorem evm_div_n4_shift_nz_stack_spec_of_branch_pred_semanticV4
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
    (hsemV4 : n4CallAddbackBeqSemanticHoldsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_branch_pred_semanticV4
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2 hsemV4

/-- Historical no-NOP alias for the V4-semantic n=4 shift-nonzero DIV
    dispatcher surface. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_branch_pred_semanticV4
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
    (hsemV4 : n4CallAddbackBeqSemanticHoldsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_pred_semanticV4
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2 hsemV4

end EvmAsm.Evm64
