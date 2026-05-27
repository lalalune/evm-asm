/-
  EvmAsm.Evm64.DivMod.Spec.N4V4ShiftNzDispatcher

  Dispatcher-level n=4, shift-nonzero DIV v4 wrapper.
-/

import EvmAsm.Evm64.DivMod.Spec.CallSkipUnconditional
import EvmAsm.Evm64.DivMod.Spec.CallSkipV4NoWrap
import EvmAsm.Evm64.DivMod.Spec.N4V4StackPre

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Remaining runtime evidence for the n=4, shift-nonzero DIV v4 dispatcher.

    This packages the call+skip runtime branch certificate, the addback carry2 runtime
    condition, and the compact addback arithmetic bounds as one predicate. -/
def n4ShiftNzDispatcherRuntimeV4 (a b : EvmWord) : Prop :=
  n4CallSkipRuntimeBranchV4 a b ∧
  isAddbackCarry2NzN4CallV4Evm a b ∧
  n4CallAddbackBeqRuntimeBounds a b

/-- Branch-sensitive runtime evidence for the n=4, shift-nonzero DIV v4
    dispatcher.

    Unlike `n4ShiftNzDispatcherRuntimeV4`, this only asks for the addback
    carry/bounds evidence on the addback-borrow branch. -/
def n4ShiftNzDispatcherBranchRuntimeV4 (a b : EvmWord) : Prop :=
  (isSkipBorrowN4CallV4Evm a b ∧ n4CallSkipRuntimeBranchV4 a b) ∨
  (isAddbackBorrowN4CallV4Evm a b ∧
   isAddbackCarry2NzN4CallV4Evm a b ∧
   n4CallAddbackBeqRuntimeBounds a b)

/-- Explicit branch/bounds evidence for the n=4, shift-nonzero DIV v4
    dispatcher.

    This is the lightweight shape produced by the arithmetic side of the n=4
    stack assembly before it has been upgraded to the runtime call+skip branch
    certificate. -/
def n4ShiftNzDispatcherBranchBoundsV4 (a b : EvmWord) : Prop :=
  n4CallSkipBranchV4 a b ∧
  isAddbackCarry2NzN4CallV4Evm a b ∧
  n4CallAddbackBeqRuntimeBounds a b

theorem n4ShiftNzDispatcherRuntimeV4_def {a b : EvmWord} :
    n4ShiftNzDispatcherRuntimeV4 a b =
      (n4CallSkipRuntimeBranchV4 a b ∧
       isAddbackCarry2NzN4CallV4Evm a b ∧
       n4CallAddbackBeqRuntimeBounds a b) :=
  rfl

theorem n4ShiftNzDispatcherBranchRuntimeV4_def {a b : EvmWord} :
    n4ShiftNzDispatcherBranchRuntimeV4 a b =
      ((isSkipBorrowN4CallV4Evm a b ∧ n4CallSkipRuntimeBranchV4 a b) ∨
       (isAddbackBorrowN4CallV4Evm a b ∧
        isAddbackCarry2NzN4CallV4Evm a b ∧
        n4CallAddbackBeqRuntimeBounds a b)) :=
  rfl

theorem n4ShiftNzDispatcherBranchBoundsV4_def {a b : EvmWord} :
    n4ShiftNzDispatcherBranchBoundsV4 a b =
      (n4CallSkipBranchV4 a b ∧
       isAddbackCarry2NzN4CallV4Evm a b ∧
       n4CallAddbackBeqRuntimeBounds a b) :=
  rfl

theorem n4ShiftNzDispatcherBranchBoundsV4.callSkipBranch {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    n4CallSkipBranchV4 a b := by
  rw [n4ShiftNzDispatcherBranchBoundsV4_def] at hevidence
  exact hevidence.1

theorem n4ShiftNzDispatcherBranchBoundsV4.addbackCarry2 {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    isAddbackCarry2NzN4CallV4Evm a b := by
  rw [n4ShiftNzDispatcherBranchBoundsV4_def] at hevidence
  exact hevidence.2.1

theorem n4ShiftNzDispatcherBranchBoundsV4.addbackRuntimeBounds {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    n4CallAddbackBeqRuntimeBounds a b := by
  rw [n4ShiftNzDispatcherBranchBoundsV4_def] at hevidence
  exact hevidence.2.2

theorem n4ShiftNzDispatcherBranchBoundsV4.of_runtime_pred {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b)
    (hbranch : n4CallSkipBranchV4 a b) :
    n4ShiftNzDispatcherBranchBoundsV4 a b := by
  rw [n4ShiftNzDispatcherRuntimeV4_def] at hruntime
  rw [n4ShiftNzDispatcherBranchBoundsV4_def]
  exact ⟨hbranch, hruntime.2.1, hruntime.2.2⟩

theorem n4ShiftNzDispatcherRuntimeV4.of_branch_bounds {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    n4ShiftNzDispatcherRuntimeV4 a b := by
  rw [n4ShiftNzDispatcherBranchBoundsV4_def] at hevidence
  rw [n4ShiftNzDispatcherRuntimeV4_def]
  exact ⟨n4CallSkipRuntimeBranchV4_of_branch_pred hevidence.1, hevidence.2.1, hevidence.2.2⟩

theorem n4ShiftNzDispatcherBranchRuntimeV4_of_runtime_pred {a b : EvmWord}
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b := by
  rw [n4ShiftNzDispatcherRuntimeV4_def] at hruntime
  rw [n4ShiftNzDispatcherBranchRuntimeV4_def]
  cases isSkipBorrowN4CallV4Evm_or_isAddbackBorrowN4CallV4Evm a b with
  | inl hskip =>
      exact Or.inl ⟨hskip, hruntime.1⟩
  | inr hadd =>
      exact Or.inr ⟨hadd, hruntime.2.1, hruntime.2.2⟩

theorem n4ShiftNzDispatcherBranchRuntimeV4_of_branch_bounds {a b : EvmWord}
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    n4ShiftNzDispatcherBranchRuntimeV4 a b :=
  n4ShiftNzDispatcherBranchRuntimeV4_of_runtime_pred
    (n4ShiftNzDispatcherRuntimeV4.of_branch_bounds hevidence)

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
        exact n4CallAddbackBeqSemanticHolds_of_runtime_bounds
          hb3nz hshift_nz h_bounds hadd hcarry2
      exact evm_div_n4_call_addback_beq_stack_spec
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu hadd hcarry2 hsem

/-- n=4, shift-nonzero DIV v4 dispatcher from the packaged runtime evidence
    predicate. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_runtime_pred
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b) :
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
  have hbranchRuntime : n4ShiftNzDispatcherBranchRuntimeV4 a b :=
    n4ShiftNzDispatcherBranchRuntimeV4_of_runtime_pred hruntime
  rw [n4ShiftNzDispatcherBranchRuntimeV4_def] at hbranchRuntime
  cases hbranchRuntime with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_of_runtime_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip.1 hskip.2)
  | inr haddRuntime =>
      have hsem : n4CallAddbackBeqSemanticHolds a b := by
        exact n4CallAddbackBeqSemanticHolds_of_runtime_bounds
          hb3nz hshift_nz haddRuntime.2.2 haddRuntime.1 haddRuntime.2.1
      exact evm_div_n4_call_addback_beq_stack_spec
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu haddRuntime.1 haddRuntime.2.1 hsem

/-- n=4, shift-nonzero DIV v4 dispatcher from branch-sensitive runtime
    evidence. This surface avoids requiring addback-only arithmetic evidence
    when the runtime borrow split is already known to take the call+skip path. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_branch_runtime
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherBranchRuntimeV4 a b) :
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
  rw [n4ShiftNzDispatcherBranchRuntimeV4_def] at hruntime
  cases hruntime with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_of_runtime_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip.1 hskip.2)
  | inr haddRuntime =>
      have hsem : n4CallAddbackBeqSemanticHolds a b := by
        exact n4CallAddbackBeqSemanticHolds_of_runtime_bounds
          hb3nz hshift_nz haddRuntime.2.2 haddRuntime.1 haddRuntime.2.1
      exact evm_div_n4_call_addback_beq_stack_spec
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu haddRuntime.1 haddRuntime.2.1 hsem


/-- n=4, shift-nonzero DIV v4 dispatcher from packaged branch/bounds
    evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_of_branch_bounds
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_branch_runtime
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchRuntimeV4_of_branch_bounds hevidence)

/-- No-NOP n=4, shift-nonzero DIV v4 dispatcher over the call branch. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_pred
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
        (evm_div_n4_call_skip_stack_spec_v4_noNop_of_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip hbranch)
  | inr hadd =>
      exact evm_div_n4_call_addback_beq_stack_spec_noNop
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu hadd hcarry2 hsem

/-- No-NOP n=4, shift-nonzero DIV v4 dispatcher with addback semantics derived
    from compact runtime bounds in the addback branch. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_runtime_bounds
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
        (evm_div_n4_call_skip_stack_spec_v4_noNop_of_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip hbranch)
  | inr hadd =>
      have hsem : n4CallAddbackBeqSemanticHolds a b := by
        exact n4CallAddbackBeqSemanticHolds_of_runtime_bounds
          hb3nz hshift_nz h_bounds hadd hcarry2
      exact evm_div_n4_call_addback_beq_stack_spec_noNop
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu hadd hcarry2 hsem

/-- No-NOP n=4, shift-nonzero DIV v4 dispatcher from packaged runtime evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_runtime_pred
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b) :
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
  have hbranchRuntime : n4ShiftNzDispatcherBranchRuntimeV4 a b :=
    n4ShiftNzDispatcherBranchRuntimeV4_of_runtime_pred hruntime
  rw [n4ShiftNzDispatcherBranchRuntimeV4_def] at hbranchRuntime
  cases hbranchRuntime with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_noNop_of_runtime_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip.1 hskip.2)
  | inr haddRuntime =>
      have hsem : n4CallAddbackBeqSemanticHolds a b := by
        exact n4CallAddbackBeqSemanticHolds_of_runtime_bounds
          hb3nz hshift_nz haddRuntime.2.2 haddRuntime.1 haddRuntime.2.1
      exact evm_div_n4_call_addback_beq_stack_spec_noNop
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu haddRuntime.1 haddRuntime.2.1 hsem

/-- No-NOP n=4, shift-nonzero DIV v4 dispatcher from branch-sensitive runtime
    evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_runtime
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherBranchRuntimeV4 a b) :
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
  rw [n4ShiftNzDispatcherBranchRuntimeV4_def] at hruntime
  cases hruntime with
  | inl hskip =>
      exact cpsTripleWithin_mono_nSteps (by decide)
        (evm_div_n4_call_skip_stack_spec_v4_noNop_of_runtime_branch_pred_hb3nz
          sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
          hb3nz hshift_nz halign hskip.1 hskip.2)
  | inr haddRuntime =>
      have hsem : n4CallAddbackBeqSemanticHolds a b := by
        exact n4CallAddbackBeqSemanticHolds_of_runtime_bounds
          hb3nz hshift_nz haddRuntime.2.2 haddRuntime.1 haddRuntime.2.1
      exact evm_div_n4_call_addback_beq_stack_spec_noNop
        sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
        hbnz hb3nz hshift_nz halign hbltu haddRuntime.1 haddRuntime.2.1 hsem


/-- No-NOP n=4, shift-nonzero DIV v4 dispatcher from packaged
    branch/bounds evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_bounds
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_runtime
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign
    (n4ShiftNzDispatcherBranchRuntimeV4_of_branch_bounds hevidence)

/-- Final named n=4, shift-nonzero DIV dispatcher surface over `divCode_v4`.
    This is the branch-predicate API consumed by later n=4 stack assembly. -/
theorem evm_div_n4_shift_nz_stack_spec
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
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_branch_pred
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2 hsem

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface over
    `divCode_noNop_v4`. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop
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
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_pred
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2 hsem


/-- Final named n=4, shift-nonzero DIV dispatcher surface from packaged
    runtime evidence. This is the stable runtime-facing API for later n=4
    unconditional assembly. -/
theorem evm_div_n4_shift_nz_stack_spec_of_runtime_pred
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_runtime_pred
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hruntime

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface from packaged
    runtime evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_runtime_pred
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherRuntimeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_runtime_pred
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hruntime

/-- Final named n=4, shift-nonzero DIV dispatcher surface from branch-sensitive
    runtime evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_of_branch_runtime
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherBranchRuntimeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_branch_runtime
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hruntime

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface from
    branch-sensitive runtime evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_branch_runtime
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hruntime : n4ShiftNzDispatcherBranchRuntimeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_runtime
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hruntime


/-- Final named n=4, shift-nonzero DIV dispatcher surface from the explicit
    callskip branch certificate plus compact addback runtime bounds. -/
theorem evm_div_n4_shift_nz_stack_spec_of_runtime_bounds
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
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_runtime_bounds
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2 h_bounds

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface from the
    explicit callskip branch certificate plus compact addback runtime bounds. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_runtime_bounds
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
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_runtime_bounds
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hbranch hcarry2 h_bounds


/-- Final named n=4, shift-nonzero DIV dispatcher surface from packaged
    branch/bounds evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_of_branch_bounds
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_of_branch_bounds
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hevidence

/-- Final named no-NOP n=4, shift-nonzero DIV dispatcher surface from packaged
    branch/bounds evidence. -/
theorem evm_div_n4_shift_nz_stack_spec_noNop_of_branch_bounds
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : n4ShiftNzDispatcherBranchBoundsV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) :=
  evm_div_n4_shift_nz_stack_spec_v4_noNop_of_branch_bounds
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hevidence

end EvmAsm.Evm64
