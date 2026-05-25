/-
  EvmAsm.Evm64.DivMod.Spec.CallSkipV4NoWrap

  Predicate-packaged surfaces for the v4 n=4 call+skip no-wrap branch.
-/

import EvmAsm.Evm64.DivMod.Spec.CallSkipV4

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- EvmWord-level certificate for the v4 call+skip no-wrap branch plus the
    supplied 128/64 upper bound used by the exact-quotient adapter. -/
def n4CallSkipNoWrapLeV4 (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  (divKTrialCallV4Q1dd u4 u3 b3').toNat *
      (divKTrialCallV4DLo b3').toNat ≤
    ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
      (divKTrialCallV4Un1 u3).toNat ∧
  (div128Quot_v4 u4 u3 b3').toNat ≤
    (u4.toNat * 2^64 + u3.toNat) / b3'.toNat

theorem n4CallSkipNoWrapLeV4_def {a b : EvmWord} :
    n4CallSkipNoWrapLeV4 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     (divKTrialCallV4Q1dd u4 u3 b3').toNat *
         (divKTrialCallV4DLo b3').toNat ≤
       ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
         (divKTrialCallV4Un1 u3).toNat ∧
     (div128Quot_v4 u4 u3 b3').toNat ≤
       (u4.toNat * 2^64 + u3.toNat) / b3'.toNat) :=
  rfl

/-- Predicate-packaged v4 call-skip semantic lower bound in the no-wrap branch. -/
theorem n4CallSkipSemanticHoldsV4_of_no_wrap_le_pred (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_no_wrap_le : n4CallSkipNoWrapLeV4 a b) :
    n4CallSkipSemanticHoldsV4 a b := by
  rw [n4CallSkipNoWrapLeV4_def] at h_no_wrap_le
  exact n4CallSkipSemanticHoldsV4_of_runtime_no_wrap_of_le a b
    hb3nz hshift_nz h_no_wrap_le.1 h_no_wrap_le.2

/-- Predicate-packaged v4 getLimbN bridge in the no-wrap branch. -/
theorem n4_call_skip_div_mod_getLimbN_v4_of_no_wrap_le_pred_hb3nz
    (a b : EvmWord)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (h_no_wrap_le : n4CallSkipNoWrapLeV4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let qHat := div128Quot_v4 u4 u3 b3'
    (EvmWord.div a b).getLimbN 0 = qHat ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  rw [n4CallSkipNoWrapLeV4_def] at h_no_wrap_le
  exact n4_call_skip_div_mod_getLimbN_v4_of_runtime_no_wrap_of_le_hb3nz a b
    hb3nz hshift_nz hborrow h_no_wrap_le.1 h_no_wrap_le.2

/-- Predicate-packaged bundled v4 call+skip stack wrapper in the no-wrap branch. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_no_wrap_le_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (h_no_wrap_le : n4CallSkipNoWrapLeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  rw [n4CallSkipNoWrapLeV4_def] at h_no_wrap_le
  exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_of_shift_nz_no_wrap_of_le
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hborrow h_no_wrap_le.1 h_no_wrap_le.2

/-- Predicate-packaged bundled no-NOP v4 call+skip stack wrapper in the no-wrap branch. -/
theorem evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_no_wrap_le_pred_hb3nz
    (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (h_no_wrap_le : n4CallSkipNoWrapLeV4 a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_noNop_v4 base)
      (divN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  rw [n4CallSkipNoWrapLeV4_def] at h_no_wrap_le
  exact evm_div_n4_call_skip_stack_pre_spec_bundled_v4_noNop_of_shift_nz_no_wrap_of_le
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hb3nz hshift_nz halign hborrow h_no_wrap_le.1 h_no_wrap_le.2

end EvmAsm.Evm64
