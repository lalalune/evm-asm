/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShiftNz

  The n=4 v5 DIV lane, shift≠0 case, with the runtime borrow case-split: from the
  stack-dispatch precondition `divModStackDispatchPreNoX1` to `divStackDispatchPostV5`
  over `divCode_noNop_v5`.  Dispatches on a bundled runtime certificate
  `n4ShiftNzLaneRuntimeCertV5` (the v5 analog of the v4 dispatcher's
  `n4ShiftNzDispatcherBranchRuntimeV4`): the skip branch applies the call-skip
  lane of conds (#7612), the addback branch applies the call-addback lane of
  conds (#7613).  The call-trial predicate is discharged from `shift≠0` via
  `isCallTrialN4_of_shift_nz`.  v5 mirror of
  `evm_div_n4_shift_nz_stack_spec_v4_of_branch_pred` (N4V4ShiftNzDispatcher).
  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallSkipOfConds
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallAddbackOfConds

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v5 call-skip trial↔v4 no-wrap bridge in `EvmWord` (`getLimbN`) form: the
    v5 trial quotient equals the v4 trial quotient on the normalized top window.
    This is exactly the `hbridge` premise consumed by `evm_div_n4_lane_callSkip_of_conds`
    (#7612), packaged as a named runtime fact.  Discharged unconditionally on the
    skip branch via #7607 (`divKTrialCallV5QHat_eq_div128Quot_v4_of_no_wrap_of_le`)
    given the no-wrap bounds; here it is carried as part of the runtime certificate. -/
def n4CallSkipBridgeV5Evm (a b : EvmWord) : Prop :=
  divKTrialCallV5QHat
    ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
    (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
      ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
    (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
      ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))) =
  div128Quot_v4
    ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
    (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
      ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
    (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
      ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))

/-- Bundled runtime certificate for the n=4 v5 shift≠0 lane: either the runtime
    took the call+skip branch (v5 no-borrow + the v4 borrow/semantic/bridge facts
    the skip lane consumes), or it took the call+addback branch (v5 addback
    borrow + carry2 + the v5 addback semantic).  v5 analog of
    `n4ShiftNzDispatcherBranchRuntimeV4`. -/
def n4ShiftNzLaneRuntimeCertV5 (a b : EvmWord) : Prop :=
  (isSkipBorrowN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
   isSkipBorrowN4CallV4Evm a b ∧
   n4CallSkipSemanticHoldsV4 a b ∧
   n4CallSkipBridgeV5Evm a b) ∨
  (isAddbackBorrowN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                           (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
   isAddbackCarry2NzN4CallV5 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
                             (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
   n4CallAddbackBeqSemanticHoldsV5 a b)

/-- n=4 v5 DIV lane, shift≠0 case, dispatching on the runtime borrow certificate.
    v5 mirror of `evm_div_n4_shift_nz_stack_spec_v4_of_branch_pred`. -/
theorem evm_div_n4_lane_shiftNz_v5_of_cert (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hcert : n4ShiftNzLaneRuntimeCertV5 a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  have hbltu : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) :=
    isCallTrialN4_of_shift_nz (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3) hb3nz hshift_nz
  rcases hcert with ⟨hbV5, hbV4, hsem, hbridge⟩ | ⟨hbV5, hcarry2, hsem⟩
  · -- call+skip branch
    exact evm_div_n4_lane_callSkip_of_conds sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hb3nz hshift_nz halign hbltu hbV5 hbV4 hsem hbridge
  · -- call+addback branch
    exact evm_div_n4_lane_callAddback_of_conds sp base a b x1Val v5 v6 v7 v10 v11Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem
      rfl rfl rfl rfl rfl rfl rfl rfl
      hb3nz hshift_nz halign hbltu hbV5 hcarry2 hsem

end EvmAsm.Evm64
