/-
  EvmAsm.Evm64.DivMod.Spec.ModN4V4StackPre

  Stack-level wrappers for n=4 MOD v4 call-addback paths.
-/

import EvmAsm.Evm64.DivMod.Spec.CallSkip
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4MaxSkipV4NoNop
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4CallSkipV4NoNop
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4CallAddbackV4NoNop

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- EvmWord-level wrapper around
    `evm_mod_n4_preloop_max_skip_spec_within_v4`. -/
theorem evm_mod_n4_preloop_max_skip_stack_pre_spec_within_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isMaxTrialN4Evm a b)
    (hborrow : isSkipBorrowN4MaxEvm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 76)
      base (base + denormOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValues sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem)
      (preloopMaxSkipPostN4 sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_preloop_max_skip_spec_within_v4 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem
    hbnz' hb3nz hshift_nz hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled variant of `evm_mod_n4_preloop_max_skip_stack_pre_spec_within_v4`. -/
theorem evm_mod_n4_preloop_max_skip_stack_pre_spec_bundled_within_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isMaxTrialN4Evm a b)
    (hborrow : isSkipBorrowN4MaxEvm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 76)
      base (base + denormOff) (modCode_v4 base)
      (modN4StackPre sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem)
      (preloopMaxSkipPostN4 sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_mod_n4_preloop_max_skip_stack_pre_spec_within_v4 sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem hbnz hb3nz hshift_nz hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      delta modN4StackPre at hp
      exact hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper around
    `evm_mod_n4_full_max_skip_spec_within_v4`. -/
theorem evm_mod_n4_full_max_skip_stack_pre_spec_within_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isMaxTrialN4Evm a b)
    (hborrow : isSkipBorrowN4MaxEvm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 76 + 2 + 23 + 10)
      base (base + nopOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValues sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem)
      (fullModN4MaxSkipPost sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_full_max_skip_spec_within_v4 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem
    hbnz' hb3nz hshift_nz hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled variant of `evm_mod_n4_full_max_skip_stack_pre_spec_within_v4`. -/
theorem evm_mod_n4_full_max_skip_stack_pre_spec_bundled_within_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hbltu : isMaxTrialN4Evm a b)
    (hborrow : isSkipBorrowN4MaxEvm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 76 + 2 + 23 + 10)
      base (base + nopOff) (modCode_v4 base)
      (modN4StackPre sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem)
      (fullModN4MaxSkipPost sp
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) := by
  have h := evm_mod_n4_full_max_skip_stack_pre_spec_within_v4 sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem hbnz hb3nz hshift_nz hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      delta modN4StackPre at hp
      exact hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper around
    `evm_mod_n4_preloop_call_skip_spec_within_v4`. The borrow hypothesis is
    stated in the v4-normalized form consumed by the compose theorem. -/
theorem evm_mod_n4_preloop_call_skip_stack_pre_spec_within_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148)
      base (base + denormOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (preloopCallSkipPostN4V4 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        scratchMem) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_preloop_call_skip_spec_within_v4 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz' hb3nz hshift_nz halign hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled variant of `evm_mod_n4_preloop_call_skip_stack_pre_spec_within_v4`. -/
theorem evm_mod_n4_preloop_call_skip_stack_pre_spec_bundled_within_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148)
      base (base + denormOff) (modCode_v4 base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (preloopCallSkipPostN4V4 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        scratchMem) := by
  have h := evm_mod_n4_preloop_call_skip_stack_pre_spec_within_v4 sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [modN4StackPreCall_unfold] at hp
      xperm_hyp hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper around
    `evm_mod_n4_preloop_call_addback_beq_spec_within_v4`. The addback borrow
    and carry hypotheses are stated in the v4-normalized form consumed by the
    compose theorem. -/
theorem evm_mod_n4_preloop_call_addback_beq_stack_pre_spec_within_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallV4Evm a b)
    (hborrow : isAddbackBorrowN4CallV4Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224)
      base (base + denormOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (preloopCallAddbackBeqPostN4V4 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        scratchMem) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_preloop_call_addback_beq_spec_within_v4 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz' hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled variant of
    `evm_mod_n4_preloop_call_addback_beq_stack_pre_spec_within_v4`. -/
theorem evm_mod_n4_preloop_call_addback_beq_stack_pre_spec_bundled_within_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallV4Evm a b)
    (hborrow : isAddbackBorrowN4CallV4Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224)
      base (base + denormOff) (modCode_v4 base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (preloopCallAddbackBeqPostN4V4 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        scratchMem) := by
  have h := evm_mod_n4_preloop_call_addback_beq_stack_pre_spec_within_v4 sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [modN4StackPreCall_unfold] at hp
      xperm_hyp hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper around `evm_mod_n4_full_call_skip_spec_within_v4`.
    The borrow hypothesis is stated in the v4-normalized form consumed by the
    compose theorem. -/
theorem evm_mod_n4_full_call_skip_stack_pre_spec_within_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (fullModN4CallSkipPostV4 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        scratchMem) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_full_call_skip_spec_within_v4 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz' hb3nz hshift_nz halign hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- Bundled variant of `evm_mod_n4_full_call_skip_stack_pre_spec_within_v4`:
    takes the precondition as a single `modN4StackPreCall` atom plus the v4
    scratch cell. -/
theorem evm_mod_n4_full_call_skip_stack_pre_spec_bundled_within_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (modCode_v4 base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (fullModN4CallSkipPostV4 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        scratchMem) := by
  have h := evm_mod_n4_full_call_skip_stack_pre_spec_within_v4 sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [modN4StackPreCall_unfold] at hp
      xperm_hyp hp)
    (fun _ hq => hq)
    h

/-- EvmWord-level wrapper around
    `evm_mod_n4_full_call_addback_beq_spec_within_v4`. The addback borrow and
    carry hypotheses are stated in the v4-normalized form consumed by the
    compose theorem. -/
theorem evm_mod_n4_full_call_addback_beq_stack_pre_spec_within_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallV4Evm a b)
    (hborrow : isAddbackBorrowN4CallV4Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (fullModN4CallAddbackBeqPostV4 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        scratchMem) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  have hraw := evm_mod_n4_full_call_addback_beq_spec_within_v4 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz' hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

/-- The four MOD output stack slots produced by the n=4 v4 call+addback path.

This isolates the arithmetic bridge still needed to turn the denormalized
addback remainder into `EvmWord.mod a b`: callers can prove this assertion
equals `evmWordIs (sp + 32) (EvmWord.mod a b)` once the remainder arithmetic
is discharged. -/
def n4CallAddbackBeqModSlotPostV4
    (sp : Word) (a b : EvmWord) : Assertion :=
  let shift := (clzResult (b.getLimbN 3)).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b.getLimbN 3 <<< (shift.toNat % 64)) |||
    (b.getLimbN 2 >>> (antiShift.toNat % 64))
  let b2' := (b.getLimbN 2 <<< (shift.toNat % 64)) |||
    (b.getLimbN 1 >>> (antiShift.toNat % 64))
  let b1' := (b.getLimbN 1 <<< (shift.toNat % 64)) |||
    (b.getLimbN 0 >>> (antiShift.toNat % 64))
  let b0' := b.getLimbN 0 <<< (shift.toNat % 64)
  let u4 := a.getLimbN 3 >>> (antiShift.toNat % 64)
  let u3 := (a.getLimbN 3 <<< (shift.toNat % 64)) |||
    (a.getLimbN 2 >>> (antiShift.toNat % 64))
  let u2 := (a.getLimbN 2 <<< (shift.toNat % 64)) |||
    (a.getLimbN 1 >>> (antiShift.toNat % 64))
  let u1 := (a.getLimbN 1 <<< (shift.toNat % 64)) |||
    (a.getLimbN 0 >>> (antiShift.toNat % 64))
  let u0 := a.getLimbN 0 <<< (shift.toNat % 64)
  let qHat := div128Quot_v4 u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let c3 := ms.2.2.2.2
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
    (u4 - c3) b0' b1' b2' b3'
  let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1
    ab.2.2.2.2 b0' b1' b2' b3'
  let un0Out := if carry = 0 then ab'.1 else ab.1
  let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
  let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
  let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
  let u0' := (un0Out >>> (shift.toNat % 64)) |||
    (un1Out <<< (antiShift.toNat % 64))
  let u1' := (un1Out >>> (shift.toNat % 64)) |||
    (un2Out <<< (antiShift.toNat % 64))
  let u2' := (un2Out >>> (shift.toNat % 64)) |||
    (un3Out <<< (antiShift.toNat % 64))
  let u3' := un3Out >>> (shift.toNat % 64)
  ((sp + 32) ↦ₘ u0') ** ((sp + 40) ↦ₘ u1') **
  ((sp + 48) ↦ₘ u2') ** ((sp + 56) ↦ₘ u3')

/-- Convert the four addback MOD remainder limb equalities into the stack-slot
    adapter consumed by `evm_mod_n4_call_addback_beq_stack_spec_within_v4_of_slot_post`. -/
theorem n4CallAddbackBeqModSlotPostV4_eq_evmWordIs_of_getLimbN
    (sp : Word) (a b : EvmWord)
    (hmod :
      let shift := (clzResult (b.getLimbN 3)).1
      let antiShift := signExtend12 (0 : BitVec 12) - shift
      let b3' := (b.getLimbN 3 <<< (shift.toNat % 64)) |||
        (b.getLimbN 2 >>> (antiShift.toNat % 64))
      let b2' := (b.getLimbN 2 <<< (shift.toNat % 64)) |||
        (b.getLimbN 1 >>> (antiShift.toNat % 64))
      let b1' := (b.getLimbN 1 <<< (shift.toNat % 64)) |||
        (b.getLimbN 0 >>> (antiShift.toNat % 64))
      let b0' := b.getLimbN 0 <<< (shift.toNat % 64)
      let u4 := a.getLimbN 3 >>> (antiShift.toNat % 64)
      let u3 := (a.getLimbN 3 <<< (shift.toNat % 64)) |||
        (a.getLimbN 2 >>> (antiShift.toNat % 64))
      let u2 := (a.getLimbN 2 <<< (shift.toNat % 64)) |||
        (a.getLimbN 1 >>> (antiShift.toNat % 64))
      let u1 := (a.getLimbN 1 <<< (shift.toNat % 64)) |||
        (a.getLimbN 0 >>> (antiShift.toNat % 64))
      let u0 := a.getLimbN 0 <<< (shift.toNat % 64)
      let qHat := div128Quot_v4 u4 u3 b3'
      let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
        (u4 - c3) b0' b1' b2' b3'
      let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1
        ab.2.2.2.2 b0' b1' b2' b3'
      let un0Out := if carry = 0 then ab'.1 else ab.1
      let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
      let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
      let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
      let u0' := (un0Out >>> (shift.toNat % 64)) |||
        (un1Out <<< (antiShift.toNat % 64))
      let u1' := (un1Out >>> (shift.toNat % 64)) |||
        (un2Out <<< (antiShift.toNat % 64))
      let u2' := (un2Out >>> (shift.toNat % 64)) |||
        (un3Out <<< (antiShift.toNat % 64))
      let u3' := un3Out >>> (shift.toNat % 64)
      (EvmWord.mod a b).getLimbN 0 = u0' ∧
      (EvmWord.mod a b).getLimbN 1 = u1' ∧
      (EvmWord.mod a b).getLimbN 2 = u2' ∧
      (EvmWord.mod a b).getLimbN 3 = u3') :
    n4CallAddbackBeqModSlotPostV4 sp a b =
      evmWordIs (sp + 32) (EvmWord.mod a b) := by
  delta n4CallAddbackBeqModSlotPostV4
  obtain ⟨hmod0, hmod1, hmod2, hmod3⟩ := hmod
  exact (evmWordIs_sp32_limbs_eq sp (EvmWord.mod a b) _ _ _ _
    hmod0 hmod1 hmod2 hmod3).symm

/-- Bundled variant of
    `evm_mod_n4_full_call_addback_beq_stack_pre_spec_within_v4`: takes the
    precondition as a single `modN4StackPreCall` atom plus the v4 scratch cell. -/
theorem evm_mod_n4_full_call_addback_beq_stack_pre_spec_bundled_within_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallV4Evm a b)
    (hborrow : isAddbackBorrowN4CallV4Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (modCode_v4 base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (fullModN4CallAddbackBeqPostV4 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        scratchMem) := by
  have h := evm_mod_n4_full_call_addback_beq_stack_pre_spec_within_v4 sp base a b
    v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [modN4StackPreCall_unfold] at hp
      xperm_hyp hp)
    (fun _ hq => hq)
    h

/-- EVM-stack-level MOD spec on the n=4 v4 call+addback (shift≠0) sub-path,
    modulo the isolated denormalized-remainder adapter.

The executable/control-flow part is fully composed here. The `hslot` premise is
the remaining arithmetic bridge: it states that the four denormalized remainder
slots produced by the v4 addback path are exactly `EvmWord.mod a b`. -/
theorem evm_mod_n4_call_addback_beq_stack_spec_within_v4_of_slot_post (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallV4Evm a b)
    (hborrow : isAddbackBorrowN4CallV4Evm a b)
    (hslot : n4CallAddbackBeqModSlotPostV4 sp a b =
      evmWordIs (sp + 32) (EvmWord.mod a b)) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (modCode_v4 base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (modN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  have h_pre := evm_mod_n4_full_call_addback_beq_stack_pre_spec_bundled_within_v4
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
  refine cpsTripleWithin_weaken (fun _ hp => hp) ?_ h_pre
  intro h hq
  simp only [fullModN4CallAddbackBeqPostV4_div128Quot_unfold, denormModPost_unfold] at hq
  apply sepConj_mono_right memIs_implies_memOwn h
  apply sepConj_mono_left (mod_n4_call_skip_stack_weaken sp a b) h
  rw [show evmWordIs sp a =
      ((sp ↦ₘ a.getLimbN 0) ** ((sp + 8) ↦ₘ a.getLimbN 1) **
       ((sp + 16) ↦ₘ a.getLimbN 2) ** ((sp + 24) ↦ₘ a.getLimbN 3))
      from evmWordIs_sp_unfold]
  rw [show evmWordIs (sp + 32) (EvmWord.mod a b) =
      n4CallAddbackBeqModSlotPostV4 sp a b from hslot.symm]
  delta n4CallAddbackBeqModSlotPostV4
  rw [divScratchValuesCall_unfold, divScratchValues_unfold]
  rw [word_add_zero] at hq
  xperm_hyp hq

/-- Variant of `evm_mod_n4_call_addback_beq_stack_spec_within_v4_of_slot_post`
    whose remaining arithmetic obligation is phrased as the four MOD getLimbN
    equalities for the denormalized addback remainder. -/
theorem evm_mod_n4_call_addback_beq_stack_spec_within_v4_of_getLimbN (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hcarry2_nz : isAddbackCarry2NzN4CallV4Evm a b)
    (hborrow : isAddbackBorrowN4CallV4Evm a b)
    (hmod :
      let shift := (clzResult (b.getLimbN 3)).1
      let antiShift := signExtend12 (0 : BitVec 12) - shift
      let b3' := (b.getLimbN 3 <<< (shift.toNat % 64)) |||
        (b.getLimbN 2 >>> (antiShift.toNat % 64))
      let b2' := (b.getLimbN 2 <<< (shift.toNat % 64)) |||
        (b.getLimbN 1 >>> (antiShift.toNat % 64))
      let b1' := (b.getLimbN 1 <<< (shift.toNat % 64)) |||
        (b.getLimbN 0 >>> (antiShift.toNat % 64))
      let b0' := b.getLimbN 0 <<< (shift.toNat % 64)
      let u4n := a.getLimbN 3 >>> (antiShift.toNat % 64)
      let u3n := (a.getLimbN 3 <<< (shift.toNat % 64)) |||
        (a.getLimbN 2 >>> (antiShift.toNat % 64))
      let u2n := (a.getLimbN 2 <<< (shift.toNat % 64)) |||
        (a.getLimbN 1 >>> (antiShift.toNat % 64))
      let u1n := (a.getLimbN 1 <<< (shift.toNat % 64)) |||
        (a.getLimbN 0 >>> (antiShift.toNat % 64))
      let u0n := a.getLimbN 0 <<< (shift.toNat % 64)
      let qHat := div128Quot_v4 u4n u3n b3'
      let ms := mulsubN4 qHat b0' b1' b2' b3' u0n u1n u2n u3n
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1
        (u4n - c3) b0' b1' b2' b3'
      let ab' := addbackN4 ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1
        ab.2.2.2.2 b0' b1' b2' b3'
      let un0Out := if carry = 0 then ab'.1 else ab.1
      let un1Out := if carry = 0 then ab'.2.1 else ab.2.1
      let un2Out := if carry = 0 then ab'.2.2.1 else ab.2.2.1
      let un3Out := if carry = 0 then ab'.2.2.2.1 else ab.2.2.2.1
      let u0' := (un0Out >>> (shift.toNat % 64)) |||
        (un1Out <<< (antiShift.toNat % 64))
      let u1' := (un1Out >>> (shift.toNat % 64)) |||
        (un2Out <<< (antiShift.toNat % 64))
      let u2' := (un2Out >>> (shift.toNat % 64)) |||
        (un3Out <<< (antiShift.toNat % 64))
      let u3' := un3Out >>> (shift.toNat % 64)
      (EvmWord.mod a b).getLimbN 0 = u0' ∧
      (EvmWord.mod a b).getLimbN 1 = u1' ∧
      (EvmWord.mod a b).getLimbN 2 = u2' ∧
      (EvmWord.mod a b).getLimbN 3 = u3') :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 224 + 2 + 23 + 10)
      base (base + nopOff) (modCode_v4 base)
      (modN4StackPreCall sp a b v5 v6 v7 v10 v11
         q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
         shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (modN4CallSkipStackPost sp a b ** memOwn (sp + signExtend12 3936)) := by
  exact evm_mod_n4_call_addback_beq_stack_spec_within_v4_of_slot_post
    sp base a b v5 v6 v7 v10 v11 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hcarry2_nz hborrow
    (n4CallAddbackBeqModSlotPostV4_eq_evmWordIs_of_getLimbN sp a b hmod)

end EvmAsm.Evm64
