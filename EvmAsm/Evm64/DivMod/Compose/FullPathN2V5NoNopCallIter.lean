/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallIter

  v5/no-NOP iter-ready call-path loop bodies for n=2 (j=2 and j=1), over
  `divCode_noNop_v5`.  Mirror of `divK_loop_body_n2_call_j{2,1}_exact_loopIterScratch_v4_noNop`
  (FullPathN2V4NoNop): case on the c3 borrow guard, dispatch to the v5 call-path
  exact-x1 norm bodies (addback / skip, #7390), and weaken the post to
  `loopIterPostN2CallScratchNoX1` via the V5 post-eq lemmas (below) + the
  code-agnostic `loopIterPostN2CallScratchNoX1_{addback,skip}` producer bridges.
  These are the iteration-ready call bodies the unified n=2 v5 loop's 8-way
  dispatch consumes for the loop-back digits.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallExactX1

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v5 call+skip j>0 NoX1 post equals the generic scratch-form post with the
    v5 trial values (mirror of `loopBodyN2CallSkipJgt0PostV4NoX1_eq_scratch`). -/
theorem loopBodyN2CallSkipJgt0PostV5NoX1_eq_scratch
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN2CallSkipJgt0PostV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
      loopBodyN2CallSkipPostJScratchNoX1 sp base j
        (divKTrialCallV5QHat u2 u1 v1)
        (divKTrialCallV5DLo v1)
        (divKTrialCallV5Un0 u1)
        (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN2CallSkipJgt0PostV5NoX1 loopBodyN2CallSkipPostJScratchNoX1
  rfl

/-- The v5 call+addback j>0 NoX1 post equals the generic scratch-form post with
    the v5 trial values (mirror of `loopBodyN2CallAddbackBeqJgt0PostV4NoX1_eq_scratch`). -/
theorem loopBodyN2CallAddbackBeqJgt0PostV5NoX1_eq_scratch
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) :
    loopBodyN2CallAddbackBeqJgt0PostV5NoX1 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
      loopBodyN2CallAddbackBeqPostJScratchNoX1 sp base j
        (divKTrialCallV5QHat u2 u1 v1)
        (divKTrialCallV5DLo v1)
        (divKTrialCallV5Un0 u1)
        (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  delta loopBodyN2CallAddbackBeqJgt0PostV5NoX1 loopBodyN2CallAddbackBeqPostJScratchNoX1
  rfl

/-- Unified j=2 N2 call iteration over v5/no-NOP code, preserving concrete `x1`
    and exposing the v5 scratch cell in the postcondition. -/
theorem divK_loop_body_n2_call_j2_exact_loopIterScratch_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v5 base)
      (loopBodyN2CallSkipJgt0NormPreV4NoX1 (2 : Word) sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal))
      (loopIterPostN2CallScratchNoX1 sp base (2 : Word)
        (divKTrialCallV5QHat u2 u1 v1)
        (divKTrialCallV5DLo v1)
        (divKTrialCallV5Un0 u1)
        (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop ** (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word) := by
      unfold mulsubN4_c3 at hborrow
      rw [if_pos hborrow]; decide
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [loopBodyN2CallAddbackBeqJgt0PostV5NoX1_eq_scratch] at hp
        rw [loopIterPostN2CallScratchNoX1_addback hborrow] at hp
        xperm_hyp hp)
      (divK_loop_body_n2_call_addback_jgt0_beq_norm_v5_noNop_exact_x1
        (2 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem raVal
        halign hbltu hborrow_nz hcarry2_nz)
  · have hborrow_zero :
        mulsubN4NoBorrow (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          rw [loopBodyN2CallSkipJgt0PostV5NoX1_eq_scratch] at hp
          rw [loopIterPostN2CallScratchNoX1_skip hborrow] at hp
          xperm_hyp hp)
        (divK_loop_body_n2_call_skip_jgt0_norm_v5_noNop_exact_x1
          (2 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_2
          jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
          retMem dMem dloMem scratchUn0 scratchMem raVal
          halign hbltu hborrow_zero)

/-- Unified j=1 N2 call iteration over v5/no-NOP code, preserving concrete `x1`
    and exposing the v5 scratch cell in the postcondition. -/
theorem divK_loop_body_n2_call_j1_exact_loopIterScratch_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v5 base)
      (loopBodyN2CallSkipJgt0NormPreV4NoX1 (1 : Word) sp
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal))
      (loopIterPostN2CallScratchNoX1 sp base (1 : Word)
        (divKTrialCallV5QHat u2 u1 v1)
        (divKTrialCallV5DLo v1)
        (divKTrialCallV5Un0 u1)
        (divKTrialCallV5ScratchOut u2 u1 v1 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop ** (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word) := by
      unfold mulsubN4_c3 at hborrow
      rw [if_pos hborrow]; decide
    exact cpsTripleWithin_weaken
      (fun h hp => hp)
      (fun h hp => by
        rw [loopBodyN2CallAddbackBeqJgt0PostV5NoX1_eq_scratch] at hp
        rw [loopIterPostN2CallScratchNoX1_addback hborrow] at hp
        xperm_hyp hp)
      (divK_loop_body_n2_call_addback_jgt0_beq_norm_v5_noNop_exact_x1
        (1 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem raVal
        halign hbltu hborrow_nz hcarry2_nz)
  · have hborrow_zero :
        mulsubN4NoBorrow (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => hp)
        (fun h hp => by
          rw [loopBodyN2CallSkipJgt0PostV5NoX1_eq_scratch] at hp
          rw [loopIterPostN2CallScratchNoX1_skip hborrow] at hp
          xperm_hyp hp)
        (divK_loop_body_n2_call_skip_jgt0_norm_v5_noNop_exact_x1
          (1 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
          jOld v5Old v6Old v7Old v10Old v11Old v2Old
          v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
          retMem dMem dloMem scratchUn0 scratchMem raVal
          halign hbltu hborrow_zero)

end EvmAsm.Evm64
