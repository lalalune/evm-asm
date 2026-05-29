/-
  EvmAsm.Evm64.DivMod.LoopIterN1.Iter10CallV5

  v5 n=1 two-iteration loop composition, ALL-CALL path (bltu_1 = bltu_0 = true).
  In the n=1 normalized call regime the running remainder stays < divisor, so
  `uHi < vTop` at every digit (`iterN1V5_true_remainder_lt_of_v0_norm_call`) and
  every digit takes the call path — the max path never occurs.  So the
  unconditional n=1 goal needs only this all-call chain, not the 16-way unified.

  Composes the j=1 and j=0 call iteration-ready bodies (#7270) into
  `loopN1Iter10PostV5 true true`.  Mirror of the v4 `(true,true)` branch of
  `divK_loop_n1_iter10_unified`.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.Iter10DefsV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_1 slt_jpos_1)

private theorem iterN1Call_v5_unfold (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    = iterWithDoubleAddback (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold iterN1Call_v5
  rfl

theorem divK_loop_n1_call_iter10_v5_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_1 : BitVec.ult u1 v0)
    (hbltu_0 : BitVec.ult (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hborrow_1 : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hborrow_0 : mulsubN4NoBorrow
      (divKTrialCallV5QHat (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 u0Orig v0)
      v0 v1 v2 v3 u0Orig
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1) :
    cpsTripleWithin 316 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopN1Iter10PreV5 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratch_un0 scratchMem)
      (loopN1Iter10PostV5 true true sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig
        retMem dMem dloMem scratch_un0 scratchMem) := by
  unfold loopN1Iter10PreV5 loopN1Iter10PreWithScratch loopN1Iter10Pre
  let r1 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  -- j=1 call body
  have J1 := divK_loop_body_n1_call_iter_jgt0_v5_spec_within_noNop (1 : Word) slt_jpos_1
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu_1 hborrow_1
  intro_lets at J1
  -- Frame j=1 with digit-0 cells (call j=1 consumes the scratch region)
  have J1f := cpsTripleWithin_frameR
    (((u_base_0 + signExtend12 0) ↦ₘ u0Orig) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J1
  -- j=0 call body, inputs from j=1's call output (old regs = j=1 loopExitPostN1 output)
  have J0 := divK_loop_body_n1_call_iter_j0_v5_spec_within_noNop
    sp (1 : Word) ((1 : Word) <<< (3 : BitVec 6).toNat) u_base_1 q_addr_1
    ((mulsubN4 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) r1.1 r1.2.2.2.2.1
    v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 q0Old
    (base + div128CallRetOff) v0 (divKTrialCallV5DLo v0) (divKTrialCallV5Un0 u0)
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) base
    halign hbltu_0 hborrow_0
  -- Frame j=0 with j=1's carried atoms only
  have J0f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 4064) ↦ₘ r1.2.2.2.2.2) ** (q_addr_1 ↦ₘ r1.1))
    (by pcFree) J0
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1CallV5 loopExitPostN1 loopExitPost at hp
      unfold loopBodyN1CallSkipJ0PreV4
      simp only [] at hp ⊢
      rw [← iterN1Call_v5_unfold] at hp
      have hj' := jpred_1
      rw [hj', u_n1_j1_0_eq_j0_4088, u_n1_j1_4088_eq_j0_4080,
          u_n1_j1_4080_eq_j0_4072, u_n1_j1_4072_eq_j0_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J1f J0f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter10PostV5
      simp only [loopIterPostN1V5_true, iterN1V5_true, if_true, sepConj_emp_right']
      xperm_hyp hp)
    full

end EvmAsm.Evm64
