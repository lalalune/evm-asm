/-
  EvmAsm.Evm64.DivMod.LoopIterN1.Iter210CallV5

  v5 n=1 three-iteration (j=2, j=1, j=0) ALL-CALL loop composition: chain the j=2
  call body onto the all-call two-iteration composition (#7275).  Same pattern as
  `Iter10CallV5`, one digit deeper.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.Iter10CallV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_2 slt_jpos_2)

private theorem iterN1Call_v5_unfold210 (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    = iterWithDoubleAddback (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold iterN1Call_v5
  rfl

/-- v5 n=1 three-iteration loop precondition (entry at j=2) with the v5 `sp+3936`
    scratch cell. -/
@[irreducible] def loopN1Iter210PreV5 (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 scratchMem : Word) : Assertion :=
  loopN1Iter210PreWithScratch sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
    retMem dMem dloMem scratch_un0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- v5 n=1 three-iteration (j=2,j=1,j=0) ALL-CALL loop postcondition.  (j=2 is
    always call, overwriting the div128 scratch, so the initial scratch values do
    not appear.) -/
@[irreducible] def loopN1Iter210PostV5 (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
    u0_orig_1 u0_orig_0 scratchMem : Word) : Assertion :=
  let r2 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  loopN1Iter10PostV5 true true sp base v0 v1 v2 v3
    u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 u0_orig_0
    (base + div128CallRetOff) v0 (divKTrialCallV5DLo v0) (divKTrialCallV5Un0 u0)
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) **
  ((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1)

theorem divK_loop_n1_call_iter210_v5_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_2 : BitVec.ult u1 v0)
    (hbltu_1 : BitVec.ult
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_0 : BitVec.ult
      (iterN1Call_v5 v0 v1 v2 v3 u0_orig_1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 v0)
    (hborrow_2 : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hborrow_1 : mulsubN4NoBorrow
      (divKTrialCallV5QHat (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 u0_orig_1 v0)
      v0 v1 v2 v3 u0_orig_1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    (hborrow_0 : mulsubN4NoBorrow
      (divKTrialCallV5QHat
        (iterN1Call_v5 v0 v1 v2 v3 u0_orig_1
          (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1 u0_orig_0 v0)
      v0 v1 v2 v3 u0_orig_0
      (iterN1Call_v5 v0 v1 v2 v3 u0_orig_1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0_orig_1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0_orig_1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0_orig_1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.2.2.1) :
    cpsTripleWithin 474 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopN1Iter210PreV5 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_1 u0_orig_0 q2Old q1Old q0Old
        retMem dMem dloMem scratch_un0 scratchMem)
      (loopN1Iter210PostV5 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_1 u0_orig_0 scratchMem) := by
  unfold loopN1Iter210PreV5 loopN1Iter210PreWithScratch loopN1Iter210Pre
  let r2 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  -- j=2 call body
  have J2 := divK_loop_body_n1_call_iter_jgt0_v5_spec_within_noNop (2 : Word) slt_jpos_2
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q2Old retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu_2 hborrow_2
  intro_lets at J2
  -- Frame j=2 with digits 1,0 cells (call j=2 consumes scratch)
  have J2f := cpsTripleWithin_frameR
    (((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat + signExtend12 0) ↦ₘ u0_orig_0) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old))
    (by pcFree) J2
  -- inner iter10 over digits 1,0 with j=2 outputs as inputs
  have I10 := divK_loop_n1_call_iter10_v5_spec_within_noNop
    sp (2 : Word) ((2 : Word) <<< (3 : BitVec 6).toNat) u_base_2 q_addr_2
    ((mulsubN4 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) r2.1 r2.2.2.2.2.1
    v0 v1 v2 v3 u0_orig_1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 u0_orig_0 q1Old q0Old
    (base + div128CallRetOff) v0 (divKTrialCallV5DLo v0) (divKTrialCallV5Un0 u0)
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) base
    halign hbltu_1 hbltu_0 hborrow_1 hborrow_0
  -- Frame iter10 with j=2's carried atoms
  have I10f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 4064) ↦ₘ r2.2.2.2.2.2) ** (q_addr_2 ↦ₘ r2.1))
    (by pcFree) I10
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1CallV5 loopExitPostN1 loopExitPost at hp
      unfold loopN1Iter10PreV5 loopN1Iter10PreWithScratch loopN1Iter10Pre
      simp only [] at hp ⊢
      rw [← iterN1Call_v5_unfold210] at hp
      have hj' := jpred_2
      rw [hj', u_n1_j2_0_eq_j1_4088, u_n1_j2_4088_eq_j1_4080,
          u_n1_j2_4080_eq_j1_4072, u_n1_j2_4072_eq_j1_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J2f I10f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN1Iter210PostV5
      xperm_hyp hp)
    full

end EvmAsm.Evm64
