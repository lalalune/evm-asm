/-
  EvmAsm.Evm64.DivMod.LoopIterN1.UnifiedCallV5

  v5 n=1 full-loop (j=3,2,1,0) ALL-CALL composition: chain the j=3 call body onto
  the all-call three-iteration composition (#7277).  Capstone of the v5 n=1 loop
  composition.  Same pattern as `Iter210CallV5`, one digit deeper; the nested
  per-digit iteration states are captured by the `fullN1S{2,1}` helper defs to keep
  the hypotheses readable.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.UnifiedDefsV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.DivMod.AddrNorm (jpred_3 slt_jpos_3)

private theorem iterN1Call_v5_unfoldU (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    = iterWithDoubleAddback (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold iterN1Call_v5
  rfl

/-- j=2-entry iteration state (after the j=3 digit). -/
private def fullN1S2 (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 : Word) :=
  let s3 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  iterN1Call_v5 v0 v1 v2 v3 u0_orig_2 s3.2.1 s3.2.2.1 s3.2.2.2.1 s3.2.2.2.2.1

/-- j=1-entry iteration state (after the j=3, j=2 digits). -/
private def fullN1S1 (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 : Word) :=
  let s2 := fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2
  iterN1Call_v5 v0 v1 v2 v3 u0_orig_1 s2.2.1 s2.2.2.1 s2.2.2.2.1 s2.2.2.2.2.1

theorem divK_loop_n1_call_unified_v5_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0
     q3Old q2Old q1Old q0Old : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu_3 : BitVec.ult u1 v0)
    (hbltu_2 : BitVec.ult (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v0)
    (hbltu_1 : BitVec.ult (fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2).2.1 v0)
    (hbltu_0 : BitVec.ult (fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1).2.1 v0)
    (hborrow_3 : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hborrow_2 : mulsubN4NoBorrow
      (divKTrialCallV5QHat (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 u0_orig_2 v0)
      v0 v1 v2 v3 u0_orig_2
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
      (iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1)
    (hborrow_1 : mulsubN4NoBorrow
      (divKTrialCallV5QHat (fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2).2.1 u0_orig_1 v0)
      v0 v1 v2 v3 u0_orig_1
      (fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2).2.1
      (fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2).2.2.1
      (fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2).2.2.2.1
      (fullN1S2 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2).2.2.2.2.1)
    (hborrow_0 : mulsubN4NoBorrow
      (divKTrialCallV5QHat (fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1).2.1 u0_orig_0 v0)
      v0 v1 v2 v3 u0_orig_0
      (fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1).2.1
      (fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1).2.2.1
      (fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1).2.2.2.1
      (fullN1S1 v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1).2.2.2.2.1) :
    cpsTripleWithin 632 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopN1UnifiedPreV5 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0_orig_2 u0_orig_1 u0_orig_0
        q3Old q2Old q1Old q0Old retMem dMem dloMem scratch_un0 scratchMem)
      (loopN1UnifiedPostV5 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop
        u0_orig_2 u0_orig_1 u0_orig_0 scratchMem) := by
  unfold loopN1UnifiedPreV5 loopN1PreWithScratch loopN1Pre
  let r3 := iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let u_base_3 := sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let u_base_2 := sp + signExtend12 4056 - (2 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_3 := sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_2 := sp + signExtend12 4088 - (2 : Word) <<< (3 : BitVec 6).toNat
  let u_base_1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
  let u_base_0 := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
  let q_addr_0 := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
  have J3 := divK_loop_body_n1_call_iter_jgt0_v5_spec_within_noNop (3 : Word) slt_jpos_3
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q3Old retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu_3 hborrow_3
  intro_lets at J3
  have J3f := cpsTripleWithin_frameR
    (((u_base_2 + signExtend12 0) ↦ₘ u0_orig_2) ** (q_addr_2 ↦ₘ q2Old) **
     ((u_base_1 + signExtend12 0) ↦ₘ u0_orig_1) ** (q_addr_1 ↦ₘ q1Old) **
     ((u_base_0 + signExtend12 0) ↦ₘ u0_orig_0) ** (q_addr_0 ↦ₘ q0Old))
    (by pcFree) J3
  have I210 := divK_loop_n1_call_iter210_v5_spec_within_noNop
    sp (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) u_base_3 q_addr_3
    ((mulsubN4 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) r3.1 r3.2.2.2.2.1
    v0 v1 v2 v3 u0_orig_2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1 u0_orig_1 u0_orig_0
    q2Old q1Old q0Old
    (base + div128CallRetOff) v0 (divKTrialCallV5DLo v0) (divKTrialCallV5Un0 u0)
    (divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) base
    halign hbltu_2 hbltu_1 hbltu_0 hborrow_2 hborrow_1 hborrow_0
  have I210f := cpsTripleWithin_frameR
    (((u_base_3 + signExtend12 4064) ↦ₘ r3.2.2.2.2.2) ** (q_addr_3 ↦ₘ r3.1))
    (by pcFree) I210
  have full := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      delta loopIterPostN1CallV5 loopExitPostN1 loopExitPost at hp
      unfold loopN1Iter210PreV5 loopN1Iter210PreWithScratch loopN1Iter210Pre
      simp only [] at hp ⊢
      rw [← iterN1Call_v5_unfoldU] at hp
      have hj' := jpred_3
      rw [hj', u_n1_j3_0_eq_j2_4088, u_n1_j3_4088_eq_j2_4080,
          u_n1_j3_4080_eq_j2_4072, u_n1_j3_4072_eq_j2_4064] at hp
      rw [sepConj_assoc'] at hp
      xperm_hyp hp)
    J3f I210f
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hp => by
      delta loopN1UnifiedPostV5
      xperm_hyp hp)
    full

end EvmAsm.Evm64
