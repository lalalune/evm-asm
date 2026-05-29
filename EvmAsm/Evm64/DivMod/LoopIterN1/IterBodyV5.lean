/-
  EvmAsm.Evm64.DivMod.LoopIterN1.IterBodyV5

  v5 n=1 call-path per-digit *iteration-ready* loop bodies: the skip loop bodies
  (#7266/#7267) with their post weakened to `loopIterPostN1CallV5` (#7269) via the
  skip bridges.  These are the v5 analogue of `divK_loop_body_n1_call_unified_jX`
  (LoopComposeN1) — but because `div128Quot_v5` is the exact floor, there is no
  addback dispatch: the no-borrow hypothesis directly drives the skip path and the
  addback branch is unreachable.  Feed the v5 n=1 loop iteration.  Bead
  `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.IterPostV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- From the v5 no-borrow hypothesis (over `divKTrialCallV5QHat`), the mulsub-c3
    skip guard (over `div128Quot_v5`) holds. -/
private theorem v5_skip_guard_of_noBorrow {v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word}
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    ¬BitVec.ult uTop (mulsubN4_c3 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3) := by
  intro hult
  unfold mulsubN4NoBorrow at hborrow
  simp_rw [divKTrialCallV5QHat_eq_div128Quot_v5] at hborrow
  unfold mulsubN4_c3 at hult
  rw [if_pos hult] at hborrow
  exact absurd hborrow (by decide)

/-- v5 n=1 call-path iteration-ready loop body, j>0 (loops back to loopBody). -/
theorem divK_loop_body_n1_call_iter_jgt0_v5_spec_within_noNop (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    cpsTripleWithin 158 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratch_un0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) ** regOwn .x1)
      (loopIterPostN1CallV5 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  intro uBase qAddr
  have J := divK_loop_body_n1_call_skip_jgt0_v5_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu hborrow
  intro_lets at J
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by rw [← loopIterPostN1CallV5_jgt0_skip (v5_skip_guard_of_noBorrow hborrow)]; exact hp)
    J

/-- v5 n=1 call-path iteration-ready loop body, j=0 (exits to denorm). -/
theorem divK_loop_body_n1_call_iter_j0_v5_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : BitVec.ult u1 v0)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      (loopBodyN1CallSkipJ0PreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem)
      (loopIterPostN1CallV5 sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have J := divK_loop_body_n1_call_skip_j0_v5_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratch_un0 scratchMem base
    halign hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by rw [← loopIterPostN1CallV5_j0_skip (v5_skip_guard_of_noBorrow hborrow)]; exact hp)
    J

end EvmAsm.Evm64
