/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Full

  The v5 n=1 loop-post → denorm-epilogue bridge: `loopN1UnifiedPostV5` (the loop
  result at `denormOff`) reduces to `fullDivN1DenormPreV5 ** fullDivN1FrameV5`, the
  denorm-epilogue entry shape plus the untouched scratch/carry frame.  Proven with
  `xperm_chunked` after abstracting the four iteration results to opaque atoms
  (`set R0..R3`) — the whole-assertion `simp`/`sep_perm` route blows `maxRecDepth`
  on the deep `iterN1Call_v5 → div128Quot_v5 → val256` cell values.  Bead
  `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5ToDenorm
import EvmAsm.Evm64.DivMod.Compose.DenormEpilogueV5
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5DenormPre
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5DigitLoopForm
import EvmAsm.Evm64.DivMod.LoopIterN1.LoopAtShapeBridgeR0V5

namespace EvmAsm.Evm64
open EvmAsm.Rv64 EvmAsm.Rv64.Tactics
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- The scratch/carry frame left untouched at `denormOff` by the v5 n=1 loop:
    the loop-exit register residue (x9/x11), the j-counter/n cells, the four
    per-digit borrow carries, and the div128 call scratch region. -/
@[irreducible] def fullDivN1FrameV5 (sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word) : Assertion :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let R3 := fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3
  let R2 := fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3
  let R1 := fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3
  let R0 := fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3
  (.x9 ↦ᵣ signExtend12 4095) ** (.x11 ↦ᵣ R0.1) **
  ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
  ((sp + signExtend12 3976) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (1 : Word)) **
  ((sp + signExtend12 4024) ↦ₘ R0.2.2.2.2.2) ** ((sp + signExtend12 4016) ↦ₘ R1.2.2.2.2.2) **
  ((sp + signExtend12 4008) ↦ₘ R2.2.2.2.2.2) ** ((sp + signExtend12 4000) ↦ₘ R3.2.2.2.2.2) **
  ((sp + signExtend12 3968) ↦ₘ (base + div128CallRetOff)) ** ((sp + signExtend12 3960) ↦ₘ v.1) **
  ((sp + signExtend12 3952) ↦ₘ divKTrialCallV5DLo v.1) **
  ((sp + signExtend12 3944) ↦ₘ divKTrialCallV5Un0 u.1) **
  ((sp + signExtend12 3936) ↦ₘ
    divKTrialCallV5ScratchOut R1.2.1 u.1 v.1
      (divKTrialCallV5ScratchOut R2.2.1 u.2.1 v.1
        (divKTrialCallV5ScratchOut R3.2.1 u.2.2.1 v.1
          (divKTrialCallV5ScratchOut u.2.2.2.2 u.2.2.2.1 v.1 scratchMem)))) **
  regOwn .x1

attribute [local irreducible] EvmWord.val256 div128Quot_v5 iterWithDoubleAddback mulsubN4 clzResult

theorem iterN1Call_v5_unfoldU' (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterN1Call_v5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
    = iterWithDoubleAddback (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold iterN1Call_v5; rfl

/-- Loop result at `denormOff` reduces to the denorm-epilogue pre plus the frame. -/
theorem loopN1UnifiedPostV5_to_denormPreV5 (sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem : Word)
    (h : PartialState)
    (hp : (loopN1UnifiedPostV5 sp base
        (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1 scratchMem **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) ** ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 3992) ↦ₘ fullDivN1Shift b0)) h) :
    (fullDivN1DenormPreV5 sp a0 a1 a2 a3 b0 b1 b2 b3 **
     fullDivN1FrameV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) h := by
  delta fullDivN1DenormPreV5 fullDivN1C3V5 fullDivN1FrameV5
  rw [← fullN1S0_eq_fullDivN1R0V5, ← fullN1S1_eq_fullDivN1R1V5, ← fullN1S2_eq_fullDivN1R2V5,
      fullDivN1R3V5_eq_iterN1Call_v5]
  delta loopN1UnifiedPostV5 loopN1Iter210PostV5 loopN1Iter10PostV5 loopIterPostN1V5
    loopIterPostN1CallV5 at hp
  dsimp only [] at hp
  rw [loopExitPostN1_j0_eq] at hp
  rw [← iterN1Call_v5_unfoldU'] at hp
  simp only [n1_ub3_off4064, n1_qa3, n2_ub2_off4064, n2_qa2,
      n3_ub1_off4064, n3_qa1, se12_32, se12_40, se12_48, se12_56,
      sepConj_emp_right'] at hp ⊢
  delta fullN1S0 fullN1S1 fullN1S2 at *
  dsimp only [] at hp ⊢
  simp only [iterN1V5_true, if_true] at hp ⊢
  set R3 := iterN1Call_v5 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0
    with hR3
  set R2 := iterN1Call_v5 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 R3.2.1 R3.2.2.1 R3.2.2.2.1 R3.2.2.2.2.1
    with hR2
  set R1 := iterN1Call_v5 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.1 R2.2.1 R2.2.2.1 R2.2.2.2.1 R2.2.2.2.2.1
    with hR1
  set R0 := iterN1Call_v5 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).1 R1.2.1 R1.2.2.1 R1.2.2.2.1 R1.2.2.2.2.1
    with hR0
  xperm_chunked hp


/-- Full n=1 DIV code path over `divCode_noNop_v5` (shift ≠ 0): preloop + capped
    loop + denorm epilogue, `base → nopOff`.  Quotient digits land in the output
    slots (`denormDivPost`); the normalized remainder limbs are in the u-cells. -/
theorem evm_div_n1_full_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 632 + (2 + 23 + 10)) base (base + nopOff)
      (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b0).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
       ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
       ((sp + signExtend12 4024) ↦ₘ u4Old) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem) **
       ((sp + signExtend12 3976) ↦ₘ jMem) **
       ((sp + signExtend12 3968) ↦ₘ retMem) **
       ((sp + signExtend12 3960) ↦ₘ dMem) **
       ((sp + signExtend12 3952) ↦ₘ dloMem) **
       ((sp + signExtend12 3944) ↦ₘ scratch_un0) **
       ((sp + signExtend12 3936) ↦ₘ scratchMem) ** regOwn .x1)
      ((denormDivPost sp (fullDivN1Shift b0)
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
          (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1
          (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1
          (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1
          (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1 **
        ((sp + signExtend12 3992) ↦ₘ fullDivN1Shift b0)) **
       fullDivN1FrameV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem) := by
  have hshift_nz' : fullDivN1Shift b0 ≠ 0 := by simp only [fullDivN1Shift]; exact hshift_nz
  have hA := evm_div_n1_to_denorm_spec_v5_noNop sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem hbnz hb3z hb2z hb1z hshift_nz halign
  have hB := evm_div_preamble_denorm_epilogue_spec_v5_noNop sp base
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    (fullDivN1Shift b0)
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    (0 : Word) (sp + signExtend12 4056) (sp + signExtend12 4088)
    (fullDivN1C3V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3)
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1
    (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1
    (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1
    (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
    hshift_nz'
  have hBf := cpsTripleWithin_frameR
    (fullDivN1FrameV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)
    (by delta fullDivN1FrameV5; pcFree) hB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      rw [show ((clzResult b0).1) = fullDivN1Shift b0 from by simp only [fullDivN1Shift]] at hp
      have hbr := loopN1UnifiedPostV5_to_denormPreV5 sp base a0 a1 a2 a3 b0 b1 b2 b3 scratchMem h hp
      rw [fullDivN1DenormPreV5_unfold] at hbr
      simp only [se12_32, se12_40, se12_48, se12_56] at hbr
      xperm_hyp hbr)
    hA hBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

end EvmAsm.Evm64
