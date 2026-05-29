/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V5PreloopShift0

  v5 n=1 shift=0 preloop composition over `divCode_noNop_v5`.  On the shift = 0
  branch the divisor is already top-bit-aligned, so normalization is skipped:
  phase-C2 takes the BEQ to copyAU, the dividend is copied verbatim into the
  u-cells, and loop-setup falls through to the loop body.  This file composes the
  shift=0-specific middle segment `copyAU + loopSetup` (copyAUOff → loopBodyOff),
  the analog of the shift≠0 `normB + normA + loopSetup` tail in
  `FullPathN1V5Preloop`.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.Compose.CopyAUV5
import EvmAsm.Evm64.DivMod.Compose.LoopSetupV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 shift=0 middle segment: copy-AU then loop-setup (BLT-not-taken), from
    `copyAUOff` to `loopBodyOff`, over `divCode_noNop_v5`.  The dividend `a[0..3]`
    lands in the u-cells (`u[4]` zeroed) and the loop counter `x5 ← n`,
    `x9 ← m = 4 − n`.  `hm_ge` rules out the degenerate `n > 4` BLT-taken case
    (holds for the n=1 lane where `n = 1`). -/
theorem divK_copyAU_loopSetup_shift0_spec_v5_noNop (sp base : Word)
    (a0 a1 a2 a3 u0 u1 u2 u3 u4 v5 v1 n : Word)
    (hm_ge : ¬BitVec.slt (signExtend12 (4 : BitVec 12) - n) (0 : Word)) :
    cpsTripleWithin 13 (base + copyAUOff) (base + loopBodyOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x9 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ u4))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ n) **
       (.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - n)) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ n) **
       ((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
       ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
       ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
       ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
       ((sp + signExtend12 4024) ↦ₘ (0 : Word))) := by
  have hCopy := divK_copyAU_spec_within_v5_noNop sp base a0 a1 a2 a3 u0 u1 u2 u3 u4 v5
  have hCopyF := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ v1) ** (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ n))
    (by pcFree) hCopy
  have hLS := divK_loopSetup_ntaken_spec_within_v5_noNop sp n v1 a3 base hm_ge
  simp only [divKLoopSetupNtakenPreNoNop_unfold, divKLoopSetupNtakenPostNoNop_unfold] at hLS
  have hLSF := cpsTripleWithin_frameR
    (((sp + signExtend12 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
     ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
     ((sp + signExtend12 4024) ↦ₘ (0 : Word)))
    (by pcFree) hLS
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hCopyF hLSF
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hFull

end EvmAsm.Evm64
