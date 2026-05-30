/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5PathShift0

  Bridge from the n=2 v5 shift=0 preloop exit (at `loopBodyOff`, the layout
  produced by `evm_div_n2_to_loopSetup_shift0_spec_v5_noNop`, #7468) to the
  loop's entry bundle `loopN2PreWithScratchV4NoX1` over the RAW divisor
  `(b0, b1, 0, 0)` and shift=0 window — the shift=0 analog of
  `loopSetupPost_to_loopN2PreWithScratchV4NoX1_framed`.  Closes the gap between
  the preloop (#7468) and the loop body (#7471) so they compose into the shift=0
  path `base → denormOff`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5PreloopShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5LoopShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN2Loop
import EvmAsm.Evm64.DivMod.Compose.FullPathN3Loop

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Bridge: shift=0 preloop exit (b2 = b3 = 0) plus the framed scratch/return
    cells implies the loop entry bundle over the raw divisor. -/
theorem n2_shift0_loopExit_to_loopN2PreWithScratch (sp : Word)
    (a0 a1 a2 a3 b0 b1 v11Old jMem retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    ∀ h,
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) **
        (.x9 ↦ᵣ (signExtend12 (4 : BitVec 12) - (2 : Word))) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x10 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ (clzResult b1).1) **
        (.x7 ↦ᵣ (clzResult b1).2 >>> (63 : Nat)) **
        (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - (clzResult b1).1)) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
        ((sp + 48) ↦ₘ (0 : Word)) ** ((sp + 56) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4056) ↦ₘ a0) ** ((sp + signExtend12 4048) ↦ₘ a1) **
        ((sp + signExtend12 4040) ↦ₘ a2) ** ((sp + signExtend12 4032) ↦ₘ a3) **
        ((sp + signExtend12 4024) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (2 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        ((sp + signExtend12 3968) ↦ₘ retMem) ** ((sp + signExtend12 3960) ↦ₘ dMem) **
        ((sp + signExtend12 3952) ↦ₘ dloMem) ** ((sp + signExtend12 3944) ↦ₘ scratchUn0) **
        ((sp + signExtend12 3936) ↦ₘ scratchMem) ** (.x1 ↦ᵣ raVal))) h →
      ((loopN2PreWithScratchV4NoX1 sp jMem (2 : Word) (clzResult b1).1
        ((clzResult b1).2 >>> (63 : Nat)) (0 : Word) v11Old
        (signExtend12 (0 : BitVec 12) - (clzResult b1).1)
        b0 b1 0 0 a2 a3 0 0 0 a1 a0 0 0 0
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b1).1))) h := by
  intro h hp
  rw [show signExtend12 (4 : BitVec 12) - (2 : Word) = (2 : Word) from by decide] at hp
  delta loopN2PreWithScratchV4NoX1 loopN2PreWithScratchNoX1 loopN2Pre
  simp only [n2_ub2_off0, n2_ub2_off4088, n2_ub2_off4080, n2_ub2_off4072, n2_ub2_off4064,
    n3_ub1_off0, n3_ub0_off0, n2_qa2, n3_qa1, n3_qa0,
    se12_32, se12_40, se12_48, se12_56] at hp ⊢
  xperm_hyp hp

end EvmAsm.Evm64
