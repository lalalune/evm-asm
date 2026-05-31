/-
  EvmAsm.Evm64.DivMod.Compose.PreloopV5Mod

  v5 preloop bricks re-pointed at `modCode_noNop_v5` (the MOD code surface).

  The preloop blocks (phase-A, CLZ, phase-C2, normB, normA, copyAU, loopSetup)
  live in the shared blocks 0–9 of the v5 code surface and never touch the
  epilogue (block 10), so each one's body extends to the MOD surface via the
  `sharedNoNop_v5_b*_mod` block subsumptions — exactly as the DIV bricks
  (`PhaseAV5.lean`, …) extend via `sharedNoNop_v5_b*_div`.

  WHY this is needed (bead `evm-asm-wbc4i.10.3.2.4.5`): a `cpsTripleWithin` over
  `divCode_noNop_v5` requires `divCode_noNop_v5.SatisfiedBy s`, i.e. the state's
  code must contain the DIV epilogue — so a DIV-surface preloop/loop spec is
  unusable for a MOD path (a MOD state lacks the DIV epilogue and there is no
  `divCode ⊆ modCode`).  Re-pointing the preloop+loop onto `modCode_noNop_v5`
  (or a shared surface) is the only sound fix; these MOD bricks are the first
  pieces.  This file accumulates them brick by brick.
-/

import EvmAsm.Evm64.DivMod.Compose.PhaseABV4NoNop
import EvmAsm.Evm64.DivMod.Compose.V5NoNop

namespace EvmAsm.Evm64

open EvmAsm.Rv64

private theorem divK_phaseA_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (divK_phaseA_code base) a = some i → (modCode_noNop_v5 base) a = some i := by
  unfold divK_phaseA_code
  intro a i h
  exact sharedNoNop_v5_b0_mod a i h

private theorem beq_singleton_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseABeqOff) (.BEQ .x5 .x0 1020)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b0_mod a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup base (divK_phaseA 1020) 7
      (by decide) (by decide)) a i h)

/-- v5 phase-A (b ≠ 0) over `modCode_noNop_v5`: OR-reduce b limbs, BEQ not taken →
    phase-B.  MOD mirror of `evm_div_phaseA_ntaken_spec_within_v5_noNop`
    (`PhaseAV5.lean`); phase-A doesn't touch the epilogue, so the body is
    identical apart from the `_mod` block subsumption. -/
theorem evm_mod_phaseA_ntaken_spec_within_v5_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v10 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0) :
    cpsTripleWithin 8 base (base + phaseBOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (b0 ||| b1 ||| b2 ||| b3)) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3)) := by
  have hbody := cpsTripleWithin_extend_code divK_phaseA_code_sub_modCode_noNop_v5
    (divK_phaseA_body_spec_within sp base b0 b1 b2 b3 v5 v10)
  have hbeq_raw := beq_spec_gen_within .x5 .x0 1020 (b0 ||| b1 ||| b2 ||| b3) (0 : Word) (base + phaseABeqOff)
  rw [show (base + phaseABeqOff : Word) + signExtend13 1020 = base + zeroPathOff from by rv64_addr,
      show (base + phaseABeqOff : Word) + 4 = base + phaseBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranchWithin_ntakenStripPure2 hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hbnz)
  have hbeq := cpsTripleWithin_extend_code beq_singleton_sub_modCode_noNop_v5 hbeq_clean
  have hbeq_framed := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3))
    (by pcFree) hbeq
  have hAB := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeq_framed
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hAB

end EvmAsm.Evm64
