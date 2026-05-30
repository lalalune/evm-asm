/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopPreloop

  Preloop setup wrappers for the n=2 v5/no-NOP full DIV path.  Mirror of
  FullPathN2V4NoNopPreloop, lifted to `divCode_noNop_v5` (the preloop runs the
  shared clz/normalize/copyAU instructions, not the differing div128 subroutine).
  Reuses the generic v5 preloop blocks (PhaseAV5/CLZV5/PhaseC2V5/NormBV5/NormAV5/
  LoopSetupV5) + the v5 phaseB code-subsumption lemmas (PhaseBV5); only the
  n=2-specific phaseB / compositions are built here.
-/

import EvmAsm.Evm64.DivMod.Compose.PhaseBV5
import EvmAsm.Evm64.DivMod.Compose.PhaseABV4NoNop
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopUnified

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- v5 phase-B (n=2 detection: b3=b2=0, b1≠0), over `divCode_noNop_v5`.
    Mirror of `evm_div_phaseB_n2_spec_within_v4_noNop` with v5 code subsumption. -/
theorem evm_div_phaseB_n2_spec_within_v5_noNop (sp base : Word)
    (b1 b2 b3 : Word) (v5 v6 v7 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem : Word)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1nz : b1 ≠ 0) :
    cpsTripleWithin 21 (base + phaseBOff) (base + clzOff) (divCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) **
       ((sp + signExtend12 3984) ↦ₘ nMem))
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ b1) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
       ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
       ((sp + signExtend12 3984) ↦ₘ (2 : Word))) := by
  have hinit1_raw := divK_phaseB_init1_spec_within sp (base + phaseBOff) q0 q1 q2 q3 u5 u6 u7
  simp only [phB_off_28] at hinit1_raw
  have hinit1 := cpsTripleWithin_extend_code divK_phaseB_init1_code_sub_divCode_noNop_v5 hinit1_raw
  have hinit1f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit1
  have hinit2_raw := divK_phaseB_init2_spec_within sp (base + phaseBInit2Off) b1 b2 v6 v7
  simp only [phB_i2_8_v4] at hinit2_raw
  have hinit2 := cpsTripleWithin_extend_code divK_phaseB_init2_code_sub_divCode_noNop_v5 hinit2_raw
  have hinit2f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hinit2
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hinit1f hinit2f
  have haddi0_raw := addi_x0_spec_gen_within .x5 v5 4 (base + phaseBStep0Off) (by nofun)
  simp only [phB_addi_4_v4, signExtend12_4] at haddi0_raw
  have haddi0 := cpsTripleWithin_extend_code addi_x5_singleton_sub_divCode_noNop_v5 haddi0_raw
  have haddi0f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi0
  have h123 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12 haddi0f
  have hbne0_raw := bne_spec_gen_within .x10 .x0 24 b3 (0 : Word) (base + phaseBBneOff)
  rw [show (base + phaseBBneOff : Word) + signExtend13 24 = base + phaseBTailOff from by
        rv64_addr, phB_bne_4_v4] at hbne0_raw
  have hbne0_clean := cpsBranchWithin_ntakenStripPure2 hbne0_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb3z ((sepConj_pure_right _).mp h_rest).2)
  have hbne0 := cpsTripleWithin_extend_code bne_x10_singleton_sub_divCode_noNop_v5 hbne0_clean
  have hbne0f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (4 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne0
  have h1234 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h123 hbne0f
  have haddi1_raw := addi_x0_spec_gen_within .x5 (4 : Word) 3 (base + phaseBStep1Off) (by nofun)
  simp only [phB_step1_4_v4, signExtend12_3] at haddi1_raw
  have haddi1 := cpsTripleWithin_extend_code addi_x5_3_sub_divCode_noNop_v5 haddi1_raw
  have haddi1f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi1
  have h12345 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h1234 haddi1f
  have hbne1_raw := bne_spec_gen_within .x7 .x0 16 b2 (0 : Word) (base + phaseBBne2Off)
  rw [show (base + phaseBBne2Off : Word) + signExtend13 16 = base + phaseBTailOff from by
        rv64_addr, phB_step1_8_v4] at hbne1_raw
  have hbne1_clean := cpsBranchWithin_ntakenStripPure2 hbne1_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd hb2z ((sepConj_pure_right _).mp h_rest).2)
  have hbne1 := cpsTripleWithin_extend_code bne_x7_16_sub_divCode_noNop_v5 hbne1_clean
  have hbne1f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (3 : Word)) ** (.x10 ↦ᵣ b3) ** (.x6 ↦ᵣ b1) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne1
  have h123456 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345 hbne1f
  have haddi2_raw := addi_x0_spec_gen_within .x5 (3 : Word) 2 (base + phaseBStep2Off) (by nofun)
  simp only [phB_step2_4_v4, signExtend12_2] at haddi2_raw
  have haddi2 := cpsTripleWithin_extend_code addi_x5_2_sub_divCode_noNop_v5 haddi2_raw
  have haddi2f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) ** (.x6 ↦ᵣ b1) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) haddi2
  have h1234567 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_chunked hp) h123456 haddi2f
  have hbne2_raw := bne_spec_gen_within .x6 .x0 8 b1 (0 : Word) (base + phaseBBne3Off)
  rw [show (base + phaseBBne3Off : Word) + signExtend13 8 = base + phaseBTailOff from by
        rv64_addr, phB_step2_8_v4] at hbne2_raw
  have hbne2_clean := cpsBranchWithin_takenStripPure2 hbne2_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd ((sepConj_pure_right _).mp h_rest).2 hb1nz)
  have hbne2 := cpsTripleWithin_extend_code bne_x6_8_sub_divCode_noNop_v5 hbne2_clean
  have hbne2f := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ (2 : Word)) ** (.x10 ↦ᵣ b3) ** (.x7 ↦ᵣ b2) **
     ((sp + 40) ↦ₘ b1) ** ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3984) ↦ₘ nMem))
    (by pcFree) hbne2
  have h12345678 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_chunked hp) h1234567 hbne2f
  have htail_raw := divK_phaseB_tail_spec_within sp (2 : Word) b1 nMem (base + phaseBTailOff)
  simp only [divK_phaseB_tail_pre_unfold, divK_phaseB_tail_post_unfold,
             phB_t_20_v4, divK_phaseB_n2_nm1_x8_v4, signExtend12_32, phB_sp8_32_v4] at htail_raw
  have htail := cpsTripleWithin_extend_code divK_phaseB_tail_code_sub_divCode_noNop_v5 htail_raw
  have htailf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) ** (.x6 ↦ᵣ b1) ** (.x7 ↦ᵣ b2) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)))
    (by pcFree) htail
  have hphaseB := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) h12345678 htailf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hphaseB

end EvmAsm.Evm64
