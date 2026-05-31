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
import EvmAsm.Evm64.DivMod.Compose.CLZ
import EvmAsm.Evm64.DivMod.Compose.Norm
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

-- ============================================================================
-- Brick 2: count-leading-zeros (clzOff → phaseC2Off) over modCode_noNop_v5.
-- MOD mirror of `divK_clz_spec_within_v5_noNop` (CLZV5.lean), `_div` → `_mod`.
-- ============================================================================

/-- CLZ block instructions are subsumed by `modCode_noNop_v5`. -/
private theorem divK_clz_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.ofProg (base + clzOff) divK_clz) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact sharedNoNop_v5_b2_mod a i h

private theorem clz_stage_sub_modCode_noNop_v5 {base : Word}
    (K M_s : BitVec 6) (M_a : BitVec 12) (k : Nat)
    (hk : k + (divK_clz_stage_prog K M_s M_a).length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take (divK_clz_stage_prog K M_s M_a).length =
      divK_clz_stage_prog K M_s M_a)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_stage_code K M_s M_a ((base + clzOff) + BitVec.ofNat 64 (4 * k))) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCode_noNop_v5 a i
    (CodeReq.ofProg_mono_sub (base + clzOff) _ divK_clz _ k
      rfl hslice hk hbound a i h)

private theorem clz_last_sub_modCode_noNop_v5 {base : Word} (k : Nat)
    (hk : k + divK_clz_last_prog.length ≤ divK_clz.length)
    (hslice : (divK_clz.drop k).take divK_clz_last_prog.length = divK_clz_last_prog)
    (hbound : 4 * divK_clz.length < 2 ^ 64) :
    ∀ a i, (divK_clz_last_code ((base + clzOff) + BitVec.ofNat 64 (4 * k))) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCode_noNop_v5 a i
    (CodeReq.ofProg_mono_sub (base + clzOff) _ divK_clz _ k
      rfl hslice hk hbound a i h)

private theorem clz_init_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + clzOff) (.ADDI .x6 .x0 0)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  exact divK_clz_code_sub_modCode_noNop_v5 a i
    (CodeReq.singleton_mono (CodeReq.ofProg_lookup (base + clzOff) divK_clz 0
      (by decide) (by decide)) a i (by rwa [show (base + clzOff : Word) =
        base + clzOff + BitVec.ofNat 64 (4 * 0) from by bv_addr] at h))

/-- v5 count-leading-zeros full brick over `modCode_noNop_v5`.  MOD mirror of
    `divK_clz_spec_within_v5_noNop`. -/
theorem divK_clz_spec_within_v5_noNop_modCode (val v6Old v7Old : Word) (base : Word) :
    cpsTripleWithin 24 (base + clzOff) (base + phaseC2Off) (modCode_noNop_v5 base)
      ((.x5 ↦ᵣ val) ** (.x6 ↦ᵣ v6Old) ** (.x7 ↦ᵣ v7Old) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x5 ↦ᵣ (clzResult val).2) ** (.x6 ↦ᵣ (clzResult val).1) **
       (.x7 ↦ᵣ (clzResult val).2 >>> (63 : Nat)) ** (.x0 ↦ᵣ (0 : Word))) := by
  unfold clzResult
  have I := divK_clz_init_spec_within v6Old (base + clzOff)
  have Ie := cpsTripleWithin_extend_code (hmono := clz_init_sub_modCode_noNop_v5) I
  have Ief := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ val) ** (.x7 ↦ᵣ v7Old)) (by pcFree) Ie
  have S0 := divK_clz_stage_combined_within 32 32 32 val (signExtend12 0) v7Old
    ((base + clzOff) + BitVec.ofNat 64 (4 * 1))
  dsimp only [] at S0
  have S0e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCode_noNop_v5 32 32 32 1
    (by decide) (by decide) (by decide)) S0
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 1) = base + clzOff + 4 from by bv_addr] at S0e
  rw [clz_addr1] at S0e
  seqFrame Ief S0e
  let v0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then val else val <<< (32 : BitVec 6).toNat
  let c0 := if val >>> (32 : BitVec 6).toNat ≠ 0 then signExtend12 (0 : BitVec 12)
    else signExtend12 (0 : BitVec 12) + signExtend12 (32 : BitVec 12)
  have S1 := divK_clz_stage_combined_within 48 16 16 v0 c0 (val >>> (32 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 5))
  dsimp only [] at S1
  have S1e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCode_noNop_v5 48 16 16 5
    (by decide) (by decide) (by decide)) S1
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 5) = base + clzOff + 20 from by bv_addr] at S1e
  rw [clz_addr2] at S1e
  seqFrame IefS0e S1e
  let v1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then v0 else v0 <<< (16 : BitVec 6).toNat
  let c1 := if v0 >>> (48 : BitVec 6).toNat ≠ 0 then c0 else c0 + signExtend12 (16 : BitVec 12)
  have S2 := divK_clz_stage_combined_within 56 8 8 v1 c1 (v0 >>> (48 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 9))
  dsimp only [] at S2
  have S2e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCode_noNop_v5 56 8 8 9
    (by decide) (by decide) (by decide)) S2
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 9) = base + clzOff + 36 from by bv_addr] at S2e
  rw [clz_addr3] at S2e
  seqFrame IefS0eS1e S2e
  let v2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then v1 else v1 <<< (8 : BitVec 6).toNat
  let c2 := if v1 >>> (56 : BitVec 6).toNat ≠ 0 then c1 else c1 + signExtend12 (8 : BitVec 12)
  have S3 := divK_clz_stage_combined_within 60 4 4 v2 c2 (v1 >>> (56 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 13))
  dsimp only [] at S3
  have S3e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCode_noNop_v5 60 4 4 13
    (by decide) (by decide) (by decide)) S3
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 13) = base + clzOff + 52 from by bv_addr] at S3e
  rw [clz_addr4] at S3e
  seqFrame IefS0eS1eS2e S3e
  let v3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then v2 else v2 <<< (4 : BitVec 6).toNat
  let c3 := if v2 >>> (60 : BitVec 6).toNat ≠ 0 then c2 else c2 + signExtend12 (4 : BitVec 12)
  have S4 := divK_clz_stage_combined_within 62 2 2 v3 c3 (v2 >>> (60 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 17))
  dsimp only [] at S4
  have S4e := cpsTripleWithin_extend_code (hmono := clz_stage_sub_modCode_noNop_v5 62 2 2 17
    (by decide) (by decide) (by decide)) S4
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 17) = base + clzOff + 68 from by bv_addr] at S4e
  rw [clz_addr5] at S4e
  seqFrame IefS0eS1eS2eS3e S4e
  let v4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then v3 else v3 <<< (2 : BitVec 6).toNat
  let c4 := if v3 >>> (62 : BitVec 6).toNat ≠ 0 then c3 else c3 + signExtend12 (2 : BitVec 12)
  have S5 := divK_clz_last_combined_within v4 c4 (v3 >>> (62 : BitVec 6).toNat)
    ((base + clzOff) + BitVec.ofNat 64 (4 * 21))
  dsimp only [] at S5
  have S5e := cpsTripleWithin_extend_code (hmono := clz_last_sub_modCode_noNop_v5 21
    (by decide) (by decide) (by decide)) S5
  rw [show (base + clzOff : Word) + BitVec.ofNat 64 (4 * 21) = base + clzOff + 84 from by bv_addr] at S5e
  rw [clz_addr6] at S5e
  seqFrame IefS0eS1eS2eS3eS4e S5e
  exact cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    IefS0eS1eS2eS3eS4eS5e

-- ============================================================================
-- Brick 3: phase-C2 (phaseC2Off → normBOff / copyAUOff) over modCode_noNop_v5.
-- MOD mirror of `divK_phaseC2_{ntaken,taken}_spec_within_v5_noNop` (PhaseC2V5.lean).
-- ============================================================================

/-- Phase-C2 block instructions are subsumed by `modCode_noNop_v5`. -/
private theorem divK_phaseC2_code_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (divK_phaseC2_code 172 (base + phaseC2Off)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  unfold divK_phaseC2_code
  intro a i h
  exact sharedNoNop_v5_b3_mod a i h

/-- BEQ x6 x0 172 singleton subsumed by `modCode_noNop_v5`. -/
private theorem beq_shift_sub_modCode_noNop_v5 {base : Word} :
    ∀ a i, (CodeReq.singleton (base + phaseC2Off + 12) (.BEQ .x6 .x0 172)) a = some i →
      (modCode_noNop_v5 base) a = some i := by
  intro a i h
  have hlookup := CodeReq.ofProg_lookup (base + phaseC2Off) (divK_phaseC2 172) 3
    (by decide) (by decide)
  rw [show (BitVec.ofNat 64 (4 * 3) : Word) = (12 : Word) from by decide] at hlookup
  exact divK_phaseC2_code_sub_modCode_noNop_v5 a i
    (CodeReq.singleton_mono hlookup a i h)

private theorem divK_phaseC2_body_modCode_noNop_v5_within
    (sp shift v2 shiftMem : Word) (base : Word) :
    cpsTripleWithin 3 (base + phaseC2Off) (base + phaseC2Off + 12) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_spec_within sp shift v2 shiftMem 172 (base + phaseC2Off)
  exact cpsTripleWithin_extend_code divK_phaseC2_code_sub_modCode_noNop_v5 hbody

/-- v5 phase-C2 (shift ≠ 0) over `modCode_noNop_v5`: BEQ not taken → normB. -/
theorem divK_phaseC2_ntaken_spec_within_v5_noNop_modCode (sp shift v2 shiftMem : Word) (base : Word)
    (hshift_nz : shift ≠ 0) :
    cpsTripleWithin 4 (base + phaseC2Off) (base + normBOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_modCode_noNop_v5_within sp shift v2 shiftMem base
  have hbeq_raw := beq_spec_gen_within .x6 .x0 172 shift (0 : Word) (base + phaseC2Off + 12)
  rw [show (base + phaseC2Off + 12 : Word) + signExtend13 172 = base + copyAUOff from by rv64_addr,
      show (base + phaseC2Off + 12 : Word) + 4 = base + normBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranchWithin_ntakenStripPure2 hbeq_raw
    (fun hp hQt => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQt
      exact absurd ((sepConj_pure_right _).mp h_rest).2 (show shift ≠ (0 : Word) from hshift_nz))
  have hbeq := cpsTripleWithin_extend_code beq_shift_sub_modCode_noNop_v5 hbeq_clean
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeqf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hC2

/-- v5 phase-C2 (shift = 0) over `modCode_noNop_v5`: BEQ taken → copyAU. -/
theorem divK_phaseC2_taken_spec_within_v5_noNop_modCode (sp shift v2 shiftMem : Word) (base : Word)
    (hshift_z : shift = 0) :
    cpsTripleWithin 4 (base + phaseC2Off) (base + copyAUOff) (modCode_noNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ v2) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ shift) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
       (.x0 ↦ᵣ (0 : Word)) ** ((sp + signExtend12 3992) ↦ₘ shift)) := by
  have hbody := divK_phaseC2_body_modCode_noNop_v5_within sp shift v2 shiftMem base
  have hbeq_raw := beq_spec_gen_within .x6 .x0 172 shift (0 : Word) (base + phaseC2Off + 12)
  rw [show (base + phaseC2Off + 12 : Word) + signExtend13 172 = base + copyAUOff from by rv64_addr,
      show (base + phaseC2Off + 12 : Word) + 4 = base + normBOff from by bv_addr] at hbeq_raw
  have hbeq_clean := cpsBranchWithin_takenStripPure2 hbeq_raw
    (fun hp hQf => by
      obtain ⟨_, _, _, _, _, h_rest⟩ := hQf
      exact absurd hshift_z ((sepConj_pure_right _).mp h_rest).2)
  have hbeq := cpsTripleWithin_extend_code beq_shift_sub_modCode_noNop_v5 hbeq_clean
  have hbeqf := cpsTripleWithin_frameR
    ((.x12 ↦ᵣ sp) ** (.x2 ↦ᵣ (signExtend12 (0 : BitVec 12) - shift)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hbeq
  have hC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hbody hbeqf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    hC2

end EvmAsm.Evm64
