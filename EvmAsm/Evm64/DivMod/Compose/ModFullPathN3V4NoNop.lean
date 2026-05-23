/-
  EvmAsm.Evm64.DivMod.Compose.ModFullPathN3V4NoNop

  v4/no-NOP MOD full-path preloop wrappers for the n=3 case.
-/

import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4V4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN3CallV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN3AddbackV4NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- No-NOP/v4 n=3 call+skip j=0 over the MOD code bundle, preserving
    concrete caller `x1`. -/
theorem divK_loop_body_n3_call_skip_j0_mod_v4_spec_within_noNop_exact_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (loopBodyN3CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN3CallSkipJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
    (divK_loop_body_n3_call_skip_j0_v4_spec_within_noNop_exact_x1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow)

/-- No-NOP/v4 n=3 call+addback j=0 over the MOD code bundle, preserving
    concrete caller `x1`. -/
theorem divK_loop_body_n3_call_addback_j0_mod_v4_spec_within_noNop_exact_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (loopBodyN3CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN3CallAddbackJ0PostV4NoX1 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
    (divK_loop_body_n3_call_addback_j0_beq_v4_spec_within_noNop_exact_x1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- No-NOP/v4 n=3 call+skip j=1 over the MOD code bundle, preserving
    concrete caller `x1`. -/
theorem divK_loop_body_n3_call_skip_j1_mod_v4_spec_within_noNop_exact_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v4 base)
      (loopBodyN3CallSkipJgt0PreV4NoX1 sp (1 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN3CallSkipJgt0PostV4NoX1 sp base (1 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
    (divK_loop_body_n3_call_skip_j1_v4_spec_within_noNop_exact_x1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow)

/-- No-NOP/v4 n=3 call+addback j=1 over the MOD code bundle, preserving
    concrete caller `x1`. -/
theorem divK_loop_body_n3_call_addback_j1_mod_v4_spec_within_noNop_exact_x1
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (base : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v4 base)
      (loopBodyN3CallSkipJgt0PreV4NoX1 sp (1 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopBodyN3CallAddbackJgt0PostV4NoX1 sp base (1 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  exact cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
    (divK_loop_body_n3_call_addback_jgt0_beq_v4_spec_within_noNop_exact_x1
      (1 : Word) EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- MOD n=3 path from entry to NormA over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_n3_to_normB_spec_within_v4_noNop (sp base : Word)
    (b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21) base (base + normAOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
       ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
       ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
       ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
       ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
       ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
       ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (normBPost sp (3 : Word) (clzResult b2).1 b0 b1 b2 b3) := by
  let shift := (clzResult b2).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  have hABCLZ := evm_mod_phaseAB_n3_clz_spec_within_v4_noNop sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem hbnz hb3z hb2nz
  have hABCLZf := cpsTripleWithin_frameR
    ((.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
     ((sp + signExtend12 3992) ↦ₘ shiftMem))
    (by pcFree) hABCLZ
  have hC2 := divK_phaseC2_ntaken_spec_within_mod_v4_noNop sp shift ((clzResult b2).2 >>> (63 : Nat))
    shiftMem base hshift_nz
  have hC2f := cpsTripleWithin_frameR
    ((.x5 ↦ᵣ (clzResult b2).2) ** (.x10 ↦ᵣ b3) **
     (.x7 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
     ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
     ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)))
    (by pcFree) hC2
  have hABC2 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABCLZf hC2f
  have hNB := divK_normB_full_spec_within_mod_v4_noNop sp b0 b1 b2 b3
    (clzResult b2).2 ((clzResult b2).2 >>> (63 : Nat))
    shift antiShift base
  simp only [normBFullPost_unfold] at hNB
  have hNBf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ b3) ** (.x0 ↦ᵣ (0 : Word)) **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNB
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hABC2 hNBf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta normBPost; xperm_hyp hq)
    hFull

/-- MOD n=3 path from entry to loop body start over the no-NOP v4 MOD code bundle. -/
theorem evm_mod_n3_to_loopSetup_spec_within_v4_noNop (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4) base (base + loopBodyOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ (clzResult b2).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
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
       ((sp + signExtend12 3992) ↦ₘ shiftMem))
      (loopSetupPost sp (3 : Word) (clzResult b2).1 a0 a1 a2 a3 b0 b1 b2 b3) := by
  let shift := (clzResult b2).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  have hNormB := evm_mod_n3_to_normB_spec_within_v4_noNop sp base b0 b1 b2 b3 v5 v6 v7 v10
    q0 q1 q2 q3 u5 u6 u7 nMem shiftMem hbnz hb3z hb2nz hshift_nz
  have hNormBf := cpsTripleWithin_frameR
    ((.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
     ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
     ((sp + signExtend12 4024) ↦ₘ u4Old))
    (by pcFree) hNormB
  have hNormA := divK_normA_full_spec_within_mod_v4_noNop sp a0 a1 a2 a3
    b0' (b0 >>> (antiShift.toNat % 64)) b3 shift antiShift
    u0Old u1Old u2Old u3Old u4Old base
  rw [divKNormAFullPreNoNop_unfold] at hNormA
  simp only [normAFullPost_unfold] at hNormA
  have hNormAf := cpsTripleWithin_frameR
    ((.x0 ↦ᵣ (0 : Word)) **
     (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
     ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
     ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) ** ((sp + signExtend12 3984) ↦ₘ (3 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hNormA
  have hNA := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by delta normBPost at hp; xperm_hyp hp) hNormBf hNormAf
  have hLS := divK_loopSetup_ntaken_spec_within_mod_v4_noNop sp (3 : Word)
    (signExtend12 (4 : BitVec 12) - (4 : Word)) u1 base
    (by decide)
  simp only [divKLoopSetupNtakenPreNoNop_unfold,
      divKLoopSetupNtakenPostNoNop_unfold] at hLS
  have hLSf := cpsTripleWithin_frameR
    ((.x10 ↦ᵣ (a0 >>> (antiShift.toNat % 64))) **
     (.x6 ↦ᵣ shift) ** (.x7 ↦ᵣ u0) ** (.x2 ↦ᵣ antiShift) **
     ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
     ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
     ((sp + 32) ↦ₘ b0') ** ((sp + 40) ↦ₘ b1') **
     ((sp + 48) ↦ₘ b2') ** ((sp + 56) ↦ₘ b3') **
     ((sp + signExtend12 4088) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4080) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4072) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
     ((sp + signExtend12 4024) ↦ₘ u4) **
     ((sp + signExtend12 4016) ↦ₘ (0 : Word)) ** ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
     ((sp + signExtend12 3992) ↦ₘ shift))
    (by pcFree) hLS
  have hFull := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hNA hLSf
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by delta loopSetupPost; xperm_hyp hq)
    hFull

end EvmAsm.Evm64
