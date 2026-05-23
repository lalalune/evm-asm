/-
  EvmAsm.Evm64.DivMod.Compose.ModFullPathN3V4NoNop

  v4/no-NOP MOD full-path preloop wrappers for the n=3 case.
-/

import EvmAsm.Evm64.DivMod.Compose.ModFullPathN4V4NoNop
import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNopMaxCall
import EvmAsm.Evm64.DivMod.LoopIterN3MaxV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN3CallV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN3AddbackV4NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Loop body n=3, max+skip, j=0 over `modCode_noNop_v4`, with
    sp-relative addresses hidden behind a named precondition. -/
theorem divK_loop_body_n3_max_skip_j0_norm_mod_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (loopBodyN3MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n3_max_skip_j0_v4_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4) raw
  rw [loopBodyN3MaxSkipPre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  delta loopBodyN3MaxSkipJ0NormPreV4
  exact raw'

/-- Loop body n=3, max+skip, j=1 over `modCode_noNop_v4`, with the
    precondition hidden behind an irreducible definition. -/
theorem divK_loop_body_n3_max_skip_j1_norm_mod_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v4 base)
      (loopBodyN3MaxSkipJ1NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3SkipPost sp (1 : Word) (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n3_max_skip_j1_v4_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN3MaxSkipJ1NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=3, max+addback, j=0 over `modCode_noNop_v4`, with
    sp-relative addresses hidden behind a named precondition. -/
theorem divK_loop_body_n3_max_addback_j0_beq_norm_mod_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (loopBodyN3MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3AddbackBeqPost sp (0 : Word) (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n3_max_addback_j0_beq_v4_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hcarry2_nz hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4) raw
  rw [loopBodyN3MaxSkipPre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  delta loopBodyN3MaxSkipJ0NormPreV4
  exact raw'

/-- Loop body n=3, max+addback, j=1 over `modCode_noNop_v4`, with the
    precondition hidden behind an irreducible definition. -/
theorem divK_loop_body_n3_max_addback_jgt0_beq_norm_mod_v4_noNop (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v4 base)
      (loopBodyN3MaxAddbackJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3AddbackBeqPost sp j (signExtend12 4095 : Word)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n3_max_addback_jgt0_beq_v4_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hcarry2_nz hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN3MaxAddbackJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=3, max path, j=0 over `modCode_noNop_v4`, preserving
    concrete `x1` and callable scratch cells as frame. -/
theorem divK_loop_body_n3_max_j0_mod_v4_spec_within_noNop_exact_x1 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      ((loopBodyN3MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      ((loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) := by
  by_cases hborrow : BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz :
        (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hborrow]
      decide
    have J := divK_loop_body_n3_max_addback_j0_beq_norm_mod_v4_noNop
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hcarry2_nz hborrow_nz
    have Jf := cpsTripleWithin_frameR
      ((sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))
      (by pcFree) J
    exact cpsTripleWithin_weaken
      (fun h hp => by xperm_hyp hp)
      (fun h hp => by
        rw [loopIterPostN3Max_addback hborrow] at hp
        xperm_hyp hp)
      Jf
  · have hborrow_zero :
        (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) = (0 : Word) := by
      rw [if_neg hborrow]
    have J := divK_loop_body_n3_max_skip_j0_norm_mod_v4_noNop
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow_zero
    have Jf := cpsTripleWithin_frameR
      ((sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))
      (by pcFree) J
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => by xperm_hyp hp)
        (fun h hp => by
          rw [loopIterPostN3Max_skip hborrow] at hp
          xperm_hyp hp)
        Jf

/-- Loop body n=3, max path, j=1 over `modCode_noNop_v4`, preserving
    concrete `x1` and callable scratch cells as frame. -/
theorem divK_loop_body_n3_max_j1_mod_v4_spec_within_noNop_exact_x1 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v4 base)
      ((loopBodyN3MaxSkipJ1NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      ((loopIterPostN3Max sp (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal))) := by
  by_cases hborrow : BitVec.ult uTop
      (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz :
        (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) ≠ (0 : Word) := by
      rw [if_pos hborrow]
      decide
    have J := divK_loop_body_n3_max_addback_jgt0_beq_norm_mod_v4_noNop
      (1 : Word) EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hcarry2_nz hborrow_nz
    have Jf := cpsTripleWithin_frameR
      ((sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))
      (by pcFree) J
    exact cpsTripleWithin_weaken
      (fun h hp => by
        delta loopBodyN3MaxSkipJ1NormPreV4 loopBodyN3MaxAddbackJgt0NormPreV4 at hp ⊢
        xperm_hyp hp)
      (fun h hp => by
        rw [loopIterPostN3Max_addback hborrow] at hp
        xperm_hyp hp)
      Jf
  · have hborrow_zero :
        (if BitVec.ult uTop
          (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
         then (1 : Word) else 0) = (0 : Word) := by
      rw [if_neg hborrow]
    have J := divK_loop_body_n3_max_skip_j1_norm_mod_v4_noNop
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow_zero
    have Jf := cpsTripleWithin_frameR
      ((sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       (sp + signExtend12 3936 ↦ₘ scratchMem) **
       (.x1 ↦ᵣ raVal))
      (by pcFree) J
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      cpsTripleWithin_weaken
        (fun h hp => by
          delta loopBodyN3MaxSkipJ1NormPreV4 at hp ⊢
          xperm_hyp hp)
        (fun h hp => by
          rw [loopIterPostN3Max_skip hborrow] at hp
          xperm_hyp hp)
        Jf

/-- Full n=3 max×max path over `modCode_noNop_v4` from the callable-ready
    v4 loop source, preserving concrete `x1`, scratch, and the j=1 stored
    u4/q atoms. -/
theorem divK_loop_n3_max_max_mod_v4_from_source_exact_loopIterScratch_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hcarry2_nz_1 : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      ¬BitVec.ult r1.2.2.2.1 v2)
    (hcarry2_nz_0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      isAddbackCarry2NzN3Max v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (152 + 152) (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1))) := by
  intro r1 uBase1 qAddr1
  have J1 := divK_loop_body_n3_max_j1_mod_v4_spec_within_noNop_exact_x1 sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old raVal
    retMem dMem dloMem scratchUn0 scratchMem hbltu_1 hcarry2_nz_1
  subst r1
  subst uBase1
  subst qAddr1
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  have J0 := divK_loop_body_n3_max_j0_mod_v4_spec_within_noNop_exact_x1 sp base
    (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old raVal retMem dMem dloMem scratchUn0 scratchMem hbltu_0 hcarry2_nz_0
  have J0f := cpsTripleWithin_frameR
    (((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN3MaxScratchX1_j1_to_max_j0_pre
      sp retMem dMem dloMem scratchUn0 scratchMem
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q0Old raVal)
    (cpsTripleWithin_weaken
      (loopN3PreWithScratchV4NoX1_to_max_j1_pre
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem)
      (fun h hp => hp)
      J1f)
    J0f

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

/-- Loop body n=3, call+skip, j=0 over `modCode_noNop_v4`, preserving
    concrete `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n3_call_skip_j0_loopIter_mod_v4_spec_within_noNop_exact_x1 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (loopBodyN3CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN3CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u3 u2 v2)
        (divKTrialCallV4DLo v2)
        (divKTrialCallV4Un0 u2)
        (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  have hb :
      ¬BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) := by
    unfold loopBodyN3CallSkipJ0BorrowV4 mulsubN4NoBorrow at hborrow
    dsimp only [] at hborrow
    intro hlt
    unfold mulsubN4_c3 at hlt
    rw [if_pos hlt] at hborrow
    exact (by decide : (1 : Word) ≠ (0 : Word)) hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      have hpost :
          ((loopBodyN3CallSkipPostJScratchNoX1 sp base (0 : Word)
            (divKTrialCallV4QHat u3 u2 v2)
            (divKTrialCallV4DLo v2)
            (divKTrialCallV4Un0 u2)
            (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop) ** (.x1 ↦ᵣ raVal)) h := by
        unfold loopBodyN3CallSkipJ0PostV4NoX1 at hp
        unfold loopBodyN3CallSkipPostJScratchNoX1
        simpa only [sepConj_assoc'] using hp
      rw [loopIterPostN3CallScratchNoX1_skip hb] at hpost
      exact hpost)
    (divK_loop_body_n3_call_skip_j0_mod_v4_spec_within_noNop_exact_x1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow)

/-- Loop body n=3, call+addback, j=0 over `modCode_noNop_v4`, preserving
    concrete `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n3_call_addback_j0_loopIter_mod_v4_spec_within_noNop_exact_x1 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (loopBodyN3CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN3CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u3 u2 v2)
        (divKTrialCallV4DLo v2)
        (divKTrialCallV4Un0 u2)
        (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  have hb :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) := by
    unfold loopBodyN3CallAddbackBorrowV4 at hborrow
    dsimp only [] at hborrow
    by_contra hlt
    rw [if_neg hlt] at hborrow
    exact hborrow rfl
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      have hpost :
          ((loopBodyN3CallAddbackBeqPostJScratchNoX1 sp base (0 : Word)
            (divKTrialCallV4QHat u3 u2 v2)
            (divKTrialCallV4DLo v2)
            (divKTrialCallV4Un0 u2)
            (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop) ** (.x1 ↦ᵣ raVal)) h := by
        unfold loopBodyN3CallAddbackJ0PostV4NoX1 at hp
        unfold loopBodyN3CallAddbackBeqPostJScratchNoX1
        simpa only [sepConj_assoc'] using hp
      rw [loopIterPostN3CallScratchNoX1_addback hb] at hpost
      exact hpost)
    (divK_loop_body_n3_call_addback_j0_mod_v4_spec_within_noNop_exact_x1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- Loop body n=3, call path, j=0 over `modCode_noNop_v4`, selecting the
    skip or addback correction from the computed mulsub borrow bit. -/
theorem divK_loop_body_n3_call_j0_mod_v4_spec_within_noNop_exact_x1 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (loopBodyN3CallSkipJ0PreV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN3CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat u3 u2 v2)
        (divKTrialCallV4DLo v2)
        (divKTrialCallV4Un0 u2)
        (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow : BitVec.ult uTop
      (mulsubN4_c3 (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      simp [loopBodyN3CallAddbackBorrowV4, hborrow]
    exact divK_loop_body_n3_call_addback_j0_loopIter_mod_v4_spec_within_noNop_exact_x1
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_nz hcarry2_nz
  · have hborrow_zero :
        loopBodyN3CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold loopBodyN3CallSkipJ0BorrowV4 mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (show 148 ≤ 224 by decide) <|
      divK_loop_body_n3_call_skip_j0_loopIter_mod_v4_spec_within_noNop_exact_x1
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_zero

/-- Full n=3 max×call path over `modCode_noNop_v4` from the callable-ready
    v4 loop source, preserving concrete `x1`, scratch, and the j=1 stored
    u4/q atoms. -/
theorem divK_loop_n3_max_call_mod_v4_from_source_exact_loopIterScratch_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : ¬BitVec.ult u3 v2)
    (hcarry2_nz_1 : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      BitVec.ult r1.2.2.2.1 v2)
    (hcarry2_nz_0 :
      let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
      loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    let r1 := iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (152 + 224) (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN3CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat r1.2.2.2.1 r1.2.2.1 v2)
        (divKTrialCallV4DLo v2)
        (divKTrialCallV4Un0 r1.2.2.1)
        (divKTrialCallV4ScratchOut r1.2.2.2.1 r1.2.2.1 v2 scratchMem)
        v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
        (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1))) := by
  intro r1 uBase1 qAddr1
  have J1 := divK_loop_body_n3_max_j1_mod_v4_spec_within_noNop_exact_x1 sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old raVal
    retMem dMem dloMem scratchUn0 scratchMem hbltu_1 hcarry2_nz_1
  subst r1
  subst uBase1
  subst qAddr1
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  have J0 := divK_loop_body_n3_call_j0_mod_v4_spec_within_noNop_exact_x1 sp base
    (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem
    halign hbltu_0 hcarry2_nz_0
  have J0f := cpsTripleWithin_frameR
    (((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN3MaxScratchX1_j1_to_call_j0_pre
      sp retMem dMem dloMem scratchUn0 scratchMem
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q0Old raVal)
    (cpsTripleWithin_weaken
      (loopN3PreWithScratchV4NoX1_to_max_j1_pre
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem)
      (fun h hp => hp)
      J1f)
    J0f

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

/-- Loop body n=3, call+skip, j=1 over `modCode_noNop_v4`, preserving
    concrete `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n3_call_skip_j1_loopIter_mod_v4_spec_within_noNop_exact_x1 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v4 base)
      (loopBodyN3CallSkipJgt0PreV4NoX1 sp (1 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN3CallScratchNoX1 sp base (1 : Word)
        (divKTrialCallV4QHat u3 u2 v2)
        (divKTrialCallV4DLo v2)
        (divKTrialCallV4Un0 u2)
        (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  have hb :
      ¬BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) := by
    unfold mulsubN4NoBorrow at hborrow
    dsimp only [] at hborrow
    intro hlt
    unfold mulsubN4_c3 at hlt
    rw [if_pos hlt] at hborrow
    exact (by decide : (1 : Word) ≠ (0 : Word)) hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      have hpost :
          ((loopBodyN3CallSkipPostJScratchNoX1 sp base (1 : Word)
            (divKTrialCallV4QHat u3 u2 v2)
            (divKTrialCallV4DLo v2)
            (divKTrialCallV4Un0 u2)
            (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop) ** (.x1 ↦ᵣ raVal)) h := by
        unfold loopBodyN3CallSkipJgt0PostV4NoX1 at hp
        unfold loopBodyN3CallSkipPostJScratchNoX1
        simpa only [sepConj_assoc'] using hp
      rw [loopIterPostN3CallScratchNoX1_skip hb] at hpost
      exact hpost)
    (divK_loop_body_n3_call_skip_j1_mod_v4_spec_within_noNop_exact_x1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow)

/-- Loop body n=3, call+addback, j=1 over `modCode_noNop_v4`, preserving
    concrete `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n3_call_addback_j1_loopIter_mod_v4_spec_within_noNop_exact_x1 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v4 base)
      (loopBodyN3CallSkipJgt0PreV4NoX1 sp (1 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN3CallScratchNoX1 sp base (1 : Word)
        (divKTrialCallV4QHat u3 u2 v2)
        (divKTrialCallV4DLo v2)
        (divKTrialCallV4Un0 u2)
        (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  have hb :
      BitVec.ult uTop
        (mulsubN4_c3 (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3) := by
    unfold loopBodyN3CallAddbackBorrowV4 at hborrow
    dsimp only [] at hborrow
    by_contra hlt
    rw [if_neg hlt] at hborrow
    exact hborrow rfl
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => by
      have hpost :
          ((loopBodyN3CallAddbackBeqPostJScratchNoX1 sp base (1 : Word)
            (divKTrialCallV4QHat u3 u2 v2)
            (divKTrialCallV4DLo v2)
            (divKTrialCallV4Un0 u2)
            (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop) ** (.x1 ↦ᵣ raVal)) h := by
        unfold loopBodyN3CallAddbackJgt0PostV4NoX1 at hp
        unfold loopBodyN3CallAddbackBeqPostJScratchNoX1
        simpa only [sepConj_assoc'] using hp
      rw [loopIterPostN3CallScratchNoX1_addback hb] at hpost
      exact hpost)
    (divK_loop_body_n3_call_addback_j1_mod_v4_spec_within_noNop_exact_x1
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz)

/-- Loop body n=3, call path, j=1 over `modCode_noNop_v4`, selecting the
    skip or addback correction from the computed mulsub borrow bit. -/
theorem divK_loop_body_n3_call_j1_mod_v4_spec_within_noNop_exact_x1 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v4 base)
      (loopBodyN3CallSkipJgt0PreV4NoX1 sp (1 : Word) jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN3CallScratchNoX1 sp base (1 : Word)
        (divKTrialCallV4QHat u3 u2 v2)
        (divKTrialCallV4DLo v2)
        (divKTrialCallV4Un0 u2)
        (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) := by
  by_cases hborrow : BitVec.ult uTop
      (mulsubN4_c3 (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)
  · have hborrow_nz : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      simp [loopBodyN3CallAddbackBorrowV4, hborrow]
    exact divK_loop_body_n3_call_addback_j1_loopIter_mod_v4_spec_within_noNop_exact_x1
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_nz hcarry2_nz
  · have hborrow_zero :
        mulsubN4NoBorrow (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (show 148 ≤ 224 by decide) <|
      divK_loop_body_n3_call_skip_j1_loopIter_mod_v4_spec_within_noNop_exact_x1
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_zero

/-- First n=3 call iteration from the callable-ready v4 loop source over
    `modCode_noNop_v4`, preserving concrete `x1` and carrying the j=0 source
    atoms as a frame. -/
theorem divK_loop_n3_call_j1_mod_v4_from_source_exact_loopIterScratch_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (modCode_noNop_v4 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN3CallScratchNoX1 sp base (1 : Word)
        (divKTrialCallV4QHat u3 u2 v2)
        (divKTrialCallV4DLo v2)
        (divKTrialCallV4Un0 u2)
        (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop **
        (.x1 ↦ᵣ raVal)) **
        (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old))) := by
  have J1 := divK_loop_body_n3_call_j1_mod_v4_spec_within_noNop_exact_x1 sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu hcarry2_nz
  have J1f := cpsTripleWithin_frameR
    ((((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 0 ↦ₘ u0Orig) **
     ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old)))
    (by pcFree) J1
  exact cpsTripleWithin_weaken
    (loopN3PreWithScratchV4NoX1_to_call_j1_pre
      sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
      retMem dMem dloMem scratchUn0 scratchMem)
    (fun h hp => hp)
    J1f

/-- Full n=3 call×call path over `modCode_noNop_v4` from the callable-ready
    v4 loop source, preserving concrete `x1` and the j=1 stored u4/q atoms. -/
theorem divK_loop_n3_call_call_mod_v4_from_source_exact_loopIterScratch_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : BitVec.ult u3 v2)
    (hcarry2_nz_1 : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_0 :
      BitVec.ult
        (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1 v2)
    (hcarry2_nz_0 :
      let r1 := iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    let r1 := iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (224 + 224) (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN3CallScratchNoX1 sp base (0 : Word)
        (divKTrialCallV4QHat r1.2.2.2.1 r1.2.2.1 v2)
        (divKTrialCallV4DLo v2)
        (divKTrialCallV4Un0 r1.2.2.1)
        (divKTrialCallV4ScratchOut r1.2.2.2.1 r1.2.2.1 v2
          (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem))
        v0 v1 v2 v3 u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
        (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1))) := by
  intro r1 uBase1 qAddr1
  have J1 := divK_loop_n3_call_j1_mod_v4_from_source_exact_loopIterScratch_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu_1 hcarry2_nz_1
  subst r1
  subst uBase1
  subst qAddr1
  have J0 := divK_loop_body_n3_call_j0_mod_v4_spec_within_noNop_exact_x1 sp base
    (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig
    (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old raVal
    (base + div128CallRetOff) v2 (divKTrialCallV4DLo v2)
    (divKTrialCallV4Un0 u2) (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
    halign hbltu_0 hcarry2_nz_0
  have J0f := cpsTripleWithin_frameR
    (((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN3CallScratchNoX1_j1_to_call_j0_pre
      sp base (divKTrialCallV4QHat u3 u2 v2) (divKTrialCallV4DLo v2)
      (divKTrialCallV4Un0 u2) (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q0Old raVal)
    J1 J0f

/-- Full n=3 call×max path over `modCode_noNop_v4` from the callable-ready
    v4 loop source, preserving concrete `x1`, scratch, and the j=1 stored
    u4/q atoms. -/
theorem divK_loop_n3_call_max_mod_v4_from_source_exact_loopIterScratch_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : BitVec.ult u3 v2)
    (hcarry2_nz_1 : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hbltu_0 :
      let r1 := iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      ¬BitVec.ult r1.2.2.2.1 v2)
    (hcarry2_nz_0 :
      let r1 := iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop
      isAddbackCarry2NzN3Max v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1) :
    let r1 := iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop
    let uBase1 := sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat
    let qAddr1 := sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin (224 + 152) (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      ((loopIterPostN3Max sp (0 : Word) v0 v1 v2 v3
        u0Orig r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 **
        (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
        (sp + signExtend12 3960 ↦ₘ v2) **
        (sp + signExtend12 3952 ↦ₘ (divKTrialCallV4DLo v2)) **
        (sp + signExtend12 3944 ↦ₘ (divKTrialCallV4Un0 u2)) **
        (sp + signExtend12 3936 ↦ₘ (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)) **
        (.x1 ↦ᵣ raVal)) **
        ((uBase1 + signExtend12 4064 ↦ₘ r1.2.2.2.2.2) **
         (qAddr1 ↦ₘ r1.1))) := by
  intro r1 uBase1 qAddr1
  have J1 := divK_loop_n3_call_j1_mod_v4_from_source_exact_loopIterScratch_noNop
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign hbltu_1 hcarry2_nz_1
  subst r1
  subst uBase1
  subst qAddr1
  have J0 := divK_loop_body_n3_max_j0_mod_v4_spec_within_noNop_exact_x1 sp base
    (1 : Word)
    ((1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat)
    (mulsubN4_c3 (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3)
    (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).1
    (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    v0 v1 v2 v3 u0Orig
    (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
    (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1
    q0Old raVal
    (base + div128CallRetOff) v2 (divKTrialCallV4DLo v2)
    (divKTrialCallV4Un0 u2) (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
    hbltu_0 hcarry2_nz_0
  have J0f := cpsTripleWithin_frameR
    (((sp + signExtend12 4056 - (1 : Word) <<< (3 : BitVec 6).toNat) +
      signExtend12 4064 ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.2) **
     ((sp + signExtend12 4088 - (1 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ
        (iterWithDoubleAddback (divKTrialCallV4QHat u3 u2 v2)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).1))
    (by pcFree) J0
  exact cpsTripleWithin_seq_perm_same_cr
    (loopIterPostN3CallScratchNoX1_j1_to_max_j0_pre
      sp base (divKTrialCallV4QHat u3 u2 v2) (divKTrialCallV4DLo v2)
      (divKTrialCallV4Un0 u2) (divKTrialCallV4ScratchOut u3 u2 v2 scratchMem)
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q0Old raVal)
    J1 J0f

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
