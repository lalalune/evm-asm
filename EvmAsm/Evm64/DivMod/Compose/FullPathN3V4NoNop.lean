/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNop

  v4/no-NOP wrappers for the n=3 DIV loop-body j=0 exit paths.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified
import EvmAsm.Evm64.DivMod.Compose.FullPathV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN3MaxV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN3CallV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN3AddbackV4NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Sp-relative n=3 max-skip j=0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN3MaxSkipJ0NormPreV4
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  (.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
  (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
  (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
  (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
  (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (3 : Word)) **
  ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
  ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
  ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
  ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
  ((sp + signExtend12 4024) ↦ₘ uTop) **
  ((sp + signExtend12 4088) ↦ₘ qOld)

/-- Sp-relative n=3 call-skip j=0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN3CallSkipJ0NormPreV4
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN3MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld **
  (sp + signExtend12 3968 ↦ₘ retMem) **
  (sp + signExtend12 3960 ↦ₘ dMem) **
  (sp + signExtend12 3952 ↦ₘ dloMem) **
  (sp + signExtend12 3944 ↦ₘ scratchUn0) **
  regOwn .x1 ** (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- n=3 max-skip j=1 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN3MaxSkipJ1NormPreV4
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  loopBodyN3MaxSkipPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld

/-- n=3 call-skip j=1 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN3CallSkipJ1NormPreV4
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN3CallSkipPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 **
  (sp + signExtend12 3936 ↦ₘ scratchMem)

/-- n=3 max-addback j>0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN3MaxAddbackJgt0NormPreV4 (j : Word)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word) : Assertion :=
  loopBodyN3MaxSkipPre sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    j v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld

/-- n=3 call-addback j>0 precondition over `divCode_noNop_v4`. -/
@[irreducible]
def loopBodyN3CallAddbackJgt0NormPreV4 (j : Word)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  loopBodyN3CallAddbackJgt0PreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem

/-- Loop body n=3, max+skip, j=0 over `divCode_noNop_v4`, with
    sp-relative addresses hidden behind a named precondition. -/
theorem divK_loop_body_n3_max_skip_j0_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN3MaxSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld)
      (loopBodyN3SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n3_max_skip_j0_v4_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  rw [loopBodyN3MaxSkipPre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  delta loopBodyN3MaxSkipJ0NormPreV4
  exact raw'

/-- Loop body n=3, max+skip, j=1 over `divCode_noNop_v4`, with
    the precondition hidden behind an irreducible definition. -/
theorem divK_loop_body_n3_max_skip_j1_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
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
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN3MaxSkipJ1NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=3, max+addback (BEQ double-addback), j>0 over
    `divCode_noNop_v4`, with the precondition hidden behind an irreducible
    definition. -/
theorem divK_loop_body_n3_max_addback_jgt0_beq_norm_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
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
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN3MaxAddbackJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=3, call+skip, j=0 over `divCode_noNop_v4`, with
    sp-relative addresses hidden behind a named precondition. -/
theorem divK_loop_body_n3_call_skip_j0_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN3CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n3_call_skip_j0_v4_spec_within_noNop
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow)
  rw [loopBodyN3CallSkipJ0PreV4_unfold] at raw
  rw [loopBodyN3CallSkipPre_unfold] at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN3CallSkipJ0NormPreV4 loopBodyN3MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Loop body n=3, call+skip, j=1 over `divCode_noNop_v4`, with
    the precondition hidden behind an irreducible definition. -/
theorem divK_loop_body_n3_call_skip_j1_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN3CallSkipJ1NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallSkipJgt0PostV4 sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw := divK_loop_body_n3_call_skip_j1_v4_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
    retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN3CallSkipJ1NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=3, call+addback (BEQ double-addback), j>0 over
    `divCode_noNop_v4`, with the precondition hidden behind an irreducible
    definition. -/
theorem divK_loop_body_n3_call_addback_jgt0_beq_norm_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN3CallAddbackJgt0NormPreV4 j sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallAddbackJgt0PostV4 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw := divK_loop_body_n3_call_addback_jgt0_beq_v4_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
    retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu hborrow hcarry2_nz
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN3CallAddbackJgt0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

/-- Loop body n=3, max+addback (BEQ double-addback), j=0 over
    `divCode_noNop_v4`, with sp-relative addresses hidden behind a named
    precondition. -/
theorem divK_loop_body_n3_max_addback_j0_beq_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult u3 v2)
    (hcarry2_nz : isAddbackCarry2NzN3Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
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
    (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4) raw
  rw [loopBodyN3MaxSkipPre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  delta loopBodyN3MaxSkipJ0NormPreV4
  exact raw'

/-- Loop body n=3, call+addback (BEQ double-addback), j=0 over
    `divCode_noNop_v4`, with sp-relative addresses hidden behind a named
    precondition. -/
theorem divK_loop_body_n3_call_addback_j0_beq_norm_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
      (loopBodyN3CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n3_call_addback_j0_beq_v4_spec_within_noNop
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow hcarry2_nz)
  rw [loopBodyN3CallSkipJ0PreV4_unfold] at raw
  rw [loopBodyN3CallSkipPre_unfold] at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN3CallSkipJ0NormPreV4 loopBodyN3MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Loop body n=3, call+skip, j=0 over `divCode_noNop_v4`, preserving
    concrete `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n3_call_skip_j0_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
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
    (cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n3_call_skip_j0_v4_spec_within_noNop_exact_x1
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow))

/-- Loop body n=3, call+skip, j=1 over `divCode_noNop_v4`, preserving
    concrete `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n3_call_skip_j1_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
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
    (cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n3_call_skip_j1_v4_spec_within_noNop_exact_x1
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow))

/-- Loop body n=3, call+addback, j=0 over `divCode_noNop_v4`, preserving
    concrete `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n3_call_addback_j0_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
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
    (cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n3_call_addback_j0_beq_v4_spec_within_noNop_exact_x1
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz))

/-- Loop body n=3, call+addback, j>0 over `divCode_noNop_v4`, preserving
    concrete `x1` and exposing the scratch loop-iteration post. -/
theorem divK_loop_body_n3_call_addback_jgt0_exact_loopIterScratch_v4_noNop (j sp base : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : loopBodyN3CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
      (loopBodyN3CallSkipJgt0PreV4NoX1 sp j jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopIterPostN3CallScratchNoX1 sp base j
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
          ((loopBodyN3CallAddbackBeqPostJScratchNoX1 sp base j
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
    (cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_divCode_noNop_v4)
      (divK_loop_body_n3_call_addback_jgt0_beq_v4_spec_within_noNop_exact_x1 j hpos
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem base halign hbltu hborrow hcarry2_nz))

/-- Loop body n=3, call path, j=0 over `divCode_noNop_v4`, selecting the
    skip or addback correction from the computed mulsub borrow bit. -/
theorem divK_loop_body_n3_call_j0_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v4 base)
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
    exact divK_loop_body_n3_call_addback_j0_exact_loopIterScratch_v4_noNop
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_nz hcarry2_nz
  · have hborrow_zero :
        loopBodyN3CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold loopBodyN3CallSkipJ0BorrowV4 mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      divK_loop_body_n3_call_skip_j0_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_zero

/-- Loop body n=3, call path, j=1 over `divCode_noNop_v4`, selecting the
    skip or addback correction from the computed mulsub borrow bit. -/
theorem divK_loop_body_n3_call_j1_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
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
    exact divK_loop_body_n3_call_addback_jgt0_exact_loopIterScratch_v4_noNop
      (1 : Word) sp base EvmAsm.Evm64.DivMod.AddrNorm.slt_jpos_1
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
      retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_nz hcarry2_nz
  · have hborrow_zero :
        mulsubN4NoBorrow (divKTrialCallV4QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
      unfold mulsubN4NoBorrow
      dsimp only
      unfold mulsubN4_c3 at hborrow
      rw [if_neg hborrow]
    exact cpsTripleWithin_mono_nSteps (by decide) <|
      divK_loop_body_n3_call_skip_j1_exact_loopIterScratch_v4_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hbltu hborrow_zero

/-- The callable-ready v4 n=3 loop source specializes to the j=1 call-body
    precondition, with j=0 source atoms retained as a frame. -/
theorem loopN3PreWithScratchV4NoX1_to_call_j1_pre
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) :
    ∀ h,
      (loopN3PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) h →
      ((loopBodyN3CallSkipJgt0PreV4NoX1 sp (1 : Word)
        jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop q1Old
        retMem dMem dloMem scratchUn0 scratchMem ** (.x1 ↦ᵣ raVal)) **
        (((sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat) +
          signExtend12 0 ↦ₘ u0Orig) **
         ((sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat) ↦ₘ q0Old))) h := by
  intro h hp
  delta loopN3PreWithScratchV4NoX1 loopN3PreWithScratchNoX1 loopN3Pre at hp
  delta loopBodyN3CallSkipJgt0PreV4NoX1
  simp only []
  xperm_hyp hp

/-- First n=3 call iteration from the callable-ready v4 loop source, preserving
    concrete `x1` and carrying the j=0 source atoms as a frame. -/
theorem divK_loop_n3_call_j1_from_source_exact_loopIterScratch_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hcarry2_nz : loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v4 base)
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
  have J1 := divK_loop_body_n3_call_j1_exact_loopIterScratch_v4_noNop sp base
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

end EvmAsm.Evm64
