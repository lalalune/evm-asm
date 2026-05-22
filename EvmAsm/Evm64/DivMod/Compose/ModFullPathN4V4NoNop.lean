/-
  EvmAsm.Evm64.DivMod.Compose.ModFullPathN4V4NoNop

  v4/no-NOP wrappers for the n=4 MOD loop-body surfaces.
-/

import EvmAsm.Evm64.DivMod.Compose.V4Code
import EvmAsm.Evm64.DivMod.Compose.FullPathN4Loop
import EvmAsm.Evm64.DivMod.LoopIterN4MaxV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN4CallV4NoNop
import EvmAsm.Evm64.DivMod.LoopIterN4AddbackV4NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- MOD epilogue over the no-NOP v4 MOD code bundle. -/
theorem divK_mod_epilogue_spec_within_noNop_v4 (sp : Word) (base : Word)
    (u0 u1 u2 u3 v5 v6 v7 v10 m0 m8 m16 m24 : Word) :
    cpsTripleWithin 10 (base + epilogueOff) (base + nopOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ u0) ** (.x6 ↦ᵣ u1) ** (.x7 ↦ᵣ u2) ** (.x10 ↦ᵣ u3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ u0) ** ((sp + 40) ↦ₘ u1) **
       ((sp + 48) ↦ₘ u2) ** ((sp + 56) ↦ₘ u3)) := by
  have hload := divK_epilogue_load_spec_within 4056 4048 4040 4032 sp u0 u1 u2 u3 v5 v6 v7 v10
    (base + epilogueOff)
  have hloade := cpsTripleWithin_extend_code (hmono := fun a i h =>
    modNoNop_v4_b10_modEpilogue a i
      (CodeReq.ofProg_mono_sub (base + epilogueOff) (base + epilogueOff) (divK_mod_epilogue 24)
        (divK_epilogue_load_prog 4056 4048 4040 4032) 0
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hload
  have hstore := divK_epilogue_store_spec_within sp (base + epilogueOff + 16) u0 u1 u2 u3 m0 m8 m16 m24 24
  rw [show (base + epilogueOff + 16 : Word) + 20 + signExtend21 24 = base + nopOff from by rv64_addr]
    at hstore
  have hstoree := cpsTripleWithin_extend_code (hmono := fun a i h =>
    modNoNop_v4_b10_modEpilogue a i
      (CodeReq.ofProg_mono_sub (base + epilogueOff) (base + epilogueOff + 16) (divK_mod_epilogue 24)
        (divK_epilogue_store_prog 24) 4
        (by bv_addr) (by decide) (by decide) (by decide) a i h)) hstore
  have hloadef := cpsTripleWithin_frameR
    (((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) ** ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
    (by pcFree) hloade
  have hstoref := cpsTripleWithin_frameR
    (((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
     ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3))
    (by pcFree) hstoree
  have h12 := cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by xperm_hyp hp) hloadef hstoref
  exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
    (fun h hp => by xperm_hyp hp)
    (fun h hq => by xperm_hyp hq)
    h12

/-- MOD epilogue over the full v4 MOD code bundle. -/
theorem divK_mod_epilogue_spec_within_v4 (sp : Word) (base : Word)
    (u0 u1 u2 u3 v5 v6 v7 v10 m0 m8 m16 m24 : Word) :
    cpsTripleWithin 10 (base + epilogueOff) (base + nopOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ m0) ** ((sp + 40) ↦ₘ m8) **
       ((sp + 48) ↦ₘ m16) ** ((sp + 56) ↦ₘ m24))
      ((.x12 ↦ᵣ (sp + 32)) ** (.x5 ↦ᵣ u0) ** (.x6 ↦ᵣ u1) ** (.x7 ↦ᵣ u2) ** (.x10 ↦ᵣ u3) **
       ((sp + signExtend12 4056) ↦ₘ u0) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + signExtend12 4040) ↦ₘ u2) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + 32) ↦ₘ u0) ** ((sp + 40) ↦ₘ u1) **
       ((sp + 48) ↦ₘ u2) ** ((sp + 56) ↦ₘ u3)) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_mod_epilogue_spec_within_noNop_v4 sp base
      u0 u1 u2 u3 v5 v6 v7 v10 m0 m8 m16 m24)

/-- Loop body n=4, max+skip, j=0 over `modCode_noNop_v4`, with
    sp-relative addresses in the precondition. -/
theorem divK_loop_body_n4_max_skip_j0_norm_mod_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult uTop v3) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld))
      (loopBodyN4SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n4_max_skip_j0_v4_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4) raw
  rw [loopBodyN4MaxSkipJ0Pre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  rw [loopBodyN4MaxSkipJ0Post_unfold] at raw'
  exact raw'

/-- Loop body n=4, max+skip, j=0 over the full `modCode_v4` bundle. -/
theorem divK_loop_body_n4_max_skip_j0_norm_mod_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult uTop v3) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) = (0 : Word) →
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (modCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld))
      (loopBodyN4SkipPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_loop_body_n4_max_skip_j0_norm_mod_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld hbltu hborrow)

/-- Loop body n=4, call+skip, j=0 over `modCode_noNop_v4`, with
    sp-relative addresses in the precondition. -/
theorem divK_loop_body_n4_call_skip_j0_norm_mod_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : loopBodyN4CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       regOwn .x1) ** (sp + signExtend12 3936 ↦ₘ scratchMem))
      (loopBodyN4CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
      (divK_loop_body_n4_call_skip_j0_v4_spec_within_noNop
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow)
  rw [loopBodyN4CallSkipJ0PreV4_unfold] at raw
  rw [loopBodyN4CallSkipJ0Pre_unfold] at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact raw

/-- Loop body n=4, call+skip, j=0 over the full `modCode_v4` bundle. -/
theorem divK_loop_body_n4_call_skip_j0_norm_mod_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : loopBodyN4CallSkipJ0BorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 148 (base + loopBodyOff) (base + denormOff) (modCode_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       regOwn .x1) ** (sp + signExtend12 3936 ↦ₘ scratchMem))
      (loopBodyN4CallSkipJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_loop_body_n4_call_skip_j0_norm_mod_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu hborrow)

/-- Loop body n=4, call+addback (BEQ double-addback), j=0 over
    `modCode_noNop_v4`, with sp-relative addresses in the precondition. -/
theorem divK_loop_body_n4_call_addback_j0_beq_norm_mod_v4_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : loopBodyN4CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN4CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (modCode_noNop_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       regOwn .x1) **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (loopBodyN4CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
      (divK_loop_body_n4_call_addback_j0_beq_v4_spec_within_noNop
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow hcarry2_nz)
  rw [loopBodyN4CallSkipJ0PreV4_unfold] at raw
  rw [loopBodyN4CallSkipJ0Pre_unfold] at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact raw

/-- Loop body n=4, call+addback (BEQ double-addback), j=0 over the full
    `modCode_v4` bundle. -/
theorem divK_loop_body_n4_call_addback_j0_beq_norm_mod_v4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult uTop v3)
    (hborrow : loopBodyN4CallAddbackBorrowV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop)
    (hcarry2_nz : loopBodyN4CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 224 (base + loopBodyOff) (base + denormOff) (modCode_v4 base)
      (((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (4 : Word)) **
       ((sp + 32) ↦ₘ v0) ** ((sp + signExtend12 4056) ↦ₘ u0) **
       ((sp + 40) ↦ₘ v1) ** ((sp + signExtend12 4048) ↦ₘ u1) **
       ((sp + 48) ↦ₘ v2) ** ((sp + signExtend12 4040) ↦ₘ u2) **
       ((sp + 56) ↦ₘ v3) ** ((sp + signExtend12 4032) ↦ₘ u3) **
       ((sp + signExtend12 4024) ↦ₘ uTop) **
       ((sp + signExtend12 4088) ↦ₘ qOld) **
       (sp + signExtend12 3968 ↦ₘ retMem) **
       (sp + signExtend12 3960 ↦ₘ dMem) **
       (sp + signExtend12 3952 ↦ₘ dloMem) **
       (sp + signExtend12 3944 ↦ₘ scratchUn0) **
       regOwn .x1) **
       (sp + signExtend12 3936 ↦ₘ scratchMem))
      (loopBodyN4CallAddbackJ0PostV4 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  exact cpsTripleWithin_modCode_noNop_v4_to_modCode_v4
    (divK_loop_body_n4_call_addback_j0_beq_norm_mod_v4_noNop sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
      retMem dMem dloMem scratchUn0 scratchMem
      halign hbltu hborrow hcarry2_nz)

end EvmAsm.Evm64
