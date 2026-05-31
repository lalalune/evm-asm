/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopMaxAddback

  v5/no-NOP norm-pre wrapper for the n=4 DIV max+addback-beq loop body (j=0).
  Mirror of the v5 n=4 max-skip norm wrapper (FullPathN4V5NoNopMax) with the raw
  max+addback-beq body (#7586) swapped in: same explicit-concrete max precondition
  (`loopBodyN4MaxSkipJ0Pre` form, no div128 scratch cells), the BEQ-nonzero
  `hborrow` + `isAddbackCarry2NzN4Max` hypotheses, and the post
  `loopBodyN4AddbackBeqPost` (identity post map).  Lifts from
  `sharedDivModCodeNoNop_v5` to `divCode_noNop_v5`.  Completes the four n=4 v5
  loop-body norm wrappers.  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V4NoNop
import EvmAsm.Evm64.DivMod.Compose.V5NoNop
import EvmAsm.Evm64.DivMod.LoopIterN4V5.MaxAddbackBeqV5NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Loop body n=4, max+addback-beq, j=0 over `divCode_noNop_v5`, with sp-relative
    addresses in the precondition (same form the preloop composition consumes). -/
theorem divK_loop_body_n4_max_addback_j0_beq_norm_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (hbltu : ¬BitVec.ult uTop v3)
    (hcarry2_nz : isAddbackCarry2NzN4Max v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3)
     then (1 : Word) else 0) ≠ (0 : Word) →
    cpsTripleWithin 152 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
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
      (loopBodyN4AddbackBeqPost sp (0 : Word) (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro hborrow
  have raw := divK_loop_body_n4_max_addback_j0_beq_v5_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base
    hbltu hcarry2_nz hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5) raw
  rw [loopBodyN4MaxSkipJ0Pre_unfold] at raw'
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw'
  exact raw'

end EvmAsm.Evm64
