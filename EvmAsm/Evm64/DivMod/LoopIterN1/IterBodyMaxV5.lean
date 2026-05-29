/-
  EvmAsm.Evm64.DivMod.LoopIterN1.IterBodyMaxV5

  v5 n=1 max-path per-digit *iteration-ready* loop bodies: the max+skip loop
  bodies (#7268) with their post weakened to `loopIterPostN1Max` via the
  version-agnostic `loopIterPostN1Max_skip` bridge.  Max-path analogue of
  `IterBodyV5` (call path).  Together they give all four iteration-ready per-digit
  bodies for the v5 n=1 loop composition.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.MaxSkipV5
import EvmAsm.Evm64.DivMod.LoopIterN1.IterPostV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 n=1 max-path iteration-ready loop body, j>0 (loops back to loopBody). -/
theorem divK_loop_body_n1_max_iter_jgt0_v5_spec_within_noNop (j : Word)
    (hpos : BitVec.slt (j + signExtend12 4095) 0 = false)
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)) :
    let uBase := sp + signExtend12 4056 - j <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - j <<< (3 : BitVec 6).toNat
    cpsTripleWithin 76 (base + loopBodyOff) (base + loopBodyOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ j) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  have hb : ¬BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) := by
    intro hult; rw [if_pos hult] at hborrow; exact absurd hborrow (by decide)
  have J := divK_loop_body_n1_max_skip_jgt0_v5_spec_within_noNop j hpos
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu hborrow
  intro_lets at J
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by rw [← loopIterPostN1Max_skip hb]; exact hp)
    J

/-- v5 n=1 max-path iteration-ready loop body, j=0 (exits to denorm). -/
theorem divK_loop_body_n1_max_iter_j0_v5_spec_within_noNop
    (sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
     v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (base : Word)
    (hbltu : ¬BitVec.ult u1 v0)
    (hborrow : (if BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) then (1 : Word) else 0) = (0 : Word)) :
    let uBase := sp + signExtend12 4056 - (0 : Word) <<< (3 : BitVec 6).toNat
    let qAddr := sp + signExtend12 4088 - (0 : Word) <<< (3 : BitVec 6).toNat
    cpsTripleWithin 76 (base + loopBodyOff) (base + denormOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x9 ↦ᵣ (0 : Word)) **
       (.x5 ↦ᵣ v5Old) ** (.x6 ↦ᵣ v6Old) **
       (.x7 ↦ᵣ v7Old) ** (.x10 ↦ᵣ v10Old) ** (.x11 ↦ᵣ v11Old) **
       (.x2 ↦ᵣ v2Old) ** (.x0 ↦ᵣ (0 : Word)) **
       (sp + signExtend12 3976 ↦ₘ jOld) ** (sp + signExtend12 3984 ↦ₘ (1 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ uTop) **
       (qAddr ↦ₘ qOld))
      (loopIterPostN1Max sp (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop) := by
  intro uBase qAddr
  have hb : ¬BitVec.ult uTop (mulsubN4_c3 (signExtend12 4095 : Word) v0 v1 v2 v3 u0 u1 u2 u3) := by
    intro hult; rw [if_pos hult] at hborrow; exact absurd hborrow (by decide)
  have J := divK_loop_body_n1_max_skip_j0_v5_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld base hbltu hborrow
  intro_lets at J
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by rw [← loopIterPostN1Max_skip hb]; exact hp)
    J

end EvmAsm.Evm64
