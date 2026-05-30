/-
  EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionAddbackV5NoNop

  v5 mulsub + correction-ADDBACK loop-body bricks over `sharedDivModCodeNoNop_v5`.

  The mulsub + addback instructions run AFTER the `div128` subroutine (the only
  block that differs between v4 and v5), so these are mechanical mirrors of the v4
  specs (`MulsubCorrectionAddback`), swapping the code surface
  `sharedDivModCodeNoNop_v4 → _v5` and the code-subsumption lemma
  `lb_sub_noNop_v4 → lb_sub_noNop_v5` (same pattern as `MulsubSkipV5`).

  Unlike the n=1 loop (single-limb divisor ⇒ exact floor ⇒ no borrow ⇒ skip
  path), the n=2/n=3/n=4 loops have a multi-limb divisor where the trial can
  overshoot and the addback FIRES — so these addback bricks are needed for the
  v5 n≥2 loop bodies.  First brick: the `BEQ` passthrough taken on the
  single-addback path (`carry ≠ 0`).  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.LoopBody.MulsubCorrectionAddback
import EvmAsm.Evm64.DivMod.Compose.V5Code

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 no-NOP variant of `divK_beq_passthrough_v4_spec_within_noNop`: on the
    single-addback path (`carry ≠ 0`) the addback `BEQ` is not taken, so control
    falls through to the store-loop.  Mechanical mirror of the v4 proof with the
    v5 code subsumption. -/
theorem divK_beq_passthrough_v5_spec_within_noNop {carry : Word} (base : Word) (hne : carry ≠ 0) :
    cpsTripleWithin 1 (base + addbackBeqOff) (base + storeLoopOff) (sharedDivModCodeNoNop_v5 base)
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word)))
      ((.x7 ↦ᵣ carry) ** (.x0 ↦ᵣ (0 : Word))) := by
  have hbeq := beq_spec_gen_within .x7 .x0 (8044 : BitVec 13) carry 0 (base + addbackBeqOff)
  rw [lb_beq_back_ntaken_local] at hbeq
  have hbeq_ext := cpsBranchWithin_extend_code (hmono :=
    lb_sub_noNop_v5 108 _ _ (by decide) (by bv_addr) (by decide)) hbeq
  have ntaken := cpsBranchWithin_ntakenPath hbeq_ext (fun hp hQt => by
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, ⟨_, hpure⟩⟩⟩ := hQt
    exact hne hpure)
  exact cpsTripleWithin_weaken
    (fun h hp => hp)
    (fun h hp => sepConj_mono_right
      (fun h' hp' => ((sepConj_pure_right h').1 hp').1) h hp)
    ntaken

/-- v5 full add-back correction over `sharedDivModCodeNoNop_v5` — instantiation of
    the generic `divK_addback_full_spec_within_of_sub` with the v5 code
    subsumption.  Mirror of `divK_addback_full_named_v4_spec_within_noNop`. -/
theorem divK_addback_full_named_v5_spec_within_noNop
    (sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4 : Word)
    (v7_init v5_init v2_init : Word) (base : Word) :
    cpsTripleWithin 37 (base + addbackInitOff) (base + addbackBeqOff) (sharedDivModCodeNoNop_v5 base)
      ((.x12 ↦ᵣ sp) ** (.x6 ↦ᵣ uBase) ** (.x7 ↦ᵣ v7_init) **
       (.x11 ↦ᵣ qHat) ** (.x5 ↦ᵣ v5_init) ** (.x2 ↦ᵣ v2_init) ** (.x0 ↦ᵣ (0 : Word)) **
       ((sp + signExtend12 32) ↦ₘ v0) ** ((uBase + signExtend12 0) ↦ₘ u0) **
       ((sp + signExtend12 40) ↦ₘ v1) ** ((uBase + signExtend12 4088) ↦ₘ u1) **
       ((sp + signExtend12 48) ↦ₘ v2) ** ((uBase + signExtend12 4080) ↦ₘ u2) **
       ((sp + signExtend12 56) ↦ₘ v3) ** ((uBase + signExtend12 4072) ↦ₘ u3) **
       ((uBase + signExtend12 4064) ↦ₘ u4))
      (addbackFullPost sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4) :=
  cpsTripleWithin_weaken
    (fun h hp => by unfold addbackFullPre; exact hp)
    (fun h hp => hp)
    (divK_addback_full_spec_within_of_sub sp uBase qHat v0 v1 v2 v3 u0 u1 u2 u3 u4
      v7_init v5_init v2_init base (sharedDivModCodeNoNop_v5 base) lb_sub_noNop_v5)

end EvmAsm.Evm64
