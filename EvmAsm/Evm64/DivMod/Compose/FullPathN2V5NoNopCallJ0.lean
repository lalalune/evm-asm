/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopCallJ0

  v5/no-NOP norm-pre wrappers for the n=2 DIV call-path j=0 loop bodies (the
  loop EXIT to denorm).  Mirror of `divK_loop_body_n2_call_skip_j0_norm_v4_noNop`
  and `divK_loop_body_n2_call_addback_j0_beq_norm_v4_noNop` (FullPathN2V4NoNop),
  lifting the raw v5 j=0 call bodies (over `sharedDivModCodeNoNop_v5`) to
  `divCode_noNop_v5` and hiding the sp-relative addresses behind the
  (code-agnostic) NormPre def `loopBodyN2CallSkipJ0NormPreV4` reused from the v4
  wrappers.  Takes the v5 borrow / carry2 hypotheses directly (the v4 wrapper
  predicates are v4-trial-specific and not reused).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4NoNop
import EvmAsm.Evm64.DivMod.Compose.V5NoNop
import EvmAsm.Evm64.DivMod.LoopIterN2V5.CallSkipV5NoNop
import EvmAsm.Evm64.DivMod.LoopIterN2V5.CallAddbackV5NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Loop body n=2, call+skip, j=0 over `divCode_noNop_v5` (loop exit), with
    sp-relative addresses hidden behind a named precondition. -/
theorem divK_loop_body_n2_call_skip_j0_norm_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
      (loopBodyN2CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallSkipJ0PostV5 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5)
      (divK_loop_body_n2_call_skip_j0_v5_spec_within_noNop
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow)
  rw [loopBodyN2CallSkipJ0PreV4_unfold] at raw
  rw [loopBodyN2CallSkipJ0Pre_unfold] at raw
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJ0NormPreV4 loopBodyN2MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

/-- Loop body n=2, call+addback (BEQ double-addback), j=0 over `divCode_noNop_v5`
    (loop exit), with sp-relative addresses hidden behind a named precondition. -/
theorem divK_loop_body_n2_call_addback_j0_beq_norm_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u2 v1)
    (hborrow : (if BitVec.ult uTop
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
      then (1 : Word) else 0) ≠ (0 : Word))
    (hcarry2_nz :
      let qHat := divKTrialCallV5QHat u2 u1 v1
      let ms := mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3
      let c3 := ms.2.2.2.2
      let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 v0 v1 v2 v3
      let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (uTop - c3) v0 v1 v2 v3
      carry = 0 → addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 v0 v1 v2 v3 ≠ 0) :
    cpsTripleWithin 234 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
      (loopBodyN2CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN2CallAddbackBeqJ0PostV5 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5)
      (divK_loop_body_n2_call_addback_j0_beq_v5_spec_within_noNop
        sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
        retMem dMem dloMem scratchUn0 scratchMem base
        halign hbltu hborrow hcarry2_nz)
  simp only [se12_32, se12_40, se12_48, se12_56,
             u_base_off0_j0, u_base_off4088_j0, u_base_off4080_j0,
             u_base_off4072_j0, u_base_off4064_j0, q_addr_j0] at raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN2CallSkipJ0NormPreV4 loopBodyN2MaxSkipJ0NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw

end EvmAsm.Evm64
