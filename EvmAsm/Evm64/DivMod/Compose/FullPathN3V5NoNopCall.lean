/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopCall

  v5/no-NOP norm-pre wrappers for the n=3 DIV call+skip loop bodies.  Mirror of
  the v4 n=3 call-skip norm wrappers (`FullPathN3V4NoNop`), lifting the raw v5
  call-skip bodies (over `sharedDivModCodeNoNop_v5`, carrying the v5 trial post
  `loopBodyN3CallSkip{J0,Jgt0}PostV5`) to `divCode_noNop_v5` via
  `sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5`, hiding the sp-relative
  addresses behind the (code-agnostic) NormPre defs reused from the v4 wrappers.
  Bead `evm-asm-wbc4i.9.3.3.2.1`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4NoNop
import EvmAsm.Evm64.DivMod.Compose.V5NoNop
import EvmAsm.Evm64.DivMod.LoopIterN3V5.CallSkipV5NoNop

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (se12_32 se12_40 se12_48 se12_56)

/-- Loop body n=3, call+skip, j=0 over `divCode_noNop_v5`, with sp-relative
    addresses hidden behind a named precondition. -/
theorem divK_loop_body_n3_call_skip_j0_norm_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + denormOff) (divCode_noNop_v5 base)
      (loopBodyN3CallSkipJ0NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallSkipJ0PostV5 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw :=
    cpsTripleWithin_extend_code
      (hmono := sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5)
      (divK_loop_body_n3_call_skip_j0_v5_spec_within_noNop
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

/-- Loop body n=3, call+skip, j=1 over `divCode_noNop_v5`, with the precondition
    hidden behind an irreducible definition. -/
theorem divK_loop_body_n3_call_skip_j1_norm_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : BitVec.ult u3 v2)
    (hborrow : mulsubN4NoBorrow (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 v3 u0 u1 u2 u3 uTop) :
    cpsTripleWithin 158 (base + loopBodyOff) (base + loopBodyOff) (divCode_noNop_v5 base)
      (loopBodyN3CallSkipJ1NormPreV4 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld retMem dMem dloMem scratchUn0 scratchMem)
      (loopBodyN3CallSkipJgt0PostV5 sp base (1 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem) := by
  have raw := divK_loop_body_n3_call_skip_j1_v5_spec_within_noNop
    sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
    v0 v1 v2 v3 u0 u1 u2 u3 uTop qOld
    retMem dMem dloMem scratchUn0 scratchMem base
    halign hbltu hborrow
  have raw' := cpsTripleWithin_extend_code
    (hmono := sharedDivModCodeNoNop_v5_sub_divCode_noNop_v5) raw
  exact cpsTripleWithin_weaken
    (fun h hp => by
      delta loopBodyN3CallSkipJ1NormPreV4 at hp
      xperm_hyp hp)
    (fun h hp => hp)
    raw'

end EvmAsm.Evm64
