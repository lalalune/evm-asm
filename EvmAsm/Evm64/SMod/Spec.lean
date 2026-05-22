/-
  EvmAsm.Evm64.SMod.Spec

  Top-level (semantic / stack-level) cpsTriple spec for `evm_smod`,
  bridging the limb-level composition to a single `evmWordIs` pre/post
  pair.

  Public spec surface for the verified v4 tail of `evm_smod`.

  The full `evm_smod_stack_spec_within` theorem is still composed from the
  verified shared bridge with the boundary blocks in a later slice.
-/

import EvmAsm.Evm64.SMod.Compose.ModCallReturnNormalized
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.SMod.Compose

theorem evm_smod_v4_tail_return_stack_spec_within
    (vRa sp base : Word)
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (h_base : base &&& 1 = 0)
    (h_stack :
      cpsTripleWithin unifiedDivBound
        (base + wrapperEndOff) ((base + wrapperEndOff) + nopOff)
        (sharedDivModCodeNoNop_v4 (base + wrapperEndOff))
        (divModStackDispatchPreCallable sp
          (smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          ((base + modCallOff) + 4)
          v2 v5 v6
          (smodAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          (smodAbsMask divisorTop)
          (smodAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop)
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (modStackDispatchPostCallable sp
          (smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
          (smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
          (.x1 ↦ᵣ ((base + modCallOff) + 4)))) :
    cpsTripleWithin (((unifiedDivBound + 1) + 21) + 1)
      (base + wrapperEndOff) (vRa &&& ~~~(1 : Word)) (smodCodeV4 base)
      (saveRaAbsThenModCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0)
      (saveRaAbsThenModCallReturnPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) :=
  saveRaAbsThenModCall_then_return_named_post_normalized_from_noNop_spec_in_smodCodeV4
    vRa sp base
    dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
    divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
    v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 h_base h_stack

end EvmAsm.Evm64
