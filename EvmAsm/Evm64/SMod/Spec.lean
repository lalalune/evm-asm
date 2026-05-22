/-
  EvmAsm.Evm64.SMod.Spec

  Top-level (semantic / stack-level) cpsTriple spec for `evm_smod`,
  bridging the limb-level composition to a single `evmWordIs` pre/post
  pair.

  GH #90 (beads slice evm-asm-kyp6). This file now exposes the first
  caller-facing stack assertion for the v4 SMOD path: the wrapper entry
  through the signed-operand normalization prefix and into the appended
  unsigned MOD callable. The final all-case `evm_smod_stack_spec_within`
  is composed in a later slice from the remaining MOD-call return bridge
  and semantic handler facts.
-/

import EvmAsm.Evm64.SMod.Compose.Base
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.SMod.Compose
open EvmAsm.Rv64.Tactics

/-- Stack-level SMOD v4 prefix bridge from the public two-word EVM stack
    assertion to the named unsigned-MOD dispatch-ready post.

    This is not the final all-case `evm_smod_stack_spec_within`: it covers
    the wrapper prefix through signed absolute-value normalization and the
    `JAL` into the appended `evm_mod_callable_v4` body. The callable body and
    return/result-sign-fix suffix stay as explicit follow-up obligations. -/
theorem evm_smod_prefix_mod_call_dispatch_ready_stack_spec_within
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld : Word)
    (dividend divisor : EvmWord)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) :
    EvmAsm.Rv64.cpsTripleWithin 49 base (base + wrapperEndOff)
      (smodCodeV4 base)
      (((((.x1 ↦ᵣ vRa) ** (.x18 ↦ᵣ vSavedOld)) **
        ((.x12 ↦ᵣ sp) ** (.x8 ↦ᵣ sDividendOld) ** (.x13 ↦ᵣ x13Old) **
          (.x9 ↦ᵣ sDivisorOld) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x10 ↦ᵣ dividendMaskOld) ** (.x7 ↦ᵣ dividendValueOld) **
          (.x11 ↦ᵣ dividendCarryOld))) **
        evmStackIs sp [dividend, divisor]) **
        ((.x2 ↦ᵣ v2) ** (.x5 ↦ᵣ v5) ** (.x6 ↦ᵣ v6) **
          EvmAsm.Evm64.divScratchValuesCallNoX1 sp
            q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
            shiftMem nMem jMem retMem dMem dloMem scratchUn0))
      (saveRaAbsThenModCallDispatchReadyPost vRa sp base
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0) := by
  exact EvmAsm.Rv64.cpsTripleWithin_weaken
    (fun _ hp => by
      simp only [evmStackIs_pair, evmWordIs,
        EvmAsm.Evm64.evm_smodDividendTopLimbOff,
        EvmAsm.Evm64.evm_smodDivisorTopLimbOff,
        EvmAsm.Rv64.signExtend12_0, EvmAsm.Rv64.signExtend12_8,
        EvmAsm.Rv64.signExtend12_16, EvmAsm.Rv64.signExtend12_24,
        EvmAsm.Rv64.signExtend12_32, EvmAsm.Rv64.signExtend12_40,
        EvmAsm.Rv64.signExtend12_48, EvmAsm.Rv64.signExtend12_56] at hp ⊢
      rw [show (sp + 0 : Word) = sp by bv_decide]
      rw [spAddr32_8, spAddr32_16, spAddr32_24] at hp
      xperm_hyp hp)
    (fun _ hp => hp)
    (saveRa_signs_abs_then_modCall_dispatchReady_spec_in_smodCodeV4
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld
      (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3)
      (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3)
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base)

-- Placeholder: final `evm_smod_stack_spec_within` lands after the remaining
-- callable-return and semantic-handler bridges are collapsed into one theorem.

end EvmAsm.Evm64
