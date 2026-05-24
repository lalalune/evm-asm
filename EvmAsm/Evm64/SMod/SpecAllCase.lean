/-
  EvmAsm.Evm64.SMod.SpecAllCase

  All-case SMOD v4 stack spec: case-splits on whether the absolute divisor is
  zero and dispatches to the bzero or nonzero wrapper as appropriate.

  GH #90 (bead evm-asm-9iqmw.9.2).
-/

import EvmAsm.Evm64.SMod.Spec
import EvmAsm.Evm64.SMod.SpecBzero

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.SMod.Compose

/-- All-case SMOD v4 canonical stack spec.  The unsigned-MOD callable proof for
    the nonzero divisor path remains an explicit parameter; the zero-divisor
    path is discharged internally via the v4 bzero theorem.

    Case split: if `divisor = 0` use the bzero wrapper;
                otherwise use the nonzero wrapper with the supplied `h_stack`. -/
theorem evm_smod_canonical_all_case_mod_call_return_stack_spec_within
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld : Word)
    (dividend divisor : EvmWord)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (h_base : base &&& 1 = 0)
    (h_stack :
      EvmAsm.Rv64.cpsTripleWithin EvmAsm.Evm64.unifiedDivBound
        (base + wrapperEndOff) ((base + wrapperEndOff) + EvmAsm.Evm64.nopOff)
        (EvmAsm.Evm64.modCode_noNop_v4 (base + wrapperEndOff))
        (EvmAsm.Evm64.divModStackDispatchPreNoX1 sp
          (smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (smodAbsSign (divisor.getLimbN 3))
          ((base + modCallOff) + 4)
          v2 v5 v6
          (smodAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          (smodAbsMask (divisor.getLimbN 3))
          (smodAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3))
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0)
        (EvmAsm.Evm64.modStackDispatchPostCallable sp
          (smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
            (dividend.getLimbN 2) (dividend.getLimbN 3))
          (smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
            (divisor.getLimbN 2) (divisor.getLimbN 3)) **
          (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
          EvmAsm.Rv64.regOwn .x9)) :
    EvmAsm.Rv64.cpsTripleWithin
      (49 + (((EvmAsm.Evm64.unifiedDivBound + 1) + 21) + 1))
      base (vRa &&& ~~~(1 : Word)) (smodCodeCanonical base)
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
      (saveRaAbsThenModCallReturnPost vRa sp base
        (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
        (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)) := by
  rcases Classical.em (divisor = 0) with h_zero | h_nz
  · -- Zero divisor: use bzero spec
    exact evm_smod_canonical_bzero_mod_call_return_stack_spec_within
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld dividend divisor
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base h_base h_zero
  · -- Nonzero divisor: use canonical spec with h_stack
    exact evm_smod_canonical_mod_call_return_stack_spec_within
      vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld dividend divisor
      v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 base h_base h_stack

end EvmAsm.Evm64
