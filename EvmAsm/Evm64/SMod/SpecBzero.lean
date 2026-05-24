/-
  EvmAsm.Evm64.SMod.SpecBzero

  Zero-divisor SMOD wrapper surfaces that discharge the appended unsigned MOD
  callable with the v4 bzero proof.
-/

import EvmAsm.Evm64.SMod.Spec
import EvmAsm.Evm64.DivMod.Spec.ModBzeroNoNop

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Evm64.SMod.Compose

/-- Canonical SMOD v4 bridge for the zero-divisor path, with the appended
    unsigned-MOD callable proof supplied by the v4 MOD bzero theorem. -/
theorem evm_smod_canonical_bzero_mod_call_return_stack_spec_within
    (vRa vSavedOld sp sDividendOld x13Old sDivisorOld
      dividendMaskOld dividendValueOld dividendCarryOld : Word)
    (dividend divisor : EvmWord)
    (v2 v5 v6 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word)
    (base : Word) (h_base : base &&& 1 = 0)
    (h_divisor_zero : divisor = 0) :
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
  let divisorSign := smodAbsSign (divisor.getLimbN 3)
  let a : EvmWord :=
    smodAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
      (dividend.getLimbN 2) (dividend.getLimbN 3)
  let b : EvmWord :=
    smodAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
      (divisor.getLimbN 2) (divisor.getLimbN 3)
  let v7 := smodAbsSum3 (divisor.getLimbN 0) (divisor.getLimbN 1)
    (divisor.getLimbN 2) (divisor.getLimbN 3)
  let v10 := smodAbsMask (divisor.getLimbN 3)
  let v11 := smodAbsCarry3 (divisor.getLimbN 0) (divisor.getLimbN 1)
    (divisor.getLimbN 2) (divisor.getLimbN 3)
  let retAddr := (base + modCallOff) + 4
  refine evm_smod_canonical_mod_call_return_stack_spec_within
    vRa vSavedOld sp sDividendOld x13Old sDivisorOld
    dividendMaskOld dividendValueOld dividendCarryOld dividend divisor
    v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    shiftMem nMem jMem retMem dMem dloMem scratchUn0 base h_base ?_
  -- Adapt bzero spec to new h_stack type (PreNoX1 → PostCallable ** .x1 ** regOwn .x9)
  have h_bzero_raw :=
    cpsTripleWithin_extend_code
      (hmono := EvmAsm.Evm64.sharedDivModCodeNoNop_v4_sub_modCode_noNop_v4)
      (evm_mod_bzero_stack_spec_within_dispatch_noNop_v4_callable_x1_uni
        sp (base + wrapperEndOff) a b retAddr v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        nMem shiftMem jMem retMem dMem dloMem scratchUn0
        (by simpa [b] using (smodAbsDivisorWord_eq_zero_iff divisor).mpr h_divisor_zero))
  -- Frame .x9 ↦ divisorSign around bzero (bzero doesn't touch x9)
  have h_bzero_framed := cpsTripleWithin_frameR (.x9 ↦ᵣ divisorSign) (by pcFree) h_bzero_raw
  -- Weaken to new h_stack type
  exact cpsTripleWithin_weaken
    (fun h hp => by
      -- PreNoX1 → (PreCallable ** (.x9 ↦ divisorSign)): same atoms, just AC
      rw [EvmAsm.Evm64.divModStackDispatchPreNoX1_unfold] at hp
      rw [EvmAsm.Evm64.divModStackDispatchPreCallable_unfold]
      xperm_hyp hp)
    (fun h hp => by
      -- (PostCallable ** .x1 ** .x9) → (PostCallable ** .x1 ** regOwn .x9)
      -- HP: ((PostCallable ** .x1) ** (.x9 ↦ divisorSign)) h
      obtain ⟨hAB, hX9, hd1, hu1, hAB_h, hX9_h⟩ := hp
      have hregown := regIs_implies_regOwn .x9 hX9 hX9_h
      have hp' : ((EvmAsm.Evm64.modStackDispatchPostCallable sp a b **
                   (.x1 ↦ᵣ retAddr)) **
                  EvmAsm.Rv64.regOwn .x9) h :=
        ⟨hAB, hX9, hd1, hu1, hAB_h, hregown⟩
      rw [sepConj_assoc] at hp'
      exact hp')
    h_bzero_framed

end EvmAsm.Evm64
