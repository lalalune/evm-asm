/-
  EvmAsm.Evm64.DivMod.Spec.ModBzeroV4ExactFrame

  Branch-certificate-free v4 exact-frame zero-divisor MOD wrappers.
-/

import EvmAsm.Evm64.DivMod.Spec.ModBzeroNoNop
import EvmAsm.Evm64.DivMod.Spec.CallablePost

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v4 zero-divisor branch of the no-NOP MOD dispatcher exposed through the
    named exact-frame callable postcondition. -/
theorem evm_mod_stack_spec_bzero_noNop_v4_preNoX1_callableExactFrame
    (sp base : Word) (a b : EvmWord)
    (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPostCallableExactFrame sp a b raVal x9Val) := by
  let frame : Assertion :=
    (.x9 ↦ᵣ x9Val) ** (.x1 ↦ᵣ raVal) ** (.x2 ↦ᵣ v2) **
    (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) **
    evmWordIs sp a **
    divScratchValuesCallNoX1 sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero := evm_mod_bzero_stack_spec_within_noNop_v4 sp base a b v5 v10 hbz
  have hFramed :
      cpsTripleWithin (8 + 5) base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
        (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) b) ** frame)
        ((((.x12 ↦ᵣ (sp + 32)) ** regOwn .x5 ** regOwn .x10 **
          (.x0 ↦ᵣ (0 : Word)) ** evmWordIs (sp + 32) (EvmWord.mod a b)) ** frame)) :=
    cpsTripleWithin_frameR frame (by
      dsimp [frame]
      rw [divScratchValuesCallNoX1_unfold]
      pcFree) hBzero
  rw [modStackDispatchPostCallableExactFrame_unfold]
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPreNoX1_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun h hq => by
        dsimp [frame] at hq
        rw [modStackDispatchPostCallable_unfold]
        simp only [sepConj_assoc', sepConj_comm', sepConj_left_comm'] at hq ⊢
        have hqOwn :
            (divScratchOwnCallNoX1 sp ** evmWordIs sp a ** (.x0 ↦ᵣ (0 : Word)) **
              (.x1 ↦ᵣ raVal) ** regOwn .x11 ** (.x12 ↦ᵣ (sp + 32)) **
              regOwn .x2 ** regOwn .x6 ** regOwn .x7 ** (.x9 ↦ᵣ x9Val) **
              regOwn .x10 ** regOwn .x5 ** evmWordIs (sp + 32) (EvmWord.mod a b)) h := by
          refine sepConj_mono ?_ ?_ h hq
          · intro hLeft hpLeft
            exact divScratchValuesCallNoX1_implies_divScratchOwnCallNoX1
              sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem
                retMem dMem dloMem scratch_un0 hLeft hpLeft
          · apply sepConj_mono_right
            apply sepConj_mono_right
            apply sepConj_mono_right
            apply sepConj_mono (regIs_implies_regOwn .x11 (v := v11))
            apply sepConj_mono_right
            apply sepConj_mono (regIs_implies_regOwn .x2 (v := v2))
            apply sepConj_mono (regIs_implies_regOwn .x6 (v := v6))
            apply sepConj_mono (regIs_implies_regOwn .x7 (v := v7))
            exact fun _ hp => hp
        exact by xperm_hyp hqOwn)
      hFramed

end EvmAsm.Evm64
