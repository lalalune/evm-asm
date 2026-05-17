/-
  EvmAsm.Evm64.DivMod.Spec.ModBzeroNoNop

  Dispatch-level zero-divisor MOD spec over `modCode_noNop`, mirroring
  the div-side `evm_div_bzero_stack_spec_within_dispatch_noNop_preserving_x1_uni`
  in `Spec/Unified.lean`. Placed in a separate file because `Spec/Unified.lean`
  is at the file-size cap.
-/

import EvmAsm.Evm64.DivMod.Spec.Base
import EvmAsm.Evm64.DivMod.Spec.Dispatcher
import EvmAsm.Evm64.DivMod.Spec.Unified

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Zero-divisor MOD dispatcher over `modCode_noNop`, preserving the exact
    incoming `x1` value. Mirror of
    `evm_div_bzero_stack_spec_within_dispatch_noNop_preserving_x1_uni`
    for the MOD callable. -/
theorem evm_mod_bzero_stack_spec_within_dispatch_noNop_preserving_x1_uni
    (sp base : Word)
    (a b : EvmWord) (v1 v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (modCode_noNop base)
      (divModStackDispatchPre sp a b
        v1 v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPostNoX1 sp a b ** (.x1 ↦ᵣ v1)) := by
  let frame : Assertion :=
    (.x1 ↦ᵣ v1) ** (.x2 ↦ᵣ v2) ** (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
    (.x11 ↦ᵣ v11) ** evmWordIs sp a **
    divScratchValuesCall sp q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0
  have hBzero := evm_mod_bzero_stack_spec_within_noNop sp base a b v5 v10 hbz
  have hFramed :=
    cpsTripleWithin_frameR frame (by dsimp [frame]; rw [divScratchValuesCall_unfold]; pcFree) hBzero
  exact cpsTripleWithin_mono_nSteps (by decide) <|
    cpsTripleWithin_weaken
      (fun _ hp => by
        rw [divModStackDispatchPre_unfold] at hp
        dsimp [frame]
        simp only [sepConj_comm', sepConj_left_comm'] at hp ⊢
        exact hp)
      (fun h hq => by
        -- Use the modBzeroDispatchPostPreservingX1Frame bundle approach:
        -- The POST is exactly the framed form, so weaken is trivial.
        exact modBzeroDispatchPostPreservingX1Frame_weaken_noX1 sp a b h
          (by rw [modBzeroDispatchPostPreservingX1Frame_unfold]; xperm_hyp hq))
      hFramed

end EvmAsm.Evm64
