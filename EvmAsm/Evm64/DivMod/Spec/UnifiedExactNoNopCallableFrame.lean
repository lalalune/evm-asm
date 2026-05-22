/-
  EvmAsm.Evm64.DivMod.Spec.UnifiedExactNoNopCallableFrame

  Named exact-frame callable wrappers for no-NOP DIV dispatcher facts.
-/

import EvmAsm.Evm64.DivMod.Spec.UnifiedExactNoNop

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Zero-divisor branch of the no-NOP DIV dispatcher exposed through the
    named exact-frame callable postcondition. -/
theorem evm_div_stack_spec_bzero_noNop_preNoX1_callableExactFrame
    (sp base : Word) (a b : EvmWord)
    (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPostCallableExactFrame sp a b raVal x9Val) := by
  simpa [divStackDispatchPostCallableExactFrame_unfold] using
    evm_div_stack_spec_bzero_noNop_preNoX1_callableExactPost
      sp base a b x9Val raVal v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz

end EvmAsm.Evm64
