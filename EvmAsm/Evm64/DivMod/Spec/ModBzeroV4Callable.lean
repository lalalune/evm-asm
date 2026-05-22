/-
  EvmAsm.Evm64.DivMod.Spec.ModBzeroV4Callable

  Branch-certificate-free v4 callable zero-divisor MOD wrappers.
-/

import EvmAsm.Evm64.DivMod.Spec.ModBzeroNoNop

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v4 zero-divisor branch of the no-NOP MOD dispatcher from the callable
    precondition shape, preserving exact caller-framed `x1`. -/
theorem evm_mod_stack_spec_bzero_noNop_v4_preCallable_callableExactX1Post
    (sp base : Word) (a b : EvmWord)
    (raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (hbz : b = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (sharedDivModCodeNoNop_v4 base)
      (divModStackDispatchPreCallable sp a b
        raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (modStackDispatchPostCallable sp a b ** (.x1 ↦ᵣ raVal)) := by
  exact evm_mod_bzero_stack_spec_within_dispatch_noNop_v4_callable_x1_uni
    sp base a b raVal v2 v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz

end EvmAsm.Evm64
