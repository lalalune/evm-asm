/-
  EvmAsm.Evm64.DivMod.Spec.DispatcherPcFree

  PC-free helpers for callable-ready DIV/MOD dispatcher preconditions.
-/

import EvmAsm.Evm64.DivMod.Spec.Dispatcher

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem divModStackDispatchPreNoX1_pcFree
    (sp : Word) (a b : EvmWord)
    (x9Val x1Val v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    (divModStackDispatchPreNoX1 sp a b x9Val x1Val v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0).pcFree := by
  rw [divModStackDispatchPreNoX1_unfold, divScratchValuesCallNoX1_unfold,
    divScratchValues_unfold]
  pcFree

instance pcFreeInst_divModStackDispatchPreNoX1
    (sp : Word) (a b : EvmWord)
    (x9Val x1Val v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (divModStackDispatchPreNoX1 sp a b x9Val x1Val v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0) :=
  ⟨divModStackDispatchPreNoX1_pcFree sp a b x9Val x1Val v2 v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem
    dloMem scratch_un0⟩

theorem divModStackDispatchPreCallable_pcFree
    (sp : Word) (a b : EvmWord)
    (x1Val v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    (divModStackDispatchPreCallable sp a b x1Val v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      shiftMem nMem jMem retMem dMem dloMem scratch_un0).pcFree := by
  rw [divModStackDispatchPreCallable_unfold, divScratchValuesCallNoX1_unfold,
    divScratchValues_unfold]
  pcFree

instance pcFreeInst_divModStackDispatchPreCallable
    (sp : Word) (a b : EvmWord)
    (x1Val v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratch_un0 : Word) :
    Assertion.PCFree
      (divModStackDispatchPreCallable sp a b x1Val v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0) :=
  ⟨divModStackDispatchPreCallable_pcFree sp a b x1Val v2 v5 v6 v7 v10 v11
    q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7 shiftMem nMem jMem retMem dMem
    dloMem scratch_un0⟩

end EvmAsm.Evm64
