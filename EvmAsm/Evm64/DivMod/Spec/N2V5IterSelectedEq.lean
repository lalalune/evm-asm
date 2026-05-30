/-
  EvmAsm.Evm64.DivMod.Spec.N2V5IterSelectedEq

  `loopN2IterSelectedV5 = iterN2V5`: the branch-selected loop iteration
  (FullPathN2V5NoNopLoopDefs) and the families iteration (FullPathN2V5Families)
  share the same definition body, so they are equal.  This bridge lets the
  per-digit remainder-collapse / step / validity lemmas (stated for `iterN2V5` in
  N2V5RemainderLt) apply to the `loopN2IterSelectedV5` intermediates that appear
  in `loopN2SelectedBorrowCarryV5` — needed to assemble
  `loopN2SelectedBorrowCarryV5_of_shape`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopDefs
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5Families

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The unified loop iteration equals the families iteration. -/
theorem loopN2IterSelectedV5_eq_iterN2V5 (bltu : Bool)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    loopN2IterSelectedV5 bltu v0 v1 v2 v3 u0 u1 u2 u3 uTop =
      iterN2V5 bltu v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  simp only [loopN2IterSelectedV5, iterN2V5]

end EvmAsm.Evm64
