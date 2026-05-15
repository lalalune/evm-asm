/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFullLoop

  Full-loop code-bundle helpers for the corrected MSB-first saved-bit EXP
  layout.  Sibling modules cover the prefix, squaring, and branch handoff;
  conditional-multiply call-block helpers live in SavedBitCondMulCall.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFullLoopBranch

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem expSavedBitBitTestNextPc (base : Word) :
    ((base + 28 : Word) + 12) = base + 40 := by
  bv_omega

theorem expSavedBitSaveNextPc (base : Word) :
    ((base + 40 : Word) + 4) = base + 44 := by
  bv_omega

theorem expSavedBitCondMulBeqNextPc (base : Word) :
    ((base + 148 : Word) + 4) = base + 152 := by
  bv_omega

theorem expSavedBitLoopBackNextPc (base : Word) :
    ((base + 256 : Word) + 8) = base + 264 := by
  bv_omega

end EvmAsm.Evm64.Exp.Compose
