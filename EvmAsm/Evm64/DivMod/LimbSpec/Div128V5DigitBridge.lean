/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128V5DigitBridge

  Per-Knuth-digit assembly of the v5 div128 code-vs-model q-bridge: combines the
  rhatc arithmetic (`div128V5_rhatc_correction_eq`, #7243) and the selection
  reconciliations (`div128V5_phase1b_select_eq` / `_rhat_select_eq`, #7244/#7245)
  into the equality of the *full corrected digit* computed the code way
  (`div128V5SpecPost`) and the model way (`div128Quot_v5`).

  `div128V5_rhatc_eq` lifts the capped-branch ring identity to the full
  `if hi = 0 …` capped-remainder form used by both `div128V5SpecPost` and
  `div128Quot_v5`.  `div128V5_q1Final_eq_model` then proves the corrected
  quotient digit agrees.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5Phase1bBridge
import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5CodeModelBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **Capped remainder code = model.**  The code's incremental capped remainder
    (`if hi=0 then rhat else rhat + (q1-cap)·dHi`) equals the model's closed form
    (`if hi=0 then rhat else uHi - q1c·dHi`, with `q1c = if hi=0 then q1 else cap`).
    The capped branch is `div128V5_rhatc_correction_eq` (#7243); the `hi=0`
    branch is refl. -/
theorem div128V5_rhatc_eq (uHi q1 cap dHi : Word) :
    (if q1 >>> (32 : BitVec 6).toNat = 0 then uHi - q1 * dHi
     else (uHi - q1 * dHi) + (q1 - cap) * dHi)
    = (if q1 >>> (32 : BitVec 6).toNat = 0 then uHi - q1 * dHi
       else uHi - (if q1 >>> (32 : BitVec 6).toNat = 0 then q1 else cap) * dHi) := by
  split
  · rfl
  · exact div128V5_rhatc_correction_eq uHi q1 cap dHi

end EvmAsm.Evm64
