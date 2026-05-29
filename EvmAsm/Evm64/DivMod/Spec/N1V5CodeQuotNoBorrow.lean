/-
  EvmAsm.Evm64.DivMod.Spec.N1V5CodeQuotNoBorrow

  Brick-6 enabler: the no-borrow condition for the div128 **code** quotient
  (`div128V5CodeQuot`, i.e. `div128V5SpecPost`'s `x11`), discharged from the
  divisor shape.

  The v5 n=1 loop-body skip composition (`divK_loop_body_n1_call_skip_*_v5`)
  composes the trial-call (whose post leaves the code quotient in `x11`) with the
  mulsub-correction-skip, which takes `hborrow : mulsubN4NoBorrow qHat …` with
  `qHat` = that code quotient.  This lemma supplies exactly that, by chaining the
  q-bridge `div128V5CodeQuot_eq_div128Quot_v5` (so the code quotient is the model
  `div128Quot_v5`) with the shape-derived no-borrow
  `mulsubN4NoBorrow_div128Quot_v5_of_norm_call` (#7242).  Bead
  `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5DigitBridge
import EvmAsm.Evm64.DivMod.Spec.N1V5NoBorrow

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The div128 code quotient equals the trial def `divKTrialCallV5QHat`
    (transitively, via the model `div128Quot_v5`). -/
theorem div128V5CodeQuot_eq_divKTrialCallV5QHat (uHi uLo vTop : Word) :
    div128V5CodeQuot uHi uLo vTop = divKTrialCallV5QHat uHi uLo vTop :=
  (div128V5CodeQuot_eq_div128Quot_v5 uHi uLo vTop).trans
    (divKTrialCallV5QHat_eq_div128Quot_v5 uHi uLo vTop).symm

/-- **No-borrow for the div128 code quotient, from shape.**  For a normalized
    one-limb divisor (`v0 ≥ 2^63`) in the call regime (`u1 < v0`), the code's
    single-limb mulsub with the code trial `div128V5CodeQuot u1 u0 v0` leaves no
    top borrow — the `hborrow` hypothesis the v5 n=1 loop-body skip consumes. -/
theorem mulsubN4NoBorrow_div128V5CodeQuot_of_norm_call
    (v0 u0 u1 uTop : Word)
    (hv0_norm : v0.toNat ≥ 2 ^ 63)
    (hcall : u1.toNat < v0.toNat) :
    mulsubN4NoBorrow (div128V5CodeQuot u1 u0 v0) v0 0 0 0 u0 u1 0 0 uTop := by
  rw [div128V5CodeQuot_eq_div128Quot_v5]
  exact mulsubN4NoBorrow_div128Quot_v5_of_norm_call v0 u0 u1 uTop hv0_norm hcall

end EvmAsm.Evm64
