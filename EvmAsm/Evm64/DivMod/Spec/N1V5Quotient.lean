/-
  EvmAsm.Evm64.DivMod.Spec.N1V5Quotient

  v5 n=1 quotient word and the carry-zero 4-digit accumulation, en route to
  `fullDivN1QuotientWordV5 = EvmWord.div a b`.

  The per-digit toolkit (`N1V5DigitSteps.lean`) provides, from shape and with NO
  `Carry2NzAll`:
  - the 4 conservations `fullDivN1R{3,2,1,0}V5_conservation_of_shape`
    (`val256(window) = q_k·v0 + val256(remainder)`), and
  - the 4 remainder-lts `fullDivN1R{3,2,1,0}V5_remainder_lt_of_shape`.

  `fullDivN1V5_four_step_nat` below accumulates the four conservation equations
  into `val256(a)·2^s = quotient·(val256(b)·2^s) + r0` (the carries are already
  zero in the v5 per-step conservations, unlike v4's raw form). With the final
  remainder-lt + the scaled-divisor identity `normV.1 = val256(b)·2^s`, this
  feeds `EvmWord.div_correct_normalized` to give
  `fullDivN1QuotientWordV5 = EvmWord.div a b` (next step).

  Bead evm-asm-wbc4i.9.1.
-/

import EvmAsm.Evm64.DivMod.Spec.N1V5DigitSteps

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The carry-zero 4-digit accumulation — public re-proof of the private
    `fullDivN1_four_step_conservation_nat`, specialized to all carries zero
    (which is exactly what the v5 per-step conservations directly provide). -/
theorem fullDivN1V5_four_step_nat
    {a b q3 q2 q1 q0 u0 u1 u2 u3 u4 r3 r2 r1 r0 : Nat}
    (hfirst : a = u0 + 2 ^ 64 * (u1 + 2 ^ 64 * (u2 + 2 ^ 64 * (u3 + 2 ^ 64 * u4))))
    (hiter3 : u3 + 2 ^ 64 * u4 = q3 * b + r3)
    (hiter2 : u2 + 2 ^ 64 * r3 = q2 * b + r2)
    (hiter1 : u1 + 2 ^ 64 * r2 = q1 * b + r1)
    (hiter0 : u0 + 2 ^ 64 * r1 = q0 * b + r0) :
    a = (q3 * 2 ^ 192 + q2 * 2 ^ 128 + q1 * 2 ^ 64 + q0) * b + r0 := by
  nlinarith

/-- v5 n=1 quotient word: the four digit quotients `fullDivN1R{0,1,2,3}V5.1`
    assembled into a 256-bit word (mirror of `fullDivN1QuotientWord`). -/
def fullDivN1QuotientWordV5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 => (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1
    | 1 => (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1
    | 2 => (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1
    | 3 => (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1)

end EvmAsm.Evm64
