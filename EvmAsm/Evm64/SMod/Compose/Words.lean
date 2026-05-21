/-
  EvmAsm.Evm64.SMod.Compose.Words

  Pure word-level helpers for SMOD composition files.
-/

import EvmAsm.Evm64.SDiv.Compose.Words

namespace EvmAsm.Evm64.SMod.Compose

/-- Absolute-value word produced by the SMOD dividend sign/absolute-value
    prefix. The computation matches SDIV; SMOD differs only in the final result
    sign, which follows the dividend sign. -/
def smodAbsDividendWord
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop : Word) : EvmWord :=
  EvmAsm.Evm64.SDiv.Compose.sdivAbsDividendWord
    dividendLimb0 dividendLimb1 dividendLimb2 dividendTop

/-- Absolute-value word produced by the SMOD divisor sign/absolute-value
    prefix. -/
def smodAbsDivisorWord
    (divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : EvmWord :=
  EvmAsm.Evm64.SDiv.Compose.sdivAbsDivisorWord
    divisorLimb0 divisorLimb1 divisorLimb2 divisorTop

/-- Word produced by conditionally negating the unsigned modulo limbs by the
    SMOD result sign. For SMOD, the result sign is the dividend sign bit. -/
def smodResultSignFixedWord
    (dividendTop limb0 limb1 limb2 limb3 : Word) : EvmWord :=
  let resultSign := dividendTop >>> (63 : BitVec 6).toNat
  let mask := (0 : Word) - resultSign
  let sum0 := (limb0 ^^^ mask) + resultSign
  let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
  let sum1 := (limb1 ^^^ mask) + carry0
  let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
  let sum2 := (limb2 ^^^ mask) + carry1
  let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
  let sum3 := (limb3 ^^^ mask) + carry2
  EvmWord.fromLimbs fun i : Fin 4 =>
    match i with
    | 0 => sum0 | 1 => sum1 | 2 => sum2 | 3 => sum3

/-- The SMOD result sign is the dividend top bit, hence it is a Boolean word. -/
theorem smodResultSign_bool (dividendTop : Word) :
    let resultSign := dividendTop >>> (63 : BitVec 6).toNat
    resultSign = 0 ∨ resultSign = 1 := by
  dsimp
  bv_decide

/-- Conditional negation by the SMOD result sign leaves zero modulo limbs
    equal to zero. -/
theorem smodResultSign_fixZeroLimbs
    (dividendTop : Word) :
    let resultSign := dividendTop >>> (63 : BitVec 6).toNat
    let mask := (0 : Word) - resultSign
    let sum0 := ((0 : Word) ^^^ mask) + resultSign
    let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
    let sum1 := ((0 : Word) ^^^ mask) + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := ((0 : Word) ^^^ mask) + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := ((0 : Word) ^^^ mask) + carry2
    sum0 = 0 ∧ sum1 = 0 ∧ sum2 = 0 ∧ sum3 = 0 := by
  dsimp
  bv_decide

/-- Top output limb of SMOD result-sign-fix is zero when the unsigned modulo
    result is zero. -/
theorem smodResultSign_fixZeroLimb3
    (dividendTop : Word) :
    let resultSign := dividendTop >>> (63 : BitVec 6).toNat
    let mask := (0 : Word) - resultSign
    let sum0 := ((0 : Word) ^^^ mask) + resultSign
    let carry0 := if BitVec.ult sum0 resultSign then (1 : Word) else 0
    let sum1 := ((0 : Word) ^^^ mask) + carry0
    let carry1 := if BitVec.ult sum1 carry0 then (1 : Word) else 0
    let sum2 := ((0 : Word) ^^^ mask) + carry1
    let carry2 := if BitVec.ult sum2 carry1 then (1 : Word) else 0
    let sum3 := ((0 : Word) ^^^ mask) + carry2
    sum3 = 0 := by
  have h := smodResultSign_fixZeroLimbs dividendTop
  simpa using h.2.2.2

end EvmAsm.Evm64.SMod.Compose
