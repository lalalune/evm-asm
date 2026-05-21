/-
  EvmAsm.Evm64.SDiv.SpecSemantic

  Pure semantic result bridge for the top-level SDIV stack spec.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCallDispatchZeroDivisor
import EvmAsm.Evm64.SDiv.Compose.DivCallExactReturnHandoff
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixZeroWordView
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64

open EvmAsm.Evm64.SDiv.Compose

/-- Nonnegative/nonnegative exact-path SDIV result bridge.

    When both input signs are zero, the assembly absolute-value helpers leave
    both operands unchanged and the result-sign-fix helper leaves the unsigned
    quotient unchanged. In that case `EvmWord.div` and `EvmWord.sdiv` agree. -/
theorem sdivResultSignFixedWord_eq_sdiv_of_nonnegative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    let dividendAbsWord :=
      sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
    sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
      EvmWord.sdiv dividend divisor := by
  dsimp
  rw [sdivAbsDividendWord_eq_word_of_sign_zero dividend hDividendSign]
  rw [sdivAbsDivisorWord_eq_word_of_sign_zero divisor hDivisorSign]
  have hResultSign :
      (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
        (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat) = (0 : Word) := by
    rw [hDividendSign, hDivisorSign]
    bv_decide
  rw [sdivResultSignFixedWord_eq_word_of_result_sign_zero _ _ _ hResultSign]
  have hDividendMsb : BitVec.msb dividend = false := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDividendSign
    simp at hDividendSign
    bv_decide
  have hDivisorMsb : BitVec.msb divisor = false := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDivisorSign
    simp at hDivisorSign
    bv_decide
  unfold EvmWord.div EvmWord.sdiv
  rw [BitVec.sdiv_eq, hDividendMsb, hDivisorMsb]
  by_cases hZero : divisor = 0
  · simp [hZero]
  · rw [if_neg hZero]

/-- Negative/negative exact-path SDIV result bridge.

    When both input signs are one, the assembly absolute-value helpers produce
    `-dividend` and `-divisor`; the result sign is zero, so the result-sign-fix
    helper leaves the unsigned quotient unchanged. This is the `true,true`
    branch of `BitVec.sdiv_eq`. -/
theorem sdivResultSignFixedWord_eq_sdiv_of_negative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    let dividendAbsWord :=
      sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
    sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
      EvmWord.sdiv dividend divisor := by
  dsimp
  rw [sdivAbsDividendWord_eq_neg_word_of_sign_one dividend hDividendSign]
  rw [sdivAbsDivisorWord_eq_neg_word_of_sign_one divisor hDivisorSign]
  have hResultSign :
      (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
        (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat) = (0 : Word) := by
    rw [hDividendSign, hDivisorSign]
    bv_decide
  rw [sdivResultSignFixedWord_eq_word_of_result_sign_zero _ _ _ hResultSign]
  have hDividendMsb : BitVec.msb dividend = true := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDividendSign
    simp at hDividendSign
    bv_decide
  have hDivisorMsb : BitVec.msb divisor = true := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDivisorSign
    simp at hDivisorSign
    bv_decide
  unfold EvmWord.div EvmWord.sdiv
  rw [BitVec.sdiv_eq, hDividendMsb, hDivisorMsb]
  by_cases hZero : -divisor = 0
  · simp [hZero]
  · rw [if_neg hZero]

/-- Nonnegative/negative exact-path SDIV result bridge.

    When only the divisor is negative, the assembly divisor absolute-value
    helper produces `-divisor` and result-sign-fix negates the unsigned
    quotient. This is the `false,true` branch of `BitVec.sdiv_eq`. -/
theorem sdivResultSignFixedWord_eq_sdiv_of_nonnegative_negative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word)) :
    let dividendAbsWord :=
      sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
    sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
      EvmWord.sdiv dividend divisor := by
  dsimp
  rw [sdivAbsDividendWord_eq_word_of_sign_zero dividend hDividendSign]
  rw [sdivAbsDivisorWord_eq_neg_word_of_sign_one divisor hDivisorSign]
  have hResultSign :
      (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
        (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat) = (1 : Word) := by
    rw [hDividendSign, hDivisorSign]
    bv_decide
  rw [sdivResultSignFixedWord_eq_neg_word_of_result_sign_one _ _ _ hResultSign]
  have hDividendMsb : BitVec.msb dividend = false := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDividendSign
    simp at hDividendSign
    bv_decide
  have hDivisorMsb : BitVec.msb divisor = true := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDivisorSign
    simp at hDivisorSign
    bv_decide
  unfold EvmWord.div EvmWord.sdiv
  rw [BitVec.sdiv_eq, hDividendMsb, hDivisorMsb]
  by_cases hZero : -divisor = 0
  · simp [hZero]
  · rw [if_neg hZero]

/-- Negative/nonnegative exact-path SDIV result bridge.

    When only the dividend is negative, the assembly dividend absolute-value
    helper produces `-dividend` and result-sign-fix negates the unsigned
    quotient. This is the `true,false` branch of `BitVec.sdiv_eq`. -/
theorem sdivResultSignFixedWord_eq_sdiv_of_negative_nonnegative
    (dividend divisor : EvmWord)
    (hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word))
    (hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word)) :
    let dividendAbsWord :=
      sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
    sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
      EvmWord.sdiv dividend divisor := by
  dsimp
  rw [sdivAbsDividendWord_eq_neg_word_of_sign_one dividend hDividendSign]
  rw [sdivAbsDivisorWord_eq_word_of_sign_zero divisor hDivisorSign]
  have hResultSign :
      (dividend.getLimbN 3 >>> (63 : BitVec 6).toNat) ^^^
        (divisor.getLimbN 3 >>> (63 : BitVec 6).toNat) = (1 : Word) := by
    rw [hDividendSign, hDivisorSign]
    bv_decide
  rw [sdivResultSignFixedWord_eq_neg_word_of_result_sign_one _ _ _ hResultSign]
  have hDividendMsb : BitVec.msb dividend = true := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDividendSign
    simp at hDividendSign
    bv_decide
  have hDivisorMsb : BitVec.msb divisor = false := by
    unfold EvmWord.getLimbN EvmWord.getLimb at hDivisorSign
    simp at hDivisorSign
    bv_decide
  unfold EvmWord.div EvmWord.sdiv
  rw [BitVec.sdiv_eq, hDividendMsb, hDivisorMsb]
  by_cases hZero : divisor = 0
  · simp [hZero]
  · rw [if_neg hZero]

/-- Exact-path SDIV result bridge for arbitrary operand signs.

    This dispatches over the two extracted sign bits and reuses the four
    sign-specific semantic bridges above. -/
theorem sdivResultSignFixedWord_eq_sdiv
    (dividend divisor : EvmWord) :
    let dividendAbsWord :=
      sdivAbsDividendWord (dividend.getLimbN 0) (dividend.getLimbN 1)
        (dividend.getLimbN 2) (dividend.getLimbN 3)
    let divisorAbsWord :=
      sdivAbsDivisorWord (divisor.getLimbN 0) (divisor.getLimbN 1)
        (divisor.getLimbN 2) (divisor.getLimbN 3)
    let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
    sdivResultSignFixedWord (dividend.getLimbN 3) (divisor.getLimbN 3)
      (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
      (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) =
      EvmWord.sdiv dividend divisor := by
  have hDividendSign :
      dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word) ∨
        dividend.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word) := by
    unfold EvmWord.getLimbN EvmWord.getLimb
    bv_decide
  have hDivisorSign :
      divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (0 : Word) ∨
        divisor.getLimbN 3 >>> (63 : BitVec 6).toNat = (1 : Word) := by
    unfold EvmWord.getLimbN EvmWord.getLimb
    bv_decide
  rcases hDividendSign with hDividendSign | hDividendSign
  · rcases hDivisorSign with hDivisorSign | hDivisorSign
    · exact sdivResultSignFixedWord_eq_sdiv_of_nonnegative
        dividend divisor hDividendSign hDivisorSign
    · exact sdivResultSignFixedWord_eq_sdiv_of_nonnegative_negative
        dividend divisor hDividendSign hDivisorSign
  · rcases hDivisorSign with hDivisorSign | hDivisorSign
    · exact sdivResultSignFixedWord_eq_sdiv_of_negative_nonnegative
        dividend divisor hDividendSign hDivisorSign
    · exact sdivResultSignFixedWord_eq_sdiv_of_negative
        dividend divisor hDividendSign hDivisorSign

end EvmAsm.Evm64
