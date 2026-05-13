/-
  EvmAsm.Evm64.SDiv.Compose.BzeroPost

  Named postconditions and frame reshaping lemmas for the SDIV zero-divisor
  div-call path.
-/

import EvmAsm.Evm64.SDiv.Compose.DivCall
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwn
import EvmAsm.Evm64.SDiv.Compose.Words

namespace EvmAsm.Evm64.SDiv.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Named postcondition after the SDIV prefix has called the unsigned DIV
    callable along the zero-divisor branch. This keeps the sign frame and the
    concrete return address bundled for the following result-sign-fix step. -/
@[irreducible]
def saveRaDivCallBzeroCallablePost
    (vRa sp base : Word)
    (dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word) : Assertion :=
  let resultSign :=
    (dividendTop >>> (63 : BitVec 6).toNat) ^^^
      (divisorTop >>> (63 : BitVec 6).toNat)
  let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
  ((EvmAsm.Evm64.divStackDispatchPostNoX1 sp
      (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
      (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
    (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
   ((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
    (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))))

theorem saveRaDivCallBzeroCallablePost_unfold
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       ((EvmAsm.Evm64.divStackDispatchPostNoX1 sp
           (sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop)
           (sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop) **
         (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
        ((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
         (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))))) := by
  delta saveRaDivCallBzeroCallablePost
  rfl

/-- Zero-divisor view of `saveRaDivCallBzeroCallablePost`: the unsigned DIV
    callable's quotient word in the EVM stack result slot is concretely zero. -/
theorem saveRaDivCallBzeroCallablePost_unfold_zero_quotient
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word}
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       (((.x12 ↦ᵣ (sp + 32)) ** regOwn .x2 **
         regOwn .x5 ** regOwn .x6 ** regOwn .x7 **
         regOwn .x10 ** regOwn .x11 ** (.x0 ↦ᵣ (0 : Word)) **
         evmWordIs sp dividendAbsWord ** evmWordIs (sp + 32) (0 : EvmWord) **
         EvmAsm.Evm64.divScratchOwnCall sp) **
        (.x1 ↦ᵣ ((base + divCallOff) + 4))) **
       ((.x8 ↦ᵣ resultSign) ** (.x9 ↦ᵣ divisorSign) **
        (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12))))) := by
  rw [saveRaDivCallBzeroCallablePost_unfold,
    EvmAsm.Evm64.divStackDispatchPostNoX1_unfold]
  dsimp only
  rw [hbz, EvmWord.div_zero_right]

/-- Frame left around the result-sign-fix precondition after the SDIV prefix
    and zero-divisor unsigned-DIV callable have run. -/
@[irreducible]
def saveRaDivCallBzeroResultSignFixFrame
    (vRa sp base divisorSign : Word) (dividendAbsWord : EvmWord) : Assertion :=
  regOwn .x2 ** regOwn .x5 ** regOwn .x6 **
  evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCall sp **
  (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
  (.x9 ↦ᵣ divisorSign) **
  (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))

theorem saveRaDivCallBzeroResultSignFixFrame_unfold
    {vRa sp base divisorSign : Word} {dividendAbsWord : EvmWord} :
    saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord =
      (regOwn .x2 ** regOwn .x5 ** regOwn .x6 **
       evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCall sp **
       (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
       (.x9 ↦ᵣ divisorSign) **
       (.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12)))) := by
  delta saveRaDivCallBzeroResultSignFixFrame
  rfl

/-- Frame remaining after exposing `x18` for the saved-RA return. -/
@[irreducible]
def saveRaDivCallBzeroSavedRaRetFrame
    (sp base divisorSign : Word) (dividendAbsWord : EvmWord) : Assertion :=
  regOwn .x2 ** regOwn .x5 ** regOwn .x6 **
  evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCall sp **
  (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
  (.x9 ↦ᵣ divisorSign)

theorem saveRaDivCallBzeroSavedRaRetFrame_unfold
    {sp base divisorSign : Word} {dividendAbsWord : EvmWord} :
    saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord =
      (regOwn .x2 ** regOwn .x5 ** regOwn .x6 **
       evmWordIs sp dividendAbsWord ** EvmAsm.Evm64.divScratchOwnCall sp **
       (.x1 ↦ᵣ ((base + divCallOff) + 4)) **
       (.x9 ↦ᵣ divisorSign)) := by
  delta saveRaDivCallBzeroSavedRaRetFrame
  rfl

/-- Expose the saved return address atom from the bzero result-sign-fix
    frame, leaving the rest as an explicit return frame. -/
theorem saveRaDivCallBzeroResultSignFixFrame_to_savedRaRet
    {vRa sp base divisorSign : Word} {dividendAbsWord : EvmWord} :
    saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord =
      ((.x18 ↦ᵣ (vRa + signExtend12 (0 : BitVec 12))) **
       saveRaDivCallBzeroSavedRaRetFrame sp base divisorSign dividendAbsWord) := by
  rw [saveRaDivCallBzeroResultSignFixFrame_unfold,
    saveRaDivCallBzeroSavedRaRetFrame_unfold]
  xperm

/-- Zero-divisor callable post reshaped as the result-sign-fix precondition
    over the current quotient cell plus an explicit frame. -/
theorem saveRaDivCallBzeroCallablePost_resultSignFixPreOwnScratch
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word}
    (hbz : sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop = 0) :
    saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       resultSignFixPreOwnScratch (sp + 32) resultSign 0 0 0 0 **
       saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord) := by
  rw [saveRaDivCallBzeroCallablePost_unfold_zero_quotient hbz]
  dsimp only
  rw [resultSignFixPreOwnScratch_unfold,
    saveRaDivCallBzeroResultSignFixFrame_unfold, evmWordIs_zero]
  rw [show (sp + 32 + signExtend12 (0 : BitVec 12) : Word) = sp + 32 by bv_addr]
  rw [show (sp + 32 + signExtend12 (8 : BitVec 12) : Word) = (sp + 32) + 8 by bv_addr]
  rw [show (sp + 32 + signExtend12 (16 : BitVec 12) : Word) = (sp + 32) + 16 by bv_addr]
  rw [show (sp + 32 + signExtend12 (24 : BitVec 12) : Word) = (sp + 32) + 24 by bv_addr]
  xperm

/-- Callable post reshaped as the result-sign-fix precondition over the
    unsigned DIV quotient plus the saved-RA/sign frame. The zero-divisor
    specialization below is the same shape with the quotient reduced to zero. -/
theorem saveRaDivCallBzeroCallablePost_resultSignFixPreOwnScratch_quotient
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word} :
    saveRaDivCallBzeroCallablePost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop =
      (let dividendAbsWord :=
         sdivAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord :=
         sdivAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let quotientWord := EvmWord.div dividendAbsWord divisorAbsWord
       let resultSign :=
         (dividendTop >>> (63 : BitVec 6).toNat) ^^^
           (divisorTop >>> (63 : BitVec 6).toNat)
       let divisorSign := divisorTop >>> (63 : BitVec 6).toNat
       resultSignFixPreOwnScratch (sp + 32) resultSign
         (quotientWord.getLimbN 0) (quotientWord.getLimbN 1)
         (quotientWord.getLimbN 2) (quotientWord.getLimbN 3) **
       saveRaDivCallBzeroResultSignFixFrame vRa sp base divisorSign dividendAbsWord) := by
  rw [saveRaDivCallBzeroCallablePost_unfold,
    EvmAsm.Evm64.divStackDispatchPostNoX1_unfold]
  dsimp only
  rw [resultSignFixPreOwnScratch_unfold,
    saveRaDivCallBzeroResultSignFixFrame_unfold, evmWordIs_sp32_unfold]
  rw [show (sp + 32 + signExtend12 (0 : BitVec 12) : Word) = sp + 32 by bv_addr]
  rw [show (sp + 32 + signExtend12 (8 : BitVec 12) : Word) = sp + 40 by bv_addr]
  rw [show (sp + 32 + signExtend12 (16 : BitVec 12) : Word) = sp + 48 by bv_addr]
  rw [show (sp + 32 + signExtend12 (24 : BitVec 12) : Word) = sp + 56 by bv_addr]
  xperm

end EvmAsm.Evm64.SDiv.Compose
