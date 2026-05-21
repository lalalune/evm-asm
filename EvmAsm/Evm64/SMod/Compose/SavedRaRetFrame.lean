/-
  EvmAsm.Evm64.SMod.Compose.SavedRaRetFrame

  Frame split for exposing the saved return address before the final SMOD
  return instruction.
-/

import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixPost
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Evm64.SMod.Compose

open EvmAsm.Rv64.Tactics

/-- Frame remaining after exposing `x18` for the saved-RA return. -/
@[irreducible]
def smodSavedRaRetFrame
    (sp base dividendTop divisorTop : Word) (dividendAbsWord : EvmWord) :
    EvmAsm.Rv64.Assertion :=
  let dividendSign := smodAbsSign dividendTop
  let divisorSign := smodAbsSign divisorTop
  (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
    (.x9 ↦ᵣ divisorSign) ** (.x8 ↦ᵣ dividendSign) **
    EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 **
    EvmAsm.Rv64.regOwn .x6 ** evmWordIs sp dividendAbsWord **
    EvmAsm.Evm64.divScratchOwnCallNoX1 sp

theorem smodSavedRaRetFrame_unfold
    {sp base dividendTop divisorTop : Word} {dividendAbsWord : EvmWord} :
    smodSavedRaRetFrame sp base dividendTop divisorTop dividendAbsWord =
      (let dividendSign := smodAbsSign dividendTop
       let divisorSign := smodAbsSign divisorTop
       (.x1 ↦ᵣ ((base + modCallOff) + 4)) **
         (.x9 ↦ᵣ divisorSign) ** (.x8 ↦ᵣ dividendSign) **
         EvmAsm.Rv64.regOwn .x2 ** EvmAsm.Rv64.regOwn .x5 **
         EvmAsm.Rv64.regOwn .x6 ** evmWordIs sp dividendAbsWord **
         EvmAsm.Evm64.divScratchOwnCallNoX1 sp) := by
  delta smodSavedRaRetFrame
  rfl

theorem smodSavedRaRetFrame_pcFree
    {sp base dividendTop divisorTop : Word} {dividendAbsWord : EvmWord} :
    (smodSavedRaRetFrame sp base dividendTop divisorTop dividendAbsWord).pcFree := by
  rw [smodSavedRaRetFrame_unfold,
    EvmAsm.Evm64.divScratchOwnCallNoX1_unfold,
    EvmAsm.Evm64.divScratchOwn_unfold]
  dsimp only
  pcFree

instance pcFreeInst_smodSavedRaRetFrame
    (sp base dividendTop divisorTop : Word) (dividendAbsWord : EvmWord) :
    EvmAsm.Rv64.Assertion.PCFree
      (smodSavedRaRetFrame sp base dividendTop divisorTop dividendAbsWord) :=
  ⟨smodSavedRaRetFrame_pcFree⟩

/-- Expose the saved return address atom from the SMOD result-sign-fix frame,
    leaving the rest as an explicit return frame. -/
theorem smodModCallResultSignFixFrame_to_savedRaRet
    {vRa sp base dividendTop divisorTop : Word} {dividendAbsWord : EvmWord} :
    smodModCallResultSignFixFrame vRa sp base dividendTop divisorTop dividendAbsWord =
      ((.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))) **
       smodSavedRaRetFrame sp base dividendTop divisorTop dividendAbsWord) := by
  rw [smodModCallResultSignFixFrame_unfold, smodSavedRaRetFrame_unfold]
  xperm

end EvmAsm.Evm64.SMod.Compose
