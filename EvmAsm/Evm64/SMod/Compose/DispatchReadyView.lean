/-
  EvmAsm.Evm64.SMod.Compose.DispatchReadyView

  SMOD-local views of the dispatch-ready post consumed by the unsigned MOD
  callable.
-/

import EvmAsm.Evm64.SMod.Compose.AbsComponents
import EvmAsm.Evm64.SMod.Compose.DispatchReadyPost

namespace EvmAsm.Evm64.SMod.Compose

/-- Unfold `saveRaAbsThenModCallDispatchReadyPost` using the SMOD-local
    absolute-value component names. -/
theorem saveRaAbsThenModCallDispatchReadyPost_unfold_smod_components
    {vRa sp base : Word}
    {dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
      divisorLimb0 divisorLimb1 divisorLimb2 divisorTop : Word}
    {v2 v5 v6 : Word}
    {q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     shiftMem nMem jMem retMem dMem dloMem scratchUn0 : Word} :
    saveRaAbsThenModCallDispatchReadyPost vRa sp base
        dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
        divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
        v2 v5 v6 q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 =
      (let dividendSign := smodAbsSign dividendTop
       let divisorSign := smodAbsSign divisorTop
       let divisorMask := smodAbsMask divisorTop
       let divisorSum3 :=
         smodAbsSum3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let divisorCarry3 :=
         smodAbsCarry3 divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       let dividendAbsWord : EvmWord :=
         smodAbsDividendWord dividendLimb0 dividendLimb1 dividendLimb2 dividendTop
       let divisorAbsWord : EvmWord :=
         smodAbsDivisorWord divisorLimb0 divisorLimb1 divisorLimb2 divisorTop
       EvmAsm.Evm64.divModStackDispatchPreNoX1 sp dividendAbsWord divisorAbsWord
           divisorSign ((base + modCallOff) + 4) v2 v5 v6 divisorSum3 divisorMask divisorCarry3
           q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
           shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((.x8 ↦ᵣ dividendSign) ** (.x13 ↦ᵣ dividendSign) **
           (.x18 ↦ᵣ (vRa + EvmAsm.Rv64.signExtend12 (0 : BitVec 12))))) := by
  rw [saveRaAbsThenModCallDispatchReadyPost_unfold]
  rfl

end EvmAsm.Evm64.SMod.Compose
