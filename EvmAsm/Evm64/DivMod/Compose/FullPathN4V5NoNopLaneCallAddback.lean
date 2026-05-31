/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallAddback

  The n=4 v5 DIV lane, call+addback-beq branch, assembled from the dispatch
  precondition to `divStackDispatchPostV5`, taking the quotient-correctness facts
  as HYPOTHESES.  Mirror of the call+skip lane (`FullPathN4V5NoNopLaneCallSkip`)
  with the full call+addback path (#7599) and the BEQ-nonzero borrow/carry2
  hypotheses.  The addback corrected quotient `q_out` is named
  (`fullDivN4CallAddbackQuotientV5`) since it is too large to inline.
  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopFullCallAddback
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDispatchPre
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopDispatchPostBridge
import EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffoldV5Div

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The n=4 v5 call+addback-beq corrected quotient `q_out` (named; defeq to the
    `q_out` baked into `fullDivN4CallAddbackBeqPostV5`). -/
def fullDivN4CallAddbackQuotientV5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Word :=
  let shift := (clzResult b3).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let b2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let b1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let b0' := b0 <<< (shift.toNat % 64)
  let u4 := a3 >>> (antiShift.toNat % 64)
  let u3 := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u2 := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u1 := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u0 := a0 <<< (shift.toNat % 64)
  let qHat := divKTrialCallV5QHat u4 u3 b3'
  let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
  let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
  if carry = 0 then qHat + signExtend12 4095 + signExtend12 4095
  else qHat + signExtend12 4095

/-- n=4 v5 DIV lane (call+addback-beq branch), from the dispatch pre to
    `divStackDispatchPostV5`, given the quotient-correctness facts. -/
theorem evm_div_n4_lane_callAddback_of_hdiv (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4 a3 b2 b3)
    (hborrow : isAddbackBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2_nz : isAddbackCarry2NzN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 = fullDivN4CallAddbackQuotientV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 = 0)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 = 0)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 = 0) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b3).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  have hpath := evm_div_n4_full_call_addback_spec_v5_noNop sp base
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    hbnz hb3nz hshift_nz halign hbltu hborrow hcarry2_nz
  refine cpsTripleWithin_mono_nSteps (by have h : unifiedDivBound = 946 := rfl; omega) <|
    cpsTripleWithin_weaken ?_ ?_ hpath
  · intro h hp
    exact n4_dispatchPre_to_pathEntry_v5 sp a b x1Val ((clzResult b3).2 >>> (63 : Nat))
      v5 v6 v7 v10 v11Old a0 a1 a2 a3 b0 b1 b2 b3
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem retMem dMem dloMem
      scratchUn0 scratchMem ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 h hp
  · intro h hq
    delta divStackDispatchPostV5
    unfold fullDivN4CallAddbackBeqPostV5 at hq
    exact n4_denormDivPost_frame_to_divStackDispatchPost_v5 sp base a b a0 a1 a2 a3
      _ (fullDivN4CallAddbackQuotientV5 a0 a1 a2 a3 b0 b1 b2 b3) _ _ _ _ _ _ _ _ _ _
      ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hq

end EvmAsm.Evm64
