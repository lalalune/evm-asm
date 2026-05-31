/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallSkipOfConds

  The n=4 v5 DIV call-skip lane, from the dispatch precondition to
  `divStackDispatchPostV5`, with the quotient-correctness facts DISCHARGED from
  the v5 call-skip word equality (#7608) — so the lane takes only the runtime
  conditions (the v4 borrow/semantic + the v5 trial↔v4 no-wrap bridge), not the
  raw `hdiv` facts.  Composes the call-skip lane skeleton (#7602,
  `evm_div_n4_lane_callSkip_of_hdiv`) with `n4_call_skip_div_mod_getLimbN_v5`
  (#7608), reconciling the `a.getLimbN i ↔ aᵢ` forms via the limb hypotheses.
  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallSkip
import EvmAsm.Evm64.DivMod.Spec.N4V5CallSkipWordLane

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- n=4 v5 DIV call-skip lane, with `hdiv` discharged from the word equality;
    takes the runtime call-skip conditions (v4 borrow/semantic + the trial↔v4
    bridge) instead. -/
theorem evm_div_n4_lane_callSkip_of_conds (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) = base + div128CallRetOff)
    (hbltu : isCallTrialN4 a3 b2 b3)
    (hborrowV5 : isSkipBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hborrowV4 : isSkipBorrowN4CallV4Evm a b)
    (hsem : n4CallSkipSemanticHoldsV4 a b)
    (hbridge :
      divKTrialCallV5QHat
        ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
        (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
        (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))) =
      div128Quot_v4
        ((a.getLimbN 3) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
        (((a.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((a.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
        (((b.getLimbN 3) <<< ((clzResult (b.getLimbN 3)).1.toNat % 64)) |||
          ((b.getLimbN 2) >>> ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult b3).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  have hb3nz' : b.getLimbN 3 ≠ 0 := by rw [hb3]; exact hb3nz
  have hb_ne : b ≠ 0 := by
    intro h; exact hb3nz' (by rw [h]; exact EvmWord.getLimbN_zero 3)
  have hshift_nz' : (clzResult (b.getLimbN 3)).1 ≠ 0 := by rw [hb3]; exact hshift_nz
  have hbnz_lor : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := fun h => hb3nz (BitVec.or_eq_zero_iff.mp h).2
  obtain ⟨hd0, hd1, hd2, hd3⟩ :=
    n4_call_skip_div_mod_getLimbN_v5 a b hb_ne hshift_nz' hborrowV4 hsem hbridge
  rw [ha2, ha3, hb2, hb3] at hd0
  exact evm_div_n4_lane_callSkip_of_hdiv sp base a b x1Val v5 v6 v7 v10 v11Old
    a0 a1 a2 a3 b0 b1 b2 b3
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz_lor hb3nz hshift_nz halign hbltu hborrowV5
    hd0 hd1 hd2 hd3

end EvmAsm.Evm64
