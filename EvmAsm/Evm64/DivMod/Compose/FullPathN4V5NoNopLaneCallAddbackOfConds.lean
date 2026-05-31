/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneCallAddbackOfConds

  The n=4 v5 DIV call+addback-beq lane, from the dispatch precondition to
  `divStackDispatchPostV5`, with the quotient-correctness facts DISCHARGED from
  the v5 call-addback word equality (#7609) + the q_out reconciliation (#7610) —
  so the lane takes only the runtime addback conditions (the v5 addback
  borrow/carry2 + the v5 addback semantic), not the raw `hdiv` facts.  Direct
  analog of the call-skip lane of conds (`FullPathN4V5NoNopLaneCallSkipOfConds`):
  composes the call-addback lane skeleton (#7603, `evm_div_n4_lane_callAddback_of_hdiv`)
  with `n4_call_addback_beq_div_getLimbN_v5` (#7609), reconciling its
  `n4CallAddbackBeqQOutV5` output to the skeleton's
  `fullDivN4CallAddbackQuotientV5` form via `fullDivN4CallAddbackQuotientV5_eq_QOutV5`
  (#7610), and the `a.getLimbN i ↔ aᵢ` / `b.getLimbN i ↔ bᵢ` forms via the limb
  hypotheses.  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackQOutReconcile
import EvmAsm.Evm64.DivMod.Spec.N4V5CallAddbackWordLane

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- n=4 v5 DIV call+addback-beq lane, with `hdiv` discharged from the word
    equality + q_out reconciliation; takes the runtime call-addback conditions
    (the v5 addback borrow/carry2 + the v5 addback semantic) instead. -/
theorem evm_div_n4_lane_callAddback_of_conds (sp base : Word) (a b : EvmWord)
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
    (hborrow : isAddbackBorrowN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry2_nz : isAddbackCarry2NzN4CallV5 a0 a1 a2 a3 b0 b1 b2 b3)
    (hsem : n4CallAddbackBeqSemanticHoldsV5 a b) :
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
  have hbnz_lor : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := fun h => hb3nz (BitVec.or_eq_zero_iff.mp h).2
  obtain ⟨hd0, hd1, hd2, hd3⟩ :=
    n4_call_addback_beq_div_getLimbN_v5 a b hb_ne hb3nz' hsem
  rw [← fullDivN4CallAddbackQuotientV5_eq_QOutV5 a b] at hd0
  rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3] at hd0
  exact evm_div_n4_lane_callAddback_of_hdiv sp base a b x1Val v5 v6 v7 v10 v11Old
    a0 a1 a2 a3 b0 b1 b2 b3
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz_lor hb3nz hshift_nz halign hbltu hborrow hcarry2_nz
    hd0 hd1 hd2 hd3

end EvmAsm.Evm64
