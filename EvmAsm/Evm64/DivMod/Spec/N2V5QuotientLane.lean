/-
  EvmAsm.Evm64.DivMod.Spec.N2V5QuotientLane

  EvmWord-level v5 n=2 quotient bridge: for the lane's `a b : EvmWord`, given the
  per-digit conservation (`hmulsub`) and quotient lower bound (`hge`),
  `fullDivN2QuotientWordV5 = EvmWord.div a b`, and each `div` limb equals the
  corresponding v5 n=2 schoolbook digit.  Lifts
  `fullDivN2QuotientWordV5_eq_div_of_mulsub_overestimate` (#7336) to `a b`
  via the getLimbN limb decompositions.  v5 counterpart of the v4 path-conditions
  bridge (N2QuotientStackBridge).  Feeds the n=2 lane post bridge.  Bead
  `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5QuotientCorrect

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

theorem fullDivN2QuotientWordV5_eq_div_lane
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      val256 a0 a1 a2 a3 =
        (((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          val256 b0 b1 b2 b3 +
        val256
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
        ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      = EvmWord.div a b := by
  have hraw := fullDivN2QuotientWordV5_eq_div_of_mulsub_overestimate
    bltu_2 bltu_1 bltu_0 hbnz hmulsub hge
  subst a0; subst a1; subst a2; subst a3; subst b0; subst b1; subst b2; subst b3
  refine hraw.trans ?_
  congr 1
  · exact EvmWord.fromLimbs_match_getLimbN_id a
  · exact EvmWord.fromLimbs_match_getLimbN_id b

/-- Per-limb form: each limb of `EvmWord.div a b` equals the corresponding v5
    n=2 schoolbook digit (limb 3 is `0`). -/
theorem div_getLimbN_eq_digit_n2_v5
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      val256 a0 a1 a2 a3 =
        (((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          val256 b0 b1 b2 b3 +
        val256
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
        ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    (EvmWord.div a b).getLimbN 0 = (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 = (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  have hw := fullDivN2QuotientWordV5_eq_div_lane bltu_2 bltu_1 bltu_0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hmulsub hge
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← hw]
  · exact fullDivN2QuotientWordV5_getLimbN0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  · exact fullDivN2QuotientWordV5_getLimbN1 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  · exact fullDivN2QuotientWordV5_getLimbN2 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  · exact fullDivN2QuotientWordV5_getLimbN3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3

end EvmAsm.Evm64
