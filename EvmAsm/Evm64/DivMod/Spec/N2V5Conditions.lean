/-
  EvmAsm.Evm64.DivMod.Spec.N2V5Conditions

  Packaged v5 n=2 path-condition predicates (`fullDivN2MulSubEqV5`,
  `fullDivN2QuotientOverestimateV5`) — the v5 counterparts of the v4 components
  in `N2QuotientStackBridge` — plus the quotient/`div.getLimbN` bridges that
  consume them.  The v5 n=2 loop will PRODUCE these two predicates (from the
  active-addback conservation + the resolved v5 trial overestimate bound); the
  n=2 lane post bridge CONSUMES the `div.getLimbN` facts.  This is the clean
  interface between the (forthcoming) loop and the (done) quotient correctness.
  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5QuotientLane

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

/-- v5 n=2 per-digit conservation (mulsub) predicate: `val256 a = q·val256 b + r`
    for the assembled v5 n=2 quotient/remainder. -/
abbrev fullDivN2MulSubEqV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  val256 a0 a1 a2 a3 =
    (((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
      ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
      ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
      val256 b0 b1 b2 b3 +
    val256
      ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1)
      ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
      ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
      ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)

/-- v5 n=2 quotient lower-bound (overestimate) predicate: `a/b ≤` the assembled
    v5 n=2 quotient. -/
abbrev fullDivN2QuotientOverestimateV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
    ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
      ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
      ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat

/-- The lane's `a b : EvmWord` div limbs equal the v5 n=2 digits, from the
    packaged conditions. -/
theorem div_getLimbN_eq_digit_n2_v5_of_conditions
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : fullDivN2MulSubEqV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge : fullDivN2QuotientOverestimateV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    (EvmWord.div a b).getLimbN 0 = (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 = (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) :=
  div_getLimbN_eq_digit_n2_v5 bltu_2 bltu_1 bltu_0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hmulsub hge

end EvmAsm.Evm64
