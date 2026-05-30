/-
  EvmAsm.Evm64.DivMod.Spec.N2V5TrialBranch

  The v5 n=2 per-digit trial-branch predicates `isTrialN2V5_j{2,1,0}` (each `bltu`
  flag = whether the running remainder's top limb is `< v.2.1`, the divisor's top
  normalized limb) and the bundled v5 n=2 path predicate `fullDivN2PathConditionsV5`
  (trial branches + the conservation/overestimate predicates from `N2V5Conditions`).
  v5 counterparts of `isTrialN2V4_j*` / `fullDivN2SelectedPathConditionsV4`
  (N2QuotientStackBridge).  The v5 n=2 loop will establish this predicate; the
  quotient correctness consumes its conservation/overestimate components.
  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5Conditions

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 n=2 trial branch, j=2 (top digit): call iff `uTop < v.2.1`. -/
def isTrialN2V5_j2 (bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_2 =
    BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
      (fullDivN2NormV b0 b1 b2 b3).2.1

/-- v5 n=2 trial branch, j=1: call iff the j=2 remainder's limb1 `< v.2.1`. -/
def isTrialN2V5_j1 (bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_1 =
    BitVec.ult
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN2NormV b0 b1 b2 b3).2.1

/-- v5 n=2 trial branch, j=0: call iff the j=1 remainder's limb1 `< v.2.1`. -/
def isTrialN2V5_j0 (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_0 =
    BitVec.ult
      (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN2NormV b0 b1 b2 b3).2.1

/-- Bundled v5 n=2 path predicate: the three trial branches plus the conservation
    and quotient-overestimate facts.  The v5 n=2 loop establishes this; the
    quotient correctness consumes the last two conjuncts. -/
def fullDivN2PathConditionsV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  isTrialN2V5_j2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  isTrialN2V5_j1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  isTrialN2V5_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN2MulSubEqV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN2QuotientOverestimateV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3

theorem fullDivN2PathConditionsV5_mulsub
    (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hpath : fullDivN2PathConditionsV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN2MulSubEqV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 :=
  hpath.2.2.2.1

theorem fullDivN2PathConditionsV5_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hpath : fullDivN2PathConditionsV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN2QuotientOverestimateV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 :=
  hpath.2.2.2.2

/-- EvmWord-level v5 n=2 quotient bridge from the bundled path predicate. -/
theorem div_getLimbN_eq_digit_n2_v5_of_path
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hpath : fullDivN2PathConditionsV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    (EvmWord.div a b).getLimbN 0 = (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 = (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) :=
  div_getLimbN_eq_digit_n2_v5_of_conditions bltu_2 bltu_1 bltu_0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz
    (fullDivN2PathConditionsV5_mulsub bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hpath)
    (fullDivN2PathConditionsV5_overestimate bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hpath)

end EvmAsm.Evm64
