/-
  EvmAsm.Evm64.DivMod.Spec.N3QuotientStackBridge

  Explicit-limb n=3 quotient bridge for Unified stack wrapper call sites.
-/

import EvmAsm.Evm64.DivMod.Spec.N3QuotientWord
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmAsm.Rv64

def isTrialN3V4_j1 (bltu : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu =
    BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
      (fullDivN3NormV b0 b1 b2 b3).2.2.1

def isTrialN3V4_j0 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_0 =
    if bltu_1 then
      BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1)
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word)).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
    else
      BitVec.ult
        (iterN3Max
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word)).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1

abbrev fullDivN3MulSubEqV4 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256 a0 a1 a2 a3 =
    (((fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
        2^64 +
      ((fullDivN3R0V4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
      EvmWord.val256 b0 b1 b2 b3 +
    EvmWord.val256
      ((fullDivN3R0V4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.1)
      ((fullDivN3R0V4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
      ((fullDivN3R0V4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
      ((fullDivN3R0V4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)

abbrev fullDivN3QuotientOverestimateV4 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
    ((fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
        2^64 +
      ((fullDivN3R0V4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).1).toNat

abbrev fullDivN3Carry2NzV4 (b0 b1 b2 b3 : Word) : Prop :=
  Carry2NzAll (fullDivN3NormV b0 b1 b2 b3).1
    (fullDivN3NormV b0 b1 b2 b3).2.1
    (fullDivN3NormV b0 b1 b2 b3).2.2.1
    (fullDivN3NormV b0 b1 b2 b3).2.2.2

abbrev fullDivN3PathConditionsV4 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  isTrialN3V4_j1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  isTrialN3V4_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN3Carry2NzV4 b0 b1 b2 b3 ∧
  fullDivN3MulSubEqV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN3QuotientOverestimateV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3

abbrev fullDivN3PathConditionsWordV4 (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) : Prop :=
  fullDivN3PathConditionsV4 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

/-- n=3 quotient bridge specialized to the explicit limb variables used by the
    unified-bound wrappers. -/
theorem fullDivN3QuotientWord_eq_div_of_limbs_mulsub_overestimate
    (bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      EvmWord.val256 a0 a1 a2 a3 =
        (((fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^64 +
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^64 +
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN3QuotientWord bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b := by
  subst a0
  subst a1
  subst a2
  subst a3
  subst b0
  subst b1
  subst b2
  subst b3
  have hraw :=
    fullDivN3QuotientWord_eq_div_of_mulsub_overestimate
      bltu_1 bltu_0 hbnz hmulsub hge
  change
    fullDivN3QuotientWord bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => a.getLimbN 0
            | 1 => a.getLimbN 1
            | 2 => a.getLimbN 2
            | 3 => a.getLimbN 3)
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => b.getLimbN 0
            | 1 => b.getLimbN 1
            | 2 => b.getLimbN 2
            | 3 => b.getLimbN 3) at hraw
  exact hraw.trans (by
    congr
    · exact EvmWord.fromLimbs_match_getLimbN_id a
    · exact EvmWord.fromLimbs_match_getLimbN_id b)

/-- Explicit-limb n=3 quotient bridge for the v4 call/max path. -/
theorem fullDivN3QuotientWordV4_eq_div_of_limbs_mulsub_overestimate
    (bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : fullDivN3MulSubEqV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge : fullDivN3QuotientOverestimateV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN3QuotientWordV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b := by
  subst a0
  subst a1
  subst a2
  subst a3
  subst b0
  subst b1
  subst b2
  subst b3
  have hraw :=
    fullDivN3QuotientWordV4_eq_div_of_mulsub_overestimate
      bltu_1 bltu_0 hbnz hmulsub hge
  change
    fullDivN3QuotientWordV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => a.getLimbN 0
            | 1 => a.getLimbN 1
            | 2 => a.getLimbN 2
            | 3 => a.getLimbN 3)
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => b.getLimbN 0
            | 1 => b.getLimbN 1
            | 2 => b.getLimbN 2
            | 3 => b.getLimbN 3) at hraw
  exact hraw.trans (by
    congr
    · exact EvmWord.fromLimbs_match_getLimbN_id a
    · exact EvmWord.fromLimbs_match_getLimbN_id b)

/-- Explicit-limb v4 quotient bridge from the bundled N3 path predicate. -/
theorem fullDivN3QuotientWordV4_eq_div_of_path_conditions
    (bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hpath : fullDivN3PathConditionsV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN3QuotientWordV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b := by
  obtain ⟨_, _, _, hmulsub, hge⟩ := hpath
  exact fullDivN3QuotientWordV4_eq_div_of_limbs_mulsub_overestimate
    bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hmulsub hge

/-- EvmWord-level v4 quotient bridge from the bundled N3 path predicate. -/
theorem fullDivN3QuotientWordV4_eq_div_of_word_path_conditions
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hpath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b) :
    fullDivN3QuotientWordV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  exact fullDivN3QuotientWordV4_eq_div_of_path_conditions
    bltu_1 bltu_0 (a := a) (b := b)
    (a0 := a.getLimbN 0) (a1 := a.getLimbN 1)
    (a2 := a.getLimbN 2) (a3 := a.getLimbN 3)
    (b0 := b.getLimbN 0) (b1 := b.getLimbN 1)
    (b2 := b.getLimbN 2) (b3 := b.getLimbN 3)
    rfl rfl rfl rfl rfl rfl rfl rfl hbnz hpath

end EvmAsm.Evm64
