/-
  EvmAsm.Evm64.DivMod.Spec.N2QuotientStackBridge

  Explicit-limb n=2 quotient bridge for Unified stack wrapper call sites.
-/

import EvmAsm.Evm64.DivMod.Spec.N2QuotientWord
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4Families
import EvmAsm.Evm64.EvmWordArith.DivAccumulate
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

abbrev fullDivN2MulSubEqV4 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256 a0 a1 a2 a3 =
    (((fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
        2^128 +
      ((fullDivN2R1V4 bltu_2 bltu_1
        a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
      ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
      EvmWord.val256 b0 b1 b2 b3 +
    EvmWord.val256
      ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.1)
      ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
      ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
      ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)

abbrev fullDivN2QuotientOverestimateV4 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
    ((fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
        2^128 +
      ((fullDivN2R1V4 bltu_2 bltu_1
        a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
      ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).1).toNat

/-- Semantic bridge for the n=2 v4 quotient word once callers provide the
    accumulated mulsub equation and quotient-overestimate bound. -/
theorem fullDivN2QuotientWordV4_eq_div_of_mulsub_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge : fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  let q0 := (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
  let q1 := (fullDivN2R1V4 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
  let q2 := (fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
  let r0 := (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
  let r1 := (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
  let r2 := (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
  let r3 := (fullDivN2R0V4 bltu_2 bltu_1 bltu_0
    a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
  have h_correct := div_correct_n2_no_shift
    (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3)
    (q0 := q0) (q1 := q1) (q2 := q2)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
    hbnz (by simpa [fullDivN2MulSubEqV4, q0, q1, q2, r0, r1, r2, r3] using hmulsub)
    (by simpa [fullDivN2QuotientOverestimateV4, q0, q1, q2] using hge)
  delta fullDivN2QuotientWordV4
  change
    EvmWord.fromLimbs (fun i : Fin 4 =>
      match i with
      | 0 => q0 | 1 => q1 | 2 => q2 | 3 => (0 : Word)) =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)
  exact h_correct.1

/-- Word-specialized n=2 v4 quotient bridge for callers that store the inputs as
    `EvmWord`s and refer to their limbs directly. -/
theorem fullDivN2QuotientWordV4_eq_div_of_getLimbN_mulsub_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hmulsub : fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hge : fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  have hraw :=
    fullDivN2QuotientWordV4_eq_div_of_mulsub_overestimate
      bltu_2 bltu_1 bltu_0 hbnz hmulsub hge
  change
    fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
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

/-- n=2 quotient bridge specialized to the explicit limb variables used by the
    unified-bound wrappers. -/
theorem fullDivN2QuotientWord_eq_div_of_limbs_mulsub_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      EvmWord.val256 a0 a1 a2 a3 =
        (((fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
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
    fullDivN2QuotientWord_eq_div_of_mulsub_overestimate
      bltu_2 bltu_1 bltu_0 hbnz hmulsub hge
  change
    fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
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

/-- n=2 quotient bridge specialized to branch constructors that store
    `a`/`b` as `EvmWord`s and refer to their limbs directly. -/
theorem fullDivN2QuotientWord_eq_div_of_getLimbN_mulsub_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hmulsub :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) =
        (((fullDivN2R2 bltu_2
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat) *
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) +
        EvmWord.val256
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1))
    (hge :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) /
        EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3) ≤
        ((fullDivN2R2 bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat) :
    fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b :=
  fullDivN2QuotientWord_eq_div_of_limbs_mulsub_overestimate
    bltu_2 bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl rfl rfl
    hbnz hmulsub hge

/-- Explicit-limb n=2 four-limb division witness using the legacy
    quotient-overestimate hypothesis. -/
theorem fullDivN2_getLimbN_of_limbs_mulsub_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      EvmWord.val256 a0 a1 a2 a3 =
        (((fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  have hdivWord :=
    fullDivN2QuotientWord_eq_div_of_limbs_mulsub_overestimate
      bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hbnz hmulsub hge
  exact fullDivN2_hdivs_of_word_eq bltu_2 bltu_1 bltu_0
    a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord

/-- n=2 four-limb division witness specialized to branch constructors that
    store `a`/`b` as `EvmWord`s and refer to their limbs directly. -/
theorem fullDivN2_getLimbN_of_getLimbN_mulsub_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hmulsub :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) =
        (((fullDivN2R2 bltu_2
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat) *
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) +
        EvmWord.val256
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1))
    (hge :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) /
        EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3) ≤
        ((fullDivN2R2 bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  exact fullDivN2_getLimbN_of_limbs_mulsub_overestimate
    bltu_2 bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl rfl rfl
    hbnz hmulsub hge

end EvmAsm.Evm64
