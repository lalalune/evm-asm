/-
  EvmAsm.Evm64.DivMod.Spec.N1TrialWitnessesNormalized

  Trial-witness eliminators for normalized n=1 DIV arithmetic facts.
-/

import EvmAsm.Evm64.DivMod.Spec.N1TrialWitnesses
import EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- GetLimb-specialized normalized n=1 quotient bridge. This is the shape
    produced by the trial-witness wrappers, before projecting the quotient word
    into individual hdiv witnesses. -/
theorem fullDivN1QuotientWord_eq_div_of_getLimbN_normalized_mulsub_remainder_lt
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hrem_lt : fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
      EvmWord.div a b := by
  have hdivWordRaw :=
    fullDivN1QuotientWord_eq_div_of_normalized_mulsub_remainder_lt
      bltu_3 bltu_2 bltu_1 bltu_0
      hbnz hmulsub hrem_lt
  have hdivEq :
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
          | 3 => b.getLimbN 3) = EvmWord.div a b := by
    exact congrArg₂ (fun x y : EvmWord => EvmWord.div x y)
      (EvmWord.fromLimbs_match_getLimbN_id a)
      (EvmWord.fromLimbs_match_getLimbN_id b)
  exact hdivWordRaw.trans hdivEq

/-- Eliminate an `N1TrialWitnesses` bundle and derive all four quotient-limb
    witnesses from normalized mulsub plus normalized final-remainder facts for
    the owned branch booleans. -/
theorem N1TrialWitnesses.exists_hdivs_of_normalized_mulsub_remainder_lt
    {a b : EvmWord}
    (htrial : N1TrialWitnesses a b)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 bltu_3 bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 bltu_3 bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 bltu_3
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨bltu_3, bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    N1TrialWitnesses.exists htrial
  obtain ⟨hmulsub, hrem_lt⟩ :=
    hpath bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_getLimbN_normalized_mulsub_remainder_lt
      bltu_3 bltu_2 bltu_1 bltu_0
      hbnz hmulsub hrem_lt
  have hdivs :=
    fullDivN1_hdivs_of_word_eq bltu_3 bltu_2 bltu_1 bltu_0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord
  exact ⟨bltu_3, bltu_2, bltu_1, bltu_0,
    hbltu_3, hbltu_2, hbltu_1, hbltu_0, hdivs⟩

/-- Eliminate an `N1TrialWitnesses` bundle and derive all four quotient-limb
    witnesses from normalized mulsub plus the legacy quotient-overestimate
    fact for the owned branch booleans. -/
theorem N1TrialWitnesses.exists_hdivs_of_normalized_mulsub_overestimate
    {a b : EvmWord}
    (htrial : N1TrialWitnesses a b)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1QuotientOverestimate bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 bltu_3 bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 bltu_3 bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 bltu_3
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  refine N1TrialWitnesses.exists_hdivs_of_normalized_mulsub_remainder_lt
    htrial hbnz ?_
  intro bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  obtain ⟨hmulsub, hge⟩ :=
    hpath bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact ⟨hmulsub,
    fullDivN1NormalizedRemainderLt_of_mulsub_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hge⟩

/-- Shape-specialized n=1 hdiv witnesses from normalized mulsub plus
    normalized final-remainder facts, with the forced first branch recorded as
    `true`. -/
theorem n1_shape_hdivs_of_normalized_mulsub_remainder_lt
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1NormalizedRemainderLt true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 true bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 true bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnz hb3z hb2z hb1z hshift_nz
  obtain ⟨hmulsub, hrem_lt⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_getLimbN_normalized_mulsub_remainder_lt
      true bltu_2 bltu_1 bltu_0
      hbnz hmulsub hrem_lt
  have hdivs :=
    fullDivN1_hdivs_of_word_eq true bltu_2 bltu_1 bltu_0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord
  exact ⟨bltu_2, bltu_1, bltu_0,
    hbltu_3, hbltu_2, hbltu_1, hbltu_0, hdivs⟩

/-- Shape-specialized n=1 hdiv witnesses from normalized mulsub plus
    quotient-overestimate facts, with the forced first branch recorded as
    `true`. -/
theorem n1_shape_hdivs_of_normalized_mulsub_overestimate
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1QuotientOverestimate true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 true bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 true bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  refine n1_shape_hdivs_of_normalized_mulsub_remainder_lt
    a b hbnz hb3z hb2z hb1z hshift_nz ?_
  intro bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  obtain ⟨hmulsub, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  exact ⟨hmulsub,
    fullDivN1NormalizedRemainderLt_of_mulsub_overestimate
      true bltu_2 bltu_1 bltu_0 hbnz hmulsub hge⟩

/-- Acceptance-shaped n=1 full division limb theorem from normalized mulsub
    plus normalized final-remainder facts. -/
theorem n1_full_div_getLimbN_of_normalized_mulsub_remainder_lt
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1NormalizedRemainderLt true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_2 bltu_1 bltu_0,
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 true bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 true bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨bltu_2, bltu_1, bltu_0, _, _, _, _, hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n1_shape_hdivs_of_normalized_mulsub_remainder_lt
      a b hbnz hb3z hb2z hb1z hshift_nz hpath
  exact ⟨bltu_2, bltu_1, bltu_0, hdiv0, hdiv1, hdiv2, hdiv3⟩

/-- Acceptance-shaped n=1 full division limb theorem from normalized mulsub
    plus quotient-overestimate facts. -/
theorem n1_full_div_getLimbN_of_normalized_mulsub_overestimate
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1NormalizedMulSubEq true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1QuotientOverestimate true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_2 bltu_1 bltu_0,
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 true bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 true bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨bltu_2, bltu_1, bltu_0, _, _, _, _, hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    n1_shape_hdivs_of_normalized_mulsub_overestimate
      a b hbnz hb3z hb2z hb1z hshift_nz hpath
  exact ⟨bltu_2, bltu_1, bltu_0, hdiv0, hdiv1, hdiv2, hdiv3⟩

end EvmAsm.Evm64
