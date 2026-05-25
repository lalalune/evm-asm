/-
  EvmAsm.Evm64.DivMod.Spec.N1TrialWitnessesNormalized

  Trial-witness eliminators for normalized n=1 DIV arithmetic facts.
-/

import EvmAsm.Evm64.DivMod.Spec.N1TrialWitnesses
import EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

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
  have hdivs :=
    fullDivN1_getLimbN_of_limbs_normalized_mulsub_remainder_lt
      bltu_3 bltu_2 bltu_1 bltu_0
      (a := a) (b := b)
      (a0 := a.getLimbN 0) (a1 := a.getLimbN 1)
      (a2 := a.getLimbN 2) (a3 := a.getLimbN 3)
      (b0 := b.getLimbN 0) (b1 := b.getLimbN 1)
      (b2 := b.getLimbN 2) (b3 := b.getLimbN 3)
      rfl rfl rfl rfl rfl rfl rfl rfl hbnz hmulsub hrem_lt
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

end EvmAsm.Evm64
