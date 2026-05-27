/-
  EvmAsm.Evm64.DivMod.Spec.N2SelectedQuotientHdivs

  Private quotient-word and hdiv package for the selected N2 DIV v4 route.
-/

import EvmAsm.Evm64.DivMod.Spec.N2CallableSelectedShapeEvidence

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Selected N2 quotient package for the final public wrapper.

    The package names the branch witnesses, quotient-word equality, and four
    quotient-limb equalities produced from selected/reachable N2 evidence. -/
inductive FullDivN2SelectedQuotientHdivs (a b : EvmWord) : Prop where
  | mk (bltu2 bltu1 bltu0 : Bool)
      (hbltu2 : isTrialN2V4_j2 bltu2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hbltu1 : isTrialN2V4_j1 bltu2 bltu1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hbltu0 : isTrialN2V4_j0 bltu2 bltu1 bltu0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hdivWord : fullDivN2QuotientWordV4 bltu2 bltu1 bltu0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b)
      (hdiv0 : (EvmWord.div a b).getLimbN 0 =
        (fullDivN2R0V4 bltu2 bltu1 bltu0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
      (hdiv1 : (EvmWord.div a b).getLimbN 1 =
        (fullDivN2R1V4 bltu2 bltu1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
      (hdiv2 : (EvmWord.div a b).getLimbN 2 =
        (fullDivN2R2V4 bltu2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
      (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word))

/-- Build the selected N2 quotient/hdiv package from the bundled selected
    evidence surface used by the final public route. -/
theorem FullDivN2SelectedQuotientHdivs.of_evidence
    {a b : EvmWord}
    (hbnz : b ≠ 0)
    (hevidence : N2CallableSelectedShapeEvidence a b) :
    FullDivN2SelectedQuotientHdivs a b := by
  obtain ⟨bltu2, bltu1, bltu0, hbltu2, hbltu1, hbltu0, hdivWord⟩ :=
    N2V4TrialWitnesses.exists_quotient_word_of_selected_path_conditions_ne_zero
      (n2V4TrialWitnesses_of_getLimbN a b)
      hbnz
      (N2CallableSelectedShapeEvidence.selectedCarry hevidence)
      (N2CallableSelectedShapeEvidence.arithmetic hevidence)
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullDivN2V4_hdivs_of_word_eq bltu2 bltu1 bltu0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord
  exact ⟨bltu2, bltu1, bltu0, hbltu2, hbltu1, hbltu0,
    hdivWord, hdiv0, hdiv1, hdiv2, hdiv3⟩

end EvmAsm.Evm64
