/-
  EvmAsm.Evm64.DivMod.Spec.N1ExactV4PathEvidence

  Bridges canonical N1 v4 path evidence into the selected semantic evidence
  package without adding more surface area to the large N1ExactV4 file.
-/

import EvmAsm.Evm64.DivMod.Spec.N1ExactV4
import EvmAsm.Evm64.DivMod.Spec.N1PathCallbacks

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Build the selected-path semantic evidence package from canonical limb
    inputs and reachable N1 path evidence. -/
theorem FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4_of_path_evidence_getLimbN
    (sp base : Word) (a b : EvmWord)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbltu3 : isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0))
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
          (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
          (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
        (b.getLimbN 3)).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
          (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
          (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
          (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
        (b.getLimbN 3)).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
          (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
          (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
          (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2)
          (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
        (b.getLimbN 3)).1)
    (hpath : N1AllTruePathEvidence a b)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  exact
    FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4_of_bltu_selected
      sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3 hbltu2 hbltu1 hbltu0
      (N1AllTruePathEvidence.selectedCarryFacts hpath)
      hfacts

end EvmAsm.Evm64
