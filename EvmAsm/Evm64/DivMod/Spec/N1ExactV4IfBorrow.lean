/-
  EvmAsm.Evm64.DivMod.Spec.N1ExactV4IfBorrow

  Selected-if-borrow evidence packages for exact N1 DIV v4 stack specs.
-/

import EvmAsm.Evm64.DivMod.Spec.N1ExactV4

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Selected-if-borrow path evidence plus semantic facts for the canonical
    full-DIV N1 v4 call/max/max/max route. This is the conditional-carry
    counterpart of `FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4`. -/
abbrev FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Prop :=
  fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    a0 a1 a2 a3 b0 b1 b2 b3
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal ∧
  FullDivN1CallMaxmaxmaxSemanticFactsV4 a0 a1 a2 a3 b0 b1 b2 b3

theorem FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_selectedInput
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal :=
  hevidence.1

theorem FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_semanticFacts
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    FullDivN1CallMaxmaxmaxSemanticFactsV4 a0 a1 a2 a3 b0 b1 b2 b3 :=
  hevidence.2

end EvmAsm.Evm64
