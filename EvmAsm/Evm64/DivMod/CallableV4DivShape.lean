import EvmAsm.Evm64.DivMod.CallableV4DivSelected
import EvmAsm.Evm64.DivMod.CallableV4DivConcreteSelected

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Private-style evidence bundle for the N1 selected-if-borrow callable shape
    route. This keeps branch facts, selected carry/path facts, and semantic
    arithmetic facts together while the final public wrapper is still being
    assembled. -/
abbrev N1CallableSelectedIfBorrowShapeEvidence (a b : EvmWord) : Prop :=
  isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
  ¬BitVec.ult
    (loopN1CallMaxmaxmaxR3
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
      0 0 0).2.1
    (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)).1 ∧
  ¬BitVec.ult
    (loopN1CallMaxmaxmaxR2
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
      0 0 0
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
    (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)).1 ∧
  ¬BitVec.ult
    (loopN1CallMaxmaxmaxR1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
      0 0 0
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
    (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)).1 ∧
  N1SelectedIfBorrowPathEvidence a b ∧
  FullDivN1CallMaxmaxmaxSemanticFactsV4
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

theorem N1CallableSelectedIfBorrowShapeEvidence.ofSelectedIfBorrowSemanticEvidence
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a b : EvmWord)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hpath : N1SelectedIfBorrowPathEvidence a b)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    N1CallableSelectedIfBorrowShapeEvidence a b := by
  obtain ⟨hbltu3, hbltu2, hbltu1, hbltu0⟩ :=
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_branchFacts
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence
  exact ⟨hbltu3, hbltu2, hbltu1, hbltu0, hpath,
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_semanticFacts
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence⟩


/-- Project the selected branch facts from the bundled N1 callable evidence. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.branchFacts {a b : EvmWord}
    (hevidence : N1CallableSelectedIfBorrowShapeEvidence a b) :
    isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1 := by
  rcases hevidence with ⟨hbltu3, hbltu2, hbltu1, hbltu0, _hpath, _hfacts⟩
  exact ⟨hbltu3, hbltu2, hbltu1, hbltu0⟩

/-- Project selected reachable path evidence from the bundled N1 callable
    evidence. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.selectedPath {a b : EvmWord}
    (hevidence : N1CallableSelectedIfBorrowShapeEvidence a b) :
    N1SelectedIfBorrowPathEvidence a b := by
  exact hevidence.2.2.2.2.1

/-- Project selected semantic facts from the bundled N1 callable evidence. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.semanticFacts {a b : EvmWord}
    (hevidence : N1CallableSelectedIfBorrowShapeEvidence a b) :
    FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  exact hevidence.2.2.2.2.2

/-- Rebuild the canonical selected-if-borrow semantic evidence package from
    the bundled N1 callable shape evidence. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.selectedIfBorrowSemanticEvidence
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a b : EvmWord)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hevidence : N1CallableSelectedIfBorrowShapeEvidence a b) :
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  obtain ⟨hbltu3, hbltu2, hbltu1, hbltu0⟩ :=
    N1CallableSelectedIfBorrowShapeEvidence.branchFacts hevidence
  exact FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_of_bltu_selected
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    hbltu3 hbltu2 hbltu1 hbltu0
    (N1SelectedIfBorrowPathEvidence.selectedCarryIfBorrowFacts
      (N1CallableSelectedIfBorrowShapeEvidence.selectedPath hevidence))
    (N1CallableSelectedIfBorrowShapeEvidence.semanticFacts hevidence)

theorem N1CallableSelectedIfBorrowShapeEvidence.ofAllTruePathSelectedIfBorrowSemanticEvidence
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a b : EvmWord)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hpath : N1AllTruePathEvidence a b)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    N1CallableSelectedIfBorrowShapeEvidence a b :=
  N1CallableSelectedIfBorrowShapeEvidence.ofSelectedIfBorrowSemanticEvidence
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    a b q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    (N1SelectedIfBorrowPathEvidence.ofAllTruePathEvidence hpath) hevidence

/-- N1 DIV v4 callable wrapper over the selected-if-borrow path, using the
    word-level nonzero and n=1 shape hypotheses instead of a limb-or premise. -/
theorem evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_shape_selectedIfBorrow
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0))
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1AllTruePathEvidence a b)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  exact
    evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_selected_if_borrow_selected_path_semantic_facts_limbNz_memOwn
      sp base a b
      v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz)
      hb3z hb2z hb1z hshift_nz halign
      hbltu3 hbltu2 hbltu1 hbltu0
      (N1SelectedIfBorrowPathEvidence.ofAllTruePathEvidence hpath) hfacts

/-- N1 DIV v4 callable wrapper over the selected-if-borrow path, using
    selected path evidence directly at the shape-level boundary. -/
theorem evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_shape_selectedIfBorrowPath
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0))
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
        0 0 0
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
        (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1)
    (hpath : N1SelectedIfBorrowPathEvidence a b)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  exact
    evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_selected_if_borrow_selected_path_semantic_facts_limbNz_memOwn
      sp base a b
      v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz)
      hb3z hb2z hb1z hshift_nz halign
      hbltu3 hbltu2 hbltu1 hbltu0 hpath hfacts

/-- N1 selected-if-borrow shape wrapper consuming a single bundled evidence
    package instead of exposing branch and selected-path facts separately. -/
theorem evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_shape_selectedIfBorrowEvidence
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hevidence : N1CallableSelectedIfBorrowShapeEvidence a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  obtain ⟨hbltu3, hbltu2, hbltu1, hbltu0⟩ :=
    N1CallableSelectedIfBorrowShapeEvidence.branchFacts hevidence
  exact evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_shape_selectedIfBorrowPath
    sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz halign
    hbltu3 hbltu2 hbltu1 hbltu0
    (N1CallableSelectedIfBorrowShapeEvidence.selectedPath hevidence)
    (N1CallableSelectedIfBorrowShapeEvidence.semanticFacts hevidence)

/-- N1 selected-if-borrow shape wrapper consuming the existing selected
    semantic-evidence package plus selected path evidence, deriving the
    callable evidence bundle internally. -/
theorem evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_shape_selectedIfBorrowSemanticEvidence
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hpath : N1SelectedIfBorrowPathEvidence a b)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  exact evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_shape_selectedIfBorrowEvidence
    sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz halign
    (N1CallableSelectedIfBorrowShapeEvidence.ofSelectedIfBorrowSemanticEvidence
      sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      a b
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      hpath hevidence)

/-- N1 selected-if-borrow shape wrapper for callers that still carry the
    all-true path package, while deriving the selected callable evidence from
    the selected semantic package internally.

    This still requires selected-if-borrow semantic evidence: all-true
    remainder-bound witnesses select the all-call route, and do not provide the
    `¬ BitVec.ult ...` max-branch facts needed by the call/max/max/max
    selected-if-borrow path. -/
theorem evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_shape_allTruePathSelectedIfBorrowSemanticEvidence
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hpath : N1AllTruePathEvidence a b)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  exact evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_shape_selectedIfBorrowSemanticEvidence
    sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz halign
    (N1SelectedIfBorrowPathEvidence.ofAllTruePathEvidence hpath) hevidence

/-- Bundled selected/reachable evidence for the N2 callable shape route.

    This keeps the selected carry and arithmetic callbacks together, avoiding
    any public dependency on the old universal `Carry2NzAll` package. -/
abbrev N2CallableSelectedShapeEvidence (a b : EvmWord) : Prop :=
  (∀ bltu_2 bltu_1 bltu_0,
    isTrialN2V4_j2 bltu_2
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    isTrialN2V4_j1 bltu_2 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    fullDivN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) ∧
  (∀ bltu_2 bltu_1 bltu_0,
    isTrialN2V4_j2 bltu_2
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    isTrialN2V4_j1 bltu_2 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))

theorem N2CallableSelectedShapeEvidence.selectedCarry {a b : EvmWord}
    (hevidence : N2CallableSelectedShapeEvidence a b) :
    ∀ bltu_2 bltu_1 bltu_0,
      isTrialN2V4_j2 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j1 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hevidence.1

theorem N2CallableSelectedShapeEvidence.arithmetic {a b : EvmWord}
    (hevidence : N2CallableSelectedShapeEvidence a b) :
    ∀ bltu_2 bltu_1 bltu_0,
      isTrialN2V4_j2 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j1 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hevidence.2

/-- N2 DIV v4 callable wrapper deriving divisor nonzero from the n=2 shape
    while consuming only selected carry evidence for the actual path. -/
theorem evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_shape_selectedCarry
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hcarry : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN2V4_j2 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j1 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_2 bltu_1 bltu_0,
      isTrialN2V4_j2 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j1 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  exact evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_limbNz_selectedCarry
    sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    (n2_limb_or_ne_zero_of_limb1_ne_zero hb1nz)
    hb3z hb2z hb1nz hshift_nz halign hcarry harith

/-- Bundled selected/reachable evidence for the N3 callable shape route.

    This keeps the selected carry and arithmetic callbacks together, avoiding
    any public dependency on the old universal `Carry2NzAll` package. -/
abbrev N3CallableSelectedShapeEvidence (a b : EvmWord) : Prop :=
  (∀ bltu_1 bltu_0,
    isTrialN3V4_j1 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    isTrialN3V4_j0 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    fullDivN3SelectedCarryV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) ∧
  (∀ bltu_1 bltu_0,
    isTrialN3V4_j1 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    isTrialN3V4_j0 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    fullDivN3MulSubEqV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientOverestimateV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))

theorem N3CallableSelectedShapeEvidence.selectedCarry {a b : EvmWord}
    (hevidence : N3CallableSelectedShapeEvidence a b) :
    ∀ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN3SelectedCarryV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hevidence.1

theorem N3CallableSelectedShapeEvidence.arithmetic {a b : EvmWord}
    (hevidence : N3CallableSelectedShapeEvidence a b) :
    ∀ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN3MulSubEqV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN3QuotientOverestimateV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hevidence.2

/-- N2 DIV v4 callable wrapper over bundled selected/reachable shape evidence. -/
theorem evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_shape_selectedEvidence
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : N2CallableSelectedShapeEvidence a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) :=
  evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_shape_selectedCarry
    sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hb3z hb2z hb1nz hshift_nz halign
    (N2CallableSelectedShapeEvidence.selectedCarry hevidence)
    (N2CallableSelectedShapeEvidence.arithmetic hevidence)


/-- N3 DIV v4 callable wrapper deriving divisor nonzero from the n=3 shape
    while consuming only selected carry evidence for the actual path. -/
theorem evm_div_callable_v4_n3_stack_pre_to_callable_post_scratch_shape_selectedCarry
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hcarry : ∀ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN3SelectedCarryV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN3MulSubEqV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN3QuotientOverestimateV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) := by
  exact evm_div_callable_v4_n3_stack_pre_to_callable_post_scratch_limbNz_selectedCarry
    sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    (n3_limb_or_ne_zero_of_limb2_ne_zero hb2nz)
    hb3z hb2nz hshift_nz halign hcarry harith

/-- N3 DIV v4 callable wrapper over bundled selected/reachable shape evidence. -/
theorem evm_div_callable_v4_n3_stack_pre_to_callable_post_scratch_shape_selectedEvidence
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hevidence : N3CallableSelectedShapeEvidence a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) :=
  evm_div_callable_v4_n3_stack_pre_to_callable_post_scratch_shape_selectedCarry
    sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hb3z hb2nz hshift_nz halign
    (N3CallableSelectedShapeEvidence.selectedCarry hevidence)
    (N3CallableSelectedShapeEvidence.arithmetic hevidence)

end EvmAsm.Evm64
