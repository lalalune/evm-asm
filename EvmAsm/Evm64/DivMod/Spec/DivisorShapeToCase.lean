/-
  EvmAsm.Evm64.DivMod.Spec.DivisorShapeToCase

  Reverse projections: each `NkShapeIs` predicate implies the corresponding
  `DivisorLimbCase` constructor. Pairs with `DivisorLimbCaseToShape` (forward
  direction) so callers can move between the inductive and named-predicate
  representations in either direction.
-/

import EvmAsm.Evm64.DivMod.Spec.UnifiedDivisorCases
import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- `N1ShapeIs` implies `DivisorLimbCase.n1`. -/
theorem N1ShapeIs.toDivisorLimbCase {b : EvmWord} (h : N1ShapeIs b) :
    DivisorLimbCase b := by
  refine DivisorLimbCase.n1 h.1 ?_ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  exact (EvmWord.ne_zero_iff_getLimbN_or).mp h.1

/-- `N2ShapeIs` implies `DivisorLimbCase.n2`. -/
theorem N2ShapeIs.toDivisorLimbCase {b : EvmWord} (h : N2ShapeIs b) :
    DivisorLimbCase b := by
  refine DivisorLimbCase.n2 h.1 ?_ h.2.1 h.2.2.1 h.2.2.2
  exact (EvmWord.ne_zero_iff_getLimbN_or).mp h.1

/-- `N3ShapeIs` implies `DivisorLimbCase.n3`. -/
theorem N3ShapeIs.toDivisorLimbCase {b : EvmWord} (h : N3ShapeIs b) :
    DivisorLimbCase b := by
  refine DivisorLimbCase.n3 h.1 ?_ h.2.1 h.2.2
  exact (EvmWord.ne_zero_iff_getLimbN_or).mp h.1

/-- `N4ShapeIs` implies `DivisorLimbCase.n4`. -/
theorem N4ShapeIs.toDivisorLimbCase {b : EvmWord} (h : N4ShapeIs b) :
    DivisorLimbCase b := by
  refine DivisorLimbCase.n4 h.1 ?_ h.2
  exact (EvmWord.ne_zero_iff_getLimbN_or).mp h.1

end EvmAsm.Evm64
