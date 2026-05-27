/-
  EvmAsm.Evm64.DivMod.Spec.DivisorShapeDecidable

  Explicit `Decidable` instances for the named `NkShapeIs` predicates so
  downstream code can use `decide` / `by_cases` on them directly without
  manual case analysis.
-/

import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

instance N1ShapeIs.decidable (b : EvmWord) : Decidable (N1ShapeIs b) := by
  unfold N1ShapeIs; exact inferInstance

instance N2ShapeIs.decidable (b : EvmWord) : Decidable (N2ShapeIs b) := by
  unfold N2ShapeIs; exact inferInstance

instance N3ShapeIs.decidable (b : EvmWord) : Decidable (N3ShapeIs b) := by
  unfold N3ShapeIs; exact inferInstance

instance N4ShapeIs.decidable (b : EvmWord) : Decidable (N4ShapeIs b) := by
  unfold N4ShapeIs; exact inferInstance

end EvmAsm.Evm64
