/-
  EvmAsm.Evm64.DivMod.Spec.DivisorFullDomainShapeNamed

  `divisor_full_domain_shape` restated using the named `NkShapeIs` predicates
  from `DivisorShapeNamed`. Identical content, cleaner naming for downstream
  consumption.
-/

import EvmAsm.Evm64.DivMod.Spec.DivisorFullDomainShape
import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Restatement of `divisor_full_domain_shape` using `NkShapeIs`. -/
theorem divisor_full_domain_shape_named (b : EvmWord) :
    b = 0 ∨ N1ShapeIs b ∨ N2ShapeIs b ∨ N3ShapeIs b ∨ N4ShapeIs b :=
  divisor_full_domain_shape b

end EvmAsm.Evm64
