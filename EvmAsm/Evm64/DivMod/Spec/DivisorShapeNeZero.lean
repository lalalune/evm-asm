/-
  EvmAsm.Evm64.DivMod.Spec.DivisorShapeNeZero

  Trivial projections: each `NkShapeIs` predicate implies `b ≠ 0`. Useful
  for downstream code that has only the shape predicate and needs the
  nonzero fact for lower-level wrappers.
-/

import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem N1ShapeIs.ne_zero {b : EvmWord} (h : N1ShapeIs b) : b ≠ 0 := h.1

theorem N2ShapeIs.ne_zero {b : EvmWord} (h : N2ShapeIs b) : b ≠ 0 := h.1

theorem N3ShapeIs.ne_zero {b : EvmWord} (h : N3ShapeIs b) : b ≠ 0 := h.1

theorem N4ShapeIs.ne_zero {b : EvmWord} (h : N4ShapeIs b) : b ≠ 0 := h.1

end EvmAsm.Evm64
