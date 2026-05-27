/-
  EvmAsm.Evm64.DivMod.Spec.DivisorBzeroExcludesShape

  Each `NkShapeIs` predicate excludes `b = 0`. Trivial corollary of
  `NkShapeIs.ne_zero` (PR #6987).
-/

import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNeZero

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem bzero_not_N1ShapeIs {b : EvmWord} (hbz : b = 0) : ¬ N1ShapeIs b :=
  fun h => h.ne_zero hbz

theorem bzero_not_N2ShapeIs {b : EvmWord} (hbz : b = 0) : ¬ N2ShapeIs b :=
  fun h => h.ne_zero hbz

theorem bzero_not_N3ShapeIs {b : EvmWord} (hbz : b = 0) : ¬ N3ShapeIs b :=
  fun h => h.ne_zero hbz

theorem bzero_not_N4ShapeIs {b : EvmWord} (hbz : b = 0) : ¬ N4ShapeIs b :=
  fun h => h.ne_zero hbz

end EvmAsm.Evm64
