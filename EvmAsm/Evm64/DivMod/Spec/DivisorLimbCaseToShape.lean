/-
  EvmAsm.Evm64.DivMod.Spec.DivisorLimbCaseToShape

  Projections from `DivisorLimbCase` constructors to the named `NkShapeIs`
  predicates. Each non-bzero constructor of `DivisorLimbCase` carries the
  facts needed to assemble the corresponding `NkShapeIs`.
-/

import EvmAsm.Evm64.DivMod.Spec.UnifiedDivisorCases
import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- A `DivisorLimbCase.n1` constructor implies `N1ShapeIs`. -/
theorem DivisorLimbCase.n1_implies_N1ShapeIs
    {b : EvmWord}
    (hbnz : b ≠ 0)
    (_hbnzOr : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0) (hb0nz : b.getLimbN 0 ≠ 0) :
    N1ShapeIs b :=
  ⟨hbnz, hb3z, hb2z, hb1z, hb0nz⟩

/-- A `DivisorLimbCase.n2` constructor implies `N2ShapeIs`. -/
theorem DivisorLimbCase.n2_implies_N2ShapeIs
    {b : EvmWord}
    (hbnz : b ≠ 0)
    (_hbnzOr : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0) :
    N2ShapeIs b :=
  ⟨hbnz, hb3z, hb2z, hb1nz⟩

/-- A `DivisorLimbCase.n3` constructor implies `N3ShapeIs`. -/
theorem DivisorLimbCase.n3_implies_N3ShapeIs
    {b : EvmWord}
    (hbnz : b ≠ 0)
    (_hbnzOr : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0) :
    N3ShapeIs b :=
  ⟨hbnz, hb3z, hb2nz⟩

/-- A `DivisorLimbCase.n4` constructor implies `N4ShapeIs`. -/
theorem DivisorLimbCase.n4_implies_N4ShapeIs
    {b : EvmWord}
    (hbnz : b ≠ 0)
    (_hbnzOr : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0) :
    N4ShapeIs b :=
  ⟨hbnz, hb3nz⟩

end EvmAsm.Evm64
