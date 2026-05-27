/-
  EvmAsm.Evm64.DivMod.Spec.N3CanonicalBltuUnique

  Uniqueness lemmas for the canonical N3 bltu values. Mirrors
  `N2CanonicalBltuUnique` for the n=3 lane.
-/

import EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidenceCanonical

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Any `bltu_1` satisfying `isTrialN3V4_j1` at `(a, b)` equals the
    canonical value. -/
theorem n3V4CanonicalBltu1_unique {a b : EvmWord} {bltu_1 : Bool}
    (h : isTrialN3V4_j1 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    bltu_1 = n3V4CanonicalBltu1 a b := h

/-- Any `bltu_0` satisfying `isTrialN3V4_j0` at `(a, b)` with the canonical
    `bltu_1` equals the canonical `bltu_0`. -/
theorem n3V4CanonicalBltu0_unique {a b : EvmWord} {bltu_0 : Bool}
    (h : isTrialN3V4_j0 (n3V4CanonicalBltu1 a b) bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    bltu_0 = n3V4CanonicalBltu0 a b := h

end EvmAsm.Evm64
