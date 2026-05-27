/-
  EvmAsm.Evm64.DivMod.Spec.N2CanonicalBltuUnique

  Uniqueness lemmas: any `bltu_X` satisfying `isTrialN2V4_jX` at `(a, b)`
  must equal `n2V4CanonicalBltuX a b`. Follows directly from the
  trial-witness predicates being equalities, but exposed as named theorems
  for downstream callers (e.g. via `rw`).
-/

import EvmAsm.Evm64.DivMod.Spec.N2CallableSelectedShapeEvidenceCanonical

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Any `bltu_2` satisfying `isTrialN2V4_j2` at `(a, b)` equals the
    canonical value. -/
theorem n2V4CanonicalBltu2_unique {a b : EvmWord} {bltu_2 : Bool}
    (h : isTrialN2V4_j2 bltu_2
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    bltu_2 = n2V4CanonicalBltu2 a b := h

/-- Any `bltu_1` satisfying `isTrialN2V4_j1` at `(a, b)` with the canonical
    `bltu_2` equals the canonical `bltu_1`. -/
theorem n2V4CanonicalBltu1_unique {a b : EvmWord} {bltu_1 : Bool}
    (h : isTrialN2V4_j1 (n2V4CanonicalBltu2 a b) bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    bltu_1 = n2V4CanonicalBltu1 a b := h

/-- Any `bltu_0` satisfying `isTrialN2V4_j0` at `(a, b)` with the canonical
    `bltu_2` and `bltu_1` equals the canonical `bltu_0`. -/
theorem n2V4CanonicalBltu0_unique {a b : EvmWord} {bltu_0 : Bool}
    (h : isTrialN2V4_j0 (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    bltu_0 = n2V4CanonicalBltu0 a b := h

end EvmAsm.Evm64
