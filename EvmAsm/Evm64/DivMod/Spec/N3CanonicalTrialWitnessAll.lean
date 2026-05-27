/-
  EvmAsm.Evm64.DivMod.Spec.N3CanonicalTrialWitnessAll

  Small ergonomic utility: combine the two canonical-bltu trial-witness
  facts (`isTrialN3V4_j{1,0}_n3V4CanonicalBltu*`) into a single conjunction.
  Mirrors `N2CanonicalTrialWitnessAll` for the n=3 lane.
-/

import EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidenceCanonical

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Both canonical-bltu trial-witness predicates for n=3 hold
    simultaneously at `n3V4CanonicalBltu{1,0}`. -/
theorem isTrialN3V4_n3V4CanonicalBltu_all (a b : EvmWord) :
    isTrialN3V4_j1 (n3V4CanonicalBltu1 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
    isTrialN3V4_j0 (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  ⟨isTrialN3V4_j1_n3V4CanonicalBltu1 a b,
   isTrialN3V4_j0_n3V4CanonicalBltu0 a b⟩

end EvmAsm.Evm64
