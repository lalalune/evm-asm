/-
  EvmAsm.Evm64.DivMod.Spec.N2CanonicalTrialWitnessAll

  Small ergonomic utility: combine the three canonical-bltu trial-witness
  facts (`isTrialN2V4_j{2,1,0}_n2V4CanonicalBltu*`) into a single conjunction.
  Downstream callers needing all three obligations at once can pull them
  from this packed lemma instead of stitching them together at every call
  site.
-/

import EvmAsm.Evm64.DivMod.Spec.N2CallableSelectedShapeEvidenceCanonical

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- All three canonical-bltu trial-witness predicates for n=2 hold
    simultaneously at `n2V4CanonicalBltu{2,1,0}`. -/
theorem isTrialN2V4_n2V4CanonicalBltu_all (a b : EvmWord) :
    isTrialN2V4_j2 (n2V4CanonicalBltu2 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
    isTrialN2V4_j1 (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
    isTrialN2V4_j0 (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b)
        (n2V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  ⟨isTrialN2V4_j2_n2V4CanonicalBltu2 a b,
   isTrialN2V4_j1_n2V4CanonicalBltu1 a b,
   isTrialN2V4_j0_n2V4CanonicalBltu0 a b⟩

end EvmAsm.Evm64
