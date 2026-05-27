/-
  EvmAsm.Evm64.DivMod.Spec.N2CanonicalPointedEvidence

  Single named abbreviation for the canonical pointed evidence used by the
  N2 v4 selected callable route. Bundles the `selectedCarry` and
  `mulsub ∧ overestimate` predicates at `n2V4CanonicalBltu{2,1,0}`.

  Pairs with `N2CallableSelectedShapeEvidence` via `.of_canonical` (reverse,
  merged in #6945) and `.selectedCarry_canonical / .arithmetic_canonical`
  (forward, merged in #6954).
-/

import EvmAsm.Evm64.DivMod.Spec.N2CallableSelectedShapeEvidenceCanonicalIff

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Canonical pointed evidence for the N2 v4 selected callable route. -/
abbrev N2CanonicalPointedEvidence (a b : EvmWord) : Prop :=
  fullDivN2SelectedCarryV4
    (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
  (fullDivN2MulSubEqV4
      (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
    fullDivN2QuotientOverestimateV4
      (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))

/-- Pack pointed-canonical proofs into the bundled abbreviation. -/
theorem N2CanonicalPointedEvidence.of_parts {a b : EvmWord}
    (hcarry : fullDivN2SelectedCarryV4
      (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : fullDivN2MulSubEqV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN2QuotientOverestimateV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    N2CanonicalPointedEvidence a b :=
  ⟨hcarry, harith⟩

/-- Extract the pointed `selectedCarry` proof from the bundled abbreviation. -/
theorem N2CanonicalPointedEvidence.selectedCarry {a b : EvmWord}
    (h : N2CanonicalPointedEvidence a b) :
    fullDivN2SelectedCarryV4
      (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  h.1

/-- Extract the pointed arithmetic conjunction from the bundled abbreviation. -/
theorem N2CanonicalPointedEvidence.arithmetic {a b : EvmWord}
    (h : N2CanonicalPointedEvidence a b) :
    fullDivN2MulSubEqV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN2QuotientOverestimateV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  h.2

/-- Canonical pointed evidence implies `N2CallableSelectedShapeEvidence`. -/
theorem N2CanonicalPointedEvidence.toCallableEvidence {a b : EvmWord}
    (h : N2CanonicalPointedEvidence a b) :
    N2CallableSelectedShapeEvidence a b :=
  N2CallableSelectedShapeEvidence.of_canonical h.1 h.2

/-- `N2CallableSelectedShapeEvidence` implies canonical pointed evidence. -/
theorem N2CanonicalPointedEvidence.ofCallableEvidence {a b : EvmWord}
    (h : N2CallableSelectedShapeEvidence a b) :
    N2CanonicalPointedEvidence a b :=
  ⟨N2CallableSelectedShapeEvidence.selectedCarry_canonical h,
   N2CallableSelectedShapeEvidence.arithmetic_canonical h⟩

/-- The canonical pointed evidence is logically equivalent to the universal
    callback bundle. -/
theorem N2CanonicalPointedEvidence_iff_callableEvidence {a b : EvmWord} :
    N2CanonicalPointedEvidence a b ↔ N2CallableSelectedShapeEvidence a b :=
  ⟨N2CanonicalPointedEvidence.toCallableEvidence,
   N2CanonicalPointedEvidence.ofCallableEvidence⟩

end EvmAsm.Evm64
