/-
  EvmAsm.Evm64.DivMod.Spec.N3CanonicalPointedEvidence

  Single named abbreviation for the canonical pointed evidence used by the
  N3 v4 selected callable route. Mirrors `N2CanonicalPointedEvidence` for
  the n=3 lane.
-/

import EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidenceCanonicalIff

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Canonical pointed evidence for the N3 v4 selected callable route. -/
abbrev N3CanonicalPointedEvidence (a b : EvmWord) : Prop :=
  fullDivN3SelectedCarryV4
    (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
  (fullDivN3MulSubEqV4
      (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
    fullDivN3QuotientOverestimateV4
      (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))

theorem N3CanonicalPointedEvidence.of_parts {a b : EvmWord}
    (hcarry : fullDivN3SelectedCarryV4
      (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : fullDivN3MulSubEqV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientOverestimateV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    N3CanonicalPointedEvidence a b :=
  ⟨hcarry, harith⟩

theorem N3CanonicalPointedEvidence.selectedCarry {a b : EvmWord}
    (h : N3CanonicalPointedEvidence a b) :
    fullDivN3SelectedCarryV4
      (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  h.1

theorem N3CanonicalPointedEvidence.arithmetic {a b : EvmWord}
    (h : N3CanonicalPointedEvidence a b) :
    fullDivN3MulSubEqV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientOverestimateV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  h.2

theorem N3CanonicalPointedEvidence.toCallableEvidence {a b : EvmWord}
    (h : N3CanonicalPointedEvidence a b) :
    N3CallableSelectedShapeEvidence a b :=
  N3CallableSelectedShapeEvidence.of_canonical h.1 h.2

theorem N3CanonicalPointedEvidence.ofCallableEvidence {a b : EvmWord}
    (h : N3CallableSelectedShapeEvidence a b) :
    N3CanonicalPointedEvidence a b :=
  ⟨N3CallableSelectedShapeEvidence.selectedCarry_canonical h,
   N3CallableSelectedShapeEvidence.arithmetic_canonical h⟩

theorem N3CanonicalPointedEvidence_iff_callableEvidence {a b : EvmWord} :
    N3CanonicalPointedEvidence a b ↔ N3CallableSelectedShapeEvidence a b :=
  ⟨N3CanonicalPointedEvidence.toCallableEvidence,
   N3CanonicalPointedEvidence.ofCallableEvidence⟩

end EvmAsm.Evm64
