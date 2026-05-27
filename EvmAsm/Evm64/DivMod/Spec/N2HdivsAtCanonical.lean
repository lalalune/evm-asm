/-
  EvmAsm.Evm64.DivMod.Spec.N2HdivsAtCanonical

  One-shot composition: pointed canonical-bltu evidence + n=2 shape facts
  to the hdiv equations at `n2V4CanonicalBltu{2,1,0}`.

  Internally pipelines `FullDivN2SelectedQuotientHdivs.of_canonical`
  (composing `N2CallableSelectedShapeEvidence.of_canonical` with the
  selected-quotient-hdiv `.of_shape_evidence` from `N2SelectedQuotientHdivsCanonical`)
  with `FullDivN2SelectedQuotientHdivs.exists_canonical` from
  `N2SelectedQuotientHdivsExistsCanonical`.

  Stacked on PR #6957 (which adds `exists_canonical`).
-/

import EvmAsm.Evm64.DivMod.Spec.N2SelectedQuotientHdivsCanonical
import EvmAsm.Evm64.DivMod.Spec.N2SelectedQuotientHdivsExistsCanonical

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N2 hdiv equations at the canonical bltu triple, derived from pointed
    canonical-bltu evidence and the n=2 divisor shape. -/
theorem n2HdivsAtCanonical_of_shape
    {a b : EvmWord}
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
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
    fullDivN2QuotientWordV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN2R0V4 (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN2R1V4 (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN2R2V4 (n2V4CanonicalBltu2 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) :=
  FullDivN2SelectedQuotientHdivs.exists_canonical
    (FullDivN2SelectedQuotientHdivs.of_canonical hb3z hb2z hb1nz hcarry harith)

end EvmAsm.Evm64
