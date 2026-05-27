/-
  EvmAsm.Evm64.DivMod.Spec.N3HdivsAtCanonical

  One-shot composition: pointed canonical-bltu evidence + n=3 shape facts
  to the hdiv equations at `n3V4CanonicalBltu{1,0}`.

  Internally pipelines `FullDivN3SelectedQuotientHdivs.of_canonical`
  (from `N3SelectedQuotientHdivsCanonical`) with `.exists_canonical`
  (from `N3SelectedQuotientHdivsExistsCanonical`).

  Mirrors `N2HdivsAtCanonical` for the n=3 lane.
-/

import EvmAsm.Evm64.DivMod.Spec.N3SelectedQuotientHdivsCanonical
import EvmAsm.Evm64.DivMod.Spec.N3SelectedQuotientHdivsExistsCanonical

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N3 hdiv equations at the canonical bltu pair, derived from pointed
    canonical-bltu evidence and the n=3 divisor shape. -/
theorem n3HdivsAtCanonical_of_shape
    {a b : EvmWord}
    (hb3z : b.getLimbN 3 = 0)
    (hb2nz : b.getLimbN 2 ≠ 0)
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
    fullDivN3QuotientWordV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 (n3V4CanonicalBltu1 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) :=
  FullDivN3SelectedQuotientHdivs.exists_canonical
    (FullDivN3SelectedQuotientHdivs.of_canonical hb3z hb2nz hcarry harith)

end EvmAsm.Evm64
