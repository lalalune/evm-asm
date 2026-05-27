/-
  EvmAsm.Evm64.DivMod.Spec.N3HdivsAtCanonicalPointedEvidence

  Bundled variant of `n3HdivsAtCanonical_of_shape` (PR #6959) that takes
  the `N3CanonicalPointedEvidence` abbreviation (PR #6964) directly.

  Mirrors `N2HdivsAtCanonicalPointedEvidence` for the n=3 lane.
-/

import EvmAsm.Evm64.DivMod.Spec.N3HdivsAtCanonical
import EvmAsm.Evm64.DivMod.Spec.N3CanonicalPointedEvidence

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N3 hdiv equations at the canonical bltu pair, derived from bundled
    `N3CanonicalPointedEvidence` and the n=3 divisor shape. -/
theorem n3HdivsAtCanonical_of_shape_pointedEvidence
    {a b : EvmWord}
    (hb3z : b.getLimbN 3 = 0)
    (hb2nz : b.getLimbN 2 ≠ 0)
    (hevidence : N3CanonicalPointedEvidence a b) :
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
  n3HdivsAtCanonical_of_shape hb3z hb2nz
    (N3CanonicalPointedEvidence.selectedCarry hevidence)
    (N3CanonicalPointedEvidence.arithmetic hevidence)

end EvmAsm.Evm64
