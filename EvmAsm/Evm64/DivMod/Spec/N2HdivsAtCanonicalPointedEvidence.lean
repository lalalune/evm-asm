/-
  EvmAsm.Evm64.DivMod.Spec.N2HdivsAtCanonicalPointedEvidence

  Bundled variant of `n2HdivsAtCanonical_of_shape` (PR #6958) that takes
  the `N2CanonicalPointedEvidence` abbreviation (PR #6963) directly,
  projects via `.selectedCarry` and `.arithmetic`, and delegates to the
  existing two-predicate composition.
-/

import EvmAsm.Evm64.DivMod.Spec.N2HdivsAtCanonical
import EvmAsm.Evm64.DivMod.Spec.N2CanonicalPointedEvidence

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N2 hdiv equations at the canonical bltu triple, derived from bundled
    `N2CanonicalPointedEvidence` and the n=2 divisor shape. -/
theorem n2HdivsAtCanonical_of_shape_pointedEvidence
    {a b : EvmWord}
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
    (hevidence : N2CanonicalPointedEvidence a b) :
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
  n2HdivsAtCanonical_of_shape hb3z hb2z hb1nz
    (N2CanonicalPointedEvidence.selectedCarry hevidence)
    (N2CanonicalPointedEvidence.arithmetic hevidence)

end EvmAsm.Evm64
