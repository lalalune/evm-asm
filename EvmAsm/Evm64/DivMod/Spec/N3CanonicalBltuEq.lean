/-
  EvmAsm.Evm64.DivMod.Spec.N3CanonicalBltuEq

  Definitional unfolding equation lemma for the canonical N3 bltu_1 value.
  (The bltu_0 case is an if-then-else; downstream callers can pattern-match
  via `cases n3V4CanonicalBltu1 a b` and use `simp [n3V4CanonicalBltu0]` for
  branch-by-branch unfolding.)

  Opt-in simp lemma; not tagged `@[simp]` by default to avoid silently
  changing existing proofs. Mirrors `N2CanonicalBltuEq`.
-/

import EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidenceCanonical

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem n3V4CanonicalBltu1_eq (a b : EvmWord) :
    n3V4CanonicalBltu1 a b =
      BitVec.ult
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1 :=
  rfl

end EvmAsm.Evm64
