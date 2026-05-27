/-
  EvmAsm.Evm64.DivMod.Spec.N3CanonicalBltu0Branches

  Branch-specific unfolding lemmas for `n3V4CanonicalBltu0`. Useful when
  the caller has determined `n3V4CanonicalBltu1 a b` (e.g. via `cases`)
  and wants the concrete `BitVec.ult` RHS for the corresponding branch.

  Pairs with `N3CanonicalBltuEq` (which only handles `bltu_1` since it has
  no if-then-else).
-/

import EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidenceCanonical

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Branch unfolding for `n3V4CanonicalBltu0` when `n3V4CanonicalBltu1 = true`. -/
theorem n3V4CanonicalBltu0_eq_of_bltu1_true {a b : EvmWord}
    (h : n3V4CanonicalBltu1 a b = true) :
    n3V4CanonicalBltu0 a b =
      BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
            (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
            (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
          (0 : Word)).2.2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1 := by
  unfold n3V4CanonicalBltu0
  rw [h]
  rfl

/-- Branch unfolding for `n3V4CanonicalBltu0` when `n3V4CanonicalBltu1 = false`. -/
theorem n3V4CanonicalBltu0_eq_of_bltu1_false {a b : EvmWord}
    (h : n3V4CanonicalBltu1 a b = false) :
    n3V4CanonicalBltu0 a b =
      BitVec.ult
        (iterN3Max
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.2
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
          (0 : Word)).2.2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1 := by
  unfold n3V4CanonicalBltu0
  rw [h]
  rfl

end EvmAsm.Evm64
