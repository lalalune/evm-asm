/-
  EvmAsm.Evm64.DivMod.Spec.N3BltBranchShapeOnly

  Shape-only closure forms for the N3 selected-carry BLT-branch predicates
  (j=1, j=0), obtained by composing the BLT predicate bridges in
  `DivBltBridgeSpecializations` with the normalisation-derived divisor
  nonzero fact.

  The remaining open obligations are:
    1. The +2 v4 trial overestimate (`hq_over`) — the val256-level
       Knuth-A v4 bound (bead `7.1.4.1` and its descendants).
    2. The named `MulsubBltC3OneOfCarryZero` invariant.

  Mirrors `N3MaxBranchShapeOnly` for the BLT side.
-/

import EvmAsm.Evm64.EvmWordArith.DivBltBridgeSpecializations
import EvmAsm.Evm64.DivMod.Spec.N3RemainderWordV4
import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N3 j=1 BLT-branch carry-2-nz at the canonical bltu_1 = true, from
    n=3 shape facts + `shift_nz`, the v4 trial overestimate, and the named
    BLT c3 invariant.  The divisor-nonzero side-condition is discharged
    via the existing `fullDivN3NormV_or_ne_zero_of_word_ne_zero_b3_zero`. -/
theorem loopBodyN3CallAddbackCarry2NzV4_at_canonical_bltu1_true_of_shape
    (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (hq_over :
      (divKTrialCallV4QHat
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1).toNat ≤
      EvmWord.val256
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2 /
      EvmWord.val256
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2 + 2)
    (hc3 : MulsubBltC3OneOfCarryZero
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
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
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2) :
    loopBodyN3CallAddbackCarry2NzV4
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
      (0 : Word) := by
  have h_shift_nz' : fullDivN3Shift (b.getLimbN 2) ≠ 0 := by
    rw [fullDivN3Shift_unfold]; exact hshift_nz
  have h_normV_or_nz := fullDivN3NormV_or_ne_zero_of_word_ne_zero_b3_zero
    b hbnz h_shift_nz' hb3z
  exact loopBodyN3CallAddbackCarry2NzV4_of_overestimate_c3 _ _ _ _ _ _ _ _ _
    h_normV_or_nz hq_over hc3

end EvmAsm.Evm64
