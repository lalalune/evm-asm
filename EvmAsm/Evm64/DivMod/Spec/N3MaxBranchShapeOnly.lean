/-
  EvmAsm.Evm64.DivMod.Spec.N3MaxBranchShapeOnly

  Shape-only closure forms for the N3 selected-carry MAX-branch predicates,
  obtained by composing the closure-form theorems in
  `N3MaxBranchFromInvariant` with the structural normalisation lemmas now
  proven in `DivN3NormVStructure`.

  The remaining open obligation in each form is exactly one instance of the
  unified `MulsubMaxC3OneOfCarryZero` invariant (the per-iteration Knuth-B
  reachability fact).  No other auxiliary hypotheses — only n=3 shape facts
  + the canonical bltu_X = false condition.
-/

import EvmAsm.Evm64.DivMod.Spec.N3MaxBranchFromInvariant
import EvmAsm.Evm64.EvmWordArith.DivN3NormVStructure

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N3 j=1 MAX-branch carry-2-nz at the canonical bltu_1 = false, from
    n=3 shape (`b3 = 0`, `b2 ≠ 0`), `shift_nz`, and the named c3 invariant.
    The two structural normalisation facts about `fullDivN3NormV` are
    discharged internally via `fullDivN3NormV_top_zero_of_shape_shift_nz`
    and `fullDivN3NormV_msb_of_b2_ne_zero`. -/
theorem isAddbackCarry2NzN3Max_at_canonical_bltu1_false_of_shape
    (a b : EvmWord)
    (hb3z : b.getLimbN 3 = 0)
    (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (hbltu1_false : n3V4CanonicalBltu1 a b = false)
    (hc3 : MulsubMaxC3OneOfCarryZero
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
    isAddbackCarry2NzN3Max
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
      (0 : Word) :=
  isAddbackCarry2NzN3Max_at_canonical_bltu1_false a b hbltu1_false
    (fullDivN3NormV_top_zero_of_shape_shift_nz
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hb3z hshift_nz)
    (fullDivN3NormV_msb_of_b2_ne_zero
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb2nz)
    hc3

/-- N3 j=0 MAX-branch carry-2-nz at the canonical bltu_0 = false, from
    n=3 shape, `shift_nz`, and the named c3 invariant.  Parametrised by
    `bltu_1 : Bool` since the j=0 input depends on `fullDivN3R1V4 bltu_1`. -/
theorem isAddbackCarry2NzN3Max_at_canonical_bltu0_false_of_shape
    (a b : EvmWord) (bltu_1 : Bool)
    (hb3z : b.getLimbN 3 = 0)
    (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (hbltu0_false :
      BitVec.ult
        (fullDivN3R1V4 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1 = false)
    (hc3 : MulsubMaxC3OneOfCarryZero
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1) :
    isAddbackCarry2NzN3Max
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 :=
  isAddbackCarry2NzN3Max_at_canonical_bltu0_false a b bltu_1 hbltu0_false
    (fullDivN3NormV_top_zero_of_shape_shift_nz
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hb3z hshift_nz)
    (fullDivN3NormV_msb_of_b2_ne_zero
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb2nz)
    hc3

end EvmAsm.Evm64
