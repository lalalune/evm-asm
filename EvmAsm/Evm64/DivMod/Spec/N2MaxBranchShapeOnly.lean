/-
  EvmAsm.Evm64.DivMod.Spec.N2MaxBranchShapeOnly

  Shape-only closure forms for the three N2 selected-carry MAX-branch
  predicates (j=2, j=1, j=0), obtained by composing the closure-form
  theorems in `N2MaxBranchFromInvariant` with the structural normalisation
  lemmas in `DivN2NormVStructure`.

  The remaining open obligation in each form is exactly one instance of the
  unified `MulsubMaxC3OneOfCarryZero` invariant (the per-iteration Knuth-B
  reachability fact).  No other auxiliary hypotheses — only n=2 shape facts
  + shift_nz + the canonical `bltu_X = false` condition.

  Mirrors `N3MaxBranchShapeOnly` for the n=2 lane.
-/

import EvmAsm.Evm64.DivMod.Spec.N2MaxBranchFromInvariant
import EvmAsm.Evm64.EvmWordArith.DivN2NormVStructure

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N2 j=2 MAX-branch carry-2-nz at the canonical bltu_2 = false, from
    n=2 shape (`b3 = 0`, `b2 = 0`, `b1 ≠ 0`), `shift_nz`, and the named c3
    invariant.  The three structural normalisation facts about
    `fullDivN2NormV` are discharged internally. -/
theorem isAddbackCarry2NzN2Max_at_canonical_bltu2_false_of_shape
    (a b : EvmWord)
    (hb3z : b.getLimbN 3 = 0)
    (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (hbltu2_false : n2V4CanonicalBltu2 a b = false)
    (hc3 : MulsubMaxC3OneOfCarryZero
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
      (0 : Word)) :
    isAddbackCarry2NzN2Max
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.1
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.1
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
      (0 : Word) (0 : Word) :=
  isAddbackCarry2NzN2Max_at_canonical_bltu2_false a b hbltu2_false
    (fullDivN2NormV_top_zero_of_shape
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3z hb2z)
    (fullDivN2NormV_v2_zero_of_shape_shift_nz
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb2z hshift_nz)
    (fullDivN2NormV_msb_of_b1_ne_zero
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb1nz)
    hc3

/-- N2 j=1 MAX-branch shape-only closure.  Parametrised by `bltu_2 : Bool`
    since the j=1 input depends on `fullDivN2R2V4 bltu_2`. -/
theorem isAddbackCarry2NzN2Max_at_canonical_bltu1_false_of_shape
    (a b : EvmWord) (bltu_2 : Bool)
    (hb3z : b.getLimbN 3 = 0)
    (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (hbltu1_false :
      BitVec.ult
        (fullDivN2R2V4 bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1 = false)
    (hc3 : MulsubMaxC3OneOfCarryZero
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.1
      (fullDivN2R2V4 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN2R2V4 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN2R2V4 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1) :
    isAddbackCarry2NzN2Max
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.1
      (fullDivN2R2V4 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN2R2V4 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN2R2V4 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
      (fullDivN2R2V4 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 :=
  isAddbackCarry2NzN2Max_at_canonical_bltu1_false a b bltu_2 hbltu1_false
    (fullDivN2NormV_top_zero_of_shape
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3z hb2z)
    (fullDivN2NormV_v2_zero_of_shape_shift_nz
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb2z hshift_nz)
    (fullDivN2NormV_msb_of_b1_ne_zero
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb1nz)
    hc3

/-- N2 j=0 MAX-branch shape-only closure.  Parametrised by `bltu_2, bltu_1
    : Bool` since the j=0 input depends on `fullDivN2R1V4 bltu_2 bltu_1`. -/
theorem isAddbackCarry2NzN2Max_at_canonical_bltu0_false_of_shape
    (a b : EvmWord) (bltu_2 bltu_1 : Bool)
    (hb3z : b.getLimbN 3 = 0)
    (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (hbltu0_false :
      BitVec.ult
        (fullDivN2R1V4 bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1 = false)
    (hc3 : MulsubMaxC3OneOfCarryZero
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).1
      (fullDivN2R1V4 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN2R1V4 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN2R1V4 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1) :
    isAddbackCarry2NzN2Max
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).1
      (fullDivN2R1V4 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN2R1V4 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN2R1V4 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
      (fullDivN2R1V4 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 :=
  isAddbackCarry2NzN2Max_at_canonical_bltu0_false a b bltu_2 bltu_1 hbltu0_false
    (fullDivN2NormV_top_zero_of_shape
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb3z hb2z)
    (fullDivN2NormV_v2_zero_of_shape_shift_nz
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb2z hshift_nz)
    (fullDivN2NormV_msb_of_b1_ne_zero
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) hb1nz)
    hc3

end EvmAsm.Evm64
