/-
  EvmAsm.Evm64.DivMod.Spec.N2MaxBranchFromInvariant

  Closes the three N2 selected-carry MAX-branch predicates (j=2, j=1, j=0)
  at the canonical bltu triple from a *named* set of inputs:

    1. shape hypothesis: `b3 = 0`, `b2 = 0`, `b1 ≠ 0` (the n=2 shape predicate),
    2. shift normalisation facts (`v.2.2.2 = 0`, `v.2.2.1 = 0`,
       `2^63 ≤ v.2.1`),
    3. the canonical `bltu_X = false` condition,
    4. an instance of `MulsubMaxC3OneOfCarryZero` at the matching
       `(v-normalised, u-window-at-j)` input.

  The bridge `isAddbackCarry2NzN2Max_of_not_ult_c3_one_of_carry_zero` from
  `DivN2MaxOverestimate` is invoked once per outer iteration j∈{2,1,0}.

  Inputs (2) and (4) are not derivable from shape alone (see
  `Counterexamples.ceN1MaxLocal_c3_one_of_carry_zero_false`); naming them
  explicitly here turns the three N2 MAX bead leaves into compositions
  with one named normalisation gap and one shared reachability gap.

  Mirrors `N3MaxBranchFromInvariant` for the n=2 lane.
-/

import EvmAsm.Evm64.EvmWordArith.DivMaxC3Invariant
import EvmAsm.Evm64.EvmWordArith.DivN2MaxOverestimate
import EvmAsm.Evm64.DivMod.Spec.N2CallableSelectedShapeEvidenceCanonical

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N2 j=2 MAX-branch carry-2-nz at the canonical bltu_2 = false, from
    structural normalisation facts and the named c3 invariant. -/
theorem isAddbackCarry2NzN2Max_at_canonical_bltu2_false
    (a b : EvmWord)
    (hbltu2_false : n2V4CanonicalBltu2 a b = false)
    (hv3z_norm :
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2 = 0)
    (hv2z_norm :
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1 = 0)
    (hv1_msb_norm :
      2^63 ≤ (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1.toNat)
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
      (0 : Word) (0 : Word) := by
  have hbltu : ¬ BitVec.ult
      (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1 := by
    unfold n2V4CanonicalBltu2 at hbltu2_false
    intro h
    rw [h] at hbltu2_false
    exact Bool.noConfusion hbltu2_false
  exact isAddbackCarry2NzN2Max_of_not_ult_c3_one_of_carry_zero _ _ _ _ _ _ _ _ _
    hv1_msb_norm hv2z_norm hv3z_norm hc3 hbltu

/-- N2 j=1 MAX-branch carry-2-nz at the canonical bltu_1 = false, from
    structural normalisation facts and the named c3 invariant.

    Parametrised by `bltu_2 : Bool` since the j=1 input depends on the j=2
    iteration result `fullDivN2R2V4 bltu_2 a b`. -/
theorem isAddbackCarry2NzN2Max_at_canonical_bltu1_false
    (a b : EvmWord) (bltu_2 : Bool)
    (hbltu1_false :
      BitVec.ult
        (fullDivN2R2V4 bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1 = false)
    (hv3z_norm :
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2 = 0)
    (hv2z_norm :
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1 = 0)
    (hv1_msb_norm :
      2^63 ≤ (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1.toNat)
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
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 := by
  have hbltu : ¬ BitVec.ult
      (fullDivN2R2V4 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1 := by
    intro h
    rw [h] at hbltu1_false
    exact Bool.noConfusion hbltu1_false
  exact isAddbackCarry2NzN2Max_of_not_ult_c3_one_of_carry_zero _ _ _ _ _ _ _ _ _
    hv1_msb_norm hv2z_norm hv3z_norm hc3 hbltu

end EvmAsm.Evm64
