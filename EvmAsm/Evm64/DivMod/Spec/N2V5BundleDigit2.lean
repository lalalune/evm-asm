/-
  EvmAsm.Evm64.DivMod.Spec.N2V5BundleDigit2

  The j=2 (first) conjunct of `loopN2SelectedBorrowCarryV5` at the lane level
  (over the `fullDivN2NormV/U` accessors), discharged from shape.  The first
  digit's window has `u3 = uTop = 0` (no collapse needed), so it applies the
  per-digit call/max carry discharges (#7454/#7455) directly after rewriting the
  normalized divisor's high limbs to zero (#7458).  Demonstrates the per-digit
  pattern of the full `loopN2SelectedBorrowCarryV5_of_shape` telescope.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5CallCarryOfCallShape
import EvmAsm.Evm64.DivMod.Spec.N2V5MaxCarryOfMaxShape
import EvmAsm.Evm64.DivMod.Spec.N2V5NormVShapeFacts

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The j=2 conjunct of the borrow-carry bundle, from shape. -/
theorem loopN2SelectedBorrowCarryV5_digit2_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hc2 : bltu_2 = true →
      BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm2 : bltu_2 = false →
      ¬ BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1) :
    (if bltu_2 then
      (BitVec.ult 0
        (mulsubN4_c3 (divKTrialCallV5QHat (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
          (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0) →
        callAddbackCarry2NzV5 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0 0)
     else
      (BitVec.ult 0
        (mulsubN4_c3 (signExtend12 4095 : Word)
          (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0) →
        isAddbackCarry2NzN2Max (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0 0)) := by
  obtain ⟨hv1n, hv2z', hv3z'⟩ := fullDivN2NormV_shape_facts b0 b1 b2 b3 hb2z hb3z hb1nz hshift_nz
  rw [hv2z', hv3z']
  cases hbl : bltu_2 with
  | true =>
    intro hborrow
    have hcall : (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2.toNat <
        (fullDivN2NormV b0 b1 b2 b3).2.1.toNat := by
      have := hc2 hbl; rw [BitVec.ult] at this; exact of_decide_eq_true this
    exact callAddbackCarry2NzV5_of_borrow_of_call_shape
      (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0 hv1n hcall hborrow
  | false =>
    intro hborrow
    exact isAddbackCarry2NzN2Max_of_borrow_of_max_shape
      (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0 hv1n (hm2 hbl) hborrow

end EvmAsm.Evm64
