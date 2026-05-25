import EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- First n=1 step carry-zero reducer. For the call branch, the step starts
    with top limb zero, so proving the `mulsubN4` carry `c3` is zero is enough
    to discharge `fullDivN1R3CarryZero`. -/
theorem fullDivN1R3CarryZero_true_of_mulsub_c3_zero
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hc3 :
      mulsubN4_c3
        (div128Quot
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1)
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        (0 : Word)
        (0 : Word) = 0) :
    fullDivN1R3CarryZero true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullDivN1R3CarryZero fullDivN1R3
  exact iterN1_true_carry_zero_of_mulsub_c3_zero
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    (0 : Word)
    (0 : Word)
    (0 : Word)
    hc3 rfl

end EvmAsm.Evm64
