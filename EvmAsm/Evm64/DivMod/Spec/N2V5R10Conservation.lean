/-
  EvmAsm.Evm64.DivMod.Spec.N2V5R10Conservation

  Digit-1 and digit-0 conservations for the v5 n=2 schoolbook call path,
  instantiating iterN2V5_true_conservation at the chained windows (each digit's
  input window is the previous digit's remainder).  Together with
  fullDivN2R2V5_conservation (#7342) these are the three links of the assembled
  fullDivN2MulSubEqV5.  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5R2Conservation

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

theorem fullDivN2R1V5_conservation (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : ((fullDivN2NormV b0 b1 b2 b3).1) ||| ((fullDivN2NormV b0 b1 b2 b3).2.1) ||| ((fullDivN2NormV b0 b1 b2 b3).2.2.1) ||| ((fullDivN2NormV b0 b1 b2 b3).2.2.2) ≠ 0)
    (hc3_one_of_borrow :
      BitVec.ult ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1) (mulsubN4 (divKTrialCallV5QHat ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.1)) ((fullDivN2NormV b0 b1 b2 b3).1) ((fullDivN2NormV b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.2) ((fullDivN2NormU a0 a1 a2 a3 b1).2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)).2.2.2.2 →
        (mulsubN4 (divKTrialCallV5QHat ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.1)) ((fullDivN2NormV b0 b1 b2 b3).1) ((fullDivN2NormV b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.2) ((fullDivN2NormU a0 a1 a2 a3 b1).2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)).2.2.2.2 = 1)
    (hcarry2 :
      isAddbackCarry2Nz (divKTrialCallV5QHat ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.1))
        ((fullDivN2NormV b0 b1 b2 b3).1) ((fullDivN2NormV b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.2) ((fullDivN2NormU a0 a1 a2 a3 b1).2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)) :
    val256 ((fullDivN2NormU a0 a1 a2 a3 b1).2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1) + ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1).toNat * 2^256 =
      ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3)).1.toNat * val256 ((fullDivN2NormV b0 b1 b2 b3).1) ((fullDivN2NormV b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.2) +
      val256
        ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3)).2.1 ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3)).2.2.1 ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3)).2.2.2.1 ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3)).2.2.2.2.1 +
      ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3)).2.2.2.2.2.toNat * 2^256 := by
  unfold fullDivN2R1V5
  exact iterN2V5_true_conservation
    ((fullDivN2NormV b0 b1 b2 b3).1) ((fullDivN2NormV b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.2) ((fullDivN2NormU a0 a1 a2 a3 b1).2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1) ((fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)
    hbnz hc3_one_of_borrow hcarry2

theorem fullDivN2R0V5_conservation (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : ((fullDivN2NormV b0 b1 b2 b3).1) ||| ((fullDivN2NormV b0 b1 b2 b3).2.1) ||| ((fullDivN2NormV b0 b1 b2 b3).2.2.1) ||| ((fullDivN2NormV b0 b1 b2 b3).2.2.2) ≠ 0)
    (hc3_one_of_borrow :
      BitVec.ult ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1) (mulsubN4 (divKTrialCallV5QHat ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.1)) ((fullDivN2NormV b0 b1 b2 b3).1) ((fullDivN2NormV b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.2) ((fullDivN2NormU a0 a1 a2 a3 b1).1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)).2.2.2.2 →
        (mulsubN4 (divKTrialCallV5QHat ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.1)) ((fullDivN2NormV b0 b1 b2 b3).1) ((fullDivN2NormV b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.2) ((fullDivN2NormU a0 a1 a2 a3 b1).1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)).2.2.2.2 = 1)
    (hcarry2 :
      isAddbackCarry2Nz (divKTrialCallV5QHat ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.1))
        ((fullDivN2NormV b0 b1 b2 b3).1) ((fullDivN2NormV b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.2) ((fullDivN2NormU a0 a1 a2 a3 b1).1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)) :
    val256 ((fullDivN2NormU a0 a1 a2 a3 b1).1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1) + ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1).toNat * 2^256 =
      ((fullDivN2R0V5 true true true a0 a1 a2 a3 b0 b1 b2 b3)).1.toNat * val256 ((fullDivN2NormV b0 b1 b2 b3).1) ((fullDivN2NormV b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.2) +
      val256
        ((fullDivN2R0V5 true true true a0 a1 a2 a3 b0 b1 b2 b3)).2.1 ((fullDivN2R0V5 true true true a0 a1 a2 a3 b0 b1 b2 b3)).2.2.1 ((fullDivN2R0V5 true true true a0 a1 a2 a3 b0 b1 b2 b3)).2.2.2.1 ((fullDivN2R0V5 true true true a0 a1 a2 a3 b0 b1 b2 b3)).2.2.2.2.1 +
      ((fullDivN2R0V5 true true true a0 a1 a2 a3 b0 b1 b2 b3)).2.2.2.2.2.toNat * 2^256 := by
  unfold fullDivN2R0V5
  exact iterN2V5_true_conservation
    ((fullDivN2NormV b0 b1 b2 b3).1) ((fullDivN2NormV b0 b1 b2 b3).2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.1) ((fullDivN2NormV b0 b1 b2 b3).2.2.2) ((fullDivN2NormU a0 a1 a2 a3 b1).1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1) ((fullDivN2R1V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)
    hbnz hc3_one_of_borrow hcarry2

end EvmAsm.Evm64
