import EvmAsm.Evm64.DivMod.LoopBody.TrialCall
import EvmAsm.Evm64.EvmWordArith.Div128QuotientBounds

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem divKTrialCallV4Q1dd_le_phase1b (uHi uLo vTop : Word) :
    (divKTrialCallV4Q1dd uHi uLo vTop).toNat ≤
      (let dHi := divKTrialCallV4DHi vTop
       let dLo := divKTrialCallV4DLo vTop
       let un1 := divKTrialCallV4Un1 uLo
       let q1 := rv64_divu uHi dHi
       let rhat := uHi - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc := if hi1 = 0 then rhat else rhat + dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
       if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c).toNat := by
  rw [divKTrialCallV4Q1dd_eq_phase2b]
  exact div128Quot_phase2b_q0'_le_self _ _ _ _

theorem divKTrialCallV4Q1dd_le_q1c (uHi uLo vTop : Word) :
    (divKTrialCallV4Q1dd uHi uLo vTop).toNat ≤
      (let dHi := divKTrialCallV4DHi vTop
       let q1 := rv64_divu uHi dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat := by
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  exact le_trans
    (divKTrialCallV4Q1dd_le_phase1b uHi uLo vTop)
    (div128Quot_q1_prime_le_q1c q1c dLo rhatUn1)

theorem divKTrialCallV4Q0d_le_q0c (uHi uLo vTop : Word) :
    (divKTrialCallV4Q0d uHi uLo vTop).toNat ≤
      (divKTrialCallV4Q0c uHi uLo vTop).toNat := by
  unfold divKTrialCallV4Q0d
  exact div128Quot_phase2b_q0'_le_self _ _ _ _

theorem divKTrialCallV4Q0dd_le_q0d (uHi uLo vTop : Word) :
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat ≤
      (divKTrialCallV4Q0d uHi uLo vTop).toNat := by
  unfold divKTrialCallV4Q0dd
  exact div128Quot_phase2b_q0'_le_self _ _ _ _

theorem divKTrialCallV4Q0dd_le_q0c (uHi uLo vTop : Word) :
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat ≤
      (divKTrialCallV4Q0c uHi uLo vTop).toNat :=
  le_trans
    (divKTrialCallV4Q0dd_le_q0d uHi uLo vTop)
    (divKTrialCallV4Q0d_le_q0c uHi uLo vTop)

end EvmAsm.Evm64
