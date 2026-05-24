/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase1bBound

  Algorithm-level Phase-1b facts for the v4 2-correction proof.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Algorithm
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.QuotientBounds
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.Un21Bridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- The pre-second-correction Phase-1b quotient `q1'` used by v4. -/
@[irreducible]
def algorithmQ1dV4 (uHi uLo vTop : Word) : Word :=
  algorithmQ1Prime uHi uLo vTop

/-- The pre-second-correction Phase-1b remainder `rhat'` used by v4. -/
@[irreducible]
def algorithmRhatdV4 (uHi uLo vTop : Word) : Word :=
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
  if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc

theorem algorithmQ1dV4_unfold (uHi uLo vTop : Word) :
    algorithmQ1dV4 uHi uLo vTop = algorithmQ1Prime uHi uLo vTop := by
  delta algorithmQ1dV4
  rfl

theorem algorithmRhatdV4_unfold (uHi uLo vTop : Word) :
    algorithmRhatdV4 uHi uLo vTop =
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
       if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc) := by
  delta algorithmRhatdV4
  rfl

/-- Phase-1b Euclidean identity for the v4 pre-second-correction pair. -/
theorem algorithmQ1dV4_rhatd_post
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63) :
    (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat +
      (algorithmRhatdV4 uHi uLo vTop).toNat = uHi.toNat := by
  have h := algorithmUn21_L2a_wrapped uHi uLo vTop hvTop_ge
  rw [algorithmQ1dV4_unfold, algorithmRhatdV4_unfold]
  unfold divKTrialCallV4DHi divKTrialCallV4DLo divKTrialCallV4Un1
  simpa using h

/-- Narrow-call Phase-1b overshoot bound for the pre-second-correction pair.

    This discharges the `h_overshoot_le_vTop` argument of
    `div128Quot_phase2b_q0'_dLo_bound_fire_case` in the
    `uHi < dHi * 2^32` sub-regime. -/
theorem algorithmQ1dV4_dLo_overshoot_le_vTop_of_uHi_lt_dHi_pow32
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_dHi_pow32 :
      uHi.toNat < (divKTrialCallV4DHi vTop).toNat * 2^32)
    (h_phase1b_post :
      (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat +
        (algorithmRhatdV4 uHi uLo vTop).toNat = uHi.toNat) :
    (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat ≤
      (algorithmRhatdV4 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat +
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
  have h_vTop_decomp : vTop.toNat =
      (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
    unfold divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have h_q_le0 := algorithmQ1Prime_le_q_true_1_plus_one uHi uLo vTop
    hvTop_ge huHi_lt_vTop (by simpa [divKTrialCallV4DHi] using huHi_lt_dHi_pow32)
  have h_q_le :
      (algorithmQ1dV4 uHi uLo vTop).toNat ≤
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) / vTop.toNat + 1 := by
    rw [algorithmQ1dV4_unfold]
    unfold divKTrialCallV4Un1
    simpa using h_q_le0
  have h_vTop_pos : 0 < vTop.toNat := by omega
  have h_qV_le :
      (algorithmQ1dV4 uHi uLo vTop).toNat * vTop.toNat ≤
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) + vTop.toNat := by
    have h_mul := Nat.mul_le_mul_right vTop.toNat h_q_le
    have h_div_mul :=
      Nat.div_mul_le_self
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) vTop.toNat
    nlinarith
  have h_u_decomp : uHi.toNat * 2^32 =
      (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (algorithmRhatdV4 uHi uLo vTop).toNat * 2^32 := by
    have h := congrArg (fun x => x * 2^32) h_phase1b_post
    nlinarith [Nat.add_mul
      ((algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat)
      (algorithmRhatdV4 uHi uLo vTop).toNat (2^32)]
  have h_qV_expand :
      (algorithmQ1dV4 uHi uLo vTop).toNat * vTop.toNat =
        (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat := by
    rw [h_vTop_decomp]
    ring
  nlinarith

/-- Narrow-call Phase-1b overshoot bound, with the Phase-1b Euclidean identity
    discharged internally. -/
theorem algorithmQ1dV4_dLo_overshoot_le_vTop_of_uHi_lt_dHi_pow32_closed
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_dHi_pow32 :
      uHi.toNat < (divKTrialCallV4DHi vTop).toNat * 2^32) :
    (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat ≤
      (algorithmRhatdV4 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat +
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
  exact algorithmQ1dV4_dLo_overshoot_le_vTop_of_uHi_lt_dHi_pow32
    uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_dHi_pow32
    (algorithmQ1dV4_rhatd_post uHi uLo vTop hvTop_ge)

end EvmAsm.Evm64
