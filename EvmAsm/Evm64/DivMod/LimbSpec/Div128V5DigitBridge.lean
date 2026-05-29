/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128V5DigitBridge

  Per-Knuth-digit assembly of the v5 div128 code-vs-model q-bridge: combines the
  rhatc arithmetic (`div128V5_rhatc_correction_eq`, #7243) and the selection
  reconciliations (`div128V5_phase1b_select_eq` / `_rhat_select_eq`, #7244/#7245)
  into the equality of the *full corrected digit* computed the code way
  (`div128V5SpecPost`) and the model way (`div128Quot_v5`).

  `div128V5_rhatc_eq` lifts the capped-branch ring identity to the full
  `if hi = 0 …` capped-remainder form used by both `div128V5SpecPost` and
  `div128Quot_v5`.  `div128V5_q1Final_eq_model` then proves the corrected
  quotient digit agrees.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5Phase1bBridge
import EvmAsm.Evm64.DivMod.LimbSpec.Div128V5CodeModelBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **Capped remainder code = model.**  The code's incremental capped remainder
    (`if hi=0 then rhat else rhat + (q1-cap)·dHi`) equals the model's closed form
    (`if hi=0 then rhat else uHi - q1c·dHi`, with `q1c = if hi=0 then q1 else cap`).
    The capped branch is `div128V5_rhatc_correction_eq` (#7243); the `hi=0`
    branch is refl. -/
theorem div128V5_rhatc_eq (uHi q1 cap dHi : Word) :
    (if q1 >>> (32 : BitVec 6).toNat = 0 then uHi - q1 * dHi
     else (uHi - q1 * dHi) + (q1 - cap) * dHi)
    = (if q1 >>> (32 : BitVec 6).toNat = 0 then uHi - q1 * dHi
       else uHi - (if q1 >>> (32 : BitVec 6).toNat = 0 then q1 else cap) * dHi) := by
  split
  · rfl
  · exact div128V5_rhatc_correction_eq uHi q1 cap dHi

/-- The div128 **code** quotient: a standalone copy of `div128V5SpecPost`'s
    `q` register (the corrected 128/64 quotient as the RISC-V code computes it,
    with the incremental capped remainders).  `div128V5SpecPost`'s `x11` is this
    by construction (`rfl`). -/
def div128V5CodeQuot (uHi uLo vTop : Word) : Word :=
  let dHi := vTop >>> (32 : BitVec 6).toNat
  let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let un1 := uLo >>> (32 : BitVec 6).toNat
  let un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
  let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else cap
  let rhatc := if hi1 = 0 then rhat else rhat + (q1 - cap) * dHi
  let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
  let qDlo1 := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
  let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
  let brhat'Hi := brhat' >>> (32 : BitVec 6).toNat
  let qDlo2 := bq1' * dLo
  let rhatUn1' := (brhat' <<< (32 : BitVec 6).toNat) ||| un1
  let q1'' := if BitVec.ult rhatUn1' qDlo2 then bq1' + signExtend12 4095 else bq1'
  let rhat'' := if BitVec.ult rhatUn1' qDlo2 then brhat' + dHi else brhat'
  let q1Final := if rhatcHi ≠ 0 then q1c else (if brhat'Hi = 0 then q1'' else bq1')
  let rhatFinal := if rhatcHi ≠ 0 then rhatc else (if brhat'Hi = 0 then rhat'' else brhat')
  let un21 := ((rhatFinal <<< (32 : BitVec 6).toNat) ||| un1) - q1Final * dLo
  let q0 := rv64_divu un21 dHi
  let rhat2 := un21 - q0 * dHi
  let hi2 := q0 >>> (32 : BitVec 6).toNat
  let q0c := if hi2 = 0 then q0 else cap
  let rhat2c := if hi2 = 0 then rhat2 else rhat2 + (q0 - cap) * dHi
  let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
  let q0Dlo1 := q0c * dLo
  let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| un0
  let bq0' := if BitVec.ult rhat2Un0 q0Dlo1 then q0c + signExtend12 4095 else q0c
  let brhat2' := if BitVec.ult rhat2Un0 q0Dlo1 then rhat2c + dHi else rhat2c
  let brhat2'Hi := brhat2' >>> (32 : BitVec 6).toNat
  let q0Dlo2 := bq0' * dLo
  let rhat2'Un0 := (brhat2' <<< (32 : BitVec 6).toNat) ||| un0
  let q0'' := if BitVec.ult rhat2'Un0 q0Dlo2 then bq0' + signExtend12 4095 else bq0'
  let q0Final := if rhat2cHi ≠ 0 then q0c else (if brhat2'Hi = 0 then q0'' else bq0')
  (q1Final <<< (32 : BitVec 6).toNat) ||| q0Final

/-- Phase-1 of the q-bridge: the code's corrected Phase-1 trial quotient digit
    `q1Final` equals the model's `q1''`.  Combines the capped-remainder bridge
    `div128V5_rhatc_eq` (rewriting the incremental `rhatc` to the model's closed
    form) with the selection reconciliation `div128V5_phase1b_select_eq`. -/
theorem div128V5_q1Final_eq_model (uHi dHi dLo un1 : Word) :
    (let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu uHi dHi
     let rhat := uHi - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else cap
     let rhatc := if hi1 = 0 then rhat else rhat + (q1 - cap) * dHi
     let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
     let qDlo1 := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
     let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
     let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
     let brhat'Hi := brhat' >>> (32 : BitVec 6).toNat
     let qDlo2 := bq1' * dLo
     let rhatUn1' := (brhat' <<< (32 : BitVec 6).toNat) ||| un1
     let q1'' := if BitVec.ult rhatUn1' qDlo2 then bq1' + signExtend12 4095 else bq1'
     if rhatcHi ≠ 0 then q1c else (if brhat'Hi = 0 then q1'' else bq1'))
    =
    (let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu uHi dHi
     let rhat := uHi - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else cap
     let rhatc := if hi1 = 0 then rhat else uHi - q1c * dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
     let phase1bFire1 :=
       decide (rhatc >>> (32 : BitVec 6).toNat = 0) && BitVec.ult rhatUn1 qDlo
     let q1' := if phase1bFire1 then q1c + signExtend12 4095 else q1c
     let rhat' := if phase1bFire1 then rhatc + dHi else rhatc
     div128Quot_phase2b_q0' q1' rhat' dLo un1) := by
  dsimp only
  rw [div128V5_rhatc_eq uHi (rv64_divu uHi dHi)
    ((BitVec.allOnes 64) >>> (32 : BitVec 6).toNat) dHi]
  exact div128V5_phase1b_select_eq _ _ dHi dLo un1

/-- Phase-1 of the q-bridge, remainder side: the code's corrected Phase-1
    remainder `rhatFinal` equals the model's `rhat''` (needed for `un21`).
    Same template as `div128V5_q1Final_eq_model`, via `div128V5_rhatc_eq` +
    `div128V5_phase1b_rhat_select_eq`. -/
theorem div128V5_rhatFinal_eq_model (uHi dHi dLo un1 : Word) :
    (let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu uHi dHi
     let rhat := uHi - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else cap
     let rhatc := if hi1 = 0 then rhat else rhat + (q1 - cap) * dHi
     let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
     let qDlo1 := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
     let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
     let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
     let brhat'Hi := brhat' >>> (32 : BitVec 6).toNat
     let qDlo2 := bq1' * dLo
     let rhatUn1' := (brhat' <<< (32 : BitVec 6).toNat) ||| un1
     let rhat'' := if BitVec.ult rhatUn1' qDlo2 then brhat' + dHi else brhat'
     if rhatcHi ≠ 0 then rhatc else (if brhat'Hi = 0 then rhat'' else brhat'))
    =
    (let cap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
     let q1 := rv64_divu uHi dHi
     let rhat := uHi - q1 * dHi
     let hi1 := q1 >>> (32 : BitVec 6).toNat
     let q1c := if hi1 = 0 then q1 else cap
     let rhatc := if hi1 = 0 then rhat else uHi - q1c * dHi
     let qDlo := q1c * dLo
     let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
     let phase1bFire1 :=
       decide (rhatc >>> (32 : BitVec 6).toNat = 0) && BitVec.ult rhatUn1 qDlo
     let q1' := if phase1bFire1 then q1c + signExtend12 4095 else q1c
     let rhat' := if phase1bFire1 then rhatc + dHi else rhatc
     if rhat' >>> (32 : BitVec 6).toNat = 0 then
       let qDlo2 := q1' * dLo
       let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| un1
       if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
     else rhat') := by
  dsimp only
  rw [div128V5_rhatc_eq uHi (rv64_divu uHi dHi)
    ((BitVec.allOnes 64) >>> (32 : BitVec 6).toNat) dHi]
  exact div128V5_phase1b_rhat_select_eq _ _ dHi dLo un1

end EvmAsm.Evm64
