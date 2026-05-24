/-
  EvmAsm.Evm64.DivMod.Spec.N3TrialWitnesses

  Mechanical branch-boolean witnesses for the n=3 DIV path.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The two n=3 trial-branch booleans always have canonical witnesses.

    This packages the mechanical branch-enumeration part needed by
    unconditional n=3 stack wrappers. The remaining non-mechanical
    obligations are the carry/addback and semantic division witnesses. -/
theorem n3_trial_witnesses (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    ∃ bltu_1 bltu_0,
      isTrialN3_j1 bltu_1 a3 b1 b2 ∧
      isTrialN3_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 := by
  let shift := (clzResult b2).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u1S := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2S := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  let bltu_1 := BitVec.ult u4_s v2'
  let r1 := iterN3 bltu_1 v0' v1' v2' v3' u1S u2S u3S u4_s (0 : Word)
  let bltu_0 := BitVec.ult r1.2.2.2.1 v2'
  refine ⟨bltu_1, bltu_0, ?_, ?_⟩
  · simp [isTrialN3_j1, bltu_1, v2', u4_s, shift, antiShift]
  · simp [isTrialN3_j0, bltu_0, bltu_1, r1, v0', v1', v2', v3',
      u1S, u2S, u3S, u4_s, shift, antiShift]

end EvmAsm.Evm64
