/-
  EvmAsm.Evm64.DivMod.Spec.N1TrialWitnesses

  Mechanical branch-boolean witnesses for the n=1 DIV path.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The four n=1 trial-branch booleans always have canonical witnesses.

    This packages the mechanical branch-enumeration part needed by
    unconditional n=1 stack wrappers. The remaining non-mechanical
    obligations are the carry/addback and semantic division witnesses. -/
theorem n1_trial_witnesses (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    ∃ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 a3 b0 ∧
      isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3 ∧
      isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3 ∧
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 := by
  let shift := (clzResult b0).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u1S := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2S := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  let bltu_3 := BitVec.ult u4_s v0'
  let r3 := iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)
  let bltu_2 := BitVec.ult r3.2.1 v0'
  let r2 := iterN1 bltu_2 v0' v1' v2' v3' u2S r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
  let bltu_1 := BitVec.ult r2.2.1 v0'
  let r1 := iterN1 bltu_1 v0' v1' v2' v3' u1S r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let bltu_0 := BitVec.ult r1.2.1 v0'
  refine ⟨bltu_3, bltu_2, bltu_1, bltu_0, ?_, ?_, ?_, ?_⟩
  · simp [isTrialN1_j3, bltu_3, v0', u4_s, shift, antiShift]
  · simp [isTrialN1_j2, bltu_2, bltu_3, r3, v0', v1', v2', v3', u3S, u4_s,
      shift, antiShift]
  · simp [isTrialN1_j1, bltu_1, bltu_2, bltu_3, r2, r3, v0', v1', v2', v3',
      u2S, u3S, u4_s, shift, antiShift]
  · simp [isTrialN1_j0, bltu_0, bltu_1, bltu_2, bltu_3, r1, r2, r3, v0', v1',
      v2', v3', u1S, u2S, u3S, u4_s, shift, antiShift]

end EvmAsm.Evm64
