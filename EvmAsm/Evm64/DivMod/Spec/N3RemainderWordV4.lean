/-
  EvmAsm.Evm64.DivMod.Spec.N3RemainderWordV4

  Packed n=3 MOD remainder word for the v4 call/max final computation.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V4
import EvmAsm.Evm64.DivMod.Compose.ModFullPathN3LoopUnified

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v4 n=3 MOD remainder word, using the v4 call-path `fullDivN3R0V4`
computation before the usual denormalization shift. -/
@[irreducible]
def fullModN3RemainderWordV4 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 =>
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
    | 1 =>
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
    | 2 =>
        (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64)))
    | 3 =>
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)))

/-- N3 MOD denorm post paired with the v4 call-path final computation. -/
@[irreducible]
def fullModN3DenormPostV4 (bltu_1 bltu_0 : Bool)
    (sp a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Assertion :=
  let shift := fullDivN3Shift b2
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  let r0 := fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  denormModPost sp shift r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 **
  ((sp + signExtend12 3992) ↦ₘ shift) **
  ((sp + signExtend12 4088) ↦ₘ r0.1) **
  ((sp + signExtend12 4080) ↦ₘ r1.1) **
  ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
  ((sp + signExtend12 4064) ↦ₘ (0 : Word))

/-- N3 MOD unified post with caller `x1` outside the assertion and the v4
div128 scratch cell framed explicitly. -/
@[irreducible]
def fullModN3UnifiedPostNoX1V4 (bltu_1 bltu_0 : Bool)
    (sp base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word) : Assertion :=
  fullModN3DenormPostV4 bltu_1 bltu_0 sp a0 a1 a2 a3 b0 b1 b2 b3 **
  fullDivN3FrameNoX1V4 bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3
    retMem dMem dloMem scratchUn0 **
  ((sp + signExtend12 3936) ↦ₘ
    fullDivN3ScratchMemV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 scratchMem)

/-- Project a packed v4 n=3 MOD remainder equality into limb equalities. -/
theorem fullModN3V4_hmods_of_word_eq
    (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hmod : fullModN3RemainderWordV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    (EvmWord.mod a b).getLimbN 0 =
      (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 1 =
      (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 2 =
      (((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64)) |||
        ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
          ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 3 =
      ((fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
        ((fullDivN3Shift b2).toNat % 64)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmod]
    delta fullModN3RemainderWordV4
    exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hmod]
    delta fullModN3RemainderWordV4
    exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hmod]
    delta fullModN3RemainderWordV4
    exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hmod]
    delta fullModN3RemainderWordV4
    exact EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
