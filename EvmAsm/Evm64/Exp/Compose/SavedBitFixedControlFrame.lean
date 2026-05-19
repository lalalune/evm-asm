/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedControlFrame

  Small control-invariant helpers for the fixed-loop induction frame.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expTwoMulFixedSavedNextLimbFrame
    (ptr nextNextLimb : Word) : Assertion :=
  (((ptr + signExtend12 (-8 : BitVec 12)) +
    signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)

theorem expTwoMulFixedSavedNextLimbFrame_unfold
    {ptr nextNextLimb : Word} :
    expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
      ((((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) := by
  delta expTwoMulFixedSavedNextLimbFrame
  rfl

theorem expTwoMulFixedSavedNextLimbFrame_pcFree
    (ptr nextNextLimb : Word) :
    (expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb).pcFree := by
  rw [expTwoMulFixedSavedNextLimbFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedSavedNextLimbFrame
    (ptr nextNextLimb : Word) :
    Assertion.PCFree
      (expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb) :=
  ⟨expTwoMulFixedSavedNextLimbFrame_pcFree ptr nextNextLimb⟩

@[irreducible]
def expTwoMulFixedSavedNextLimbFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr : Word) : Assertion :=
  expTwoMulFixedSavedNextLimbFrame ptr
    (exponentWord.getLimbN (2 - (k + 1) / 64))

theorem expTwoMulFixedSavedNextLimbFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr : Word} :
    expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr =
      expTwoMulFixedSavedNextLimbFrame ptr
        (exponentWord.getLimbN (2 - (k + 1) / 64)) := by
  delta expTwoMulFixedSavedNextLimbFrameN
  rfl

theorem expTwoMulFixedSavedNextLimbFrameN_eq_of_nextNext
    {exponentWord : EvmWord} {k : Nat} {ptr nextNextLimb : Word}
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
      expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr := by
  rw [expTwoMulFixedSavedNextLimbFrameN_unfold, hNextNext]

theorem expTwoMulFixedSavedNextLimbFrameN_succ_no_reload
    {exponentWord : EvmWord} {k : Nat} {ptr : Word}
    (hMod : k % 64 < 62) :
    expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr =
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr := by
  rw [expTwoMulFixedSavedNextLimbFrameN_unfold,
    expTwoMulFixedSavedNextLimbFrameN_unfold]
  congr 1
  congr 1
  have hdiv : (k + 2) / 64 = (k + 1) / 64 := by
    omega
  rw [show (k + 1 + 1) / 64 = (k + 2) / 64 by omega, hdiv]

theorem expTwoMulFixedControlInvariant_nextLimb
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp) :
    nextLimb = exponentWord.getLimbN (2 - k / 64) := by
  exact hControl.2

theorem expTwoMulFixedControlInvariant_nextLimb_succ_no_reload
    {exponentWord : EvmWord} {k : Nat}
    {c6 ptr nextLimb evmSp : Word}
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    nextLimb = exponentWord.getLimbN (2 - (k + 1) / 64) := by
  have hMod :=
    expTwoMulFixedControlInvariant_no_reload_mod hControl hC6
  rw [expTwoMulFixedControlInvariant_nextLimb hControl]
  have hdiv : (k + 1) / 64 = k / 64 := by
    omega
  rw [hdiv]

end EvmAsm.Evm64.Exp.Compose
