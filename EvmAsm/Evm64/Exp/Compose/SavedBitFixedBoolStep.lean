/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedBoolStep

  Bool-indexed semantic result bridge for one fixed saved-bit EXP iteration.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Concrete accumulator word produced by one fixed-loop iteration, indexed by
    the consumed exponent bit. This packages the skip and cond-mul result
    shapes behind a single Bool for the future induction step. -/
def expTwoMulFixedBranchResult
    (bit : Bool) (a0 a1 a2 a3 r0 r1 r2 r3 : Word) : EvmWord :=
  if bit then
    expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3
  else
    expSquaringCallSquareW r0 r1 r2 r3

theorem expTwoMulFixedBranchResult_false
    (a0 a1 a2 a3 r0 r1 r2 r3 : Word) :
    expTwoMulFixedBranchResult false a0 a1 a2 a3 r0 r1 r2 r3 =
      expSquaringCallSquareW r0 r1 r2 r3 := by
  rfl

theorem expTwoMulFixedBranchResult_true
    (a0 a1 a2 a3 r0 r1 r2 r3 : Word) :
    expTwoMulFixedBranchResult true a0 a1 a2 a3 r0 r1 r2 r3 =
      expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3 := by
  rfl

theorem expTwoMulFixedAccumulatorStep_eq_branchResult
    {baseWord : EvmWord} {bit : Bool}
    {a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hBase : baseWord = expResultWord a0 a1 a2 a3) :
    expTwoMulFixedAccumulatorStep baseWord
        (expResultWord r0 r1 r2 r3) bit =
      expTwoMulFixedBranchResult bit a0 a1 a2 a3 r0 r1 r2 r3 := by
  cases bit
  · exact expTwoMulFixedAccumulatorStep_false_eq_squareW
      baseWord r0 r1 r2 r3
  · exact expTwoMulFixedAccumulatorStep_true_eq_condRw hBase

/-- Bool-unified semantic accumulator successor for the concrete branch result.

    The machine-level one-step proof can establish the output accumulator is
    `expTwoMulFixedBranchResult bit ...`; this lemma advances the semantic
    invariant for either branch without exposing separate skip/cond-mul names
    to the induction theorem. -/
theorem expTwoMulFixedAccumulatorInvariant_succ_of_branchResult
    {baseWord exponentWord : EvmWord} {k : Nat} {bit : Bool}
    {a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hBit : bit = expTwoMulFixedProcessedBit exponentWord k)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 0)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 1)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 2)
      ((expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3).getLimbN 3) := by
  refine
    expTwoMulFixedAccumulatorInvariant_succ_of_step (bit := bit)
      hInv ?_ ?_
  · rw [expResultWord_getLimbN_self]
    exact (expTwoMulFixedAccumulatorStep_eq_branchResult hBase).symm
  · rw [hBit]
    exact expTwoMulFixedAccumulatorStep_eq_target_succ
      baseWord exponentWord hk

end EvmAsm.Evm64.Exp.Compose
