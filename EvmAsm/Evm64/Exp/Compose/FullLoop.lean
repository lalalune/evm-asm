/-
  EvmAsm.Evm64.Exp.Compose.FullLoop

  Small full-loop prep helpers for EXP.  The static EXP body contains JALs to
  the out-of-line `mul_callable`, so full-loop composition needs a code bundle
  that contains both the top-level EXP program and the callable multiply body.
-/

import EvmAsm.Evm64.Exp.Compose.TopCodeSpecs
import EvmAsm.Evm64.Multiply.Callable

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Code required by the top-level EXP program plus the external
    `mul_callable` body reached by both JALs in one loop iteration. -/
abbrev evmExpWithMulCode (base mulTarget : Word)
    (mulOff : BitVec 21) (skipOff backOff : BitVec 13) : CodeReq :=
  (evmExpCode base mulOff skipOff backOff).union (mul_callable_code mulTarget)

theorem evmExpWithMulCode_exp_sub {base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (evmExpCode base mulOff skipOff backOff) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i := by
  unfold evmExpWithMulCode
  exact CodeReq.union_mono_left

theorem evmExpWithMulCode_mul_sub {base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (evmExpCode base mulOff skipOff backOff) (mul_callable_code mulTarget)) :
    ∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i := by
  unfold evmExpWithMulCode
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

/-- Lift a top-level EXP-body spec into the combined EXP+MUL code bundle. -/
theorem cpsTripleWithin_extend_evmExpWithMulCode {nSteps : Nat}
    {entry exit_ base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_
      (evmExpCode base mulOff skipOff backOff) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code (hmono := evmExpWithMulCode_exp_sub) h

/-- Lift a multiply-callable spec into the combined EXP+MUL code bundle. -/
theorem cpsTripleWithin_extend_mulCallable_evmExpWithMulCode {nSteps : Nat}
    {entry exit_ base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (hd : CodeReq.Disjoint
      (evmExpCode base mulOff skipOff backOff) (mul_callable_code mulTarget))
    (h : cpsTripleWithin nSteps entry exit_ (mul_callable_code mulTarget) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpWithMulCode_mul_sub (base := base) (mulTarget := mulTarget)
      (mulOff := mulOff) (skipOff := skipOff) (backOff := backOff) hd)
    h

theorem evmExpWithMulCode_block_subs {base mulTarget : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (evmExpCode base mulOff skipOff backOff) (mul_callable_code mulTarget)) :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_prologue) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 24)
      EvmAsm.Evm64.exp_loop_pointer_advance) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (expIterBodyFullCode (base + 28) mulOff skipOff backOff) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 260)
      EvmAsm.Evm64.exp_loop_pointer_restore) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 264) EvmAsm.Evm64.exp_epilogue) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i) ∧
    (∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpWithMulCode base mulTarget mulOff skipOff backOff) a = some i) := by
  rcases evmExpCode_block_subs (base := base) (mulOff := mulOff)
      (skipOff := skipOff) (backOff := backOff) with
    ⟨h_prologue, h_pointer_advance, h_iter, h_pointer_restore, h_epilogue⟩
  exact
    ⟨fun a i h => evmExpWithMulCode_exp_sub a i (h_prologue a i h),
     fun a i h => evmExpWithMulCode_exp_sub a i (h_pointer_advance a i h),
     fun a i h => evmExpWithMulCode_exp_sub a i (h_iter a i h),
     fun a i h => evmExpWithMulCode_exp_sub a i (h_pointer_restore a i h),
     fun a i h => evmExpWithMulCode_exp_sub a i (h_epilogue a i h),
     evmExpWithMulCode_mul_sub hd⟩

end EvmAsm.Evm64.Exp.Compose
