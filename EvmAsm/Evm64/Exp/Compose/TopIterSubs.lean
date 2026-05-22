/-
  EvmAsm.Evm64.Exp.Compose.TopIterSubs

  Iteration sub-block inclusion lemmas for the top-level EXP code bundles.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBase
import EvmAsm.Evm64.Exp.Compose.EvmExpCode
import EvmAsm.Evm64.Exp.AddrNorm

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem expTopSavedBitLoopBackNextPc (base : Word) :
    ((base + 256 : Word) + 8) = base + 264 := by
  bv_omega

/-- Bit-test sub-block directly included in the top-level EXP code bundle. -/
theorem evmExpCode_iter_bit_test_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 28) EvmAsm.Evm64.exp_bit_test_block) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_bit_test_sub a i h)

/-- Squaring-call sub-block directly included in the top-level EXP code bundle. -/
theorem evmExpCode_iter_squaring_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (exp_squaring_call_block_code (base + 40) mulOff) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterSquaringAddr] at h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_squaring_sub a i h)

/-- Conditional-multiply sub-block directly included in the top-level EXP code
    bundle. -/
theorem evmExpCode_iter_cond_mul_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_skip_block_code
      (base + 144) mulOff skipOff) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterCondMulAddr] at h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_cond_mul_sub a i h)

/-- MSB bit-test sub-block directly included in the corrected saved-bit
    top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_bit_test_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 28) EvmAsm.Evm64.exp_msb_bit_test_block)
      a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_bit_test_sub a i h)

/-- Save-bit sub-block directly included in the corrected saved-bit top-level
    EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_save_bit_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 40) EvmAsm.Evm64.exp_save_bit_block)
      a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterSquaringAddr] at h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_save_bit_sub a i h)

/-- Squaring-call sub-block directly included in the corrected saved-bit
    top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_squaring_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (exp_squaring_call_block_code (base + 44) mulOff) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterSavedBitSquaringAddr] at h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_squaring_sub a i h)

/-- Saved-bit conditional-multiply sub-block directly included in the
    corrected saved-bit top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_cond_mul_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 148) mulOff skipOff) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterSavedBitCondMulAddr] at h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_cond_mul_sub a i h)

/-- Saved-bit loop-back sub-block directly included in the corrected saved-bit
    top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_iter_loop_back_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 256)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterSavedBitLoopBackAddr] at h
  exact evmExpMsbSavedBitCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitCode_loop_back_sub a i h)

theorem evmExpMsbSavedBitTwoMulCode_iter_loop_back_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 256)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (evmExpMsbSavedBitTwoMulCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterSavedBitLoopBackAddr] at h
  exact evmExpMsbSavedBitTwoMulCode_iter_body_sub a i
    (expIterBodyFullMsbSavedBitTwoMulCode_loop_back_sub a i h)

/-- Saved-bit conditional-multiply BEQ skip-gate directly included in the
    corrected saved-bit top-level EXP code bundle. -/
theorem evmExpMsbSavedBitCode_cond_mul_beq_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.singleton (base + 148) (.BEQ .x18 .x0 skipOff))
      a = some i →
      (evmExpMsbSavedBitCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  exact evmExpMsbSavedBitCode_iter_cond_mul_sub a i
    (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_beq_sub
      (base + 148) mulOff skipOff a i h)

/-- Loop-back sub-block directly included in the top-level EXP code bundle. -/
theorem evmExpCode_iter_loop_back_sub {base : Word}
    {mulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 252)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (evmExpCode base mulOff skipOff backOff) a = some i := by
  intro a i h
  rw [EvmAsm.Evm64.Exp.AddrNorm.expTopIterLoopBackAddr] at h
  exact evmExpCode_iter_body_sub a i (expIterBodyFullCode_loop_back_sub a i h)

end EvmAsm.Evm64.Exp.Compose
