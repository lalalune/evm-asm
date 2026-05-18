/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulFixedIter

  CodeReq decomposition for the fixed x19 two-MUL saved-bit EXP iteration.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulIter

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- CodeReq decomposition for the fixed saved-bit iteration with separate
    MUL-call offsets at the squaring and conditional-multiply JAL sites. -/
abbrev expIterBodyFullMsbSavedBitTwoMulFixedCode (base : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : CodeReq :=
  CodeReq.unionAll [
    CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block_fixed,
    CodeReq.ofProg (base + 28) EvmAsm.Evm64.exp_save_bit_block,
    exp_squaring_call_block_code (base + 32) squaringMulOff,
    EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 136) condMulOff skipOff,
    CodeReq.ofProg (base + 244) (EvmAsm.Evm64.exp_loop_back backOff)
  ]

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg (base : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13) :
    expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff =
      CodeReq.ofProg base
        (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
          squaringMulOff condMulOff skipOff backOff) := by
  unfold expIterBodyFullMsbSavedBitTwoMulFixedCode
  unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
  simp only [EvmAsm.Rv64.seq]
  unfold Program
  rw [CodeReq.ofProg_append]
  have h28 :
      base + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_msb_bit_test_block_fixed).length) = base + 28 := by
    rw [EvmAsm.Evm64.exp_msb_bit_test_block_fixed_length]
    rfl
  rw [h28]
  rw [CodeReq.ofProg_append]
  have h32 :
      (base + 28 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_save_bit_block).length) = base + 32 := by
    rw [EvmAsm.Evm64.exp_save_bit_block_length]
    bv_addr
  rw [h32]
  rw [CodeReq.ofProg_append]
  have h136 :
      (base + 32 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_squaring_call_block squaringMulOff).length) =
        base + 136 := by
    rw [EvmAsm.Evm64.exp_squaring_call_block_length]
    bv_addr
  rw [h136]
  rw [CodeReq.ofProg_append]
  have h244 :
      (base + 136 : Word) + BitVec.ofNat 64 (4 *
        (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block
          condMulOff skipOff).length) = base + 244 := by
    rw [EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_length]
    bv_addr
  rw [h244]
  rw [← exp_squaring_call_block_code_eq_ofProg (base + 32) squaringMulOff]
  rw [← EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg
    (base + 136) condMulOff skipOff]
  simp only [CodeReq.unionAll_cons, CodeReq.unionAll_nil, CodeReq.union_empty_right]

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_bit_test_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block_fixed)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base base
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_msb_bit_test_block_fixed 0
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_msb_bit_test_block_fixed_length])
    (by simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length])

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_save_bit_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 28) EvmAsm.Evm64.exp_save_bit_block)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 28)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    EvmAsm.Evm64.exp_save_bit_block 7
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_save_bit_block_length])
    (by simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length])

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_squaring_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (exp_squaring_call_block_code (base + 32) squaringMulOff)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg,
    exp_squaring_call_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 32)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_squaring_call_block squaringMulOff) 8
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_squaring_call_block_length])
    (by simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length])

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_cond_mul_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 136) condMulOff skipOff) a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg,
    EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 136)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block
      condMulOff skipOff) 34
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_length])
    (by simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length])

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_loop_back_sub {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (CodeReq.ofProg (base + 244)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg]
  exact CodeReq.ofProg_mono_sub base (base + 244)
    (EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      squaringMulOff condMulOff skipOff backOff)
    (EvmAsm.Evm64.exp_loop_back backOff) 61
    (by bv_omega)
    (by
      unfold EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed
      simp only [EvmAsm.Rv64.seq]
      unfold Program
      rfl)
    (by
      simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length,
        EvmAsm.Evm64.exp_loop_back_length])
    (by simp [EvmAsm.Evm64.exp_iter_body_full_msb_saved_bit_two_mul_fixed_length])

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_block_subs {base : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    (∀ a i, (CodeReq.ofProg base EvmAsm.Evm64.exp_msb_bit_test_block_fixed)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 28) EvmAsm.Evm64.exp_save_bit_block)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (exp_squaring_call_block_code (base + 32) squaringMulOff)
      a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (EvmAsm.Evm64.exp_cond_mul_call_with_saved_bit_skip_block_code
      (base + 136) condMulOff skipOff) a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) ∧
    (∀ a i, (CodeReq.ofProg (base + 244)
      (EvmAsm.Evm64.exp_loop_back backOff)) a = some i →
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) a = some i) := by
  exact ⟨expIterBodyFullMsbSavedBitTwoMulFixedCode_bit_test_sub,
    expIterBodyFullMsbSavedBitTwoMulFixedCode_save_bit_sub,
    expIterBodyFullMsbSavedBitTwoMulFixedCode_squaring_sub,
    expIterBodyFullMsbSavedBitTwoMulFixedCode_cond_mul_sub,
    expIterBodyFullMsbSavedBitTwoMulFixedCode_loop_back_sub⟩

end EvmAsm.Evm64.Exp.Compose
