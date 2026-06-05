/-
  EvmAsm.Codegen.Programs.Modexp

  EIP-2565 / Osaka MODEXP gas helpers extracted from Noop.lean to keep
  that file under the 1500-line hard cap.
-/

import EvmAsm.Codegen.Programs.PrecompileRuntime

namespace EvmAsm.Codegen

def modexpReadLengthAsm (suffix : String) (fieldOff : Nat) (dstReg : String) : String :=
  "  li " ++ dstReg ++ ", 0\n" ++
  "  li x29, 0\n" ++
  ".Lmodexp_len_loop_" ++ suffix ++ "_" ++ toString fieldOff ++ ":\n" ++
  "  li x31, 32\n" ++
  "  beq x29, x31, .Lmodexp_len_done_" ++ suffix ++ "_" ++ toString fieldOff ++ "\n" ++
  "  addi x31, x29, " ++ toString fieldOff ++ "\n" ++
  "  bgeu x31, x17, .Lmodexp_len_missing_" ++ suffix ++ "_" ++ toString fieldOff ++ "\n" ++
  "  add x31, x18, x31\n" ++
  "  lbu x16, 0(x31)\n" ++
  "  j .Lmodexp_len_have_byte_" ++ suffix ++ "_" ++ toString fieldOff ++ "\n" ++
  ".Lmodexp_len_missing_" ++ suffix ++ "_" ++ toString fieldOff ++ ":\n" ++
  "  li x16, 0\n" ++
  ".Lmodexp_len_have_byte_" ++ suffix ++ "_" ++ toString fieldOff ++ ":\n" ++
  "  li x31, 30\n" ++
  "  bltu x29, x31, .Lmodexp_len_high_" ++ suffix ++ "_" ++ toString fieldOff ++ "\n" ++
  "  slli " ++ dstReg ++ ", " ++ dstReg ++ ", 8\n" ++
  "  or " ++ dstReg ++ ", " ++ dstReg ++ ", x16\n" ++
  "  j .Lmodexp_len_next_" ++ suffix ++ "_" ++ toString fieldOff ++ "\n" ++
  ".Lmodexp_len_high_" ++ suffix ++ "_" ++ toString fieldOff ++ ":\n" ++
  "  bnez x16, 1f\n" ++
  ".Lmodexp_len_next_" ++ suffix ++ "_" ++ toString fieldOff ++ ":\n" ++
  "  addi x29, x29, 1\n" ++
  "  j .Lmodexp_len_loop_" ++ suffix ++ "_" ++ toString fieldOff ++ "\n" ++
  ".Lmodexp_len_done_" ++ suffix ++ "_" ++ toString fieldOff ++ ":\n" ++
  "  li x31, 1024\n" ++
  "  bltu x31, " ++ dstReg ++ ", 1f\n"

def modexpByteLog2Asm (suffix : String) : String :=
  "  li x31, 128\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_7_" ++ suffix ++ "\n" ++
  "  li x31, 64\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_6_" ++ suffix ++ "\n" ++
  "  li x31, 32\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_5_" ++ suffix ++ "\n" ++
  "  li x31, 16\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_4_" ++ suffix ++ "\n" ++
  "  li x31, 8\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_3_" ++ suffix ++ "\n" ++
  "  li x31, 4\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_2_" ++ suffix ++ "\n" ++
  "  li x31, 2\n" ++
  "  bgeu x16, x31, .Lmodexp_log2_1_" ++ suffix ++ "\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_7_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 7\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_6_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 6\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_5_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 5\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_4_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 4\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_3_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 3\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_2_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 2\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_log2_1_" ++ suffix ++ ":\n" ++
  "  addi x27, x27, 1\n" ++
  "  j .Lmodexp_log_done_" ++ suffix ++ "\n"

def modexpPrecompileGasAsm
    (suffix : String) (inOffsetOff inSizeOff : Nat) : String :=
  "  la x15, evm_precompile_frame\n" ++
  "  li x16, 1\n" ++
  "  sd x16, 0(x15)\n" ++
  "  sd x0, 8(x15)\n" ++
  "  ld x17, " ++ toString inSizeOff ++ "(x12)\n" ++
  "  ld x18, " ++ toString inOffsetOff ++ "(x12)\n" ++
  "  add x18, x13, x18\n" ++
  modexpReadLengthAsm suffix 0 "x21" ++
  modexpReadLengthAsm suffix 32 "x22" ++
  modexpReadLengthAsm suffix 64 "x23" ++
  "  mv x24, x21\n" ++
  "  bgeu x24, x23, .Lmodexp_max_done_" ++ suffix ++ "\n" ++
  "  mv x24, x23\n" ++
  ".Lmodexp_max_done_" ++ suffix ++ ":\n" ++
  "  addi x25, x24, 7\n" ++
  "  srli x25, x25, 3\n" ++
  "  li x31, 32\n" ++
  "  bltu x31, x24, .Lmodexp_complex_large_" ++ suffix ++ "\n" ++
  "  li x26, 16\n" ++
  "  j .Lmodexp_complex_done_" ++ suffix ++ "\n" ++
  ".Lmodexp_complex_large_" ++ suffix ++ ":\n" ++
  "  mul x26, x25, x25\n" ++
  "  slli x26, x26, 1\n" ++
  ".Lmodexp_complex_done_" ++ suffix ++ ":\n" ++
  "  li x27, 0\n" ++
  "  li x30, 0\n" ++
  "  mv x28, x22\n" ++
  "  li x31, 32\n" ++
  "  bgeu x31, x28, .Lmodexp_head_len_done_" ++ suffix ++ "\n" ++
  "  mv x28, x31\n" ++
  ".Lmodexp_head_len_done_" ++ suffix ++ ":\n" ++
  "  li x29, 0\n" ++
  ".Lmodexp_head_loop_" ++ suffix ++ ":\n" ++
  "  beq x29, x28, .Lmodexp_head_done_zero_" ++ suffix ++ "\n" ++
  "  addi x31, x21, 96\n" ++
  "  add x31, x31, x29\n" ++
  "  bgeu x31, x17, .Lmodexp_head_missing_" ++ suffix ++ "\n" ++
  "  add x31, x18, x31\n" ++
  "  lbu x16, 0(x31)\n" ++
  "  j .Lmodexp_head_have_byte_" ++ suffix ++ "\n" ++
  ".Lmodexp_head_missing_" ++ suffix ++ ":\n" ++
  "  li x16, 0\n" ++
  ".Lmodexp_head_have_byte_" ++ suffix ++ ":\n" ++
  "  bnez x16, .Lmodexp_head_nonzero_" ++ suffix ++ "\n" ++
  "  addi x29, x29, 1\n" ++
  "  j .Lmodexp_head_loop_" ++ suffix ++ "\n" ++
  ".Lmodexp_head_nonzero_" ++ suffix ++ ":\n" ++
  "  li x30, 1\n" ++
  "  sub x27, x28, x29\n" ++
  "  addi x27, x27, -1\n" ++
  "  slli x27, x27, 3\n" ++
  modexpByteLog2Asm suffix ++
  ".Lmodexp_head_done_zero_" ++ suffix ++ ":\n" ++
  ".Lmodexp_log_done_" ++ suffix ++ ":\n" ++
  "  li x31, 32\n" ++
  "  bltu x31, x22, .Lmodexp_iter_large_exp_" ++ suffix ++ "\n" ++
  "  beqz x30, .Lmodexp_iter_zero_head_" ++ suffix ++ "\n" ++
  "  mv x28, x27\n" ++
  "  j .Lmodexp_iter_max_" ++ suffix ++ "\n" ++
  ".Lmodexp_iter_large_exp_" ++ suffix ++ ":\n" ++
  "  addi x28, x22, -32\n" ++
  "  slli x28, x28, 4\n" ++
  "  add x28, x28, x27\n" ++
  "  j .Lmodexp_iter_max_" ++ suffix ++ "\n" ++
  ".Lmodexp_iter_zero_head_" ++ suffix ++ ":\n" ++
  "  li x28, 0\n" ++
  ".Lmodexp_iter_max_" ++ suffix ++ ":\n" ++
  "  bnez x28, .Lmodexp_iter_done_" ++ suffix ++ "\n" ++
  "  li x28, 1\n" ++
  ".Lmodexp_iter_done_" ++ suffix ++ ":\n" ++
  "  mul x16, x26, x28\n" ++
  "  li x31, 500\n" ++
  "  bgeu x16, x31, .Lmodexp_cost_done_" ++ suffix ++ "\n" ++
  "  mv x16, x31\n" ++
  ".Lmodexp_cost_done_" ++ suffix ++ ":\n" ++
  chargePrecompileGasAsm "x16" "x31" ++
  "  or x24, x21, x23\n" ++
  "  beqz x24, 7b\n" ++
  "  j 1f\n"


end EvmAsm.Codegen
