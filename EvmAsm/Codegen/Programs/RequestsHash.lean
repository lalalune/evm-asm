/-
  EvmAsm.Codegen.Programs.RequestsHash

  RISC-V helper for the EIP-7685 execution header `requests_hash`:
  `sha256(concat(sha256(type_byte || request_payload) for non-empty request
  kinds in ascending type order))`.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

def executionRequestsHashFunction : String :=
  "execution_requests_hash:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # SszExecutionRequests section\n" ++
  "  mv s1, a1                   # section length\n" ++
  "  mv s2, a2                   # output hash\n" ++
  "  li t0, 12; bltu s1, t0, .Lerh_fail\n" ++
  "  mv a0, s0; jal ra, bgv_u32le; mv s3, a0\n" ++
  "  addi a0, s0, 4; jal ra, bgv_u32le; mv s4, a0\n" ++
  "  addi a0, s0, 8; jal ra, bgv_u32le; mv s5, a0\n" ++
  "  li t0, 12; bltu s3, t0, .Lerh_fail\n" ++
  "  bltu s4, s3, .Lerh_fail\n" ++
  "  bltu s5, s4, .Lerh_fail\n" ++
  "  bltu s1, s5, .Lerh_fail\n" ++
  "  la s6, erh_digests          # next digest output\n" ++
  "  li s7, 0                    # digest count\n" ++
  "  # deposits: type 0x00, body [s3,s4)\n" ++
  "  sub s8, s4, s3; beqz s8, .Lerh_withdrawals\n" ++
  "  add s9, s0, s3; li s10, 0; jal ra, erh_hash_one\n" ++
  "  addi s6, s6, 32; addi s7, s7, 1\n" ++
  ".Lerh_withdrawals:\n" ++
  "  sub s8, s5, s4; beqz s8, .Lerh_consolidations\n" ++
  "  add s9, s0, s4; li s10, 1; jal ra, erh_hash_one\n" ++
  "  addi s6, s6, 32; addi s7, s7, 1\n" ++
  ".Lerh_consolidations:\n" ++
  "  sub s8, s1, s5; beqz s8, .Lerh_final\n" ++
  "  add s9, s0, s5; li s10, 2; jal ra, erh_hash_one\n" ++
  "  addi s6, s6, 32; addi s7, s7, 1\n" ++
  ".Lerh_final:\n" ++
  "  la a0, erh_digests; slli a1, s7, 5; mv a2, s2; jal ra, zkvm_sha256\n" ++
  "  li a0, 0; j .Lerh_ret\n" ++
  ".Lerh_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lerh_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret\n" ++
  "erh_hash_one:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  la t0, erh_blob; sb s10, 0(t0)\n" ++
  "  addi t1, t0, 1; mv t2, s9; mv t3, s8\n" ++
  ".Lerh_copy:\n" ++
  "  beqz t3, .Lerh_hash\n" ++
  "  lbu t4, 0(t2); sb t4, 0(t1)\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lerh_copy\n" ++
  ".Lerh_hash:\n" ++
  "  la a0, erh_blob; addi a1, s8, 1; mv a2, s6; jal ra, zkvm_sha256\n" ++
  "  ld ra, 0(sp); addi sp, sp, 16; ret"

def executionRequestsHashDataSection : String :=
  ".balign 32\n" ++
  "erh_digests:\n  .zero 96\n" ++
  ".balign 32\n" ++
  "erh_requests_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "erh_blob:\n  .zero 1572865\n"

def executionRequestsHashShaDataSection : String :=
  ".balign 8\n" ++
  "sha256_w_iv:\n" ++
  "  .quad 0xbb67ae856a09e667\n" ++
  "  .quad 0xa54ff53a3c6ef372\n" ++
  "  .quad 0x9b05688c510e527f\n" ++
  "  .quad 0x5be0cd191f83d9ab\n" ++
  ".balign 8\n" ++
  "sha256_w_state:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "sha256_w_input:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "sha256_w_params:\n" ++
  "  .quad sha256_w_state\n" ++
  "  .quad sha256_w_input\n"

end EvmAsm.Codegen
