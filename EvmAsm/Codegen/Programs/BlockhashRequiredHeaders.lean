/-
  EvmAsm.Codegen.Programs.BlockhashRequiredHeaders

  Bytecode scanners for stateless BLOCKHASH witness-depth validation.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## codes_blockhash_required_headers -- conservative BLOCKHASH witness-depth scan.

    Scans SSZ witness.codes bytecode entries for the concrete compiler pattern
    `PUSH1 offset; NUMBER; SUB; BLOCKHASH` (and the commuted
    `NUMBER; PUSH1 offset; SUB; BLOCKHASH` form). Returns the maximum observed
    offset. The top-level verdict uses this only for transaction-bearing blocks
    to reject witnesses whose header list is shorter than a code path can demand,
    matching execution-specs' in-window BLOCKHASH missing-header failure. -/
def codesBlockhashRequiredHeadersFunction : String :=
  "codes_blockhash_required_headers:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                  # witness.codes section ptr\n" ++
  "  mv s1, a1                  # witness.codes section len\n" ++
  "  mv s2, a2                  # max-required-headers out ptr\n" ++
  "  li s5, 0                   # running max offset\n" ++
  "  sd zero, 0(s2)\n" ++
  "  beqz s1, .Lcbrh_ok\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s3, t0, 2             # N = first_offset / 4\n" ++
  "  li s4, 0                   # code index\n" ++
  ".Lcbrh_item_loop:\n" ++
  "  beq s4, s3, .Lcbrh_ok\n" ++
  "  slli t0, s4, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # item start offset\n" ++
  "  add s6, s0, t2             # item start ptr\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lcbrh_use_section_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)              # next item offset\n" ++
  "  j .Lcbrh_have_end_off\n" ++
  ".Lcbrh_use_section_end:\n" ++
  "  mv t4, s1                  # last item ends at section_len\n" ++
  ".Lcbrh_have_end_off:\n" ++
  "  bltu t4, t2, .Lcbrh_fail\n" ++
  "  sub s7, t4, t2             # remaining item bytes\n" ++
  "  li t5, 5\n" ++
  "  bltu s7, t5, .Lcbrh_next_item\n" ++
  ".Lcbrh_scan_loop:\n" ++
  "  li t5, 5\n" ++
  "  bltu s7, t5, .Lcbrh_next_item\n" ++
  "  lbu t0, 0(s6)\n" ++
  "  li t1, 0x60\n" ++
  "  beq t0, t1, .Lcbrh_try_push_number_sub\n" ++
  "  li t1, 0x43\n" ++
  "  beq t0, t1, .Lcbrh_try_number_push_sub\n" ++
  "  j .Lcbrh_advance\n" ++
  ".Lcbrh_try_push_number_sub:\n" ++
  "  lbu t2, 2(s6); li t3, 0x43; bne t2, t3, .Lcbrh_advance\n" ++
  "  lbu t2, 3(s6); li t3, 0x03; bne t2, t3, .Lcbrh_advance\n" ++
  "  lbu t2, 4(s6); li t3, 0x40; bne t2, t3, .Lcbrh_advance\n" ++
  "  lbu t4, 1(s6)              # offset\n" ++
  "  bleu t4, s5, .Lcbrh_advance\n" ++
  "  mv s5, t4\n" ++
  "  j .Lcbrh_advance\n" ++
  ".Lcbrh_try_number_push_sub:\n" ++
  "  lbu t2, 1(s6); li t3, 0x60; bne t2, t3, .Lcbrh_advance\n" ++
  "  lbu t2, 3(s6); li t3, 0x03; bne t2, t3, .Lcbrh_advance\n" ++
  "  lbu t2, 4(s6); li t3, 0x40; bne t2, t3, .Lcbrh_advance\n" ++
  "  lbu t4, 2(s6)              # offset\n" ++
  "  bleu t4, s5, .Lcbrh_advance\n" ++
  "  mv s5, t4\n" ++
  ".Lcbrh_advance:\n" ++
  "  addi s6, s6, 1\n" ++
  "  addi s7, s7, -1\n" ++
  "  j .Lcbrh_scan_loop\n" ++
  ".Lcbrh_next_item:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lcbrh_item_loop\n" ++
  ".Lcbrh_ok:\n" ++
  "  sd s5, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcbrh_ret\n" ++
  ".Lcbrh_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lcbrh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

end EvmAsm.Codegen
