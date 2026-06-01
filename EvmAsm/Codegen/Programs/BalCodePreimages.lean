/-
  EvmAsm.Codegen.Programs.BalCodePreimages

  BAL-scoped witness.codes preimage gate for the stateless verdict.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.StateCompose

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_code_preimages_valid -- reject code-read-shaped accounts whose
    non-empty code_hash is absent from witness.codes.

    This mirrors the executable spec shape where `build_code_db(witness.codes)`
    maps `keccak(code) -> code`, and `WitnessState.get_code` raises if an
    executing or EXTCODE-touched account's non-empty code_hash is not present.
    The helper is deliberately narrow: balance/nonce-only BAL entries do not
    prove that account bytecode was read, so they are skipped. Pure
    account-touch rows are skipped only when `bbcv_skip_touch_only` is set by
    the caller for withdrawal-only blocks. A pure account-touch row whose
    pre-state code hash is exactly keccak(0x00) is also skipped: EIP-7708
    selfdestruct beneficiaries can have one-byte STOP code without requiring
    the bytecode preimage. A pure account-touch row is also accepted when a
    pure account-touch row for the block fee recipient is also skipped:
    Amsterdam warms/touches coinbase without reading its bytecode. A
    literal `PUSH20 <address>; EXTCODEHASH` occurs in witness bytecode, since
    EXTCODEHASH reads the account leaf's code_hash and does not call
    WitnessState.get_code. Rows that carry storage or code activity still
    reject the extcodesize helper's status 5 and leave deeper obligations for
    later gates. -/
def balCodePreimagesValidFunction : String :=
  "bal_code_preimages_valid:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # BAL ptr\n" ++
  "  mv s1, a1                   # BAL len\n" ++
  "  mv s2, a2                   # parent header RLP ptr\n" ++
  "  mv s3, a3                   # parent header RLP len\n" ++
  "  mv s4, a4                   # witness.state ptr\n" ++
  "  mv s5, a5                   # witness.state len\n" ++
  "  mv s6, a6                   # witness.codes ptr\n" ++
  "  mv s7, a7                   # witness.codes len\n" ++
  "  mv a0, s0; mv a1, s1; la a2, bbcv_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_count; ld s8, 0(t0)\n" ++
  "  li s9, 0\n" ++
  ".Lbbcv_loop:\n" ++
  "  beq s9, s8, .Lbbcv_ok\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s9; la a3, bbcv_off; la a4, bbcv_size\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_off; ld t1, 0(t0); add s10, s0, t1\n" ++
  "  la t0, bbcv_size; ld t1, 0(t0); la t2, bbcv_acct_len; sd t1, 0(t2)\n" ++
  "  mv a0, s10; mv a1, t1; li a2, 0; la a3, bbcv_addr_off; la a4, bbcv_addr_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_addr_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lbbcv_parse_fail\n" ++
  "  li t1, 1; la t0, bbcv_touch_only; sd t1, 0(t0)\n" ++
  "  # Balance/nonce-only BAL entries record scalar account effects and do\n" ++
  "  # not imply that account bytecode was read. Pure account-touch rows\n" ++
  "  # are skipped only when the caller marks withdrawal-only mode.\n" ++
  "  mv a0, s10; la t0, bbcv_acct_len; ld a1, 0(t0); li a2, 1; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s10, t1; la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0); bnez t1, .Lbbcv_check_code_non_touch\n" ++
  "  mv a0, s10; la t0, bbcv_acct_len; ld a1, 0(t0); li a2, 2; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s10, t1; la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0); bnez t1, .Lbbcv_check_code_non_touch\n" ++
  "  mv a0, s10; la t0, bbcv_acct_len; ld a1, 0(t0); li a2, 3; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s10, t1; la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0)\n" ++
  "  la t2, bbcv_balance_count; sd t1, 0(t2)\n" ++
  "  mv a0, s10; la t0, bbcv_acct_len; ld a1, 0(t0); li a2, 4; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s10, t1; la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0)\n" ++
  "  la t2, bbcv_nonce_count; sd t1, 0(t2)\n" ++
  "  mv a0, s10; la t0, bbcv_acct_len; ld a1, 0(t0); li a2, 5; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s10, t1; la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0); bnez t1, .Lbbcv_check_code_non_touch\n" ++
  "  la t0, bbcv_balance_count; ld t1, 0(t0)\n" ++
  "  la t2, bbcv_nonce_count; ld t3, 0(t2)\n" ++
  "  or t4, t1, t3\n" ++
  "  bnez t4, .Lbbcv_next\n" ++
  "  la t0, bbcv_fee_recipient_valid; ld t0, 0(t0); beqz t0, .Lbbcv_touch_skip_flags\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add t1, s10, t1\n" ++
  "  la t2, bbcv_fee_recipient\n" ++
  "  li t3, 20\n" ++
  ".Lbbcv_fee_recipient_cmp:\n" ++
  "  beqz t3, .Lbbcv_next\n" ++
  "  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lbbcv_touch_skip_flags\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbbcv_fee_recipient_cmp\n" ++
  ".Lbbcv_touch_skip_flags:\n" ++
  "  la t0, bbcv_skip_touch_only; ld t4, 0(t0)\n" ++
  "  bnez t4, .Lbbcv_next\n" ++
  "  j .Lbbcv_check_code\n" ++
  ".Lbbcv_check_code_non_touch:\n" ++
  "  la t0, bbcv_touch_only; sd zero, 0(t0)\n" ++
  ".Lbbcv_check_code:\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a2, s10, t1\n" ++
  "  mv a0, s2; mv a1, s3; mv a3, s4; mv a4, s5; mv a5, s6; mv a6, s7\n" ++
  "  jal ra, extcodesize_at_header_state_root\n" ++
  "  li t0, 5; beq a0, t0, .Lbbcv_maybe_stop_touch\n" ++
  ".Lbbcv_next:\n" ++
  "  addi s9, s9, 1; j .Lbbcv_loop\n" ++
  ".Lbbcv_ok:\n" ++
  "  li a0, 0; j .Lbbcv_ret\n" ++
  ".Lbbcv_maybe_stop_touch:\n" ++
  "  la t0, bbcv_touch_only; ld t1, 0(t0); beqz t1, .Lbbcv_missing_code\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a2, s10, t1\n" ++
  "  mv a0, s2; mv a1, s3; mv a3, s4; mv a4, s5; la a5, bbcv_code_hash\n" ++
  "  jal ra, code_hash_at_header_state_root\n" ++
  "  bnez a0, .Lbbcv_missing_code\n" ++
  "  la t0, bbcv_code_hash; la t1, bbcv_stop_code_hash\n" ++
  "  ld t2, 0(t0); ld t3, 0(t1); bne t2, t3, .Lbbcv_check_extcodehash_literal\n" ++
  "  ld t2, 8(t0); ld t3, 8(t1); bne t2, t3, .Lbbcv_check_extcodehash_literal\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbbcv_check_extcodehash_literal\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbbcv_check_extcodehash_literal\n" ++
  "  j .Lbbcv_next\n" ++
  ".Lbbcv_check_extcodehash_literal:\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a2, s10, t1\n" ++
  "  mv a0, s6; mv a1, s7\n" ++
  "  jal ra, bal_codes_contains_push20_extcodehash\n" ++
  "  bnez a0, .Lbbcv_next\n" ++
  "  j .Lbbcv_missing_code\n" ++
  ".Lbbcv_missing_code:\n" ++
  "  li a0, 1; j .Lbbcv_ret\n" ++
  ".Lbbcv_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbbcv_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret\n" ++
  "\n" ++
  "# Return 1 iff any witness code contains PUSH20 <addr>; EXTCODEHASH.\n" ++
  "# This recognizes the EIP-8025 optional-proof case where EXTCODEHASH only\n" ++
  "# needs account.code_hash from the trie leaf, not the bytecode preimage.\n" ++
  "bal_codes_contains_push20_extcodehash:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp)\n" ++
  "  sd s3, 24(sp); sd s4, 32(sp); sd s5, 40(sp)\n" ++
  "  mv s0, a0                  # witness.codes section ptr\n" ++
  "  mv s1, a1                  # witness.codes section len\n" ++
  "  mv s2, a2                  # 20-byte target address ptr\n" ++
  "  beqz s1, .Lbce_no\n" ++
  "  lwu t0, 0(s0)              # first element offset = 4*N\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0\n" ++
  ".Lbce_elem_loop:\n" ++
  "  beq s4, s3, .Lbce_no\n" ++
  "  slli t0, s4, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # element offset\n" ++
  "  add s5, s0, t2             # element start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lbce_elem_end_section\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # element end\n" ++
  "  j .Lbce_have_elem_end\n" ++
  ".Lbce_elem_end_section:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lbce_have_elem_end:\n" ++
  "  sub t4, t4, s5             # element len\n" ++
  "  li t5, 22\n" ++
  "  bltu t4, t5, .Lbce_next_elem\n" ++
  "  sub t6, t4, t5             # max start offset\n" ++
  "  li t0, 0                   # scan offset\n" ++
  ".Lbce_scan_loop:\n" ++
  "  bgtu t0, t6, .Lbce_next_elem\n" ++
  "  add t1, s5, t0\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  li t3, 0x73                # PUSH20\n" ++
  "  bne t2, t3, .Lbce_advance_scan\n" ++
  "  li t3, 0                   # address byte index\n" ++
  ".Lbce_addr_loop:\n" ++
  "  li t2, 20\n" ++
  "  beq t3, t2, .Lbce_check_opcode\n" ++
  "  add t4, t1, t3\n" ++
  "  lbu t4, 1(t4)\n" ++
  "  add t5, s2, t3\n" ++
  "  lbu t5, 0(t5)\n" ++
  "  bne t4, t5, .Lbce_advance_scan\n" ++
  "  addi t3, t3, 1\n" ++
  "  j .Lbce_addr_loop\n" ++
  ".Lbce_check_opcode:\n" ++
  "  lbu t4, 21(t1)\n" ++
  "  li t5, 0x3f                # EXTCODEHASH\n" ++
  "  beq t4, t5, .Lbce_yes\n" ++
  ".Lbce_advance_scan:\n" ++
  "  addi t0, t0, 1\n" ++
  "  j .Lbce_scan_loop\n" ++
  ".Lbce_next_elem:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lbce_elem_loop\n" ++
  ".Lbce_yes:\n" ++
  "  li a0, 1; j .Lbce_ret\n" ++
  ".Lbce_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbce_ret:\n" ++
  "  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp)\n" ++
  "  ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

end EvmAsm.Codegen
