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
    The helper is deliberately narrow: balance-only and nonce-only BAL entries
    are transfer/account-creation effects, not code reads, so they are skipped.
    All other BAL entries still reject the extcodesize helper's status 5 and
    leave deeper obligations for later gates. -/
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
  "  # Balance-only / nonce-only BAL entries record transfer/account-creation\n" ++
  "  # effects and do not imply that the account bytecode was read.\n" ++
  "  # Skip exactly [addr, [], [], nonempty_balance_changes, [], []] or\n" ++
  "  # [addr, [], [], [], nonempty_nonce_changes, []].\n" ++
  "  mv a0, s10; la t0, bbcv_acct_len; ld a1, 0(t0); li a2, 1; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s10, t1; la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0); bnez t1, .Lbbcv_check_code\n" ++
  "  mv a0, s10; la t0, bbcv_acct_len; ld a1, 0(t0); li a2, 2; la a3, bbcv_field_off; la a4, bbcv_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_off; ld t1, 0(t0); add a0, s10, t1; la t0, bbcv_field_len; ld a1, 0(t0); la a2, bbcv_field_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbcv_parse_fail\n" ++
  "  la t0, bbcv_field_count; ld t1, 0(t0); bnez t1, .Lbbcv_check_code\n" ++
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
  "  la t0, bbcv_field_count; ld t1, 0(t0); bnez t1, .Lbbcv_check_code\n" ++
  "  la t0, bbcv_balance_count; ld t1, 0(t0)\n" ++
  "  la t2, bbcv_nonce_count; ld t3, 0(t2)\n" ++
  "  beqz t1, .Lbbcv_maybe_nonce_only\n" ++
  "  beqz t3, .Lbbcv_next\n" ++
  "  j .Lbbcv_check_code\n" ++
  ".Lbbcv_maybe_nonce_only:\n" ++
  "  bnez t3, .Lbbcv_next\n" ++
  ".Lbbcv_check_code:\n" ++
  "  la t0, bbcv_addr_off; ld t1, 0(t0); add a2, s10, t1\n" ++
  "  mv a0, s2; mv a1, s3; mv a3, s4; mv a4, s5; mv a5, s6; mv a6, s7\n" ++
  "  jal ra, extcodesize_at_header_state_root\n" ++
  "  li t0, 5; beq a0, t0, .Lbbcv_missing_code\n" ++
  ".Lbbcv_next:\n" ++
  "  addi s9, s9, 1; j .Lbbcv_loop\n" ++
  ".Lbbcv_ok:\n" ++
  "  li a0, 0; j .Lbbcv_ret\n" ++
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
  "  ret"

end EvmAsm.Codegen
