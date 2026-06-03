/-
  EvmAsm.Codegen.Programs.BalAccountHasStateChange

  Cheap BAL AccountChanges classifier for post-state-root replay.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_has_state_change -- detect state-affecting BAL rows

    a0 = AccountChanges RLP ptr   a1 = AccountChanges length
    a0 (output) = 0 no post-state change / 1 has post-state change / 2 parse fail.

    AccountChanges fields:
      [address, storage_changes, storage_reads, balance_changes, nonce_changes, code_changes]
    `storage_reads` are read-only, so only fields 1, 3, 4, and 5 can affect the
    post-state root. -/
def balAccountHasStateChangeFunction : String :=
  "bal_account_has_state_change:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  li s2, 1; jal ra, .Lbahsc_check\n" ++
  "  li s2, 3; jal ra, .Lbahsc_check\n" ++
  "  li s2, 4; jal ra, .Lbahsc_check\n" ++
  "  li s2, 5; jal ra, .Lbahsc_check\n" ++
  "  li a0, 0; j .Lbahsc_ret\n" ++
  ".Lbahsc_check:\n" ++
  "  mv s3, ra\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; la a3, bahsc_off; la a4, bahsc_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbahsc_parse_fail\n" ++
  "  la t0, bahsc_off; ld t0, 0(t0); add a0, s0, t0\n" ++
  "  la t0, bahsc_len; ld a1, 0(t0); la a2, bahsc_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbahsc_parse_fail\n" ++
  "  la t0, bahsc_count; ld t0, 0(t0); bnez t0, .Lbahsc_changed\n" ++
  "  mv ra, s3; ret\n" ++
  ".Lbahsc_changed:\n" ++
  "  li a0, 1; j .Lbahsc_ret\n" ++
  ".Lbahsc_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbahsc_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskBalAccountHasStateChangeDataSection : String :=
  ".balign 8\n" ++
  "bahsc_off:\n  .zero 8\n" ++
  "bahsc_len:\n  .zero 8\n" ++
  "bahsc_count:\n  .zero 8\n"

end EvmAsm.Codegen
