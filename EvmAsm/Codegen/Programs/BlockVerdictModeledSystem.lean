/-
  EvmAsm.Codegen.Programs.BlockVerdictModeledSystem

  Small block-verdict helper split out for the file-size hard cap.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bsr_apply_modeled_system_post_fields

    Apply tx-level BAL balance/nonce post-fields to an already-recorded system
    account descriptor. Storage changes stay with the explicit EIP-2935/EIP-4788
    replay in BlockVerdict, avoiding duplicate state-trie descriptors for the
    same system contract while still honoring SELFDESTRUCT value transfers to
    that account.

    a0 = AccountChanges ptr   a1 = AccountChanges len   a2 = descriptor index
    a0 (output) = 0 ok / 1 parse or rewrite failure. -/
def bsrApplyModeledSystemPostFieldsFunction : String :=
  "bsr_apply_modeled_system_post_fields:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # AccountChanges ptr\n" ++
  "  mv s1, a1                   # AccountChanges len\n" ++
  "  mv s2, a2                   # system descriptor index\n" ++
  "  mv a0, s0; mv a1, s1; la a2, baap_bal; la a3, baap_bal_len; la a4, baap_nonce; la a5, baap_nonce_len\n" ++
  "  jal ra, bal_account_post_fields\n" ++
  "  bnez a0, .Lbams_pf_fail\n" ++
  "  slli t0, s2, 5; slli t1, s2, 3; add t0, t0, t1; la t1, bsr_changes; add s5, t1, t0\n" ++
  "  ld s3, 16(s5)               # current account value ptr\n" ++
  "  ld s4, 24(s5)               # current account value len\n" ++
  "  la t0, baap_nonce_len; ld t0, 0(t0); li t1, -1; beq t0, t1, .Lbams_pf_balance\n" ++
  "  mv a0, s3; mv a1, s4; li a2, 0; la a3, baap_nonce; mv a4, t0; la a5, baap_tmp; la a6, baap_tmp_len\n" ++
  "  jal ra, account_set_uint_field\n" ++
  "  bnez a0, .Lbams_pf_fail\n" ++
  "  la s3, baap_tmp; la t0, baap_tmp_len; ld s4, 0(t0)\n" ++
  ".Lbams_pf_balance:\n" ++
  "  la t0, baap_bal_len; ld t0, 0(t0); li t1, -1; beq t0, t1, .Lbams_pf_copy\n" ++
  "  mv a0, s3; mv a1, s4; li a2, 1; la a3, baap_bal; mv a4, t0; la a5, baap_tmp2; la a6, baap_tmp2_len\n" ++
  "  jal ra, account_set_uint_field\n" ++
  "  bnez a0, .Lbams_pf_fail\n" ++
  "  la s3, baap_tmp2; la t0, baap_tmp2_len; ld s4, 0(t0)\n" ++
  ".Lbams_pf_copy:\n" ++
  "  ld a0, 16(s5); mv a1, s3; mv a2, s4\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  sd s4, 24(s5)\n" ++
  "  li a0, 0; j .Lbams_pf_ret\n" ++
  ".Lbams_pf_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbams_pf_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

end EvmAsm.Codegen
