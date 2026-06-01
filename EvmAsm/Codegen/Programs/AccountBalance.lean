/-
  EvmAsm.Codegen.Programs.AccountBalance

  account_add_balance (bead evm-asm-fhsxz.2.1): credit a wei delta to the
  balance field of an Ethereum account RLP. This is the per-withdrawal state
  mutation that Step 2 (header/withdrawal-only valid blocks) applies before
  recomputing the post-state root via mpt_state_root.

  An account value is rlp([nonce, balance, storageRoot, codeHash]); a
  withdrawal credits `amount_gwei * 1e9` wei to an EXISTING account's balance
  (a value-only update — no structural change). The balance is the RLP item
  at index 1, encoded as a minimal big-endian integer. We:
    1. read item 1 (the current balance bytes) via rlp_list_nth_item,
    2. right-align it into a 32-byte big-endian buffer,
    3. add the 32-byte delta with a byte-wise carry,
    4. strip leading zeros to minimal form and rlp_encode_bytes it,
    5. mpt_splice_slot the account list, replacing item 1 with the new
       balance encoding (which recomputes the outer list prefix).

  Reuses mpt_splice_slot / mset_memcpy (Programs/MptSet.lean) and the RLP
  read/encode helpers (Programs/RlpRead.lean). All multi-byte work is on
  8-aligned scratch; account/balance bytes are copied byte-wise (no-misaligned
  invariant).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.MptSet

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## account_add_balance -- balance += delta on an account RLP

    a0 = account RLP ptr        a1 = account RLP length
    a2 = delta ptr (32-byte big-endian)
    a3 = output buffer ptr      a4 = u64 out length ptr
    a0 (output) = 0 (ok) / 1 (parse fail / balance > 32 bytes)

    new account = rlp([nonce, balance+delta, storageRoot, codeHash]). -/
def accountAddBalanceFunction : String :=
  "account_add_balance:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # account ptr\n" ++
  "  mv s1, a1                   # account len\n" ++
  "  mv s2, a2                   # delta32 ptr\n" ++
  "  mv s3, a3                   # out ptr\n" ++
  "  mv s4, a4                   # out_len ptr\n" ++
  "  # read balance item (index 1).\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, aab_bal_off; la a4, aab_bal_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laab_fail\n" ++
  "  # zero the 32-byte balance buffer.\n" ++
  "  la t0, aab_bal32\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t1, aab_bal_len; ld t1, 0(t1)   # balance content length\n" ++
  "  li t2, 32; bgtu t1, t2, .Laab_fail\n" ++
  "  # src = account + bal_off; dst = aab_bal32 + (32 - bal_len) (right-align).\n" ++
  "  la t2, aab_bal_off; ld t2, 0(t2); add t2, s0, t2\n" ++
  "  la t3, aab_bal32; li t4, 32; sub t4, t4, t1; add t3, t3, t4\n" ++
  "  mv t5, t1\n" ++
  ".Laab_cp:\n" ++
  "  beqz t5, .Laab_cp_done\n" ++
  "  lbu t6, 0(t2); sb t6, 0(t3)\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t5, t5, -1\n" ++
  "  j .Laab_cp\n" ++
  ".Laab_cp_done:\n" ++
  "  # big-endian add delta32 into aab_bal32: i = 31 .. 0, carry.\n" ++
  "  la t0, aab_bal32                  # balance buf base\n" ++
  "  li t2, 31                         # byte index\n" ++
  "  li t3, 0                          # carry\n" ++
  ".Laab_add:\n" ++
  "  add t4, t0, t2                    # &bal[i]\n" ++
  "  lbu t5, 0(t4)\n" ++
  "  add t6, s2, t2; lbu t6, 0(t6)     # delta[i]\n" ++
  "  add t5, t5, t6; add t5, t5, t3\n" ++
  "  andi t6, t5, 0xff; sb t6, 0(t4)\n" ++
  "  srli t3, t5, 8                    # new carry\n" ++
  "  beqz t2, .Laab_add_done\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Laab_add\n" ++
  ".Laab_add_done:\n" ++
  "  # minimal length: first nonzero byte from index 0.\n" ++
  "  la t0, aab_bal32; li t1, 0\n" ++
  ".Laab_scan:\n" ++
  "  li t2, 32; beq t1, t2, .Laab_scan_done\n" ++
  "  add t3, t0, t1; lbu t3, 0(t3); bnez t3, .Laab_scan_done\n" ++
  "  addi t1, t1, 1; j .Laab_scan\n" ++
  ".Laab_scan_done:\n" ++
  "  li t2, 32; sub t2, t2, t1         # minimal length\n" ++
  "  la t3, aab_bal32; add t3, t3, t1  # minimal ptr\n" ++
  "  # rlp_encode_bytes(minimal) -> aab_enc (the new balance item bytes).\n" ++
  "  mv a0, t3; mv a1, t2\n" ++
  "  la a2, aab_enc; la a3, aab_enc_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  # splice account item 1 with the new balance encoding.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, aab_enc; la t0, aab_enc_len; ld a4, 0(t0)\n" ++
  "  mv a5, s3; mv a6, s4\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  j .Laab_ret\n" ++
  ".Laab_fail:\n" ++
  "  li a0, 1\n" ++
  ".Laab_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_account_add_balance`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  account_len (u64)
      +16 delta (32-byte big-endian)
      +48 account RLP bytes
    Output layout:
      OUTPUT+0 : new account RLP length (u64)
      OUTPUT+8 : new account RLP bytes -/
def ziskAccountAddBalancePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account_len\n" ++
  "  addi a2, t0, 16             # delta32 ptr\n" ++
  "  addi a0, t0, 48             # account ptr\n" ++
  "  li a3, 0xa0010008           # out at OUTPUT+8\n" ++
  "  li a4, 0xa0010000           # out_len at OUTPUT+0\n" ++
  "  jal ra, account_add_balance\n" ++
  "  li t0, 0xa0010200; sd a0, 0(t0)   # status (debug) at OUTPUT+512\n" ++
  "  j .Laab_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountAddBalanceFunction ++ "\n" ++
  ".Laab_pdone:"

def ziskAccountAddBalanceDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mset_span_start:\n  .zero 8\n" ++
  "mset_span_size:\n  .zero 8\n" ++
  "mset_payload_start:\n  .zero 8\n" ++
  "mset_head_len:\n  .zero 8\n" ++
  "mset_tail_start:\n  .zero 8\n" ++
  "mset_tail_len:\n  .zero 8\n" ++
  "mset_new_payload_len:\n  .zero 8\n" ++
  "mset_prefix_len:\n  .zero 8\n" ++
  "mset_cursor:\n  .zero 8\n" ++
  "aab_bal_off:\n  .zero 8\n" ++
  "aab_bal_len:\n  .zero 8\n" ++
  "aab_enc_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aab_bal32:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "aab_enc:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "aab_out_pad:\n  .zero 8"

def ziskAccountAddBalanceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountAddBalancePrologue
  dataAsm     := ziskAccountAddBalanceDataSection
}

end EvmAsm.Codegen
