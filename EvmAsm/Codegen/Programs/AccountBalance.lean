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
import EvmAsm.Codegen.Programs.Account

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

/-! ## account_set_uint_field -- replace an account RLP uint field exactly

    a0 = account RLP ptr        a1 = account RLP length
    a2 = field index (0 nonce / 1 balance)
    a3 = value ptr (big-endian bytes)  a4 = value length (<= 32)
    a5 = output buffer ptr      a6 = u64 out length ptr
    a0 (output) = 0 (ok) / 1 (parse fail / value too long)

    The value is encoded as a canonical RLP integer, then spliced into the
    account list at the requested field. This is the BAL post-value analogue of
    account_add_balance: withdrawal replay adds a delta, BAL replay sets the
    exact post nonce/balance reported by the block access list. -/
def accountSetUintFieldFunction : String :=
  "account_set_uint_field:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # account ptr\n" ++
  "  mv s1, a1                   # account len\n" ++
  "  mv s2, a2                   # field index\n" ++
  "  mv s3, a3                   # value ptr\n" ++
  "  mv s4, a4                   # value len\n" ++
  "  mv s5, a5                   # out ptr\n" ++
  "  mv s6, a6                   # out len ptr\n" ++
  "  li t0, 32; bgtu s4, t0, .Lasuf_fail\n" ++
  "  mv a0, s3; mv a1, s4; la a2, aab_enc\n" ++
  "  jal ra, rlp_encode_uint_be\n" ++
  "  la t0, aab_enc_len; sd a0, 0(t0)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  la a3, aab_enc; la t0, aab_enc_len; ld a4, 0(t0)\n" ++
  "  mv a5, s5; mv a6, s6\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  j .Lasuf_ret\n" ++
  ".Lasuf_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lasuf_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 80\n" ++
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


/-- `zisk_account_set_uint_field`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  account_len (u64)
      +16 field_index (u64, 0 nonce / 1 balance)
      +24 value_len (u64)
      +32 value bytes (big-endian, up to 32 bytes)
      +64 account RLP bytes
    Output layout:
      OUTPUT+0 : new account RLP length (u64)
      OUTPUT+8 : new account RLP bytes
      OUTPUT+512 : status -/
def ziskAccountSetUintFieldPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account_len\n" ++
  "  ld a2, 16(t0)               # field_index\n" ++
  "  ld a4, 24(t0)               # value_len\n" ++
  "  addi a3, t0, 32             # value ptr\n" ++
  "  addi a0, t0, 64             # account ptr\n" ++
  "  li a5, 0xa0010008           # out at OUTPUT+8\n" ++
  "  li a6, 0xa0010000           # out_len at OUTPUT+0\n" ++
  "  jal ra, account_set_uint_field\n" ++
  "  li t0, 0xa0010200; sd a0, 0(t0)   # status at OUTPUT+512\n" ++
  "  j .Lasuf_pdone\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  ".Lasuf_pdone:"

def ziskAccountSetUintFieldProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountSetUintFieldPrologue
  dataAsm     := ziskAccountAddBalanceDataSection
}

/-! ## selfdestruct_balance_transfer -- SELFDESTRUCT account-RLP balance move

    Apply the balance mutation from post-Cancun SELFDESTRUCT to already-loaded
    originator and beneficiary account RLP values. This mirrors
    execution-specs' `move_ether(originator, beneficiary, originator_balance)`
    plus the same-transaction-created burn rule:

    * different beneficiary: originator balance becomes zero; beneficiary is
      credited by the originator's pre-transfer balance;
    * same beneficiary, not created in this transaction: net no-op;
    * same beneficiary, created in this transaction: balance is burned, so the
      returned account has zero balance.

    Calling convention:
      a0 = origin account ptr       a1 = origin account len
      a2 = beneficiary account ptr  a3 = beneficiary account len
      a4 = same-address flag        a5 = origin-created-in-tx flag
      a6 = output base

    Output layout at `a6`:
      +0    origin result len
      +8    beneficiary result len
      +16   origin result account bytes
      +128  beneficiary result account bytes

    a0 returns 0 on success, 1 on parse/splice failure. -/
def selfdestructBalanceTransferFunction : String :=
  "selfdestruct_balance_transfer:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # origin ptr\n" ++
  "  mv s1, a1                   # origin len\n" ++
  "  mv s2, a2                   # beneficiary ptr\n" ++
  "  mv s3, a3                   # beneficiary len\n" ++
  "  mv s4, a4                   # same-address flag\n" ++
  "  mv s5, a5                   # origin created in tx flag\n" ++
  "  mv s6, a6                   # output base\n" ++
  "  sd zero, 0(s6); sd zero, 8(s6)\n" ++
  "  addi s7, s6, 16             # origin output ptr\n" ++
  "  bnez s4, .Lsdbt_same\n" ++
  "  # Different beneficiary: extract origin balance as the beneficiary delta.\n" ++
  "  mv a0, s0; mv a1, s1; la a2, aab_bal32\n" ++
  "  jal ra, account_extract_balance\n" ++
  "  bnez a0, .Lsdbt_fail\n" ++
  "  la t0, aab_bal32; la t1, sdbt_delta32\n" ++
  "  ld t2, 0(t0); sd t2, 0(t1); ld t2, 8(t0); sd t2, 8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  # Set origin balance to zero.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1; la a3, aab_bal32; li a4, 0\n" ++
  "  mv a5, s7; mv a6, s6\n" ++
  "  jal ra, account_set_uint_field\n" ++
  "  bnez a0, .Lsdbt_fail\n" ++
  "  # Credit beneficiary with the extracted origin balance.\n" ++
  "  addi t0, s6, 128\n" ++
  "  mv a0, s2; mv a1, s3; la a2, sdbt_delta32; mv a3, t0\n" ++
  "  addi a4, s6, 8\n" ++
  "  jal ra, account_add_balance\n" ++
  "  bnez a0, .Lsdbt_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lsdbt_ret\n" ++
  ".Lsdbt_same:\n" ++
  "  bnez s5, .Lsdbt_same_created\n" ++
  "  # Same non-created account: move_ether subtracts and adds back, net no-op.\n" ++
  "  sd s1, 0(s6); sd s1, 8(s6)\n" ++
  "  mv a0, s7; mv a1, s0; mv a2, s1\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  addi a0, s6, 128; mv a1, s0; mv a2, s1\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  li a0, 0\n" ++
  "  j .Lsdbt_ret\n" ++
  ".Lsdbt_same_created:\n" ++
  "  # Same created account: move_ether is a no-op, then the created account burns.\n" ++
  "  la t0, aab_bal32; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1; mv a3, t0; li a4, 0\n" ++
  "  mv a5, s7; mv a6, s6\n" ++
  "  jal ra, account_set_uint_field\n" ++
  "  bnez a0, .Lsdbt_fail\n" ++
  "  ld t0, 0(s6); sd t0, 8(s6)\n" ++
  "  addi a0, s6, 128; mv a1, s7; mv a2, t0\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  li a0, 0\n" ++
  "  j .Lsdbt_ret\n" ++
  ".Lsdbt_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lsdbt_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_selfdestruct_balance_transfer`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8   origin_len
      +16  beneficiary_len
      +24  same-address flag
      +32  origin-created-in-tx flag
      +40  origin account RLP bytes, fixed 512-byte slot
      +552 beneficiary account RLP bytes
    Output layout:
      OUTPUT+0    origin result len
      OUTPUT+8    beneficiary result len
      OUTPUT+16   origin result account RLP
      OUTPUT+128  beneficiary result account RLP
      OUTPUT+248  status -/
def ziskSelfdestructBalanceTransferPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # origin_len\n" ++
  "  ld a3, 16(t0)               # beneficiary_len\n" ++
  "  ld a4, 24(t0)               # same-address flag\n" ++
  "  ld a5, 32(t0)               # origin-created-in-tx flag\n" ++
  "  addi a0, t0, 40             # origin account ptr\n" ++
  "  addi a2, t0, 552            # beneficiary account ptr\n" ++
  "  li a6, 0xa0010000           # output base\n" ++
  "  jal ra, selfdestruct_balance_transfer\n" ++
  "  li t0, 0xa00100f8; sd a0, 0(t0)   # status at OUTPUT+248\n" ++
  "  j .Lsdbt_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  accountAddBalanceFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  selfdestructBalanceTransferFunction ++ "\n" ++
  ".Lsdbt_pdone:"

def ziskSelfdestructBalanceTransferProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSelfdestructBalanceTransferPrologue
  dataAsm     := ziskAccountExtractBalanceDataSection ++ "\n" ++ ziskAccountAddBalanceDataSection ++ "\n" ++
    ".balign 8\nsdbt_delta32:\n  .zero 32"
}

end EvmAsm.Codegen
