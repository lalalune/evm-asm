/-
  EvmAsm.Codegen.Programs.Block

  Block-body and withdrawal cluster lifted out of
  `EvmAsm.Codegen.Programs` per the file-size hard cap. Groups
  every block-body-level helper plus the withdrawal pipeline.

  Withdrawal pipeline:
    K49  withdrawal_decode
    K65  withdrawals_sum_amounts
    K77  process_withdrawal
    K78  process_withdrawals_block

  Block-body helpers:
    K83  block_body_decode
    K84  block_validate_ommers_empty
    K85  block_withdrawals_total
    K86  block_summary
    K89  block_body_blob_gas_total
    K91  block_validate_blob_gas_consistency
    K97  block_compute_tx_hashes
    K124 block_count_withdrawals
    K125 block_count_transactions

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.Header

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## withdrawal_decode -- PR-K49 4-field withdrawal RLP decoder

    Decode a post-Shanghai Withdrawal record into a flat struct.
    Each withdrawal is an RLP list with 4 fields (Python:
    `ethereum.forks.shanghai.fork_types.Withdrawal`):

      rlp([index, validator_index, address, amount])

    `apply_body` iterates `block.withdrawals`, decodes each one
    via this helper, and applies the credit to the recipient's
    balance (amount is in Gwei).

    Output struct (48 bytes; 8-byte aligned for sd):

       0..  8  index           (u64 LE)
       8.. 16  validator_index (u64 LE)
      16.. 36  address         (20 B)
      36.. 40  zero pad
      40.. 48  amount          (u64 LE; in Gwei)

    Calling convention:
      a0 (input)  : withdrawal_rlp ptr
      a1 (input)  : withdrawal_rlp byte length
      a2 (input)  : 48-byte output struct ptr
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (not a 4-item list,
                    field too long, or address not 20 bytes). -/
def withdrawalDecodeFunction : String :=
  "withdrawal_decode:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # wd_rlp ptr\n" ++
  "  mv s1, a1                  # wd_rlp_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: index (u64 at offset 0)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lwd_fail\n" ++
  "  # Field 1: validator_index (u64 at offset 8)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lwd_fail\n" ++
  "  # Field 2: address (20 bytes at offset 16)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, wd_offset; la a4, wd_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lwd_fail\n" ++
  "  la t0, wd_length; ld t1, 0(t0)\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lwd_fail\n" ++
  "  la t0, wd_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 16\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  lwu t5, 16(t3); sw t5, 16(t4)\n" ++
  "  # Pad bytes 20..24 of address slot (struct 36..40) are zero (from caller zeroing).\n" ++
  "  # Field 3: amount (u64 at offset 40)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  addi a3, s2, 40\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lwd_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lwd_ret\n" ++
  ".Lwd_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lwd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_withdrawal_decode`: probe BuildUnit. Reads (wd_len,
    wd_bytes) from host input, writes (status, 48-byte struct)
    to OUTPUT. -/
def ziskWithdrawalDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # wd_len\n" ++
  "  addi a0, a3, 16             # wd ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 48 bytes (6 dwords).\n" ++
  "  mv t0, a2\n" ++
  "  li t1, 6\n" ++
  ".Lwd_zinit:\n" ++
  "  beqz t1, .Lwd_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lwd_zinit\n" ++
  ".Lwd_zdone:\n" ++
  "  jal ra, withdrawal_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lwd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  ".Lwd_pdone:"

def ziskWithdrawalDecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8"

def ziskWithdrawalDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWithdrawalDecodePrologue
  dataAsm     := ziskWithdrawalDecodeDataSection
}

/-! ## block_body_decode -- PR-K83

    Decode a post-Shanghai block body RLP into three sub-list
    (offset, length) pairs. The body is `rlp([transactions,
    ommers, withdrawals])`:

      Field 0: transactions   (list of typed tx envelopes)
      Field 1: ommers         (empty list post-merge: 0xc0)
      Field 2: withdrawals    (Shanghai+: list of [index, vi,
                              address, amount])

    Output struct layout (48 bytes):

         0..  8  transactions_offset (u64; within body_rlp)
         8.. 16  transactions_length (u64; full encoded sub-list)
        16.. 24  ommers_offset       (u64)
        24.. 32  ommers_length       (u64)
        32.. 40  withdrawals_offset  (u64)
        40.. 48  withdrawals_length  (u64)

    Composes PR-K20 `rlp_list_nth_item` three times. The
    (offset, length) of each sub-list is the FULL encoded item
    (including its own RLP list prefix), per K20's list-item
    contract — so callers can recurse into each with another
    `rlp_list_nth_item` call.

    For pre-Shanghai bodies (only 2 fields), this helper fails
    on the third call. Such bodies aren't relevant for the
    amsterdam stateless guest.

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : 48-byte output struct ptr
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (not a 3-item list).

    Pure composition of PR-K20. No new `.data` scratch beyond
    what K20 needs (none). -/
def blockBodyDecodeFunction : String :=
  "block_body_decode:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_len\n" ++
  "  mv s2, a2                   # output struct ptr\n" ++
  "  # Field 0: transactions\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  mv a3, s2\n" ++
  "  addi a4, s2, 8\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbd_fail\n" ++
  "  # Field 1: ommers\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  addi a3, s2, 16\n" ++
  "  addi a4, s2, 24\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbd_fail\n" ++
  "  # Field 2: withdrawals\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  addi a3, s2, 32\n" ++
  "  addi a4, s2, 40\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbd_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lbbd_ret\n" ++
  ".Lbbd_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbbd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_body_decode`: probe BuildUnit. Reads (body_len,
    body_bytes) from host input, writes (status, 48-byte struct)
    to OUTPUT (56 bytes total). -/
def ziskBlockBodyDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  mv t0, a2; li t1, 6\n" ++
  ".Lbbd_zinit:\n" ++
  "  beqz t1, .Lbbd_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lbbd_zinit\n" ++
  ".Lbbd_zdone:\n" ++
  "  jal ra, block_body_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbbd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  ".Lbbd_pdone:"

def ziskBlockBodyDecodeDataSection : String :=
  ".section .data\n" ++
  "bbd_pad:\n" ++
  "  .zero 8"

def ziskBlockBodyDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockBodyDecodePrologue
  dataAsm     := ziskBlockBodyDecodeDataSection
}

/-! ## block_validate_ommers_empty -- PR-K84

    Verify the post-merge invariant that a block body's ommers
    field is the empty RLP list (`0xc0`). The Merge fork removed
    uncle blocks; every post-merge block must have an empty
    ommers list, matching `EMPTY_OMMERS_HASH` in the header.

    Composes PR-K83 `block_body_decode` + a single-byte check
    on the ommers sub-list.

    An empty RLP list is encoded as the single byte `0xc0`. So
    the check is:
      - ommers_length == 1
      - body_rlp[ommers_offset] == 0xc0

    Calling convention:
      a0 (input)  : block_body_rlp ptr
      a1 (input)  : block_body_rlp byte length
      ra (input)  : return
      a0 (output) :
        0 : ommers is empty (post-merge ok)
        1 : ommers is non-empty (reject — pre-merge or invalid)
        2 : RLP parse failure

    Uses 48 bytes of `.data` scratch (`bvoe_struct`). -/
def blockValidateOmmersEmptyFunction : String :=
  "block_validate_ommers_empty:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  la a2, bvoe_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbvoe_parse_fail\n" ++
  "  la t0, bvoe_struct\n" ++
  "  ld t1, 24(t0)               # ommers_length\n" ++
  "  li t2, 1\n" ++
  "  bne t1, t2, .Lbvoe_not_empty\n" ++
  "  ld t3, 16(t0)               # ommers_offset\n" ++
  "  add t3, s0, t3\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  li t5, 0xc0\n" ++
  "  bne t4, t5, .Lbvoe_not_empty\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvoe_ret\n" ++
  ".Lbvoe_not_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvoe_ret\n" ++
  ".Lbvoe_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbvoe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_block_validate_ommers_empty`: probe BuildUnit. Reads
    (body_len, body_bytes) from host input, writes 8-byte status
    to OUTPUT. -/
def ziskBlockValidateOmmersEmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  jal ra, block_validate_ommers_empty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvoe_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockValidateOmmersEmptyFunction ++ "\n" ++
  ".Lbvoe_pdone:"

def ziskBlockValidateOmmersEmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bvoe_struct:\n" ++
  "  .zero 48"

def ziskBlockValidateOmmersEmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateOmmersEmptyPrologue
  dataAsm     := ziskBlockValidateOmmersEmptyDataSection
}

/-! ## process_withdrawal -- PR-K77

    Apply a Shanghai+ Withdrawal credit to a recipient's account
    balance. Per Python's `process_withdrawal`:

      account.balance += withdrawal.amount * 10^9

    The withdrawal amount is denominated in Gwei; the balance is
    in wei. We convert by multiplying by `GWEI_TO_WEI = 10^9`.

    Composes:
      - PR-K56 `u256_from_u64_be` — zero-extend amount to u256
      - PR-K54 `u256_mul_u64_be`  — × 10^9 to convert Gwei → wei
      - PR-K51 `u256_add_be`      — fold credit into balance

    The mul step can't realistically overflow u256: amount ≤ 2^41
    Gwei (full validator balance ~32 ETH ≈ 2^35 Gwei; ≤ 2^41
    even for stake-pool aggregates), so amount × 10^9 < 2^71 ≪
    2^256. The add can't realistically overflow either since
    mainnet total wei < 2^87. Both are checked as safety nets.

    Calling convention:
      a0 (input)  : withdrawal struct ptr (48 B; from PR-K49
                    `withdrawal_decode`, with amount at offset 40)
      a1 (input)  : account.balance ptr (32 B u256 BE; modified
                    in place)
      ra (input)  : return
      a0 (output) : 0 success / 1 overflow on mul or add.

    Uses 32 bytes of `.data` scratch (`pw_amount_wei`) plus the
    40-byte `u256m_acc` scratch from PR-K54. -/
def processWithdrawalFunction : String :=
  "process_withdrawal:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                   # withdrawal struct ptr\n" ++
  "  mv s1, a1                   # balance ptr\n" ++
  "  # Step 1: zero-extend amount (Gwei) to u256.\n" ++
  "  ld t0, 40(s0)               # amount (u64)\n" ++
  "  mv a0, t0\n" ++
  "  la a1, pw_amount_wei\n" ++
  "  jal ra, u256_from_u64_be\n" ++
  "  # Step 2: amount_wei = amount × 10^9 (in place).\n" ++
  "  la a0, pw_amount_wei\n" ++
  "  li a1, 1000000000\n" ++
  "  la a2, pw_amount_wei\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lpw_fail\n" ++
  "  # Step 3: balance += amount_wei.\n" ++
  "  mv a0, s1\n" ++
  "  la a1, pw_amount_wei\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lpw_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lpw_ret\n" ++
  ".Lpw_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lpw_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_process_withdrawal`: probe BuildUnit. Reads (48 B
    withdrawal struct, 32 B initial balance) from host input;
    copies initial balance to OUTPUT + 8, calls
    process_withdrawal on it, then writes status to OUTPUT. -/
def ziskProcessWithdrawalPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a2, 0x40000000\n" ++
  "  addi a0, a2, 8              # withdrawal struct ptr\n" ++
  "  li a1, 0xa0010008           # balance buffer at OUTPUT + 8\n" ++
  "  # Copy initial balance (input offset 48..80) to OUTPUT + 8.\n" ++
  "  addi t0, a2, 56             # initial balance ptr\n" ++
  "  ld t1,  0(t0); sd t1,  0(a1)\n" ++
  "  ld t1,  8(t0); sd t1,  8(a1)\n" ++
  "  ld t1, 16(t0); sd t1, 16(a1)\n" ++
  "  ld t1, 24(t0); sd t1, 24(a1)\n" ++
  "  jal ra, process_withdrawal\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lpw_pdone\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  processWithdrawalFunction ++ "\n" ++
  ".Lpw_pdone:"

def ziskProcessWithdrawalDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "pw_amount_wei:\n" ++
  "  .zero 32"

def ziskProcessWithdrawalProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskProcessWithdrawalPrologue
  dataAsm     := ziskProcessWithdrawalDataSection
}

/-! ## process_withdrawals_block -- PR-K78

    Iterate over a block's RLP-encoded withdrawals list and apply
    each Gwei→wei credit to a parallel pre-fetched balance array.
    Mirrors the inner loop of Python's `apply_body`:

      for wd in block.withdrawals:
          process_withdrawal(state, wd)

    Caller responsibilities:
      1. Pre-fetch the current balance of each withdrawal recipient
         from the state trie (via PR-K28 `account_at_address` etc.)
         into a parallel `balances[N]` array (each 32 B u256 BE).
      2. After this helper returns, write each updated `balances[i]`
         back to state (via the still-pending MPT mutation path).

    The parallel-array indirection lets this PR ship without
    requiring the MPT mutation infrastructure that
    `compute_state_root_and_trie_changes` will add.

    Composes:
      - PR-K47 `rlp_list_count_items` — outer cardinality
      - PR-K20 `rlp_list_nth_item`    — per-entry bounds
      - PR-K49 `withdrawal_decode`    — extract amount
      - PR-K77 `process_withdrawal`   — credit `balances[i]`

    Calling convention:
      a0 (input)  : withdrawals_rlp ptr
      a1 (input)  : withdrawals_rlp byte length
      a2 (input)  : balances array ptr (N × 32 B; in-place updated)
      ra (input)  : return
      a0 (output) :
        0  : success (every entry credited)
        1  : RLP parse failure at outer count or entry walk
        2  : `withdrawal_decode` failed on an entry
        3  : `process_withdrawal` overflow on credit step

    Uses 64 bytes of `.data` scratch (`pwb_count`,
    `pwb_entry_offset`, `pwb_entry_length`, `pwb_struct[48]`)
    plus `pw_amount_wei` and `u256m_acc` carried in from K77. -/
def processWithdrawalsBlockFunction : String :=
  "process_withdrawals_block:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # rlp_ptr\n" ++
  "  mv s1, a1                   # rlp_len\n" ++
  "  mv s2, a2                   # balances ptr\n" ++
  "  # Step 1: count outer entries\n" ++
  "  la a2, pwb_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lpwb_fail_parse\n" ++
  "  la t0, pwb_count; ld s3, 0(t0)\n" ++
  "  li s5, 0                    # current entry index i\n" ++
  ".Lpwb_loop:\n" ++
  "  beq s5, s3, .Lpwb_done\n" ++
  "  # Get entry i bounds\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s5\n" ++
  "  la a3, pwb_entry_offset\n" ++
  "  la a4, pwb_entry_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lpwb_fail_parse\n" ++
  "  # Decode entry into pwb_struct (48 B)\n" ++
  "  la t0, pwb_entry_offset; ld t1, 0(t0)\n" ++
  "  la t0, pwb_entry_length; ld t2, 0(t0)\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  la a2, pwb_struct\n" ++
  "  jal ra, withdrawal_decode\n" ++
  "  bnez a0, .Lpwb_fail_decode\n" ++
  "  # process_withdrawal(struct, &balances[i])\n" ++
  "  la a0, pwb_struct\n" ++
  "  # balances[i] = s2 + i * 32\n" ++
  "  slli s4, s5, 5\n" ++
  "  add a1, s2, s4\n" ++
  "  jal ra, process_withdrawal\n" ++
  "  bnez a0, .Lpwb_fail_credit\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lpwb_loop\n" ++
  ".Lpwb_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lpwb_ret\n" ++
  ".Lpwb_fail_parse:\n" ++
  "  li a0, 1\n" ++
  "  j .Lpwb_ret\n" ++
  ".Lpwb_fail_decode:\n" ++
  "  li a0, 2\n" ++
  "  j .Lpwb_ret\n" ++
  ".Lpwb_fail_credit:\n" ++
  "  li a0, 3\n" ++
  ".Lpwb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_process_withdrawals_block`: probe BuildUnit. Reads
    (wd_count u64, balances initial N × 32 B, rlp_len u64,
    rlp_bytes) from host input. Writes (status, balances after
    credits) to OUTPUT. -/
def ziskProcessWithdrawalsBlockPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld t1, 8(a4)                # wd_count (N)\n" ++
  "  # Copy initial balances (input offset 16..16+N*32) to OUTPUT + 8.\n" ++
  "  addi t2, a4, 16             # source ptr\n" ++
  "  li t3, 0xa0010008           # dst ptr\n" ++
  "  slli t4, t1, 5              # N × 32 bytes\n" ++
  "  add t5, t3, t4              # dst end\n" ++
  ".Lpwb_copy:\n" ++
  "  beq t3, t5, .Lpwb_copy_done\n" ++
  "  ld t6, 0(t2)\n" ++
  "  sd t6, 0(t3)\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, 8\n" ++
  "  j .Lpwb_copy\n" ++
  ".Lpwb_copy_done:\n" ++
  "  # Now read rlp_len and rlp ptr.\n" ++
  "  add t0, a4, t4              # 0x40000000 + 16 + N*32\n" ++
  "  ld a1, 16(t0)               # rlp_len at offset 16+N*32\n" ++
  "  addi a0, t0, 24             # rlp ptr after the length\n" ++
  "  li a2, 0xa0010008           # balances array\n" ++
  "  jal ra, process_withdrawals_block\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lpwb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  processWithdrawalFunction ++ "\n" ++
  processWithdrawalsBlockFunction ++ "\n" ++
  ".Lpwb_pdone:"

def ziskProcessWithdrawalsBlockDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "pw_amount_wei:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "pwb_count:\n" ++
  "  .zero 8\n" ++
  "pwb_entry_offset:\n" ++
  "  .zero 8\n" ++
  "pwb_entry_length:\n" ++
  "  .zero 8\n" ++
  "pwb_struct:\n" ++
  "  .zero 48"

def ziskProcessWithdrawalsBlockProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskProcessWithdrawalsBlockPrologue
  dataAsm     := ziskProcessWithdrawalsBlockDataSection
}

/-! ## withdrawals_sum_amounts -- PR-K65 block withdrawal-credit total

    Walk an RLP-encoded list of Shanghai+ Withdrawal records
    (one Withdrawal = `rlp([index, validator_index, address,
    amount])`) and return the total of all `amount` fields
    (in Gwei) as a `u64`.

    Used by `apply_body` to compute the block's total
    withdrawal credit before applying it to recipient
    balances — useful as a sanity check against the
    `withdrawals_root` MPT computation and for tracking
    coinbase credits per block.

    First multi-helper composition on the K-stack:
    - PR-K47 `rlp_list_count_items` — outer cardinality
    - PR-K20 `rlp_list_nth_item` — per-entry bounds
    - PR-K49 `withdrawal_decode` — extract `amount` (u64 at
      struct offset 40)

    Each entry's `amount` is added to a u64 accumulator with
    overflow detection (unsigned-wrap check: if `sum < prev`,
    we overflowed). On overflow the function returns status=2
    so the caller can react (in practice withdrawals per block
    are capped at 16 with amounts ≤ ~2^41 Gwei, so overflow
    can't occur on valid chains, but the check makes garbage
    input safe).

    Calling convention:
      a0 (input)  : withdrawals_rlp ptr
      a1 (input)  : withdrawals_rlp byte length
      a2 (input)  : u64 out ptr (sum of all amounts in Gwei)
      ra (input)  : return
      a0 (output) :
        0  : success
        1  : parse fail (output zeroed)
        2  : sum overflowed u64 (output zeroed)

    Uses 64 bytes of `.data` scratch
    (`wsa_count`, `wsa_entry_offset`, `wsa_entry_length`,
    `wsa_struct[48]`). -/
def withdrawalsSumAmountsFunction : String :=
  "withdrawals_sum_amounts:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # rlp_ptr\n" ++
  "  mv s1, a1                   # rlp_len\n" ++
  "  mv s2, a2                   # out_ptr\n" ++
  "  # Step 1: count = rlp_list_count_items(...)\n" ++
  "  la a2, wsa_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lwsa_fail\n" ++
  "  la t0, wsa_count; ld s3, 0(t0)\n" ++
  "  li s4, 0                    # acc (u64)\n" ++
  "  li s5, 0                    # i\n" ++
  ".Lwsa_loop:\n" ++
  "  beq s5, s3, .Lwsa_done\n" ++
  "  # Step 2: get entry i bounds.\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s5\n" ++
  "  la a3, wsa_entry_offset\n" ++
  "  la a4, wsa_entry_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lwsa_fail\n" ++
  "  # Step 3: decode entry into wsa_struct.\n" ++
  "  la t0, wsa_entry_offset; ld t1, 0(t0)\n" ++
  "  la t0, wsa_entry_length; ld t2, 0(t0)\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  la a2, wsa_struct\n" ++
  "  jal ra, withdrawal_decode\n" ++
  "  bnez a0, .Lwsa_fail\n" ++
  "  # Step 4: accumulate amount (at struct offset 40) with overflow.\n" ++
  "  la t0, wsa_struct; ld t1, 40(t0)\n" ++
  "  add t2, s4, t1\n" ++
  "  bltu t2, s4, .Lwsa_overflow\n" ++
  "  mv s4, t2\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lwsa_loop\n" ++
  ".Lwsa_done:\n" ++
  "  sd s4, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lwsa_ret\n" ++
  ".Lwsa_overflow:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 2\n" ++
  "  j .Lwsa_ret\n" ++
  ".Lwsa_fail:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 1\n" ++
  ".Lwsa_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_withdrawals_sum_amounts`: probe BuildUnit. Reads
    (rlp_len, rlp_bytes) from host input, writes (status, sum)
    to OUTPUT (16 bytes total). -/
def ziskWithdrawalsSumAmountsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # rlp_len\n" ++
  "  addi a0, a3, 16             # rlp ptr\n" ++
  "  li a2, 0xa0010008           # out ptr\n" ++
  "  sd zero, 0(a2)\n" ++
  "  jal ra, withdrawals_sum_amounts\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwsa_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalsSumAmountsFunction ++ "\n" ++
  ".Lwsa_pdone:"

def ziskWithdrawalsSumAmountsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wsa_count:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_offset:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_length:\n" ++
  "  .zero 8\n" ++
  "wsa_struct:\n" ++
  "  .zero 48"

def ziskWithdrawalsSumAmountsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWithdrawalsSumAmountsPrologue
  dataAsm     := ziskWithdrawalsSumAmountsDataSection
}

/-! ## block_withdrawals_total -- PR-K85

    Extract the withdrawals sub-list from a block body RLP and
    return the total of all withdrawal `amount` fields (in Gwei)
    as a u64.

    Composes:
      - PR-K83 `block_body_decode` — split body → 3 (off, len) pairs
      - PR-K65 `withdrawals_sum_amounts` — sum amount across the
        decoded withdrawals sub-list

    Useful for cross-checking block-level invariants (e.g., the
    `withdrawals_root` MPT computation) and for receipt analysis.

    Status encoding lets callers floor(status / 100) to identify
    the failing step:

      0          : success — total written to *out
      1          : block_body_decode failed (not a 3-item list)
      101..102   : withdrawals_sum_amounts failed
                   (101 = parse error, 102 = u64 overflow)

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : u64 out ptr (total Gwei across all
                    withdrawals)
      ra (input)  : return
      a0 (output) : composite status code.

    Uses 48 bytes of `.data` scratch (`bwt_struct`) — separate
    from K83's probe-only struct so the two compose cleanly. -/
def blockWithdrawalsTotalFunction : String :=
  "block_withdrawals_total:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_len\n" ++
  "  mv s2, a2                   # out ptr\n" ++
  "  # Step 1: block_body_decode\n" ++
  "  la a2, bwt_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbwt_body_fail\n" ++
  "  # Step 2: withdrawals_sum_amounts on withdrawals sub-list.\n" ++
  "  la t0, bwt_struct\n" ++
  "  ld t1, 32(t0)               # withdrawals_offset\n" ++
  "  ld t2, 40(t0)               # withdrawals_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, withdrawals_sum_amounts\n" ++
  "  beqz a0, .Lbwt_ret\n" ++
  "  li t3, 100\n" ++
  "  add a0, a0, t3              # 1 → 101, 2 → 102\n" ++
  "  j .Lbwt_ret\n" ++
  ".Lbwt_body_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbwt_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_withdrawals_total`: probe BuildUnit. Reads
    (body_len, body_bytes) from host input, writes (status,
    total_gwei u64) to OUTPUT (16 bytes total). -/
def ziskBlockWithdrawalsTotalPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  li a2, 0xa0010008           # out ptr\n" ++
  "  sd zero, 0(a2)\n" ++
  "  jal ra, block_withdrawals_total\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbwt_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalsSumAmountsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockWithdrawalsTotalFunction ++ "\n" ++
  ".Lbwt_pdone:"

def ziskBlockWithdrawalsTotalDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wsa_count:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_offset:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_length:\n" ++
  "  .zero 8\n" ++
  "wsa_struct:\n" ++
  "  .zero 48\n" ++
  ".balign 8\n" ++
  "bwt_struct:\n" ++
  "  .zero 48"

def ziskBlockWithdrawalsTotalProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockWithdrawalsTotalPrologue
  dataAsm     := ziskBlockWithdrawalsTotalDataSection
}

/-! ## block_count_withdrawals -- PR-K124

    Return `len(block.withdrawals)` as a u64, directly from the
    body RLP. Useful for receipt bookkeeping, withdrawal-array
    sizing, and as a pre-flight before per-withdrawal processing
    via PR-K78 `process_withdrawals_block`.

    PR-K85 `block_withdrawals_total` already does the per-withdrawal
    sum across the same list; K124 is the narrow counter when only
    the cardinality matters.

    Composes:
      - PR-K83 `block_body_decode`    — split body
      - PR-K47 `rlp_list_count_items` — N

    Status decade encoding (floor(status/100) identifies failing
    step):

      0          : success
      1          : `block_body_decode` failed
      101        : `rlp_list_count_items` on withdrawals failed

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : u64 out ptr (count)
      ra (input)  : return
      a0 (output) : composite status

    Uses 48 bytes of `.data` scratch (`bcw_struct`) plus K83/K47's
    own scratch slots. -/
/-! ## block_count_transactions -- PR-K125

    Return `len(block.transactions)` as a u64, directly from the
    body RLP. Useful for receipt bookkeeping, per-tx iteration
    sizing, and as a pre-flight before per-tx processing.

    PR-K86 `block_summary` already extracts tx_count alongside
    withdrawal_total and ommers_empty; K125 is the narrow counter
    when only the tx-count cardinality matters (mirror of PR-K124
    `block_count_withdrawals`).

    Composes:
      - PR-K83 `block_body_decode`    — split body
      - PR-K47 `rlp_list_count_items` — N

    Status decade encoding (floor(status/100) identifies failing
    step):

      0          : success
      1          : `block_body_decode` failed
      101        : `rlp_list_count_items` on withdrawals failed
    Status decade encoding:
      0          : success
      1          : `block_body_decode` failed
      101        : `rlp_list_count_items` on txs failed

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : u64 out ptr (count)
      ra (input)  : return
      a0 (output) : composite status

    Uses 48 bytes of `.data` scratch (`bcw_struct`) plus K83/K47's
    own scratch slots. -/
def blockCountWithdrawalsFunction : String :=
  "block_count_withdrawals:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_rlp_len\n" ++
  "  mv s2, a2                   # count out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Step 1: block_body_decode \u2192 bcw_struct.\n" ++
  "  la a2, bcw_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbcw_body_fail\n" ++
  "  # Step 2: rlp_list_count_items on withdrawals sub-list.\n" ++
  "  la t0, bcw_struct\n" ++
  "  ld t1, 32(t0)               # withdrawals_offset\n" ++
  "  ld t2, 40(t0)               # withdrawals_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbcw_ret\n" ++
  "  li a0, 101\n" ++
  "  j .Lbcw_ret\n" ++
  ".Lbcw_body_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbcw_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_count_withdrawals`: probe BuildUnit. Reads
    (body_len, body_bytes), writes (status, withdrawal_count) to
    OUTPUT (16 bytes). -/
def ziskBlockCountWithdrawalsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  li a2, 0xa0010008           # count out\n" ++
  "  jal ra, block_count_withdrawals\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbcw_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockCountWithdrawalsFunction ++ "\n" ++
  ".Lbcw_pdone:"

def ziskBlockCountWithdrawalsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bcw_struct:\n" ++
  "  .zero 48"

def ziskBlockCountWithdrawalsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockCountWithdrawalsPrologue
  dataAsm     := ziskBlockCountWithdrawalsDataSection
}

def blockCountTransactionsFunction : String :=
  "block_count_transactions:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_rlp_len\n" ++
  "  mv s2, a2                   # count out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # Step 1: block_body_decode \u2192 bct_struct.\n" ++
  "  la a2, bct_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbct_body_fail\n" ++
  "  # Step 2: rlp_list_count_items on txs sub-list.\n" ++
  "  la t0, bct_struct\n" ++
  "  ld t1, 0(t0)                # txs_offset\n" ++
  "  ld t2, 8(t0)                # txs_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbct_ret\n" ++
  "  li a0, 101\n" ++
  "  j .Lbct_ret\n" ++
  ".Lbct_body_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbct_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_count_transactions`: probe BuildUnit. Reads
    (body_len, body_bytes), writes (status, tx_count) to OUTPUT. -/
def ziskBlockCountTransactionsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  li a2, 0xa0010008           # count out\n" ++
  "  jal ra, block_count_transactions\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbct_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockCountTransactionsFunction ++ "\n" ++
  ".Lbct_pdone:"

def ziskBlockCountTransactionsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bct_struct:\n" ++
  "  .zero 48"

def ziskBlockCountTransactionsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockCountTransactionsPrologue
  dataAsm     := ziskBlockCountTransactionsDataSection
}

/-! ## block_summary -- PR-K86

    One-pass block body audit. Decode the body, then extract:

      tx_count                u64   — count of transactions
      withdrawal_total_gwei   u64   — sum of withdrawal amounts
      ommers_empty            u64   — 1 if ommers is empty, else 0

    Useful for receipt / consensus-layer cross-checks and as a
    convenient single-call entry point for callers that need
    multiple block-level summaries.

    Composes:
      - PR-K83 `block_body_decode`      — split body
      - PR-K47 `rlp_list_count_items`   — count txs
      - PR-K65 `withdrawals_sum_amounts` — sum withdrawal amounts
      - Inline check                    — ommers length == 1, byte == 0xc0

    Output struct (24 bytes):
      0..  8  tx_count
      8.. 16  withdrawal_total_gwei
     16.. 24  ommers_empty (0 or 1)

    Status encoding:
      0          : success
      1          : block_body_decode failed
      101..102   : rlp_list_count_items on txs failed (1=parse fail)
                   — only code 101 is observed in practice
      201..202   : withdrawals_sum_amounts failed (1=parse / 2=overflow)

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : 24-byte output struct ptr
      ra (input)  : return
      a0 (output) : composite status code.

    Uses 48 bytes of `.data` scratch (`bsum_struct`). -/
def blockSummaryFunction : String :=
  "block_summary:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_len\n" ++
  "  mv s2, a2                   # output struct ptr\n" ++
  "  # Step 1: block_body_decode → bsum_struct.\n" ++
  "  la a2, bsum_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbsum_body_fail\n" ++
  "  # Step 2: tx_count = rlp_list_count_items(txs sub-list).\n" ++
  "  la t0, bsum_struct\n" ++
  "  ld t1, 0(t0)                # txs_offset\n" ++
  "  ld t2, 8(t0)                # txs_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  addi a2, s2, 0              # out[0..8] = tx_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbsum_s3\n" ++
  "  li t3, 100\n" ++
  "  add a0, a0, t3              # 1 → 101\n" ++
  "  j .Lbsum_ret\n" ++
  ".Lbsum_s3:\n" ++
  "  # Step 3: withdrawals_sum_amounts → out[8..16].\n" ++
  "  la t0, bsum_struct\n" ++
  "  ld t1, 32(t0)               # withdrawals_offset\n" ++
  "  ld t2, 40(t0)               # withdrawals_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  addi a2, s2, 8              # out[8..16] = total\n" ++
  "  jal ra, withdrawals_sum_amounts\n" ++
  "  beqz a0, .Lbsum_s4\n" ++
  "  li t3, 200\n" ++
  "  add a0, a0, t3              # 1 → 201, 2 → 202\n" ++
  "  j .Lbsum_ret\n" ++
  ".Lbsum_s4:\n" ++
  "  # Step 4: ommers_empty check → out[16..24] (0 or 1).\n" ++
  "  la t0, bsum_struct\n" ++
  "  ld t1, 24(t0)               # ommers_length\n" ++
  "  li t2, 1\n" ++
  "  bne t1, t2, .Lbsum_ommers_not_empty\n" ++
  "  ld t3, 16(t0)               # ommers_offset\n" ++
  "  add t3, s0, t3\n" ++
  "  lbu t4, 0(t3)\n" ++
  "  li t5, 0xc0\n" ++
  "  bne t4, t5, .Lbsum_ommers_not_empty\n" ++
  "  li t6, 1\n" ++
  "  sd t6, 16(s2)\n" ++
  "  j .Lbsum_ok\n" ++
  ".Lbsum_ommers_not_empty:\n" ++
  "  sd zero, 16(s2)\n" ++
  ".Lbsum_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbsum_ret\n" ++
  ".Lbsum_body_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbsum_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_summary`: probe BuildUnit. Reads (body_len,
    body_bytes), writes (status, tx_count, wd_total, ommers_empty)
    to OUTPUT (32 bytes total). -/
def ziskBlockSummaryPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # body_len\n" ++
  "  addi a0, a3, 16             # body ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  sd zero,  0(a2)\n" ++
  "  sd zero,  8(a2)\n" ++
  "  sd zero, 16(a2)\n" ++
  "  jal ra, block_summary\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbsum_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  withdrawalDecodeFunction ++ "\n" ++
  withdrawalsSumAmountsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockSummaryFunction ++ "\n" ++
  ".Lbsum_pdone:"

def ziskBlockSummaryDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wd_offset:\n" ++
  "  .zero 8\n" ++
  "wd_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "wsa_count:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_offset:\n" ++
  "  .zero 8\n" ++
  "wsa_entry_length:\n" ++
  "  .zero 8\n" ++
  "wsa_struct:\n" ++
  "  .zero 48\n" ++
  ".balign 8\n" ++
  "bsum_struct:\n" ++
  "  .zero 48"

def ziskBlockSummaryProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockSummaryPrologue
  dataAsm     := ziskBlockSummaryDataSection
}

/-! ## block_body_blob_gas_total -- PR-K89

    Sum blob_gas_used over all EIP-4844 (type 3) txs in a block body:

      block.blob_gas_used = sum(
        len(tx.blob_versioned_hashes) × GAS_PER_BLOB
        for tx in block.transactions
        if tx.type == 3
      )

    Useful for the consensus rule
    `header.blob_gas_used == this sum` (post-Cancun).

    Composes:
      - PR-K83 `block_body_decode`            — split body
      - PR-K47 `rlp_list_count_items`         — number of txs
      - PR-K20 `rlp_list_nth_item`            — i-th tx bytes
      - PR-K40 `tx_type_dispatch`             — typed-tx detector
      - PR-K88 `tx_eip4844_compute_blob_gas`  — per-tx blob gas

    Iteration policy: skip every non-type-3 tx without examining
    its body. Pre-Cancun blocks (no type-3 txs) return 0 cleanly.

    Status encoding (callers can floor(status/100) to identify
    the failing step):

      0          : success
      1          : block_body_decode failed
      101        : rlp_list_count_items failed
      201        : rlp_list_nth_item failed
      301        : tx_type_dispatch failed
      401..402   : tx_eip4844_compute_blob_gas failed
                   (1=K45 decode fail, 2=K64 sum fail)

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : gas_per_blob (u64; 131072 on mainnet Cancun)
      a3 (input)  : u64 out ptr (receives total blob_gas_used)
      ra (input)  : return
      a0 (output) : composite status code

    Uses 48 bytes `.data` scratch (`bbbgt_struct`) plus the small
    scratch buffers inherited from K88 / K83. -/
def blockBodyBlobGasTotalFunction : String :=
  "block_body_blob_gas_total:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s3, a2                   # gas_per_blob\n" ++
  "  mv s4, a3                   # out ptr\n" ++
  "  li s5, 0                    # total = 0\n" ++
  "  # Step 1: block_body_decode → bbbgt_struct\n" ++
  "  la a2, bbbgt_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbbbgt_body_fail\n" ++
  "  # Load txs sub-list bounds.\n" ++
  "  la t0, bbbgt_struct\n" ++
  "  ld t1, 0(t0)                # txs_offset\n" ++
  "  ld s2, 8(t0)                # s2 = txs_length\n" ++
  "  add s1, s0, t1              # s1 = absolute txs ptr\n" ++
  "  # Step 2: tx_count = rlp_list_count_items(txs)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  la a2, bbbgt_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbbbgt_loop_init\n" ++
  "  li a0, 101\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_loop_init:\n" ++
  "  la t0, bbbgt_count\n" ++
  "  ld s7, 0(t0)                # s7 = tx_count\n" ++
  "  li s6, 0                    # s6 = i\n" ++
  ".Lbbbgt_loop:\n" ++
  "  beq s6, s7, .Lbbbgt_done\n" ++
  "  # rlp_list_nth_item(s1, s2, s6, &item_off, &item_len)\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s6\n" ++
  "  la a3, bbbgt_item_off\n" ++
  "  la a4, bbbgt_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  beqz a0, .Lbbbgt_after_nth\n" ++
  "  li a0, 201\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_after_nth:\n" ++
  "  la t0, bbbgt_item_off\n" ++
  "  ld t1, 0(t0)                # item_off\n" ++
  "  la t0, bbbgt_item_len\n" ++
  "  ld t2, 0(t0)                # item_len\n" ++
  "  add t3, s1, t1              # tx_ptr = txs + item_off\n" ++
  "  # tx_type_dispatch(tx_ptr, item_len, &type, &inner_off)\n" ++
  "  mv a0, t3\n" ++
  "  mv a1, t2\n" ++
  "  la a2, bbbgt_type\n" ++
  "  la a3, bbbgt_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  beqz a0, .Lbbbgt_after_dispatch\n" ++
  "  li a0, 301\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_after_dispatch:\n" ++
  "  la t0, bbbgt_type\n" ++
  "  ld t1, 0(t0)                # type\n" ++
  "  li t4, 3\n" ++
  "  bne t1, t4, .Lbbbgt_step\n" ++
  "  # type 3: compute blob_gas\n" ++
  "  la t0, bbbgt_item_off\n" ++
  "  ld t1, 0(t0)                # item_off\n" ++
  "  la t0, bbbgt_item_len\n" ++
  "  ld t2, 0(t0)                # item_len\n" ++
  "  la t0, bbbgt_inner_off\n" ++
  "  ld t5, 0(t0)                # inner_off\n" ++
  "  add t3, s1, t1\n" ++
  "  add a0, t3, t5              # inner_ptr = tx_ptr + inner_off\n" ++
  "  sub a1, t2, t5              # inner_len = item_len - inner_off\n" ++
  "  mv a2, s3                   # gas_per_blob\n" ++
  "  la a3, bbbgt_blob_gas\n" ++
  "  jal ra, tx_eip4844_compute_blob_gas\n" ++
  "  beqz a0, .Lbbbgt_after_blob\n" ++
  "  li t0, 400\n" ++
  "  add a0, a0, t0              # 1 → 401, 2 → 402\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_after_blob:\n" ++
  "  la t0, bbbgt_blob_gas\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s5, s5, t1              # total += blob_gas\n" ++
  ".Lbbbgt_step:\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lbbbgt_loop\n" ++
  ".Lbbbgt_done:\n" ++
  "  sd s5, 0(s4)                # *out = total\n" ++
  "  li a0, 0\n" ++
  "  j .Lbbbgt_ret\n" ++
  ".Lbbbgt_body_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbbbgt_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_block_body_blob_gas_total`: probe BuildUnit. Reads
    (body_len, gas_per_blob, body_bytes) from host input,
    writes (status, total_blob_gas) to OUTPUT (16 bytes). -/
def ziskBlockBodyBlobGasTotalPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # body_len\n" ++
  "  ld a2, 16(a4)               # gas_per_blob\n" ++
  "  addi a0, a4, 24             # body ptr\n" ++
  "  li a3, 0xa0010008           # out u64 ptr\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, block_body_blob_gas_total\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbbbgt_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  txEip4844ComputeBlobGasFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyBlobGasTotalFunction ++ "\n" ++
  ".Lbbbgt_pdone:"

def ziskBlockBodyBlobGasTotalDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bgvh_count_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "tcbg_struct:\n" ++
  "  .zero 248\n" ++
  ".balign 8\n" ++
  "bbbgt_struct:\n" ++
  "  .zero 48\n" ++
  ".balign 8\n" ++
  "bbbgt_count:\n" ++
  "  .zero 8\n" ++
  "bbbgt_item_off:\n" ++
  "  .zero 8\n" ++
  "bbbgt_item_len:\n" ++
  "  .zero 8\n" ++
  "bbbgt_type:\n" ++
  "  .zero 8\n" ++
  "bbbgt_inner_off:\n" ++
  "  .zero 8\n" ++
  "bbbgt_blob_gas:\n" ++
  "  .zero 8"

def ziskBlockBodyBlobGasTotalProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockBodyBlobGasTotalPrologue
  dataAsm     := ziskBlockBodyBlobGasTotalDataSection
}

/-! ## block_validate_blob_gas_consistency -- PR-K91

    Cancun-era consensus rule: the value of `header.blob_gas_used`
    must equal the sum of per-tx blob gas across the block's body.

      header.blob_gas_used == sum(
        len(tx.blob_versioned_hashes) × GAS_PER_BLOB
        for tx in block.transactions
        if tx.type == 3
      )

    Composes:
      - PR-K53 `rlp_field_to_u64`        — extract header field 17
      - PR-K89 `block_body_blob_gas_total` — sum over body

    The Python reference (`forks/amsterdam/fork.py`) enforces this
    inside `apply_body`. This helper packages the check into a
    single ECALL-shaped routine so callers don't need to thread
    intermediate values through registers.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : body_rlp ptr
      a3 (input)  : body_rlp byte length
      a4 (input)  : gas_per_blob (u64; 131072 on mainnet Cancun)
      ra (input)  : return
      a0 (output) : composite status code

    Status decade encoding (floor(status/100) identifies the
    failing step):

      0          : success — header.blob_gas_used == body total
      1          : header parse / field 17 missing / not u64
      2          : mismatch (header.blob_gas_used ≠ body total)
      101        : body decode failed
      201        : body rlp_list_count_items failed
      301        : body rlp_list_nth_item failed
      401        : body tx_type_dispatch failed
      501..502   : body tx_eip4844_compute_blob_gas forwarded
                   (501 = K45 decode, 502 = K64 sum)

    Uses 32 bytes of `.data` scratch (`bvbgc_header_bgu` +
    `bvbgc_body_total`) plus the scratch buffers inherited from
    PR-K89 / K88 / K83. -/
def blockValidateBlobGasConsistencyFunction : String :=
  "block_validate_blob_gas_consistency:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a2                   # body_rlp ptr\n" ++
  "  mv s1, a3                   # body_len\n" ++
  "  mv s2, a4                   # gas_per_blob\n" ++
  "  # Step 1: extract header.blob_gas_used (field 17, u64).\n" ++
  "  # a0,a1 still hold (header_ptr, header_len).\n" ++
  "  li a2, 17\n" ++
  "  la a3, bvbgc_header_bgu\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Lbvbgc_step2\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvbgc_ret\n" ++
  ".Lbvbgc_step2:\n" ++
  "  # Step 2: body total via K89.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2                   # gas_per_blob\n" ++
  "  la a3, bvbgc_body_total\n" ++
  "  jal ra, block_body_blob_gas_total\n" ++
  "  beqz a0, .Lbvbgc_compare\n" ++
  "  # K89 returns: 1=body decode, 101=count, 201=nth, 301=dispatch,\n" ++
  "  # 401..402=K88 forwarded. Re-map onto our 101+ decade space.\n" ++
  "  li t0, 100\n" ++
  "  add a0, a0, t0              # 1→101, 101→201, 201→301, 301→401,\n" ++
  "                              # 401→501, 402→502\n" ++
  "  j .Lbvbgc_ret\n" ++
  ".Lbvbgc_compare:\n" ++
  "  la t0, bvbgc_header_bgu\n" ++
  "  ld t1, 0(t0)\n" ++
  "  la t0, bvbgc_body_total\n" ++
  "  ld t2, 0(t0)\n" ++
  "  beq t1, t2, .Lbvbgc_ok\n" ++
  "  li a0, 2\n" ++
  "  j .Lbvbgc_ret\n" ++
  ".Lbvbgc_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lbvbgc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_validate_blob_gas_consistency`: probe BuildUnit.
    Input layout (LE u64s + variable bytes):
      bytes  0.. 8 : header_len
      bytes  8..16 : body_len
      bytes 16..24 : gas_per_blob
      bytes 24..   : header_rlp ‖ body_rlp (concatenated, no padding
                     between)
    OUTPUT layout (8 bytes):
      bytes  0.. 8 : status code -/
def ziskBlockValidateBlobGasConsistencyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # header_len\n" ++
  "  ld a3, 16(a5)               # body_len\n" ++
  "  ld a4, 24(a5)               # gas_per_blob\n" ++
  "  addi a0, a5, 32             # header_ptr\n" ++
  "  add a2, a0, a1              # body_ptr = header_ptr + header_len\n" ++
  "  jal ra, block_validate_blob_gas_consistency\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbvbgc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txEip4844DecodeFunction ++ "\n" ++
  blobGasUsedFromVersionedHashesFunction ++ "\n" ++
  txEip4844ComputeBlobGasFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyBlobGasTotalFunction ++ "\n" ++
  blockValidateBlobGasConsistencyFunction ++ "\n" ++
  ".Lbvbgc_pdone:"

def ziskBlockValidateBlobGasConsistencyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "t48_offset:\n" ++
  "  .zero 8\n" ++
  "t48_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bgvh_count_scratch:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "tcbg_struct:\n" ++
  "  .zero 248\n" ++
  ".balign 8\n" ++
  "bbbgt_struct:\n" ++
  "  .zero 48\n" ++
  ".balign 8\n" ++
  "bbbgt_count:\n" ++
  "  .zero 8\n" ++
  "bbbgt_item_off:\n" ++
  "  .zero 8\n" ++
  "bbbgt_item_len:\n" ++
  "  .zero 8\n" ++
  "bbbgt_type:\n" ++
  "  .zero 8\n" ++
  "bbbgt_inner_off:\n" ++
  "  .zero 8\n" ++
  "bbbgt_blob_gas:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bvbgc_header_bgu:\n" ++
  "  .zero 8\n" ++
  "bvbgc_body_total:\n" ++
  "  .zero 8"

def ziskBlockValidateBlobGasConsistencyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateBlobGasConsistencyPrologue
  dataAsm     := ziskBlockValidateBlobGasConsistencyDataSection
}

/-! ## block_compute_tx_hashes -- PR-K97

    Walk the block body's `transactions` RLP list and compute the
    keccak256 of each encoded tx, packed into a contiguous output
    buffer. For each item returned by PR-K20 `rlp_list_nth_item`:

      tx_hash = keccak256(tx_bytes_as_returned_by_nth_item)

    `rlp_list_nth_item` returns the byte-string content for typed
    txs (so for a type-3 EIP-4844 tx the bytes are
    `[0x03 || rlp(inner)]`) and the full RLP list bytes for legacy
    txs. In both cases the tx hash on Ethereum is
    `keccak256(encoded_bytes)`, which is precisely what this helper
    computes — matching what `Block.transactions` callers feed
    downstream (receipts, MPT keys, etc.).

    Composes:
      - PR-K47 `rlp_list_count_items` — N
      - PR-K20 `rlp_list_nth_item`    — per-item bounds
      - PR-K3  `zkvm_keccak256`       — per-item hash

    Calling convention:
      a0 (input)  : txs_list_rlp ptr (the txs sub-list bytes)
      a1 (input)  : txs_list byte length
      a2 (input)  : output buffer ptr (must hold N × 32 bytes)
      a3 (input)  : u64 out count ptr (writes N on success)
      ra (input)  : return
      a0 (output) : composite status

    Status decade encoding:
      0          : success — N hashes written, *count = N
      101        : `rlp_list_count_items` failed
      201        : `rlp_list_nth_item` failed (mid-loop)

    Uses 32 bytes of `.data` scratch (`bcth_item_off` +
    `bcth_item_len` + `bcth_count`). -/
def blockComputeTxHashesFunction : String :=
  "block_compute_tx_hashes:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # txs_list ptr\n" ++
  "  mv s1, a1                   # txs_len\n" ++
  "  mv s2, a2                   # out hashes buffer\n" ++
  "  mv s3, a3                   # out count ptr\n" ++
  "  # Step 1: rlp_list_count_items.\n" ++
  "  la a2, bcth_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  beqz a0, .Lbcth_loop_init\n" ++
  "  li a0, 101\n" ++
  "  j .Lbcth_ret\n" ++
  ".Lbcth_loop_init:\n" ++
  "  la t0, bcth_count\n" ++
  "  ld s5, 0(t0)                # N = tx_count\n" ++
  "  li s4, 0                    # i = 0\n" ++
  ".Lbcth_loop:\n" ++
  "  beq s4, s5, .Lbcth_done\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s4\n" ++
  "  la a3, bcth_item_off\n" ++
  "  la a4, bcth_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  beqz a0, .Lbcth_after_nth\n" ++
  "  li a0, 201\n" ++
  "  j .Lbcth_ret\n" ++
  ".Lbcth_after_nth:\n" ++
  "  la t0, bcth_item_off\n" ++
  "  ld t1, 0(t0)\n" ++
  "  la t0, bcth_item_len\n" ++
  "  ld t2, 0(t0)\n" ++
  "  add a0, s0, t1              # tx_ptr\n" ++
  "  mv a1, t2                   # tx_len\n" ++
  "  slli s6, s4, 5              # i × 32\n" ++
  "  add a2, s2, s6              # &out[i*32]\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lbcth_loop\n" ++
  ".Lbcth_done:\n" ++
  "  sd s5, 0(s3)                # *count = N\n" ++
  "  li a0, 0\n" ++
  ".Lbcth_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_compute_tx_hashes`: probe BuildUnit. Reads
    (txs_list_len, txs_list_bytes) from host input, writes
    (status, count, N × 32-byte hashes) to OUTPUT. The host caller
    must size OUTPUT for at least 16 + N × 32 bytes.
    Input layout:
      bytes  0.. 8 : txs_list_len
      bytes  8..   : txs_list RLP bytes
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : count (u64 LE)
      bytes 16..   : N concatenated 32-byte hashes -/
def ziskBlockComputeTxHashesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # txs_list_len\n" ++
  "  addi a0, a4, 16             # txs_list ptr\n" ++
  "  li a2, 0xa0010010           # hashes buffer (OUTPUT + 16)\n" ++
  "  li a3, 0xa0010008           # count ptr (OUTPUT + 8)\n" ++
  "  sd zero, 0(a3)\n" ++
  "  jal ra, block_compute_tx_hashes\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbcth_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockComputeTxHashesFunction ++ "\n" ++
  ".Lbcth_pdone:"

def ziskBlockComputeTxHashesDataSection : String :=
  ".section .data\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 8\n" ++
  "bcth_count:\n" ++
  "  .zero 8\n" ++
  "bcth_item_off:\n" ++
  "  .zero 8\n" ++
  "bcth_item_len:\n" ++
  "  .zero 8"

def ziskBlockComputeTxHashesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockComputeTxHashesPrologue
  dataAsm     := ziskBlockComputeTxHashesDataSection
}

/-! ## block_validate_2tx_full -- PR-K176

    Full validation of a 2-tx Ethereum block: combines the
    per-header chain check (K174) with the
    `transactions_root` MPT match (K171) into a single
    end-to-end predicate. Calling this on `(parent_rlp,
    header_rlp, tx0, tx1)` returns `is_valid = 1` iff both:

      1. validate_header_pair(parent, header) accepts:
         child.parent_hash == keccak(parent),
         child.number == parent.number + 1,
         child.timestamp > parent.timestamp,
         check_gas_limit(child, parent) == 0
      2. block_validate_transactions_root_two_tx(header, tx0, tx1)
         accepts: header.transactions_root matches the trie
         root of the two-tx MPT.

    This composition is the per-block invariant for a 2-tx block
    in the chain (modulo the body-side checks ECRECOVER / EVM
    execution still gates).

    Calling convention:
      a0 (input)  : parent_rlp ptr
      a1 (input)  : parent_rlp byte length
      a2 (input)  : header_rlp ptr  (the child header)
      a3 (input)  : header_rlp byte length
      a4 (input)  : tx0 ptr
      a5 (input)  : tx0 byte length
      a6 (input)  : tx1 ptr
      a7 (input)  : tx1 byte length
      ra (input)  : return
      (out via shadow regs)  : caller passes the is_valid u64
                                output pointer via memory; see
                                prologue for the wiring.
      a0 (output) :
        0 : success -- predicate written
        nonzero : propagated status code:
          1   header-pair child parse failure
          2   header-pair child.parent_hash size mismatch
          3   header-pair parent field-extract failure
          4   header-pair child field-extract failure
          11  tx-root header parse failure
          12  tx-root header.transactions_root size mismatch

    The is_valid output pointer is read from `bv2f_out_ptr`
    (an indirection slot in `.data`) to keep the calling
    convention within the 8 a-register limit. The prologue
    initializes this slot to `0xa0010008`. -/
def blockValidate2txFullFunction : String :=
  "block_validate_2tx_full:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # parent\n" ++
  "  mv s2, a2; mv s3, a3                # header (child)\n" ++
  "  mv s4, a4; mv s5, a5                # tx0\n" ++
  "  mv s6, a6; mv s7, a7                # tx1\n" ++
  "  la t0, bv2f_out_ptr; ld s8, 0(t0)   # is_valid u64 out\n" ++
  "  sd zero, 0(s8)\n" ++
  "  # ---- (A) Header pair check ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s2; mv a3, s3\n" ++
  "  la a4, bv2f_pair_valid\n" ++
  "  jal ra, validate_header_pair\n" ++
  "  beqz a0, .Lbv2f_pair_status_ok\n" ++
  "  # Propagate pair status (1..4) to caller; keep same numbering.\n" ++
  "  j .Lbv2f_ret\n" ++
  ".Lbv2f_pair_status_ok:\n" ++
  "  la t0, bv2f_pair_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbv2f_pred_false\n" ++
  "  # ---- (B) Transactions-root MPT check ----\n" ++
  "  mv a0, s2; mv a1, s3                # header (child)\n" ++
  "  mv a2, s4; mv a3, s5                # tx0\n" ++
  "  mv a4, s6; mv a5, s7                # tx1\n" ++
  "  la a6, bv2f_tx_root_valid\n" ++
  "  jal ra, block_validate_transactions_root_two_tx\n" ++
  "  beqz a0, .Lbv2f_tx_root_status_ok\n" ++
  "  # Remap K171 status (1=parse, 2=size) into 11/12 to keep\n" ++
  "  # distinguishable from K174 codes.\n" ++
  "  addi a0, a0, 10\n" ++
  "  j .Lbv2f_ret\n" ++
  ".Lbv2f_tx_root_status_ok:\n" ++
  "  la t0, bv2f_tx_root_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbv2f_pred_false\n" ++
  "  # Both invariants hold.\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s8)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbv2f_ret\n" ++
  ".Lbv2f_pred_false:\n" ++
  "  sd zero, 0(s8)\n" ++
  "  li a0, 0\n" ++
  ".Lbv2f_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_block_validate_2tx_full`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : header_rlp_len
      bytes 16..24 : tx0_len
      bytes 24..32 : tx1_len
      bytes 32..   : parent_rlp || header_rlp || tx0 || tx1
    Output layout:
      bytes  0.. 8 : status (0=ok, 1..4 pair, 11..12 tx-root)
      bytes  8..16 : is_valid (1 if both invariants hold) -/
def ziskBlockValidate2txFullPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0xa0010008\n" ++
  "  la t5, bv2f_out_ptr\n" ++
  "  sd t6, 0(t5)\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1,  8(a7)              # parent_rlp_len\n" ++
  "  ld a3, 16(a7)              # header_rlp_len\n" ++
  "  ld a5, 24(a7)              # tx0_len\n" ++
  "  ld t0, 32(a7)              # tx1_len\n" ++
  "  la t1, bv2f_tx1_len; sd t0, 0(t1)\n" ++
  "  addi a0, a7, 40            # parent_rlp ptr\n" ++
  "  add a2, a0, a1             # header_rlp ptr\n" ++
  "  add a4, a2, a3             # tx0 ptr\n" ++
  "  add a6, a4, a5             # tx1 ptr\n" ++
  "  la t1, bv2f_tx1_len; ld t0, 0(t1)\n" ++
  "  mv a7, t0                  # tx1_len\n" ++
  "  jal ra, block_validate_2tx_full\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbv2f_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  mptBranchPayloadTwoSlotsFunction ++ "\n" ++
  mptBranchNodeEncodeFunction ++ "\n" ++
  mptBranchNodeKeccakFunction ++ "\n" ++
  mptTwoLeafRootIndexedFunction ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  blockValidateTransactionsRootTwoTxFunction ++ "\n" ++
  blockValidate2txFullFunction ++ "\n" ++
  ".Lbv2f_pdone:"

def ziskBlockValidate2txFullDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32\n" ++
  "vhp_link_valid:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_number:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhp_child_number:\n" ++
  "  .zero 8\n" ++
  "vhp_child_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_child_gas_limit:\n" ++
  "  .zero 8\n" ++
  "mlnen_field_len:\n" ++
  "  .zero 8\n" ++
  "mlnen_hp_len:\n" ++
  "  .zero 8\n" ++
  "mlnen_cursor:\n" ++
  "  .zero 8\n" ++
  "mlnen_total_payload:\n" ++
  "  .zero 8\n" ++
  "mlnen_hp_buf:\n" ++
  "  .zero 1024\n" ++
  "mlnen_payload_buf:\n" ++
  "  .zero 16384\n" ++
  "mbne_field_len:\n" ++
  "  .zero 8\n" ++
  "mbnk_node_len:\n" ++
  "  .zero 8\n" ++
  "mbnk_node_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_nib0:\n" ++
  "  .zero 1\n" ++
  "mtlri_nib1:\n" ++
  "  .zero 1\n" ++
  ".balign 8\n" ++
  "mtlri_leaf_0_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_leaf_0_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_leaf_1_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_leaf_1_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_slot_0_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_slot_0_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_slot_1_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_slot_1_buf:\n" ++
  "  .zero 16384\n" ++
  "mtlri_branch_payload_len:\n" ++
  "  .zero 8\n" ++
  "mtlri_branch_payload:\n" ++
  "  .zero 16384\n" ++
  "bvtr_offset:\n" ++
  "  .zero 8\n" ++
  "bvtr_length:\n" ++
  "  .zero 8\n" ++
  "bvtr_claimed_root:\n" ++
  "  .zero 32\n" ++
  "bvtr_computed_root:\n" ++
  "  .zero 32\n" ++
  "bv2f_out_ptr:\n" ++
  "  .zero 8\n" ++
  "bv2f_pair_valid:\n" ++
  "  .zero 8\n" ++
  "bv2f_tx_root_valid:\n" ++
  "  .zero 8\n" ++
  "bv2f_tx1_len:\n" ++
  "  .zero 8"

def ziskBlockValidate2txFullProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidate2txFullPrologue
  dataAsm     := ziskBlockValidate2txFullDataSection
}

/-! ## block_body_extract_2tx -- PR-K177

    Extract the two transactions from a block body whose
    transactions list contains exactly two items, while also
    asserting that the ommers list is the empty list (`0xc0`)
    -- the post-merge invariant.

    Body RLP layout (post-Shanghai):
      `rlp([transactions, ommers, withdrawals])`

    This helper:
      1. Decodes the body with K83 `block_body_decode`.
      2. Verifies `ommers_length == 1` and the single byte is
         `0xc0` (== `rlp([])`, the empty list).
      3. Counts the transactions list with K47
         `rlp_list_count_items`; requires count == 2.
      4. Extracts tx0 and tx1 with K20 `rlp_list_nth_item` on
         the inner transactions list, returning (offset, len)
         in the OUTER body's address space (offset relative to
         body_rlp, ready to feed into K171 etc.).

    Output struct (32 bytes):
       0..  8  tx0_offset (in body_rlp)
       8.. 16  tx0_length
      16.. 24  tx1_offset
      24.. 32  tx1_length

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : 32-byte output struct ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : body RLP parse failure (not a 3-item list)
        2 : ommers not the empty list
        3 : transactions list count != 2
        4 : transactions list item extraction failure -/
def blockBodyExtract2txFunction : String :=
  "block_body_extract_2tx:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # body_rlp ptr\n" ++
  "  mv s1, a1                   # body_rlp len\n" ++
  "  mv s2, a2                   # output struct\n" ++
  "  # (1) Decode body into bbe_body_struct (48 B)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, bbe_body_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbbe_parse_fail\n" ++
  "  # (2) Verify ommers == 0xc0\n" ++
  "  la t0, bbe_body_struct; ld t1, 16(t0)        # ommers_offset\n" ++
  "  ld t2, 24(t0)                                # ommers_length\n" ++
  "  li t3, 1\n" ++
  "  bne t2, t3, .Lbbe_ommers_fail\n" ++
  "  add t1, s0, t1                               # &body[off]\n" ++
  "  lbu t4, 0(t1)\n" ++
  "  li t5, 0xc0\n" ++
  "  bne t4, t5, .Lbbe_ommers_fail\n" ++
  "  # (3) Count transactions list\n" ++
  "  la t0, bbe_body_struct; ld s3, 0(t0)         # txs_offset (in body)\n" ++
  "  ld s4, 8(t0)                                 # txs_length\n" ++
  "  add a0, s0, s3                               # txs_list ptr\n" ++
  "  mv a1, s4\n" ++
  "  la a2, bbe_tx_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbe_txs_fail\n" ++
  "  la t0, bbe_tx_count; ld t1, 0(t0)\n" ++
  "  li t2, 2\n" ++
  "  bne t1, t2, .Lbbe_count_fail\n" ++
  "  # (4) Extract tx0\n" ++
  "  add a0, s0, s3; mv a1, s4; li a2, 0\n" ++
  "  la a3, bbe_item_off; la a4, bbe_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbe_txs_fail\n" ++
  "  la t0, bbe_item_off; ld t1, 0(t0)\n" ++
  "  add t1, t1, s3                               # offset relative to body\n" ++
  "  sd t1, 0(s2)\n" ++
  "  la t0, bbe_item_len; ld t1, 0(t0)\n" ++
  "  sd t1, 8(s2)\n" ++
  "  # Extract tx1\n" ++
  "  add a0, s0, s3; mv a1, s4; li a2, 1\n" ++
  "  la a3, bbe_item_off; la a4, bbe_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbbe_txs_fail\n" ++
  "  la t0, bbe_item_off; ld t1, 0(t0)\n" ++
  "  add t1, t1, s3\n" ++
  "  sd t1, 16(s2)\n" ++
  "  la t0, bbe_item_len; ld t1, 0(t0)\n" ++
  "  sd t1, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbbe_ret\n" ++
  ".Lbbe_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbbe_ret\n" ++
  ".Lbbe_ommers_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lbbe_ret\n" ++
  ".Lbbe_count_fail:\n" ++
  "  li a0, 3\n" ++
  "  j .Lbbe_ret\n" ++
  ".Lbbe_txs_fail:\n" ++
  "  li a0, 4\n" ++
  ".Lbbe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_body_extract_2tx`: probe BuildUnit.
    Input layout:
      bytes 0.. 8 : body_rlp_len
      bytes 8..   : body_rlp
    Output layout:
      bytes  0.. 8 : status (0..4)
      bytes  8..40 : 32-byte struct (tx0 off+len, tx1 off+len) -/
def ziskBlockBodyExtract2txPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # body_rlp_len\n" ++
  "  addi a0, a7, 16             # body_rlp ptr\n" ++
  "  li a2, 0xa0010008           # output struct ptr\n" ++
  "  jal ra, block_body_extract_2tx\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbbe_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyExtract2txFunction ++ "\n" ++
  ".Lbbe_pdone:"

def ziskBlockBodyExtract2txDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bbe_body_struct:\n" ++
  "  .zero 48\n" ++
  "bbe_tx_count:\n" ++
  "  .zero 8\n" ++
  "bbe_item_off:\n" ++
  "  .zero 8\n" ++
  "bbe_item_len:\n" ++
  "  .zero 8"

def ziskBlockBodyExtract2txProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockBodyExtract2txPrologue
  dataAsm     := ziskBlockBodyExtract2txDataSection
}

/-! ## block_validate_2tx_full_with_body -- PR-K178

    Single-call end-to-end validator for a 2-tx Ethereum block,
    taking `(parent_rlp, header_rlp, body_rlp)` and returning
    one is_valid u64. Composes K177 + K176:

      1. K177 `block_body_extract_2tx(body_rlp)` decodes the
         body, verifies `[txs, ommers, withdrawals]` shape with
         exactly two transactions and empty ommers, and returns
         `(tx0_off, tx0_len, tx1_off, tx1_len)` in body-relative
         coordinates.
      2. K176 `block_validate_2tx_full(parent, header, tx0, tx1)`
         verifies all four header-pair invariants plus the
         transactions_root MPT match using the extracted tx
         slices.

    This is the body-aware shape of `validate_block` for 2-tx
    blocks; it is the natural endpoint of the K-series chain
    once both the header and body sides are covered.

    Calling convention:
      a0 (input)  : parent_rlp ptr
      a1 (input)  : parent_rlp byte length
      a2 (input)  : header_rlp ptr
      a3 (input)  : header_rlp byte length
      a4 (input)  : body_rlp ptr
      a5 (input)  : body_rlp byte length
      a6 (input)  : u64 out (is_valid)
      ra (input)  : return
      a0 (output) :
        0  success -- predicate written
        1..4   propagated from `block_body_extract_2tx`
              (1 parse, 2 ommers, 3 count, 4 inner extract)
        11..14 propagated from `block_validate_2tx_full`
              (11..14 == pair codes 1..4)
        21..22 propagated from K171 inside K176
              (tx-root parse / size codes 11..12 + 10) -/
def blockValidate2txFullWithBodyFunction : String :=
  "block_validate_2tx_full_with_body:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1          # parent\n" ++
  "  mv s2, a2; mv s3, a3          # header\n" ++
  "  mv s4, a4; mv s5, a5          # body\n" ++
  "  mv s6, a6                     # is_valid out\n" ++
  "  sd zero, 0(s6)\n" ++
  "  # ---- (A) Extract tx0 / tx1 from body ----\n" ++
  "  mv a0, s4; mv a1, s5\n" ++
  "  la a2, bv2fb_struct\n" ++
  "  jal ra, block_body_extract_2tx\n" ++
  "  beqz a0, .Lbv2fb_body_ok\n" ++
  "  # Propagate body status (1..4) unchanged.\n" ++
  "  j .Lbv2fb_ret\n" ++
  ".Lbv2fb_body_ok:\n" ++
  "  # Resolve tx0 / tx1 pointers in body address space.\n" ++
  "  la t0, bv2fb_struct\n" ++
  "  ld t1,  0(t0)                # tx0_off (in body)\n" ++
  "  ld t2,  8(t0)                # tx0_len\n" ++
  "  ld t3, 16(t0)                # tx1_off\n" ++
  "  ld t4, 24(t0)                # tx1_len\n" ++
  "  add t1, s4, t1               # tx0 ptr\n" ++
  "  add t3, s4, t3               # tx1 ptr\n" ++
  "  la t5, bv2f_out_ptr; sd s6, 0(t5)   # wire is_valid out through indirection\n" ++
  "  # K176 takes 8 a-regs; the is_valid out is read from\n" ++
  "  # bv2f_out_ptr (already set above).\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s2; mv a3, s3\n" ++
  "  mv a4, t1; mv a5, t2\n" ++
  "  mv a6, t3; mv a7, t4\n" ++
  "  jal ra, block_validate_2tx_full\n" ++
  "  beqz a0, .Lbv2fb_check_pred\n" ++
  "  # K176 status: 1..4 pair, 11..12 tx-root. Remap to\n" ++
  "  # 11..14 and 21..22 so callers can distinguish from\n" ++
  "  # body-extract codes (1..4).\n" ++
  "  li t0, 5\n" ++
  "  bltu a0, t0, .Lbv2fb_remap_pair\n" ++
  "  # K176 a0 in {11, 12} -> {21, 22}\n" ++
  "  addi a0, a0, 10\n" ++
  "  j .Lbv2fb_ret\n" ++
  ".Lbv2fb_remap_pair:\n" ++
  "  # K176 a0 in {1..4} -> {11..14}\n" ++
  "  addi a0, a0, 10\n" ++
  "  j .Lbv2fb_ret\n" ++
  ".Lbv2fb_check_pred:\n" ++
  "  # K176 already wrote is_valid via the indirection slot.\n" ++
  "  li a0, 0\n" ++
  ".Lbv2fb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_validate_2tx_full_with_body`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : header_rlp_len
      bytes 16..24 : body_rlp_len
      bytes 24..   : parent_rlp || header_rlp || body_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid -/
def ziskBlockValidate2txFullWithBodyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1,  8(a7)                # parent_rlp_len\n" ++
  "  ld a3, 16(a7)                # header_rlp_len\n" ++
  "  ld a5, 24(a7)                # body_rlp_len\n" ++
  "  addi a0, a7, 32              # parent_rlp ptr\n" ++
  "  add a2, a0, a1               # header_rlp ptr\n" ++
  "  add a4, a2, a3               # body_rlp ptr\n" ++
  "  li a6, 0xa0010008            # is_valid out\n" ++
  "  jal ra, block_validate_2tx_full_with_body\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbv2fb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  mptBranchPayloadTwoSlotsFunction ++ "\n" ++
  mptBranchNodeEncodeFunction ++ "\n" ++
  mptBranchNodeKeccakFunction ++ "\n" ++
  mptTwoLeafRootIndexedFunction ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  blockValidateTransactionsRootTwoTxFunction ++ "\n" ++
  blockValidate2txFullFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyExtract2txFunction ++ "\n" ++
  blockValidate2txFullWithBodyFunction ++ "\n" ++
  ".Lbv2fb_pdone:"

def ziskBlockValidate2txFullWithBodyDataSection : String :=
  ziskBlockValidate2txFullDataSection ++ "\n" ++
  "bv2fb_struct:\n" ++
  "  .zero 32\n" ++
  "bbe_body_struct:\n" ++
  "  .zero 48\n" ++
  "bbe_tx_count:\n" ++
  "  .zero 8\n" ++
  "bbe_item_off:\n" ++
  "  .zero 8\n" ++
  "bbe_item_len:\n" ++
  "  .zero 8"

def ziskBlockValidate2txFullWithBodyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidate2txFullWithBodyPrologue
  dataAsm     := ziskBlockValidate2txFullWithBodyDataSection
}

/-! ## block_validate_empty_ommers_hash -- PR-K179

    Extract the header's `ommers_hash` field (field 1, 32
    bytes) and verify it equals the post-merge constant
    `EMPTY_OMMERS_HASH = keccak256(rlp([]))`:

      0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347

    Post-merge, all blocks have an empty ommers list (per EIP-3675),
    so this is the canonical per-header check that complements
    K177's body-side ommers-empty assertion. Pre-merge headers
    fail this trivially.

    The 32-byte constant is materialized as a `.data` blob and
    compared 4 × `ld`/`bne` against the field-1 content.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out (is_valid: 1 if matches the constant)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : header parse failure
        2 : field 1 length != 32 bytes -/
def blockValidateEmptyOmmersHashFunction : String :=
  "block_validate_empty_ommers_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # header_rlp ptr\n" ++
  "  mv s1, a1                   # header_rlp len\n" ++
  "  mv s2, a2                   # is_valid out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # ---- Extract header.ommers_hash (field 1) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, bveoh_offset; la a4, bveoh_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbveoh_parse_fail\n" ++
  "  la t0, bveoh_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbveoh_size_fail\n" ++
  "  # 32-byte compare against the post-merge constant.\n" ++
  "  la t0, bveoh_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1                                  # &header[off]\n" ++
  "  la t4, bveoh_empty_ommers_hash\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lbveoh_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lbveoh_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lbveoh_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lbveoh_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbveoh_ret\n" ++
  ".Lbveoh_neq:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbveoh_ret\n" ++
  ".Lbveoh_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbveoh_ret\n" ++
  ".Lbveoh_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbveoh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_validate_empty_ommers_hash`: probe BuildUnit.
    Input layout:
      bytes 0..8  : header_rlp_len
      bytes 8..   : header_rlp
    Output layout:
      bytes  0.. 8 : status (0..2)
      bytes  8..16 : is_valid (1 if matches the constant) -/
def ziskBlockValidateEmptyOmmersHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  addi a0, a7, 16             # header_rlp ptr\n" ++
  "  li a2, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_empty_ommers_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbveoh_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockValidateEmptyOmmersHashFunction ++ "\n" ++
  ".Lbveoh_pdone:"

def ziskBlockValidateEmptyOmmersHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bveoh_offset:\n" ++
  "  .zero 8\n" ++
  "bveoh_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bveoh_empty_ommers_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47"

def ziskBlockValidateEmptyOmmersHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateEmptyOmmersHashPrologue
  dataAsm     := ziskBlockValidateEmptyOmmersHashDataSection
}

/-! ## block_validate_no_withdrawals_pair -- PR-K180

    Pair check for blocks with no withdrawals: confirm both
    sides claim it.

      Header side: `header.withdrawals_root == EMPTY_TRIE_ROOT`
                   (= keccak256(rlp(b''))
                    = 0x56e81f17...3b421)
        via K161 `header_root_is_empty_trie` with field index 16.

      Body side: `block_body.field[2] (withdrawals) == rlp([])`
                 == `0xc0` (the empty-list RLP encoding).
        via K83 `block_body_decode` + 1-byte check.

    Both must hold; mismatch on either side fails the pair.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : body_rlp ptr
      a3 (input)  : body_rlp byte length
      a4 (input)  : u64 out (is_valid: 1 iff both predicates hold)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : body parse failure (not 3-item list)
        2 : header parse failure / field 16 missing
        3 : header field 16 length != 32 -/
def blockValidateNoWithdrawalsPairFunction : String :=
  "block_validate_no_withdrawals_pair:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a2; mv s3, a3                # body\n" ++
  "  mv s4, a4                            # is_valid out\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # ---- Body side: withdrawals (field 2) == 0xc0 ----\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, bvnw_body_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbvnw_body_fail\n" ++
  "  la t0, bvnw_body_struct\n" ++
  "  ld t1, 32(t0)                       # withdrawals_offset\n" ++
  "  ld t2, 40(t0)                       # withdrawals_length\n" ++
  "  li t3, 1\n" ++
  "  bne t2, t3, .Lbvnw_pred_false\n" ++
  "  add t1, s2, t1\n" ++
  "  lbu t4, 0(t1)\n" ++
  "  li t5, 0xc0\n" ++
  "  bne t4, t5, .Lbvnw_pred_false\n" ++
  "  # ---- Header side: withdrawals_root (field 16) == EMPTY_TRIE_ROOT ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 16\n" ++
  "  la a3, bvnw_field_off; la a4, bvnw_field_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbvnw_header_parse_fail\n" ++
  "  la t0, bvnw_field_len; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbvnw_header_size_fail\n" ++
  "  la t0, bvnw_field_off; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1                              # &header.withdrawals_root\n" ++
  "  la t4, bvnw_empty_trie_root\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lbvnw_pred_false\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lbvnw_pred_false\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lbvnw_pred_false\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lbvnw_pred_false\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvnw_ret\n" ++
  ".Lbvnw_pred_false:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvnw_ret\n" ++
  ".Lbvnw_body_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvnw_ret\n" ++
  ".Lbvnw_header_parse_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lbvnw_ret\n" ++
  ".Lbvnw_header_size_fail:\n" ++
  "  li a0, 3\n" ++
  ".Lbvnw_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_block_validate_no_withdrawals_pair`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : body_rlp_len
      bytes 16..   : header_rlp || body_rlp
    Output layout:
      bytes  0.. 8 : status (0..3)
      bytes  8..16 : is_valid -/
def ziskBlockValidateNoWithdrawalsPairPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1,  8(a7)                # header_rlp_len\n" ++
  "  ld a3, 16(a7)                # body_rlp_len\n" ++
  "  addi a0, a7, 24              # header_rlp ptr\n" ++
  "  add a2, a0, a1               # body_rlp ptr\n" ++
  "  li a4, 0xa0010008            # is_valid out\n" ++
  "  jal ra, block_validate_no_withdrawals_pair\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvnw_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockValidateNoWithdrawalsPairFunction ++ "\n" ++
  ".Lbvnw_pdone:"

def ziskBlockValidateNoWithdrawalsPairDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bvnw_body_struct:\n" ++
  "  .zero 48\n" ++
  "bvnw_field_off:\n" ++
  "  .zero 8\n" ++
  "bvnw_field_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bvnw_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21"

def ziskBlockValidateNoWithdrawalsPairProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateNoWithdrawalsPairPrologue
  dataAsm     := ziskBlockValidateNoWithdrawalsPairDataSection
}

end EvmAsm.Codegen
