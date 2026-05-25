/-
  EvmAsm.Codegen.Programs.BlockBody

  Block-body extraction + chain-level body aggregators carved
  out of `EvmAsm.Codegen.Programs.Block` per the file-size hard
  cap. Hosts:

    K223  block_body_extract_tx_count
    K224  block_body_extract_withdrawal_count
    K225  block_body_summary
    K226  block_body_validate_empty
    K227  chain_body_total_tx_count
    K228  chain_body_total_withdrawal_count

  Compose K83 `block_body_decode` (Block.lean) + K47 / K20 from
  `RlpRead.lean`. `BlockBody.lean` imports Block + RlpRead.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Block

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_body_extract_tx_count -- PR-K223

    Given a block body RLP, decode it (3-field shape:
    `[txs, ommers, withdrawals]`) and return the number of
    items in the transactions list. Useful for dispatching to
    N-specific validators (K177 for N=2, K188 for N=1, etc.)
    or for chain monitoring.

    Composes K83 `block_body_decode` + K47 `rlp_list_count_items`.

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : u64 out (tx count)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : body RLP parse failure
        2 : transactions list count walk failed -/
def blockBodyExtractTxCountFunction : String :=
  "block_body_extract_tx_count:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body ptr\n" ++
  "  mv s1, a1                   # body len\n" ++
  "  mv s2, a2                   # out u64\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # 1. Decode body to get tx-list (offset, length)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, bbetc_body_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbbetc_parse_fail\n" ++
  "  # 2. Count tx-list items\n" ++
  "  la t0, bbetc_body_struct\n" ++
  "  ld t1, 0(t0)                # txs_offset\n" ++
  "  ld t2, 8(t0)                # txs_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  mv a2, s2                   # write count to caller's u64\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbetc_count_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lbbetc_ret\n" ++
  ".Lbbetc_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbbetc_ret\n" ++
  ".Lbbetc_count_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbbetc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskBlockBodyExtractTxCountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, block_body_extract_tx_count\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbbetc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyExtractTxCountFunction ++ "\n" ++
  ".Lbbetc_pdone:"

def ziskBlockBodyExtractTxCountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bbetc_body_struct:\n" ++
  "  .zero 48"

def ziskBlockBodyExtractTxCountProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockBodyExtractTxCountPrologue
  dataAsm     := ziskBlockBodyExtractTxCountDataSection
}

/-! ## block_body_extract_withdrawal_count -- PR-K224

    Decode a 3-field block body (`[txs, ommers, withdrawals]`)
    and return the cardinality of the withdrawals list. Analogue
    of K223 for field 2.

    Composes K83 `block_body_decode` + K47 `rlp_list_count_items`.

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : u64 out (withdrawal count)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : body RLP parse failure
        2 : withdrawals list count walk failed -/
def blockBodyExtractWithdrawalCountFunction : String :=
  "block_body_extract_withdrawal_count:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # body\n" ++
  "  mv s2, a2                            # out u64\n" ++
  "  sd zero, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, bbewc_body_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbbewc_parse_fail\n" ++
  "  la t0, bbewc_body_struct\n" ++
  "  ld t1, 32(t0)               # withdrawals_offset\n" ++
  "  ld t2, 40(t0)               # withdrawals_length\n" ++
  "  add a0, s0, t1\n" ++
  "  mv a1, t2\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbewc_count_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lbbewc_ret\n" ++
  ".Lbbewc_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbbewc_ret\n" ++
  ".Lbbewc_count_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbbewc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskBlockBodyExtractWithdrawalCountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, block_body_extract_withdrawal_count\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbbewc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyExtractWithdrawalCountFunction ++ "\n" ++
  ".Lbbewc_pdone:"

def ziskBlockBodyExtractWithdrawalCountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bbewc_body_struct:\n" ++
  "  .zero 48"

def ziskBlockBodyExtractWithdrawalCountProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockBodyExtractWithdrawalCountPrologue
  dataAsm     := ziskBlockBodyExtractWithdrawalCountDataSection
}

/-! ## block_body_summary -- PR-K225

    Decode a 3-field block body and return a (tx_count,
    ommers_count, withdrawal_count) tuple as a 24-byte struct
    (three u64s). One-shot body summary primitive useful for
    dispatch / monitoring.

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : 24-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : body RLP parse failure
        2 : a sub-list count walk failed -/
def blockBodySummaryFunction : String :=
  "block_body_summary:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # body ptr\n" ++
  "  mv s1, a1                   # body len\n" ++
  "  mv s2, a2                   # out 24B struct\n" ++
  "  sd zero, 0(s2); sd zero, 8(s2); sd zero, 16(s2)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, bbs_body_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbbs_parse_fail\n" ++
  "  la t0, bbs_body_struct\n" ++
  "  # tx count\n" ++
  "  ld t1, 0(t0); ld t2, 8(t0)\n" ++
  "  add a0, s0, t1; mv a1, t2; mv a2, s2\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbs_count_fail\n" ++
  "  la t0, bbs_body_struct\n" ++
  "  # ommers count\n" ++
  "  ld t1, 16(t0); ld t2, 24(t0)\n" ++
  "  add a0, s0, t1; mv a1, t2; addi a2, s2, 8\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbs_count_fail\n" ++
  "  la t0, bbs_body_struct\n" ++
  "  # withdrawal count\n" ++
  "  ld t1, 32(t0); ld t2, 40(t0)\n" ++
  "  add a0, s0, t1; mv a1, t2; addi a2, s2, 16\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbbs_count_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lbbs_ret\n" ++
  ".Lbbs_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbbs_ret\n" ++
  ".Lbbs_count_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbbs_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskBlockBodySummaryPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, block_body_summary\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbbs_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodySummaryFunction ++ "\n" ++
  ".Lbbs_pdone:"

def ziskBlockBodySummaryDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bbs_body_struct:\n" ++
  "  .zero 48"

def ziskBlockBodySummaryProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockBodySummaryPrologue
  dataAsm     := ziskBlockBodySummaryDataSection
}

/-! ## block_body_validate_empty -- PR-K226

    Predicate: decode the 3-field block body and verify all
    three lists (txs, ommers, withdrawals) are empty (each
    field == `0xc0`, the RLP encoding of `[]`).

    Tight body-side counterpart to K182's body checks; the
    canonical "this body matches a no-execution block" primitive.

    Calling convention:
      a0 (input)  : body_rlp ptr
      a1 (input)  : body_rlp byte length
      a2 (input)  : u64 out (is_valid: 1 if all 3 lists empty)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : body RLP parse failure -/
def blockBodyValidateEmptyFunction : String :=
  "block_body_validate_empty:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # body\n" ++
  "  mv s2, a2                            # is_valid out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, bbve_body_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbbve_parse_fail\n" ++
  "  la t0, bbve_body_struct\n" ++
  "  # Each of the 3 list fields must have length 1 and byte 0xc0\n" ++
  "  li t6, 0xc0\n" ++
  "  # txs (offset=0, len=8)\n" ++
  "  ld t1, 0(t0); ld t2, 8(t0)\n" ++
  "  li t3, 1; bne t2, t3, .Lbbve_pred_false\n" ++
  "  add t1, s0, t1; lbu t4, 0(t1); bne t4, t6, .Lbbve_pred_false\n" ++
  "  # ommers (offset=16, len=24)\n" ++
  "  ld t1, 16(t0); ld t2, 24(t0)\n" ++
  "  li t3, 1; bne t2, t3, .Lbbve_pred_false\n" ++
  "  add t1, s0, t1; lbu t4, 0(t1); bne t4, t6, .Lbbve_pred_false\n" ++
  "  # withdrawals (offset=32, len=40)\n" ++
  "  ld t1, 32(t0); ld t2, 40(t0)\n" ++
  "  li t3, 1; bne t2, t3, .Lbbve_pred_false\n" ++
  "  add t1, s0, t1; lbu t4, 0(t1); bne t4, t6, .Lbbve_pred_false\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  ".Lbbve_pred_false:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbbve_ret\n" ++
  ".Lbbve_parse_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbbve_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskBlockBodyValidateEmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, block_body_validate_empty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbbve_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyValidateEmptyFunction ++ "\n" ++
  ".Lbbve_pdone:"

def ziskBlockBodyValidateEmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bbve_body_struct:\n" ++
  "  .zero 48"

def ziskBlockBodyValidateEmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockBodyValidateEmptyPrologue
  dataAsm     := ziskBlockBodyValidateEmptyDataSection
}

/-! ## chain_body_total_tx_count -- PR-K227

    Aggregate `tx_count` (from K223 `block_body_extract_tx_count`)
    across an N-element array of block bodies into a single u64
    sum. Useful for chain-level metrics ("how many txs in the
    last 256 blocks").

    The sum is plain u64; for mainnet typical block tx counts
    (≤ ~500) and N ≤ 256, the total stays well below 2^64.

    Calling convention:
      a0 (input)  : N (body count)
      a1 (input)  : body_lengths ptr (u64[N])
      a2 (input)  : bodies ptr (concatenated)
      a3 (input)  : u64 out (total_tx_count)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : body parse failure on some body (sum is partial)
        2 : tx-list count walk failed on some body -/
def chainBodyTotalTxCountFunction : String :=
  "chain_body_total_tx_count:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # body_lengths\n" ++
  "  mv s2, a2                   # bodies\n" ++
  "  mv s3, a3                   # out u64\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0                    # i\n" ++
  "  beqz s0, .Lcbttc_done\n" ++
  ".Lcbttc_loop:\n" ++
  "  beq s4, s0, .Lcbttc_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)                # body_len\n" ++
  "  mv a0, s2                   # body_ptr\n" ++
  "  la a2, cbttc_per_count\n" ++
  "  jal ra, block_body_extract_tx_count\n" ++
  "  bnez a0, .Lcbttc_propagate\n" ++
  "  la t0, cbttc_per_count; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3); add t2, t2, t1; sd t2, 0(s3)\n" ++
  "  # advance\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lcbttc_loop\n" ++
  ".Lcbttc_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcbttc_propagate:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainBodyTotalTxCountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  jal ra, chain_body_total_tx_count\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcbttc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyExtractTxCountFunction ++ "\n" ++
  chainBodyTotalTxCountFunction ++ "\n" ++
  ".Lcbttc_pdone:"

def ziskChainBodyTotalTxCountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bbetc_body_struct:\n" ++
  "  .zero 48\n" ++
  "cbttc_per_count:\n" ++
  "  .zero 8"

def ziskChainBodyTotalTxCountProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainBodyTotalTxCountPrologue
  dataAsm     := ziskChainBodyTotalTxCountDataSection
}

/-! ## chain_body_total_withdrawal_count -- PR-K228

    Analogue of K227 for withdrawals: aggregate
    `block_body_extract_withdrawal_count` (K224) across an
    N-element array of block bodies into a single u64 sum.

    Calling convention:
      a0 (input)  : N (body count)
      a1 (input)  : body_lengths ptr (u64[N])
      a2 (input)  : bodies ptr (concatenated)
      a3 (input)  : u64 out (total_withdrawal_count)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : body parse failure
        2 : withdrawal-list count walk failed -/
def chainBodyTotalWithdrawalCountFunction : String :=
  "chain_body_total_withdrawal_count:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0\n" ++
  "  beqz s0, .Lcbtwc_done\n" ++
  ".Lcbtwc_loop:\n" ++
  "  beq s4, s0, .Lcbtwc_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)\n" ++
  "  mv a0, s2\n" ++
  "  la a2, cbtwc_per_count\n" ++
  "  jal ra, block_body_extract_withdrawal_count\n" ++
  "  bnez a0, .Lcbtwc_propagate\n" ++
  "  la t0, cbtwc_per_count; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3); add t2, t2, t1; sd t2, 0(s3)\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lcbtwc_loop\n" ++
  ".Lcbtwc_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcbtwc_propagate:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

def ziskChainBodyTotalWithdrawalCountPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  jal ra, chain_body_total_withdrawal_count\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcbtwc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockBodyExtractWithdrawalCountFunction ++ "\n" ++
  chainBodyTotalWithdrawalCountFunction ++ "\n" ++
  ".Lcbtwc_pdone:"

def ziskChainBodyTotalWithdrawalCountDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bbewc_body_struct:\n" ++
  "  .zero 48\n" ++
  "cbtwc_per_count:\n" ++
  "  .zero 8"

def ziskChainBodyTotalWithdrawalCountProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainBodyTotalWithdrawalCountPrologue
  dataAsm     := ziskChainBodyTotalWithdrawalCountDataSection
}


end EvmAsm.Codegen
