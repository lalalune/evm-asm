/-
  EvmAsm.Codegen.Programs.BlockEmpty

  Empty-block validators (single-block, parent-link, chain) carved
  out of `EvmAsm.Codegen.Programs.BlockValidate` per the file-size
  hard cap. Hosts:

    K181  block_validate_empty_receipts_root
    K182  block_validate_empty_block
    K183  validate_empty_block_with_parent
    K184  validate_empty_block_chain

  Compose K83 / K172 / K72 / K173 / K174 + the K20 / K34 RLP
  helpers + the Keccak bridge.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.HeaderChain
import EvmAsm.Codegen.Programs.Block

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_validate_empty_receipts_root -- PR-K181

    Header field 5 (`receipts_root`) equals `EMPTY_TRIE_ROOT`
    iff the block has zero transactions (since receipts only
    arise from txs -- withdrawals do not generate receipts).
    This primitive checks the predicate directly.

    Used by:
      * Empty-block validators (composed with K179 + K161 + K177).
      * Sanity-check on stateless inputs that claim zero txs.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out (is_valid: 1 if root matches the constant)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : header parse failure / field 5 missing
        2 : field 5 length != 32 -/
def blockValidateEmptyReceiptsRootFunction : String :=
  "block_validate_empty_receipts_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                   # header_rlp ptr\n" ++
  "  mv s1, a1                   # header_rlp len\n" ++
  "  mv s2, a2                   # is_valid out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  # ---- Extract header.receipts_root (field 5) ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, bverr_offset; la a4, bverr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbverr_parse_fail\n" ++
  "  la t0, bverr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbverr_size_fail\n" ++
  "  la t0, bverr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  la t4, bverr_empty_trie_root\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lbverr_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lbverr_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lbverr_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lbverr_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbverr_ret\n" ++
  ".Lbverr_neq:\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbverr_ret\n" ++
  ".Lbverr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbverr_ret\n" ++
  ".Lbverr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbverr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_validate_empty_receipts_root`: probe BuildUnit.
    Input layout:
      bytes 0..8 : header_rlp_len
      bytes 8..  : header_rlp
    Output layout:
      bytes 0..8  : status (0..2)
      bytes 8..16 : is_valid -/
def ziskBlockValidateEmptyReceiptsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  addi a0, a7, 16             # header_rlp ptr\n" ++
  "  li a2, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_empty_receipts_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbverr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockValidateEmptyReceiptsRootFunction ++ "\n" ++
  ".Lbverr_pdone:"

def ziskBlockValidateEmptyReceiptsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bverr_offset:\n" ++
  "  .zero 8\n" ++
  "bverr_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bverr_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21"

def ziskBlockValidateEmptyReceiptsRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateEmptyReceiptsRootPrologue
  dataAsm     := ziskBlockValidateEmptyReceiptsRootDataSection
}

/-! ## block_validate_empty_block -- PR-K182

    Validator for a *completely empty* post-merge block:
    zero transactions, empty ommers, no withdrawals. Used as a
    fast-path or smoke-test entry point for stateless inputs
    that promise no body execution.

    Predicates checked (all must hold):

      Header side:
        H1. transactions_root  == EMPTY_TRIE_ROOT     (K171-style constant)
        H2. ommers_hash        == EMPTY_OMMERS_HASH   (K179)
        H3. receipts_root      == EMPTY_TRIE_ROOT     (K181)
        H4. withdrawals_root   == EMPTY_TRIE_ROOT     (K180 header side)
      Body side:
        B1. body has 3 fields  [txs, ommers, withdrawals]
        B2. txs        == rlp([]) == 0xc0
        B3. ommers     == rlp([]) == 0xc0
        B4. withdrawals == rlp([]) == 0xc0

    All eight checks compose into a single is_valid u64.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : body_rlp ptr
      a3 (input)  : body_rlp byte length
      a4 (input)  : u64 out (is_valid)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : body parse failure
        2 : header parse failure
        3 : header field-size mismatch (some 32-byte root field
            had length != 32) -/
def blockValidateEmptyBlockFunction : String :=
  "block_validate_empty_block:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a2; mv s3, a3                # body\n" ++
  "  mv s4, a4                            # is_valid out\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # ---- Body side: 3 fields, all empty ----\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, beb_body_struct\n" ++
  "  jal ra, block_body_decode\n" ++
  "  bnez a0, .Lbeb_body_fail\n" ++
  "  # B2..B4: each field length must be 1 and the byte 0xc0\n" ++
  "  la t0, beb_body_struct\n" ++
  "  li t6, 0xc0\n" ++
  "  ld t1,  0(t0); ld t2,  8(t0)        # txs (off, len)\n" ++
  "  li t3, 1; bne t2, t3, .Lbeb_pred_false\n" ++
  "  add t1, s2, t1; lbu t4, 0(t1); bne t4, t6, .Lbeb_pred_false\n" ++
  "  ld t1, 16(t0); ld t2, 24(t0)        # ommers (off, len)\n" ++
  "  li t3, 1; bne t2, t3, .Lbeb_pred_false\n" ++
  "  add t1, s2, t1; lbu t4, 0(t1); bne t4, t6, .Lbeb_pred_false\n" ++
  "  ld t1, 32(t0); ld t2, 40(t0)        # withdrawals (off, len)\n" ++
  "  li t3, 1; bne t2, t3, .Lbeb_pred_false\n" ++
  "  add t1, s2, t1; lbu t4, 0(t1); bne t4, t6, .Lbeb_pred_false\n" ++
  "  # ---- Header side: 4 root checks ----\n" ++
  "  # H1: transactions_root (field 4) == EMPTY_TRIE_ROOT\n" ++
  "  li a0, 4\n" ++
  "  la a1, beb_empty_trie_root\n" ++
  "  jal ra, beb_check_header_field_32B\n" ++
  "  beqz a0, .Lbeb_pred_false\n" ++
  "  bltz a0, .Lbeb_header_size_fail\n" ++
  "  li t0, 2; beq a0, t0, .Lbeb_header_parse_fail\n" ++
  "  # H2: ommers_hash (field 1) == EMPTY_OMMERS_HASH\n" ++
  "  li a0, 1\n" ++
  "  la a1, beb_empty_ommers_hash\n" ++
  "  jal ra, beb_check_header_field_32B\n" ++
  "  beqz a0, .Lbeb_pred_false\n" ++
  "  li t0, 3; beq a0, t0, .Lbeb_header_size_fail\n" ++
  "  li t0, 2; beq a0, t0, .Lbeb_header_parse_fail\n" ++
  "  # H3: receipts_root (field 5) == EMPTY_TRIE_ROOT\n" ++
  "  li a0, 5\n" ++
  "  la a1, beb_empty_trie_root\n" ++
  "  jal ra, beb_check_header_field_32B\n" ++
  "  beqz a0, .Lbeb_pred_false\n" ++
  "  li t0, 3; beq a0, t0, .Lbeb_header_size_fail\n" ++
  "  li t0, 2; beq a0, t0, .Lbeb_header_parse_fail\n" ++
  "  # H4: withdrawals_root (field 16) == EMPTY_TRIE_ROOT\n" ++
  "  li a0, 16\n" ++
  "  la a1, beb_empty_trie_root\n" ++
  "  jal ra, beb_check_header_field_32B\n" ++
  "  beqz a0, .Lbeb_pred_false\n" ++
  "  li t0, 3; beq a0, t0, .Lbeb_header_size_fail\n" ++
  "  li t0, 2; beq a0, t0, .Lbeb_header_parse_fail\n" ++
  "  # All eight checks passed.\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbeb_ret\n" ++
  ".Lbeb_pred_false:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbeb_ret\n" ++
  ".Lbeb_body_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbeb_ret\n" ++
  ".Lbeb_header_parse_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lbeb_ret\n" ++
  ".Lbeb_header_size_fail:\n" ++
  "  li a0, 3\n" ++
  ".Lbeb_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret\n" ++
  "\n" ++
  "# Helper: check header[a0 = field_idx] is a 32B value equal to\n" ++
  "# the constant at a1 (32B ptr). Reads s0/s1 = header_rlp ptr/len.\n" ++
  "# Returns a0: 1 = match, 0 = predicate false, 2 = parse fail,\n" ++
  "# 3 = size fail.\n" ++
  "beb_check_header_field_32B:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd a1, 8(sp)                          # save constant ptr\n" ++
  "  mv a2, a0\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a3, beb_off; la a4, beb_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbeb_chk_parse\n" ++
  "  la t0, beb_len; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbeb_chk_size\n" ++
  "  la t0, beb_off; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4, 8(sp)                          # constant ptr\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lbeb_chk_neq\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lbeb_chk_neq\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lbeb_chk_neq\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lbeb_chk_neq\n" ++
  "  li a0, 1\n" ++
  "  j .Lbeb_chk_ret\n" ++
  ".Lbeb_chk_neq:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbeb_chk_ret\n" ++
  ".Lbeb_chk_parse:\n" ++
  "  li a0, 2\n" ++
  "  j .Lbeb_chk_ret\n" ++
  ".Lbeb_chk_size:\n" ++
  "  li a0, 3\n" ++
  ".Lbeb_chk_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_block_validate_empty_block`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..16 : body_rlp_len
      bytes 16..   : header_rlp || body_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid -/
def ziskBlockValidateEmptyBlockPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1,  8(a7)                # header_rlp_len\n" ++
  "  ld a3, 16(a7)                # body_rlp_len\n" ++
  "  addi a0, a7, 24              # header_rlp ptr\n" ++
  "  add a2, a0, a1               # body_rlp ptr\n" ++
  "  li a4, 0xa0010008            # is_valid out\n" ++
  "  jal ra, block_validate_empty_block\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbeb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockValidateEmptyBlockFunction ++ "\n" ++
  ".Lbeb_pdone:"

def ziskBlockValidateEmptyBlockDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "beb_body_struct:\n" ++
  "  .zero 48\n" ++
  "beb_off:\n" ++
  "  .zero 8\n" ++
  "beb_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "beb_empty_trie_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  ".balign 8\n" ++
  "beb_empty_ommers_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47"

def ziskBlockValidateEmptyBlockProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateEmptyBlockPrologue
  dataAsm     := ziskBlockValidateEmptyBlockDataSection
}

/-! ## validate_empty_block_with_parent -- PR-K183

    Full validator for an empty post-merge block linked to a
    parent: composes K174 `validate_header_pair` (4 pair
    invariants between parent and child header) with K182
    `block_validate_empty_block` (4 header empty-root checks +
    4 body emptiness checks).

    Per-block predicate (all 12 must hold):

      A. validate_header_pair(parent, child) accepts:
         child.parent_hash == keccak256(parent_rlp)
         child.number == parent.number + 1
         child.timestamp > parent.timestamp
         check_gas_limit(child, parent) == 0
      B. block_validate_empty_block(child, body) accepts:
         child.transactions_root  == EMPTY_TRIE_ROOT
         child.ommers_hash        == EMPTY_OMMERS_HASH
         child.receipts_root      == EMPTY_TRIE_ROOT
         child.withdrawals_root   == EMPTY_TRIE_ROOT
         body.txs                 == 0xc0
         body.ommers              == 0xc0
         body.withdrawals         == 0xc0

    The is_valid u64 is 1 iff all 12 predicates hold.

    Calling convention:
      a0 (input)  : parent_rlp ptr
      a1 (input)  : parent_rlp byte length
      a2 (input)  : child_rlp ptr
      a3 (input)  : child_rlp byte length
      a4 (input)  : body_rlp ptr
      a5 (input)  : body_rlp byte length
      a6 (input)  : u64 out (is_valid)
      ra (input)  : return
      a0 (output) :
        0       : success -- predicate written
        1..4    : propagated from validate_header_pair
                  (1 child parse, 2 phash size, 3 parent field,
                   4 child field)
        11..13  : propagated from block_validate_empty_block
                  (11 body parse, 12 header parse, 13 header size) -/
def validateEmptyBlockWithParentFunction : String :=
  "validate_empty_block_with_parent:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # parent\n" ++
  "  mv s2, a2; mv s3, a3                # child header\n" ++
  "  mv s4, a4; mv s5, a5                # body\n" ++
  "  mv s6, a6                            # is_valid out\n" ++
  "  sd zero, 0(s6)\n" ++
  "  # ---- (A) Pair check ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s2; mv a3, s3\n" ++
  "  la a4, vebwp_pair_valid\n" ++
  "  jal ra, validate_header_pair\n" ++
  "  beqz a0, .Lvebwp_pair_status_ok\n" ++
  "  # Propagate K174 status (1..4) unchanged.\n" ++
  "  j .Lvebwp_ret\n" ++
  ".Lvebwp_pair_status_ok:\n" ++
  "  la t0, vebwp_pair_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lvebwp_pred_false\n" ++
  "  # ---- (B) Empty-block check ----\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  mv a2, s4; mv a3, s5\n" ++
  "  la a4, vebwp_empty_valid\n" ++
  "  jal ra, block_validate_empty_block\n" ++
  "  beqz a0, .Lvebwp_empty_status_ok\n" ++
  "  # K182 returns 1..3 -- shift to 11..13.\n" ++
  "  addi a0, a0, 10\n" ++
  "  j .Lvebwp_ret\n" ++
  ".Lvebwp_empty_status_ok:\n" ++
  "  la t0, vebwp_empty_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lvebwp_pred_false\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvebwp_ret\n" ++
  ".Lvebwp_pred_false:\n" ++
  "  sd zero, 0(s6)\n" ++
  "  li a0, 0\n" ++
  ".Lvebwp_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_validate_empty_block_with_parent`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : child_rlp_len
      bytes 16..24 : body_rlp_len
      bytes 24..   : parent_rlp || child_rlp || body_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid -/
def ziskValidateEmptyBlockWithParentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1,  8(a7)                # parent_rlp_len\n" ++
  "  ld a3, 16(a7)                # child_rlp_len\n" ++
  "  ld a5, 24(a7)                # body_rlp_len\n" ++
  "  addi a0, a7, 32              # parent_rlp ptr\n" ++
  "  add a2, a0, a1               # child_rlp ptr\n" ++
  "  add a4, a2, a3               # body_rlp ptr\n" ++
  "  li a6, 0xa0010008            # is_valid out\n" ++
  "  jal ra, validate_empty_block_with_parent\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvebwp_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockValidateEmptyBlockFunction ++ "\n" ++
  validateEmptyBlockWithParentFunction ++ "\n" ++
  ".Lvebwp_pdone:"

def ziskValidateEmptyBlockWithParentDataSection : String :=
  ziskBlockValidateEmptyBlockDataSection ++ "\n" ++
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
  "vebwp_pair_valid:\n" ++
  "  .zero 8\n" ++
  "vebwp_empty_valid:\n" ++
  "  .zero 8"

def ziskValidateEmptyBlockWithParentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateEmptyBlockWithParentPrologue
  dataAsm     := ziskValidateEmptyBlockWithParentDataSection
}

/-! ## validate_empty_block_chain -- PR-K184

    Iterate `validate_empty_block_with_parent` (K183) over an
    N-element chain of (header, body) pairs and verify every
    link in the chain is a valid empty-block step. This is the
    direct analogue of K175 `validate_header_chain` extended to
    cover both header AND body sides; it is the natural
    endpoint of stateless validation for the all-empty fast path.

    Input layout (length-prefix tables + flat byte blob):

      headers[0..N) -- N header RLPs concatenated
      bodies[0..N)  -- N body  RLPs concatenated

    The first header is the *parent* of headers[1]; we verify
    `validate_empty_block_with_parent(headers[i], headers[i+1],
                                       bodies[i+1])`
    for i in 0..N-1, i.e. N-1 link checks. The first body is
    not used (the parent's body is upstream); we only validate
    the empty-block predicate against bodies[1..N).

    Vacuous-true on N == 0 and N == 1 (no link to verify).

    Calling convention:
      a0 (input)  : N (block count)
      a1 (input)  : header_lengths ptr (u64[N])
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : body_lengths ptr   (u64[N])
      a4 (input)  : bodies ptr  (concatenated)
      a5 (input)  : u64 out (is_valid)
      a6 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        nonzero : propagated status from
                  `validate_empty_block_with_parent` for the
                  first failing pair -/
def validateEmptyBlockChainFunction : String :=
  "validate_empty_block_chain:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths ptr\n" ++
  "  mv s2, a2                   # headers ptr\n" ++
  "  mv s3, a3                   # body_lengths ptr\n" ++
  "  mv s4, a4                   # bodies ptr\n" ++
  "  mv s5, a5                   # is_valid out\n" ++
  "  mv s6, a6                   # first_bad_index out\n" ++
  "  sd zero, 0(s5)\n" ++
  "  sd zero, 0(s6)\n" ++
  "  # Vacuous-true for N == 0 or N == 1.\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lvebc_vacuous\n" ++
  "  # Walking pointers (all callee-saved across inner calls):\n" ++
  "  #   s7 = parent header ptr\n" ++
  "  #   s8 = child header ptr (computed each iter)\n" ++
  "  #   s9 = i (current index)\n" ++
  "  #   s10 = bodies running ptr (for body[i+1])\n" ++
  "  mv s7, s2                   # parent header ptr = headers[0]\n" ++
  "  mv s10, s4                  # bodies ptr starts at bodies[0]\n" ++
  "  # Skip body[0] (parent's body, not used in this chain shape)\n" ++
  "  ld t0, 0(s3)\n" ++
  "  add s10, s10, t0\n" ++
  "  li s9, 0                    # i = 0\n" ++
  ".Lvebc_loop:\n" ++
  "  addi t0, s9, 1\n" ++
  "  beq t0, s0, .Lvebc_done\n" ++
  "  # parent_len = header_lengths[i]; child_len = header_lengths[i+1]\n" ++
  "  slli t1, s9, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld a1, 0(t1)                # parent_len (callee passes through args)\n" ++
  "  ld a3, 8(t1)                # child_len\n" ++
  "  add s8, s7, a1              # child ptr = parent ptr + parent_len\n" ++
  "  # body_len = body_lengths[i+1]\n" ++
  "  slli t4, t0, 3\n" ++
  "  add t4, s3, t4\n" ++
  "  ld a5, 0(t4)                # body_len\n" ++
  "  # Stash advance deltas in callee-saved s11 (parent_len already\n" ++
  "  # consumed via a1) and reuse a1/a5 across the call -- they're\n" ++
  "  # caller-saved but we re-derive them after the call below.\n" ++
  "  mv a0, s7\n" ++
  "  mv a2, s8\n" ++
  "  mv a4, s10\n" ++
  "  la a6, vebc_pair_valid\n" ++
  "  jal ra, validate_empty_block_with_parent\n" ++
  "  bnez a0, .Lvebc_status_fail\n" ++
  "  la t0, vebc_pair_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lvebc_pred_false\n" ++
  "  # Advance to next pair -- re-derive parent_len and body_len\n" ++
  "  # since t-regs and a-regs were clobbered by the call.\n" ++
  "  slli t1, s9, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld t2, 0(t1)                # parent_len[i]\n" ++
  "  add s7, s7, t2              # parent ptr += parent_len\n" ++
  "  addi t3, s9, 1\n" ++
  "  slli t3, t3, 3\n" ++
  "  add t3, s3, t3\n" ++
  "  ld t4, 0(t3)                # body_len[i+1]\n" ++
  "  add s10, s10, t4            # bodies ptr += body_len\n" ++
  "  addi s9, s9, 1\n" ++
  "  j .Lvebc_loop\n" ++
  ".Lvebc_done:\n" ++
  ".Lvebc_vacuous:\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvebc_ret\n" ++
  ".Lvebc_pred_false:\n" ++
  "  sd zero, 0(s5)\n" ++
  "  sd s9, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvebc_ret\n" ++
  ".Lvebc_status_fail:\n" ++
  "  sd s9, 0(s6)\n" ++
  ".Lvebc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_validate_empty_block_chain`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths (u64[N])
      bytes  8+8N..8+16N : body_lengths (u64[N])
      bytes  8+16N.. : concatenated headers || concatenated bodies
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid
      bytes 16..24 : first_bad_index -/
def ziskValidateEmptyBlockChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16             # header_lengths ptr\n" ++
  "  slli t0, a0, 3              # 8*N\n" ++
  "  add a3, a1, t0              # body_lengths ptr\n" ++
  "  add a2, a3, t0              # headers ptr = body_lengths + 8N\n" ++
  "  # bodies ptr = headers + sum(header_lengths)\n" ++
  "  mv a4, a2\n" ++
  "  mv t1, a1                   # header_lengths cursor\n" ++
  "  mv t2, a0                   # remaining\n" ++
  ".Lvebc_sum:\n" ++
  "  beqz t2, .Lvebc_sum_done\n" ++
  "  ld t3, 0(t1)\n" ++
  "  add a4, a4, t3\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  j .Lvebc_sum\n" ++
  ".Lvebc_sum_done:\n" ++
  "  li a5, 0xa0010008           # is_valid out\n" ++
  "  li a6, 0xa0010010           # first_bad_index out\n" ++
  "  jal ra, validate_empty_block_chain\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvebc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  blockBodyDecodeFunction ++ "\n" ++
  blockValidateEmptyBlockFunction ++ "\n" ++
  validateEmptyBlockWithParentFunction ++ "\n" ++
  validateEmptyBlockChainFunction ++ "\n" ++
  ".Lvebc_pdone:"

def ziskValidateEmptyBlockChainDataSection : String :=
  ziskValidateEmptyBlockWithParentDataSection ++ "\n" ++
  "vebc_pair_valid:\n" ++
  "  .zero 8"

def ziskValidateEmptyBlockChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateEmptyBlockChainPrologue
  dataAsm     := ziskValidateEmptyBlockChainDataSection
}


end EvmAsm.Codegen
