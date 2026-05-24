/-
  EvmAsm.Codegen.Programs.HeaderFields

  Single-32B-field (and one 20B beneficiary) extractors carved
  out of `EvmAsm.Codegen.Programs.Header` per the file-size
  hard cap. Hosts the K201..K208 family:

    K201  header_extract_state_root         (field 3)
    K202  header_extract_parent_hash        (field 0)
    K203  header_extract_receipts_root      (field 5)
    K204  header_extract_transactions_root  (field 4)
    K205  header_extract_withdrawals_root   (field 16)
    K206  header_extract_ommers_hash        (field 1)
    K207  header_extract_prev_randao        (field 13)
    K208  header_extract_beneficiary        (field 2, 20B)

  All eight functions share the same shape: K20 `rlp_list_nth_item`
  + a fixed-size memcpy + status code (0/1/2). They depend only on
  `rlp_list_nth_item` from `Programs/RlpRead.lean`.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## header_extract_state_root -- PR-K201

    Extract `state_root` (field 3, 32 bytes) from a header RLP
    and copy it to a caller-supplied 32-byte output buffer.

    `header_minimal_decode` already extracts state_root as part
    of a 4-field bundle (parent_hash + state_root + number +
    timestamp); this primitive is the tight standalone variant
    for callers that only need the state_root.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 3 missing
        2 : field 3 length != 32 -/
def headerExtractStateRootFunction : String :=
  "header_extract_state_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, hesr_offset; la a4, hesr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhesr_parse_fail\n" ++
  "  la t0, hesr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhesr_size_fail\n" ++
  "  la t0, hesr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhesr_ret\n" ++
  ".Lhesr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhesr_ret\n" ++
  ".Lhesr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhesr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_state_root`: probe BuildUnit.
    Input layout:
      bytes 0..8 : header_rlp_len
      bytes 8..  : header_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..40 : 32-byte state_root -/
def ziskHeaderExtractStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  addi a0, a7, 16             # header_rlp ptr\n" ++
  "  li a2, 0xa0010008           # 32 B output\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhesr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  ".Lhesr_pdone:"

def ziskHeaderExtractStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractStateRootPrologue
  dataAsm     := ziskHeaderExtractStateRootDataSection
}

/-! ## header_extract_parent_hash -- PR-K202

    Extract `parent_hash` (field 0, 32 bytes) from a header
    RLP and copy it to a caller-supplied 32-byte output buffer.
    Standalone variant of the field-0 access already inside
    K17 / K94 / K173 / K183.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 0 missing
        2 : field 0 length != 32 -/
def headerExtractParentHashFunction : String :=
  "header_extract_parent_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, heph_offset; la a4, heph_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lheph_parse_fail\n" ++
  "  la t0, heph_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lheph_size_fail\n" ++
  "  la t0, heph_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lheph_ret\n" ++
  ".Lheph_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lheph_ret\n" ++
  ".Lheph_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lheph_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_parent_hash`: probe BuildUnit. -/
def ziskHeaderExtractParentHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_parent_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lheph_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractParentHashFunction ++ "\n" ++
  ".Lheph_pdone:"

def ziskHeaderExtractParentHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "heph_offset:\n" ++
  "  .zero 8\n" ++
  "heph_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractParentHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractParentHashPrologue
  dataAsm     := ziskHeaderExtractParentHashDataSection
}

/-! ## header_extract_receipts_root -- PR-K203

    Extract `receipts_root` (field 5, 32 bytes) from a header
    RLP and copy it to a caller-supplied 32-byte output buffer.

    Tight standalone analogue of K201 (state_root, field 3)
    and K202 (parent_hash, field 0).

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 5 missing
        2 : field 5 length != 32 -/
def headerExtractReceiptsRootFunction : String :=
  "header_extract_receipts_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, herr_offset; la a4, herr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lherr_parse_fail\n" ++
  "  la t0, herr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lherr_size_fail\n" ++
  "  la t0, herr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lherr_ret\n" ++
  ".Lherr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lherr_ret\n" ++
  ".Lherr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lherr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_receipts_root`: probe BuildUnit. -/
def ziskHeaderExtractReceiptsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_receipts_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lherr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractReceiptsRootFunction ++ "\n" ++
  ".Lherr_pdone:"

def ziskHeaderExtractReceiptsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "herr_offset:\n" ++
  "  .zero 8\n" ++
  "herr_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractReceiptsRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractReceiptsRootPrologue
  dataAsm     := ziskHeaderExtractReceiptsRootDataSection
}

/-! ## header_extract_transactions_root -- PR-K204

    Extract `transactions_root` (field 4, 32 bytes) from a
    header RLP. Tight standalone analogue of K201 / K202 / K203.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 4 missing
        2 : field 4 length != 32 -/
def headerExtractTransactionsRootFunction : String :=
  "header_extract_transactions_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  la a3, hetr_offset; la a4, hetr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhetr_parse_fail\n" ++
  "  la t0, hetr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhetr_size_fail\n" ++
  "  la t0, hetr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhetr_ret\n" ++
  ".Lhetr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhetr_ret\n" ++
  ".Lhetr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhetr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_transactions_root`: probe BuildUnit. -/
def ziskHeaderExtractTransactionsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_transactions_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhetr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractTransactionsRootFunction ++ "\n" ++
  ".Lhetr_pdone:"

def ziskHeaderExtractTransactionsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hetr_offset:\n" ++
  "  .zero 8\n" ++
  "hetr_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractTransactionsRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractTransactionsRootPrologue
  dataAsm     := ziskHeaderExtractTransactionsRootDataSection
}

/-! ## header_extract_withdrawals_root -- PR-K205

    Extract `withdrawals_root` (field 16, 32 bytes) from a
    Shanghai+ header RLP. Tight standalone analogue of K201..
    K204 for the post-Shanghai field 16.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 16 missing (pre-Shanghai)
        2 : field 16 length != 32 -/
def headerExtractWithdrawalsRootFunction : String :=
  "header_extract_withdrawals_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 16\n" ++
  "  la a3, hewr_offset; la a4, hewr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhewr_parse_fail\n" ++
  "  la t0, hewr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhewr_size_fail\n" ++
  "  la t0, hewr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhewr_ret\n" ++
  ".Lhewr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhewr_ret\n" ++
  ".Lhewr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhewr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_withdrawals_root`: probe BuildUnit. -/
def ziskHeaderExtractWithdrawalsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_withdrawals_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhewr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractWithdrawalsRootFunction ++ "\n" ++
  ".Lhewr_pdone:"

def ziskHeaderExtractWithdrawalsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hewr_offset:\n" ++
  "  .zero 8\n" ++
  "hewr_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractWithdrawalsRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractWithdrawalsRootPrologue
  dataAsm     := ziskHeaderExtractWithdrawalsRootDataSection
}

/-! ## header_extract_ommers_hash -- PR-K206

    Extract `ommers_hash` (field 1, 32 bytes) -- post-merge
    always equal to `keccak256(rlp([])) = 0x1dcc4de8...`. Tight
    standalone analogue of K201..K205. -/
def headerExtractOmmersHashFunction : String :=
  "header_extract_ommers_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, heoh_offset; la a4, heoh_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lheoh_parse_fail\n" ++
  "  la t0, heoh_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lheoh_size_fail\n" ++
  "  la t0, heoh_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lheoh_ret\n" ++
  ".Lheoh_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lheoh_ret\n" ++
  ".Lheoh_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lheoh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskHeaderExtractOmmersHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_ommers_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lheoh_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractOmmersHashFunction ++ "\n" ++
  ".Lheoh_pdone:"

def ziskHeaderExtractOmmersHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "heoh_offset:\n" ++
  "  .zero 8\n" ++
  "heoh_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractOmmersHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractOmmersHashPrologue
  dataAsm     := ziskHeaderExtractOmmersHashDataSection
}

/-! ## header_extract_prev_randao -- PR-K207

    Extract `prev_randao` (field 13, 32 bytes; was `mix_hash`
    pre-merge). Source of post-merge randomness. Tight
    standalone analogue of the field-1/3/5 extractors. -/
def headerExtractPrevRandaoFunction : String :=
  "header_extract_prev_randao:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 13\n" ++
  "  la a3, hepr_offset; la a4, hepr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhepr_parse_fail\n" ++
  "  la t0, hepr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhepr_size_fail\n" ++
  "  la t0, hepr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhepr_ret\n" ++
  ".Lhepr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhepr_ret\n" ++
  ".Lhepr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhepr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskHeaderExtractPrevRandaoPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_prev_randao\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhepr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractPrevRandaoFunction ++ "\n" ++
  ".Lhepr_pdone:"

def ziskHeaderExtractPrevRandaoDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hepr_offset:\n" ++
  "  .zero 8\n" ++
  "hepr_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractPrevRandaoProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractPrevRandaoPrologue
  dataAsm     := ziskHeaderExtractPrevRandaoDataSection
}

/-! ## header_extract_beneficiary -- PR-K208

    Extract `beneficiary` / `coinbase` (field 2, 20 bytes) from
    a header RLP. The 20-byte analogue of the K201..K207 family
    of 32-byte single-field extractors.

    Note: K68 `coinbase_extract_from_header` already exists and
    handles the same field; this is the canonical
    `header_extract_*` shape for consistency with the
    K201..K207 naming convention.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 20-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 2 missing
        2 : field 2 length != 20 -/
def headerExtractBeneficiaryFunction : String :=
  "header_extract_beneficiary:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, hebe_offset; la a4, hebe_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhebe_parse_fail\n" ++
  "  la t0, hebe_length; ld t1, 0(t0)\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lhebe_size_fail\n" ++
  "  la t0, hebe_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  # 20 bytes = 2 × ld + 1 × lwu / sw\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  lwu t4, 16(t3); sw t4, 16(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhebe_ret\n" ++
  ".Lhebe_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhebe_ret\n" ++
  ".Lhebe_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhebe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_beneficiary`: probe BuildUnit. -/
def ziskHeaderExtractBeneficiaryPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_beneficiary\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhebe_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractBeneficiaryFunction ++ "\n" ++
  ".Lhebe_pdone:"

def ziskHeaderExtractBeneficiaryDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hebe_offset:\n" ++
  "  .zero 8\n" ++
  "hebe_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractBeneficiaryProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractBeneficiaryPrologue
  dataAsm     := ziskHeaderExtractBeneficiaryDataSection
}


end EvmAsm.Codegen
